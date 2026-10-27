module

public import CFSG.RankThree.GF2n.Smith81.S81XU2
public import CFSG.RankThree.GF2n.Smith81.S81VDefs

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG CFSG.Open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary Module
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.U6Cube

variable {F : Type} [Field F] {σ : F ≃+* F}

private theorem herm_e3uT0Vec_zero [CharP F 2] (i j : Fin 3) :
    herm σ (e3uT0Vec i) (e3uT0Vec j) = 0 := by
  have h11 : (1 : F) + 1 = 0 := by
    rw [one_add_one_eq_two]
    exact CharTwo.two_eq_zero
  fin_cases i <;> fin_cases j <;> simp [herm, e3uT0Vec, Fin.sum_univ_six, h11]

private theorem linearIndependent_e3uT0Vec :
    LinearIndependent F (e3uT0Vec : Fin 3 → Fin 6 → F) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 := congrFun hc 0
  have h2 := congrFun hc 2
  have h4 := congrFun hc 4
  simp [Fin.sum_univ_three, e3uT0Vec, Finset.sum_apply] at h0 h2 h4
  intro i
  fin_cases i
  · exact h0
  · exact h2
  · exact h4

private theorem herm_span_e3uT0Vec_zero [CharP F 2] {x y : Fin 6 → F}
    (hx : x ∈ Submodule.span F (Set.range (e3uT0Vec : Fin 3 → Fin 6 → F)))
    (hy : y ∈ Submodule.span F (Set.range (e3uT0Vec : Fin 3 → Fin 6 → F))) :
    herm σ x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact herm_e3uT0Vec_zero i j
    | zero => exact herm_zero_right σ _
    | add y y' _ _ h1 h2 => rw [herm_add_right, h1, h2, add_zero]
    | smul c y _ h1 => rw [herm_smul_right, h1, mul_zero]
  | zero => exact herm_zero_left σ _
  | add x x' _ _ h1 h2 => rw [herm_add_left, h1, h2, add_zero]
  | smul c x _ h1 => rw [herm_smul_left, h1, mul_zero]

theorem isTotIso_W₀ [CharP F 2] : IsTotIso σ (W₀ F) ∧ finrank F (W₀ F) = 3 := by
  refine ⟨fun x hx y hy => herm_span_e3uT0Vec_zero hx hy, ?_⟩
  show finrank F (Submodule.span F (Set.range (e3uT0Vec : Fin 3 → Fin 6 → F))) = 3
  rw [finrank_span_eq_card linearIndependent_e3uT0Vec, Fintype.card_fin]

theorem e3uU0Sub_eq_ptStab : e3uU0Sub σ = PtStab σ (W₀ F) := by
  ext g
  rw [mem_ptStab (σ := σ)]
  have hg_iff : g ∈ e3uU0Sub σ ↔ ∀ i : Fin 3,
      ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec i) = e3uT0Vec i :=
    Iff.rfl
  rw [hg_iff]
  constructor
  · intro hg w hw
    have hw' : w ∈ Submodule.span F (Set.range (e3uT0Vec : Fin 3 → Fin 6 → F)) := hw
    clear hw
    induction hw' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [CFSG.ClassicalGroups.Unitary.smul_def]
      exact hg i
    | zero => exact smul_zero g
    | add x y _ _ h1 h2 => rw [smul_add, h1, h2]
    | smul c x _ h1 => rw [smul_comm, h1]
  · intro hg i
    have h := hg (e3uT0Vec i) (Submodule.subset_span (Set.mem_range_self i))
    rw [CFSG.ClassicalGroups.Unitary.smul_def] at h
    exact h

theorem exists_su_smul_W₀ [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ)
    {W : Submodule F (Fin 6 → F)} (hti : IsTotIso σ W) (h3 : finrank F W = 3) :
    ∃ g : SUid σ 6, ∀ v, v ∈ W ↔ ∃ w ∈ W₀ F, g • w = v := by
  obtain ⟨b⟩ : Nonempty (Basis (Fin 3) F W) := ⟨Module.finBasisOfFinrankEq F W h3⟩
  obtain ⟨vv, hvv⟩ : ∃ vv : Fin 3 → Fin 6 → F, vv = fun i => (b i : Fin 6 → F) := ⟨_, rfl⟩
  have hvvW : ∀ i, vv i ∈ W := by
    intro i
    rw [hvv]
    exact (b i).2
  have hli : LinearIndependent F vv := by
    rw [hvv]
    exact b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hiso : ∀ i j, ∑ k, σ (vv i k) * vv j k = 0 := fun i j => hti _ (hvvW i) _ (hvvW j)
  have hrep : ∀ v ∈ W, ∃ c : Fin 3 → F, ∑ i, c i • vv i = v := by
    intro v hv
    refine ⟨b.repr ⟨v, hv⟩, ?_⟩
    have h := congrArg Subtype.val (b.sum_repr ⟨v, hv⟩)
    rw [hvv]
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h
  obtain ⟨g, l, hl0, h0, h1, h2⟩ := u6_exists_su_of_ti hσ (u6_iotaMulti_ne_zero_of_li hli) hiso
  have hg0 : g • e3uT0Vec 0 = l • vv 0 := by
    rw [CFSG.ClassicalGroups.Unitary.smul_def]
    exact h0
  have hg1 : g • e3uT0Vec 1 = vv 1 := by
    rw [CFSG.ClassicalGroups.Unitary.smul_def]
    exact h1
  have hg2 : g • e3uT0Vec 2 = vv 2 := by
    rw [CFSG.ClassicalGroups.Unitary.smul_def]
    exact h2
  have hE : ∀ i : Fin 3, e3uT0Vec i ∈ W₀ F := fun i =>
    Submodule.subset_span (Set.mem_range_self i)
  have hgE : ∀ i : Fin 3, g • e3uT0Vec i ∈ W := by
    intro i
    fin_cases i
    · show g • e3uT0Vec 0 ∈ W
      rw [hg0]
      exact W.smul_mem l (hvvW 0)
    · show g • e3uT0Vec 1 ∈ W
      rw [hg1]
      exact hvvW 1
    · show g • e3uT0Vec 2 ∈ W
      rw [hg2]
      exact hvvW 2
  have hmem : ∀ w ∈ W₀ F, g • w ∈ W := by
    intro w hw
    have hw' : w ∈ Submodule.span F (Set.range (e3uT0Vec : Fin 3 → Fin 6 → F)) := hw
    clear hw
    induction hw' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hgE i
    | zero => rw [smul_zero]; exact W.zero_mem
    | add x y _ _ h1 h2 => rw [smul_add]; exact W.add_mem h1 h2
    | smul c x _ h1 => rw [smul_comm]; exact W.smul_mem c h1
  refine ⟨g, fun v => ⟨fun hvW => ?_, fun h => ?_⟩⟩
  · obtain ⟨c, hc⟩ := hrep v hvW
    refine ⟨(c 0 * l⁻¹) • e3uT0Vec 0 + c 1 • e3uT0Vec 1 + c 2 • e3uT0Vec 2, ?_, ?_⟩
    · exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (hE 0))
        (Submodule.smul_mem _ _ (hE 1))) (Submodule.smul_mem _ _ (hE 2))
    · have hc0 : c 0 * l⁻¹ * l = c 0 := by
        rw [mul_assoc, inv_mul_cancel₀ hl0, mul_one]
      rw [smul_add, smul_add, smul_comm g (c 0 * l⁻¹), smul_comm g (c 1), smul_comm g (c 2),
        hg0, hg1, hg2, smul_smul, hc0, ← hc, Fin.sum_univ_three]
  · obtain ⟨w, hw, rfl⟩ := h
    exact hmem w hw

theorem ptStab_conj {W W' : Submodule F (Fin 6 → F)} (g : SUid σ 6)
    (hW' : ∀ v, v ∈ W' ↔ ∃ w ∈ W, g • w = v) :
    PtStab σ W' = (PtStab σ W).map (MulAut.conj g).toMonoidHom := by
  ext h
  rw [mem_ptStab (σ := σ), Subgroup.mem_map]
  constructor
  · intro hh
    refine ⟨g⁻¹ * h * g, ?_, ?_⟩
    · rw [mem_ptStab (σ := σ)]
      intro w hw
      have h1 : h • g • w = g • w := hh (g • w) ((hW' (g • w)).mpr ⟨w, hw, rfl⟩)
      rw [mul_smul, mul_smul, h1, inv_smul_smul]
    · show g * (g⁻¹ * h * g) * g⁻¹ = h
      group
  · rintro ⟨k, hk, rfl⟩ v hv
    obtain ⟨w, hw, rfl⟩ := (hW' v).mp hv
    have hkw : k • w = w := (mem_ptStab (σ := σ)).mp hk w hw
    show (g * k * g⁻¹) • g • w = g • w
    rw [mul_smul, inv_smul_smul, mul_smul, hkw]

end CFSG.RankThree.GF2n.Smith81.S81V
