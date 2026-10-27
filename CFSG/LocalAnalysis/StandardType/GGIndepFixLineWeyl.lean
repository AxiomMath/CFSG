module

public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineFamilyDefs
public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep3
public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep4
public import CFSG.LocalAnalysis.StandardType.GGFLWReflForm
public import CFSG.LocalAnalysis.StandardType.GGFLWTree
public import CFSG.LocalAnalysis.StandardType.GGFLWPairing

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l6w4_nonempty_index {ι : Type} {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M) :
    Nonempty ι := by
  rcases hM with ⟨n, e, hn, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩
  · exact ⟨e ⟨0, by omega⟩⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩

private lemma l6w4_nonempty_fintype {ι : Type} {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M) :
    Nonempty (Fintype ι) := by
  rcases hM with ⟨n, e, hn, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩
  · exact ⟨Fintype.ofEquiv (Fin n) e⟩
  · exact ⟨Fintype.ofEquiv (Fin 6) e⟩
  · exact ⟨Fintype.ofEquiv (Fin 7) e⟩
  · exact ⟨Fintype.ofEquiv (Fin 8) e⟩
  · exact ⟨Fintype.ofEquiv (Fin 4) e⟩
  · exact ⟨Fintype.ofEquiv (Fin 2) e⟩

private lemma l6w4_six_bond_card {ι : Type} [Fintype ι] {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) {i j : ι} (h6 : M.M i j = 6) : Fintype.card ι = 2 := by
  rcases hM with ⟨n, e, hn, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ | ⟨e, hF⟩ |
    ⟨e, hG⟩
  · exfalso
    subst hA
    change (CoxeterMatrix.A n).M (e.symm i) (e.symm j) = 6 at h6
    simp only [CoxeterMatrix.A, Matrix.of_apply] at h6
    split_ifs at h6 <;> omega
  · exfalso
    subst hB
    change (CoxeterMatrix.B n).M (e.symm i) (e.symm j) = 6 at h6
    simp only [CoxeterMatrix.B, Matrix.of_apply] at h6
    split_ifs at h6 <;> omega
  · exfalso
    subst hD
    change (ggCoxeterMatrixD n).M (e.symm i) (e.symm j) = 6 at h6
    simp only [ggCoxeterMatrixD, Matrix.of_apply] at h6
    split_ifs at h6 <;> omega
  · exfalso
    subst hE
    change CoxeterMatrix.E₆.M (e.symm i) (e.symm j) = 6 at h6
    generalize e.symm i = a at h6
    generalize e.symm j = b at h6
    fin_cases a <;> fin_cases b <;> simp [CoxeterMatrix.E₆] at h6
  · exfalso
    subst hE
    change CoxeterMatrix.E₇.M (e.symm i) (e.symm j) = 6 at h6
    generalize e.symm i = a at h6
    generalize e.symm j = b at h6
    fin_cases a <;> fin_cases b <;> simp [CoxeterMatrix.E₇] at h6
  · exfalso
    subst hE
    change CoxeterMatrix.E₈.M (e.symm i) (e.symm j) = 6 at h6
    generalize e.symm i = a at h6
    generalize e.symm j = b at h6
    fin_cases a <;> fin_cases b <;> simp [CoxeterMatrix.E₈] at h6
  · exfalso
    subst hF
    change CoxeterMatrix.F₄.M (e.symm i) (e.symm j) = 6 at h6
    generalize e.symm i = a at h6
    generalize e.symm j = b at h6
    fin_cases a <;> fin_cases b <;> simp [CoxeterMatrix.F₄] at h6
  · exact (Fintype.card_congr e.symm).trans (Fintype.card_fin 2)

theorem ggFixLine_not_linWeyl {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x)
    (hF2 : Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) = 2) :
    ¬ ZS.LinWeyl p (ggFixLineQ S) := by
  intro hlw
  obtain ⟨ι', M, hM, f, hf⟩ := hlw
  haveI : Fintype ι' := Classical.choice (l6w4_nonempty_fintype hM)
  haveI : DecidableEq ι' := Classical.decEq ι'
  let sg : ι' → (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) :=
    fun i => (f (M.simple i) : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s))
  choose c β hc hβ hform using fun i => ggFLW_isRefl_form S.odd (hf i)
  have hgen : Subgroup.closure (Set.range M.simple) = ⊤ := by
    have hh := CoxeterSystem.subgroup_closure_range_simple (cs := M.toCoxeterSystem)
    simpa [CoxeterMatrix.toCoxeterSystem_simple] using hh
  have hfs : Subgroup.closure (Set.range (fun i => f (M.simple i))) = ⊤ := by
    have hrange : Set.range (fun i => f (M.simple i)) = f '' Set.range M.simple := by
      ext y; constructor
      · rintro ⟨i, rfl⟩; exact ⟨M.simple i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    rw [hrange]
    change Subgroup.closure (f.toMonoidHom '' Set.range M.simple) = ⊤
    rw [← MonoidHom.map_closure f.toMonoidHom (Set.range M.simple), hgen, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr f.surjective
  have hQgen : ggFixLineQ S = Subgroup.closure (Set.range sg) := by
    have hrange : Set.range sg =
        (Subgroup.subtype (ggFixLineQ S)) '' Set.range (fun i => f (M.simple i)) := by
      ext y; constructor
      · rintro ⟨i, rfl⟩; exact ⟨f (M.simple i), ⟨i, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    have hh : Subgroup.closure (Set.range sg) = ggFixLineQ S := by
      rw [hrange, ← MonoidHom.map_closure (Subgroup.subtype (ggFixLineQ S))
        (Set.range (fun i => f (M.simple i))), hfs, Subgroup.map_top]
      exact Subgroup.range_subtype (ggFixLineQ S)
    exact hh.symm
  let W : Submodule (ZMod p) ↥(ggFixLineT r s) := Submodule.span (ZMod p) (Set.range c)
  let SW : Subgroup (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) :=
    { carrier := {a | ∀ w, w ∈ W ↔ a w ∈ W}
      one_mem' := by intro w; simp
      mul_mem' := by
        rintro a b ha hb w
        rw [LinearEquiv.mul_apply, hb w, ha (b w)]
      inv_mem' := by
        rintro a ha w
        have h1 : a (a⁻¹ w) = w := by
          have := congrArg (fun e : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s) => e w)
            (mul_inv_cancel a)
          simpa [LinearEquiv.mul_apply] using this
        have h2 := (ha (a⁻¹ w)).symm
        rwa [h1] at h2 }
  have hgen_mem_SW : ∀ i, sg i ∈ SW := by
    intro i w
    constructor
    · intro hw
      rw [hform i w]
      exact W.sub_mem hw (W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩))
    · intro hw
      have hsq : sg i (sg i w) = w := by
        have hh : sg i * sg i = 1 := (hf i).1
        have h2 : (sg i * sg i) w = w := by rw [hh]; rfl
        rwa [LinearEquiv.mul_apply] at h2
      rw [← hsq, hform i (sg i w)]
      exact W.sub_mem hw (W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩))
  have hclosure_le : Subgroup.closure (Set.range sg) ≤ SW := by
    rw [Subgroup.closure_le]
    rintro a ⟨i, rfl⟩
    exact hgen_mem_SW i
  have hWinv : ∀ a ∈ ggFixLineQ S, ∀ w ∈ W, a w ∈ W := by
    intro a ha w hw
    rw [hQgen] at ha
    exact ((hclosure_le ha) w).mp hw
  have hWcases : W = ⊥ ∨ W = ⊤ := (ggFixLine_Q_absIrred S).1 W hWinv
  have hspan : Submodule.span (ZMod p) (Set.range c) = ⊤ := by
    rcases hWcases with hbot | htop
    · exfalso
      obtain ⟨i⟩ := l6w4_nonempty_index hM
      have hmem : c i ∈ W := Submodule.subset_span (Set.mem_range_self i)
      rw [hbot] at hmem
      exact hc i (by simpa using hmem)
    · exact htop
  have hb6 : ∀ a b : ι', a ≠ b → M.M a b ≠ 6 := by
    intro a b _ h6
    have hcard : Fintype.card ι' = 2 := l6w4_six_bond_card hM h6
    have hTge : N - 1 ≤ Module.finrank (ZMod p) ↥(ggFixLineT r s) := (ggFixLine_T_props S).2.2.1
    have hle : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) (Set.range c)) ≤
        Fintype.card ι' := finrank_range_le_card c
    rw [hspan, finrank_top] at hle
    have h5 := S.five_le
    omega
  have hpe : ∀ i j, i ≠ j → (β i (c j) = 0 ↔ M.M i j = 2) ∧ (β j (c i) = 0 ↔ M.M i j = 2) :=
    fun i j hij => ggFLW_pairing_edge S.odd M hM (ggFixLineQ S) f c β hform hβ hb6 i j hij
  obtain ⟨C, hCartan, hCbonds⟩ := ggFLW_cartanTree_bonds (ι := ι') hM
  let P : ι' → ι' → ZMod p := fun i j => β i (c j)
  have hP : ∀ i j, i ≠ j → (P i j ≠ 0 ↔ C i j ≠ 0) := by
    intro i j hij
    have h1 : P i j ≠ 0 ↔ M.M i j ≠ 2 := not_congr (hpe i j hij).1
    have h2 : M.M i j ≠ 2 ↔ 3 ≤ M.M i j := by
      constructor
      · intro hne
        rcases ggFLW_entries hM i j hij with hh | hh | hh | hh
        · exact absurd hh hne
        · omega
        · omega
        · omega
      · intro h3
        rcases ggFLW_entries hM i j hij with hh | hh | hh | hh <;> omega
    have h3 : 3 ≤ M.M i j ↔ C i j ≠ 0 := (hCbonds i j hij).symm
    exact h1.trans (h2.trans h3)
  obtain ⟨d, hd, hsym⟩ := ggFLW_symmetrizer C hCartan P hP
  let F : Submodule (ZMod p) ↥(ggFixLineT r s) :=
    ggLinFix ((ggFixLineQ S) : Set (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)))
  have hFinv : ∀ a ∈ ggFixLineQ S, ∀ w ∈ F, a w ∈ F := by
    intro a ha w hw
    change ∀ b ∈ (ggFixLineQ S : Set (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s))),
      b w = w at hw
    change ∀ b ∈ (ggFixLineQ S : Set (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s))),
      b (a w) = a w
    intro b hb
    have h1 : (b * a) w = w := hw (b * a) (mul_mem hb ha)
    calc b (a w) = (b * a) w := rfl
      _ = w := h1
      _ = a w := (hw a ha).symm
  have hFcases : F = ⊥ ∨ F = ⊤ := (ggFixLine_Q_absIrred S).1 F hFinv
  have hFbot : F = ⊥ := by
    rcases hFcases with hbot | htop
    · exact hbot
    · exfalso
      obtain ⟨i⟩ := l6w4_nonempty_index hM
      have hgiQ : sg i ∈ ggFixLineQ S := by
        rw [hQgen]; exact Subgroup.subset_closure (Set.mem_range_self i)
      have hgi : sg i = 1 := by
        ext w
        have hw : w ∈ F := by rw [htop]; exact Submodule.mem_top
        change ∀ b ∈ (ggFixLineQ S : Set (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s))),
          b w = w at hw
        simpa using hw (sg i) hgiQ
      have hne : sg i ≠ 1 := by
        intro h1
        have h2 : Module.finrank (ZMod p) (ggLinMove (sg i)) = 1 := (hf i).2
        rw [h1] at h2
        have h3 : ggLinMove (1 : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) = ⊥ := by
          rw [Submodule.eq_bot_iff]
          intro y hy
          rw [ggLinMove, LinearMap.mem_range] at hy
          obtain ⟨z, hz⟩ := hy
          simpa using hz.symm
        rw [h3] at h2
        simp at h2
      exact hne hgi
  have hker : ∀ v : ↥(ggFixLineT r s), (∀ i, β i v = 0) → v = 0 := by
    intro v hv
    have hvF : v ∈ F := by
      change ∀ b ∈ (ggFixLineQ S : Set (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s))),
        b v = v
      intro b hb
      rw [hQgen] at hb
      induction hb using Subgroup.closure_induction with
      | mem a ha =>
          obtain ⟨i, rfl⟩ := ha
          rw [hform i v, hv i, zero_smul, sub_zero]
      | one => rfl
      | mul a b _ _ iha ihb => rw [LinearEquiv.mul_apply, ihb, iha]
      | inv a _ iha =>
          have h1 : a⁻¹ (a v) = v := by
            have := congrArg (fun e : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s) => e v)
              (inv_mul_cancel a)
            simpa [LinearEquiv.mul_apply] using this
          rw [iha] at h1
          exact h1
    have : v ∈ (⊥ : Submodule (ZMod p) ↥(ggFixLineT r s)) := by
      rw [← hFbot]; exact hvF
    simpa using this
  obtain ⟨B, hrad, hBgen⟩ :=
    ggFLW_invariantForm S.odd c β sg hform hβ hspan hker d hd hsym
  have hB : ∀ a ∈ ggFixLineQ S, ∀ u v, B (a u) (a v) = B u v := by
    intro a ha
    rw [hQgen] at ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
        obtain ⟨i, rfl⟩ := ha
        exact hBgen i
    | one => intro u v; simp
    | mul a b _ _ iha ihb =>
        intro u v
        show B (a (b u)) (a (b v)) = B u v
        rw [iha (b u) (b v), ihb u v]
    | inv a _ iha =>
        intro u v
        have h1 : a (a⁻¹ u) = u := by
          have := congrArg (fun e : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s) => e u)
            (mul_inv_cancel a)
          simpa [LinearEquiv.mul_apply] using this
        have h2 : a (a⁻¹ v) = v := by
          have := congrArg (fun e : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s) => e v)
            (mul_inv_cancel a)
          simpa [LinearEquiv.mul_apply] using this
        have h := iha (a⁻¹ u) (a⁻¹ v)
        rw [h1, h2] at h
        exact h.symm
  obtain ⟨w, hwne, hw⟩ := ggFixLine_form_degenerate S hF2 B hB
  exact hwne (hrad w hw)

theorem ggFixLineNotWeyl_holds : GGFixLineNotWeyl := by
  intro p N _ V _ _ ι h α r s x S hF2
  exact ggFixLine_not_linWeyl S hF2

end CFSG.StandardType

end
