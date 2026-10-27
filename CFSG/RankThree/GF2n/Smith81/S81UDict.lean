module

public import CFSG.RankThree.GF2n.Smith81.S81UModelDef
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.A5Cube Matrix exteriorPower
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

@[expose] noncomputable def projW (σ : F ≃+* F) (τ : F) (η : Cube F) : Cube F := τ • η + theta σ (τ • η)

theorem projW_add (τ : F) (η η' : Cube F) : projW σ τ (η + η') = projW σ τ η + projW σ τ η' := by
  unfold projW
  rw [smul_add, map_add]
  abel

theorem projW_mem_Wsub (hσ : ∀ c, σ (σ c) = c) (τ : F) (η : Cube F) : projW σ τ η ∈ Wsub σ := by
  rw [mem_Wsub_iff]
  unfold projW
  rw [map_add, theta_theta hσ]
  exact add_comm _ _

theorem projW_of_mem {τ : F} (hτ : τ + σ τ = 1) {w : Cube F} (hw : w ∈ Wsub σ) :
    projW σ τ w = w := by
  rw [mem_Wsub_iff] at hw
  unfold projW
  rw [theta_smul, hw, ← add_smul, hτ, one_smul]

theorem projW_rho (hσ : ∀ c, σ (σ c) = c) (τ : F) {g : GL (Fin 6) F} (hg : g ∈ SUid σ 6) (η : Cube F) :
    projW σ τ (rho F g η) = rho F g (projW σ τ η) := by
  unfold projW
  rw [← map_smul (rho F g) τ η, theta_rho hg, map_add]

private theorem h61_add_self (x : Cube F) : x + x = 0 := by
  rw [← two_smul F, CharTwo.two_eq_zero, zero_smul]

private theorem h61_sub_eq_add (x y : Cube F) : x - y = x + y := by
  rw [sub_eq_add_neg, neg_eq_iff_add_eq_zero.mpr (h61_add_self y)]

theorem mem_Rw_iff (hσ : IsUnitaryInvolution σ) (t : SUid σ 6) (r : Wform σ) :
    r ∈ Rw σ t ↔ ∃ η : Cube F, (r : Cube F) = rho F (t : GL (Fin 6) F) η - η := by
  simp only [Rw, Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨(w : Cube F), ?_⟩
    rw [Submodule.coe_sub, Wact_apply]
  · rintro ⟨η, hη⟩
    obtain ⟨τ, hτ⟩ := hσ.trace_surj 1 (map_one σ)
    have hr : (r : Cube F) ∈ Wsub σ := mem_Wform_iff.mp r.2
    have hrη : (r : Cube F) = rho F (t : GL (Fin 6) F) η + η := by
      rw [hη, h61_sub_eq_add]
    have key : (r : Cube F) = rho F (t : GL (Fin 6) F) (projW σ τ η) + projW σ τ η := by
      rw [← projW_of_mem hτ hr, hrη, projW_add, projW_rho hσ.invol τ t.2 η]
    refine ⟨⟨projW σ τ η, mem_Wform_iff.mpr (projW_mem_Wsub hσ.invol τ η)⟩, ?_⟩
    apply Subtype.ext
    show (r : Cube F) = rho F (t : GL (Fin 6) F) (projW σ τ η) - projW σ τ η
    rw [key, h61_sub_eq_add]

theorem mem_Cw_iff (t : SUid σ 6) (c : Wform σ) :
    c ∈ Cw σ t ↔ rho F (t : GL (Fin 6) F) (c : Cube F) = c := by
  simp only [Cw, Set.mem_setOf_eq]
  constructor
  · intro h
    rw [← Wact_apply t c, h]
  · intro h
    apply Subtype.ext
    rw [Wact_apply t c, h]

theorem CR_of_F (hσ : IsUnitaryInvolution σ) (t : SUid σ 6)
    (h : ∀ η : Cube F, rho F (t : GL (Fin 6) F) η = η → ∃ η' : Cube F, η = rho F (t : GL (Fin 6) F) η' - η') :
    ∀ c ∈ Cw σ t, c ∈ Rw σ t := by
  intro c hc
  exact (mem_Rw_iff hσ t c).mpr (h (c : Cube F) ((mem_Cw_iff t c).mp hc))

theorem beta_ne_of_root (hσ : IsUnitaryInvolution σ) (t : SUid σ 6) (p : Wform σ)
    (hp : (p : Cube F) ∈ RootPt σ) (hβ : beta F (rho F (t : GL (Fin 6) F) (p : Cube F)) (p : Cube F) ≠ 0) :
    ∃ p₁ p₂ : Wform σ, (p₁ : Cube F) ∈ RootPt σ ∧ (p₂ : Cube F) ∈ RootPt σ ∧
      p₁ + p₂ ∈ Rw σ t ∧ beta F (p₁ : Cube F) (p₂ : Cube F) ≠ 0 := by
  refine ⟨Wact σ t p, p, ?_, hp, ?_, ?_⟩
  · rw [Wact_apply t p]
    exact rho_mem_RootPt t.2 hp
  · simp only [Rw, Set.mem_setOf_eq]
    refine ⟨p, ?_⟩
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_sub, Wact_apply t p, h61_sub_eq_add]
  · rw [Wact_apply t p]
    exact hβ

theorem eq_top_of_rho_frame_cubeBasis_mem (Sf : GL (Fin 6) F) (X : Submodule F (Cube F))
    (h : ∀ I : Set.powersetCard (Fin 6) 3, rho F Sf (cubeBasis F I) ∈ X) : X = ⊤ := by
  rw [eq_top_iff]
  intro η _
  have hη : rho F Sf (rho F Sf⁻¹ η) = η := by
    have h1 := A5Cube.rho_mul_apply Sf Sf⁻¹ η
    rw [mul_inv_cancel, A5Cube.rho_one, Module.End.one_apply] at h1
    exact h1.symm
  have hζ : rho F Sf⁻¹ η =
      ∑ I : Set.powersetCard (Fin 6) 3, coord F (rho F Sf⁻¹ η) I • cubeBasis F I :=
    ((cubeBasis F).sum_repr (rho F Sf⁻¹ η)).symm
  rw [← hη, hζ, map_sum]
  refine X.sum_mem fun I _ => ?_
  rw [map_smul (rho F Sf)]
  exact X.smul_mem _ (h I)

private theorem h70_mem_Wform (hσ : IsUnitaryInvolution σ) (τ : F) (η : Cube F) :
    projW σ τ η ∈ Wform σ :=
  mem_Wform_iff.mpr (projW_mem_Wsub hσ.invol τ η)

private theorem h70_projW_zero (τ : F) : projW σ τ (0 : Cube F) = 0 := by
  unfold projW
  simp

private theorem h70_Pi_sub_rho (hσ : IsUnitaryInvolution σ) (τ : F) (g : SUid σ 6) (x : Cube F) :
    projW σ τ (rho F (g : GL (Fin 6) F) x - x) =
      rho F (g : GL (Fin 6) F) (projW σ τ x) - projW σ τ x := by
  rw [h61_sub_eq_add, h61_sub_eq_add, projW_add, projW_rho hσ.invol τ g.2]

private theorem h70_Pi_smul_sub (hσ : IsUnitaryInvolution σ) (τ : F) (g : SUid σ 6) (a : F)
    (x : Cube F) :
    projW σ τ (a • (rho F (g : GL (Fin 6) F) x - x)) =
      rho F (g : GL (Fin 6) F) (projW σ τ (a • x)) - projW σ τ (a • x) := by
  rw [smul_sub, ← map_smul (rho F (g : GL (Fin 6) F)) a x, h70_Pi_sub_rho hσ τ g]

private theorem h70_fixed (hσ : IsUnitaryInvolution σ) (τ : F) (t : SUid σ 6) (a : F) (ξ : Cube F)
    (hξ : rho F (t : GL (Fin 6) F) ξ = ξ) :
    rho F (t : GL (Fin 6) F) (projW σ τ (a • ξ)) = projW σ τ (a • ξ) := by
  rw [← projW_rho hσ.invol τ t.2, map_smul (rho F (t : GL (Fin 6) F)) a ξ, hξ]

theorem covW_of_F (hσ : IsUnitaryInvolution σ) (t : SUid σ 6)
    (h : ∀ η : Cube F, η ∈ Submodule.span F {v : Cube F |
      ∃ g ∈ Gcent σ t, ∃ η' : Cube F, v = rho F (g : GL (Fin 6) F) η' - η'}) :
    ∀ w : Wform σ, w ∈ AddSubgroup.closure {v : Wform σ |
      ∃ g ∈ Gcent σ t, ∃ w' : Wform σ, v = Wact σ g w' - w'} := by
  obtain ⟨τ, hτ⟩ := hσ.trace_surj 1 (map_one σ)
  have claim : ∀ η : Cube F, η ∈ Submodule.span F {v : Cube F |
      ∃ g ∈ Gcent σ t, ∃ η' : Cube F, v = rho F (g : GL (Fin 6) F) η' - η'} →
      ∀ a : F, ∃ s ∈ AddSubgroup.closure {v : Wform σ |
        ∃ g ∈ Gcent σ t, ∃ w' : Wform σ, v = Wact σ g w' - w'},
        (s : Cube F) = projW σ τ (a • η) := by
    intro η hη
    induction hη using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, η', rfl⟩ := hx
      intro a
      obtain ⟨w', hw'⟩ : ∃ w' : Wform σ, (w' : Cube F) = projW σ τ (a • η') :=
        ⟨⟨projW σ τ (a • η'), h70_mem_Wform hσ τ _⟩, rfl⟩
      refine ⟨Wact σ g w' - w', AddSubgroup.subset_closure ⟨g, hg, w', rfl⟩, ?_⟩
      rw [Submodule.coe_sub, Wact_apply, hw', h70_Pi_smul_sub hσ τ g a η']
    | zero =>
      intro a
      exact ⟨0, AddSubgroup.zero_mem _, by simp [h70_projW_zero]⟩
    | add x y hx hy ihx ihy =>
      intro a
      obtain ⟨s₁, hs₁, e₁⟩ := ihx a
      obtain ⟨s₂, hs₂, e₂⟩ := ihy a
      refine ⟨s₁ + s₂, AddSubgroup.add_mem _ hs₁ hs₂, ?_⟩
      rw [Submodule.coe_add, e₁, e₂, smul_add, projW_add]
    | smul b x hx ih =>
      intro a
      rw [smul_smul]
      exact ih (a * b)
  intro w
  obtain ⟨s, hs, hseq⟩ := claim (w : Cube F) (h (w : Cube F)) 1
  rw [one_smul, projW_of_mem hτ (mem_Wform_iff.mp w.2)] at hseq
  have hsw : s = w := Subtype.ext hseq
  rw [← hsw]
  exact hs

theorem covC_of_F (hσ : IsUnitaryInvolution σ) (t : SUid σ 6)
    (h : ∀ ξ : Cube F, rho F (t : GL (Fin 6) F) ξ = ξ →
      ξ ∈ LinearMap.range (rho F (t : GL (Fin 6) F) - 1) ⊔ Submodule.span F {v : Cube F |
        ∃ g ∈ Gcent σ t, ∃ ξ' : Cube F, rho F (t : GL (Fin 6) F) ξ' = ξ' ∧
          v = rho F (g : GL (Fin 6) F) ξ' - ξ'}) :
    ∀ c ∈ Cw σ t, ∃ r ∈ Rw σ t, c - r ∈ AddSubgroup.closure {v : Wform σ |
      ∃ g ∈ Gcent σ t, ∃ c' ∈ Cw σ t, v = Wact σ g c' - c'} := by
  obtain ⟨τ, hτ⟩ := hσ.trace_surj 1 (map_one σ)
  have claim : ∀ z : Cube F, z ∈ Submodule.span F {v : Cube F |
      ∃ g ∈ Gcent σ t, ∃ ξ' : Cube F, rho F (t : GL (Fin 6) F) ξ' = ξ' ∧
        v = rho F (g : GL (Fin 6) F) ξ' - ξ'} →
      ∀ a : F, ∃ s ∈ AddSubgroup.closure {v : Wform σ |
        ∃ g ∈ Gcent σ t, ∃ c' ∈ Cw σ t, v = Wact σ g c' - c'},
        (s : Cube F) = projW σ τ (a • z) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, ξ', hξ', rfl⟩ := hx
      intro a
      obtain ⟨c', hc'⟩ : ∃ c' : Wform σ, (c' : Cube F) = projW σ τ (a • ξ') :=
        ⟨⟨projW σ τ (a • ξ'), h70_mem_Wform hσ τ _⟩, rfl⟩
      have hc'Cw : c' ∈ Cw σ t := by
        rw [mem_Cw_iff, hc', h70_fixed hσ τ t a ξ' hξ']
      refine ⟨Wact σ g c' - c', AddSubgroup.subset_closure ⟨g, hg, c', hc'Cw, rfl⟩, ?_⟩
      rw [Submodule.coe_sub, Wact_apply, hc', h70_Pi_smul_sub hσ τ g a ξ']
    | zero =>
      intro a
      exact ⟨0, AddSubgroup.zero_mem _, by simp [h70_projW_zero]⟩
    | add x y hx hy ihx ihy =>
      intro a
      obtain ⟨s₁, hs₁, e₁⟩ := ihx a
      obtain ⟨s₂, hs₂, e₂⟩ := ihy a
      refine ⟨s₁ + s₂, AddSubgroup.add_mem _ hs₁ hs₂, ?_⟩
      rw [Submodule.coe_add, e₁, e₂, smul_add, projW_add]
    | smul b x hx ih =>
      intro a
      rw [smul_smul]
      exact ih (a * b)
  intro c hc
  have hc' : rho F (t : GL (Fin 6) F) (c : Cube F) = c := (mem_Cw_iff t c).mp hc
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (h (c : Cube F) hc')
  obtain ⟨η₀, hη₀⟩ := LinearMap.mem_range.mp hy
  have hy' : y = rho F (t : GL (Fin 6) F) η₀ - η₀ := by
    rw [← hη₀]
    simp [LinearMap.sub_apply, Module.End.one_apply]
  have hPi : projW σ τ y + projW σ τ z = (c : Cube F) := by
    rw [← projW_add, hyz, projW_of_mem hτ (mem_Wform_iff.mp c.2)]
  obtain ⟨r, hr⟩ : ∃ r : Wform σ, (r : Cube F) = projW σ τ y :=
    ⟨⟨projW σ τ y, h70_mem_Wform hσ τ y⟩, rfl⟩
  refine ⟨r, ?_, ?_⟩
  · rw [mem_Rw_iff hσ t]
    refine ⟨projW σ τ η₀, ?_⟩
    rw [hr, hy', h70_Pi_sub_rho hσ τ t]
  · obtain ⟨s, hs, hsz⟩ := claim z hz 1
    rw [one_smul] at hsz
    have hcs : c - r = s := by
      apply Subtype.ext
      rw [Submodule.coe_sub, hsz, hr, ← hPi]
      abel
    rw [hcs]
    exact hs

theorem P3_of_F (hσ : IsUnitaryInvolution σ) (t : SUid σ 6) (U : Set (SUid σ 6))
    (hU : ∀ u ∈ U, u ∈ Gcent σ t)
    (h1 : ∀ u ∈ U, ∀ ξ : Cube F, rho F (t : GL (Fin 6) F) ξ = ξ →
      rho F (u : GL (Fin 6) F) ξ - ξ ∈ LinearMap.range (rho F (t : GL (Fin 6) F) - 1))
    (h2 : ∀ ξ : Cube F, rho F (t : GL (Fin 6) F) ξ = ξ →
      (∀ u ∈ U, rho F (u : GL (Fin 6) F) ξ = ξ) →
        ξ ∈ LinearMap.range (rho F (t : GL (Fin 6) F) - 1)) :
    (∀ u ∈ U, u ∈ Gcent σ t) ∧ (∀ u ∈ U, ∀ c ∈ Cw σ t, Wact σ u c - c ∈ Rw σ t) ∧
      ∀ c ∈ Cw σ t, (∀ u ∈ U, Wact σ u c = c) → c ∈ Rw σ t := by
  refine ⟨hU, ?_, ?_⟩
  · intro u hu c hc
    rw [mem_Rw_iff hσ t]
    obtain ⟨η, hη⟩ := LinearMap.mem_range.mp (h1 u hu (c : Cube F) ((mem_Cw_iff t c).mp hc))
    refine ⟨η, ?_⟩
    rw [Submodule.coe_sub, Wact_apply, ← hη]
    simp [LinearMap.sub_apply, Module.End.one_apply]
  · intro c hc hfix
    have hfix' : ∀ u ∈ U, rho F (u : GL (Fin 6) F) (c : Cube F) = (c : Cube F) := by
      intro u hu
      have h' : ((Wact σ u c : Wform σ) : Cube F) = (c : Cube F) :=
        congrArg Subtype.val (hfix u hu)
      rw [Wact_apply] at h'
      exact h'
    rw [mem_Rw_iff hσ t]
    obtain ⟨η, hη⟩ := LinearMap.mem_range.mp (h2 (c : Cube F) ((mem_Cw_iff t c).mp hc) hfix')
    refine ⟨η, ?_⟩
    rw [← hη]
    simp [LinearMap.sub_apply, Module.End.one_apply]

end CFSG.RankThree.GF2n.Smith81.U6Cube
