module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2TwoA
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Mod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt IsSp4)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
  {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}

private noncomputable def w183b2_swapEquiv (hL : Br2TwoComp Y T L₁ L₂) : ↥L₁ ≃* ↥L₂ :=
  (Subgroup.equivMapOfInjective L₁ (MulAut.conj (Classical.choose hL.swap)).toMonoidHom
      (MulAut.conj (Classical.choose hL.swap)).injective).trans
    (MulEquiv.subgroupCongr
      (show L₁.map (MulAut.conj (Classical.choose hL.swap)).toMonoidHom = L₂ from
        (Classical.choose_spec hL.swap).2))

private theorem w183b2_shape_of_swap (hL : Br2TwoComp Y T L₁ L₂)
    (hshape : IsL3 ↥L₁ 2 ∨ IsAlt ↥L₁ 6 ∨ IsSp4 ↥L₁ 2) :
    IsL3 ↥L₂ 2 ∨ IsAlt ↥L₂ 6 ∨ IsSp4 ↥L₂ 2 := by
  let e := w183b2_swapEquiv hL
  rcases hshape with h | h | h
  · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)
  · rcases h with ⟨f⟩
    exact Or.inr (Or.inl ⟨e.symm.trans f⟩)
  · exact Or.inr (Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e h))

theorem br2_false_of_two_sided (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (hL : Br2TwoComp Y T L₁ L₂)
    (hmem : ∀ D ∈ Γ, D ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    {ED : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} (hED : Br2ED Γ VA m δ ED)
    {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ) (hDT : D ≤ T)
    (hD₁ : ¬ D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hD₂ : ¬ D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)))
    (hD3 : 3 ≤ mOf D (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ∨
      3 ≤ mOf D (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))))
    (hshape : IsL3 ↥L₁ 2 ∨ IsAlt ↥L₁ 6 ∨ IsSp4 ↥L₁ 2) (hFD : FinG11Models) : False := by
  have hDY : D ≤ Y := hc.h131.le_G D hD
  have hD₁' : ∀ d ∈ D, ∀ a ∈ L₁, d * a * d⁻¹ ∈ L₁ := by
    intro d hd a ha
    exact ((Subgroup.mem_normalizer_iff.mp (hmem D hD hd)) a).mp ha
  have hmem₂ : D ≤ Subgroup.normalizer (L₂ : Set (LGL 2 V)) := by
    intro d hd
    exact (Br2TwoComp.mem_normalizer_iff hL (hDY hd)).mp (hmem D hD hd)
  have hD₂' : ∀ d ∈ D, ∀ b ∈ L₂, d * b * d⁻¹ ∈ L₂ := by
    intro d hd b hb
    exact ((Subgroup.mem_normalizer_iff.mp (hmem₂ hd)) b).mp hb
  have hcent : ∀ d ∈ D, (∀ a ∈ L₁, d * a = a * d) → (∀ b ∈ L₂, d * b = b * d) → d = 1 :=
    fun d hd h₁ h₂ => hL.cent d (hDY hd) h₁ h₂
  have hs₂ := w183b2_shape_of_swap hL hshape
  have hmod := w183b2_mod_prop hL.simple₁ hL.nonab₁ hL.simple₂ hL.nonab₂ hL.comm
    hD₁' hD₂' (hc.h131.isElemAb D hD) (hc.h131.quadratic D hD) hcent
    hD₁ hD₂ hD3 hshape hs₂ hFD
  exact w183b2_two_false_of_mod hc hL hmem hED hD hDT hD₁ hD₂ hmod

end CFSG.LocalAnalysis.WeakClosure81

end
