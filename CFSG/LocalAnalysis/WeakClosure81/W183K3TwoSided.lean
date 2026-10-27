module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3CoreSetting
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Side
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Mod
public import CFSG.LocalAnalysis.WeakClosure81.W183B2TwoA
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
  {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}

theorem w183k3_two_VA_inf_fixSub (hc : Br1Base Y Γ VA T 𝒢 Zs m i₀ δ)
    (hL : Br3TwoComp Y T L₁ L₂) {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ)
    (hmem : D ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    (hD₁ : ¬ D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hD₂ : ¬ D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V))) :
    VA D ⊓ CFSG.SignalizerFunctorTheorem.Quadratic.fixSub L₂ = ⊥ ∧
      VA D ⊓ CFSG.SignalizerFunctorTheorem.Quadratic.fixSub L₁ = ⊥ := by
  have hDY : D ≤ Y := hc.h131.le_G D hD
  exact ⟨w183b2_VA_inf_fixSub_of_quasi hc.h131 hD hL.quasi₂ hL.odd₂ hL.le₂
      (fun d hd => (hL.mem_normalizer_iff (hDY hd)).mp (hmem hd)) hD₁,
    w183b2_VA_inf_fixSub_of_quasi hc.h131 hD hL.quasi₁ hL.odd₁ hL.le₁ hmem hD₂⟩

theorem br3_false_of_two_sided (rows : Br3Rows) (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (hL : Br3TwoComp Y T L₁ L₂)
    (hmem : ∀ D ∈ Γ, D ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    {ED : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} (hED : Br2ED Γ VA m δ ED)
    {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ) (hDT : D ≤ T)
    (hD₁ : ¬ D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hD₂ : ¬ D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)))
    (hD3 : 3 ≤ mOf D (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ∨
      3 ≤ mOf D (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))))
    (hshape : IsL3 (↥L₁ ⧸ Subgroup.center ↥L₁) 2 ∨ IsAlt (↥L₁ ⧸ Subgroup.center ↥L₁) 6)
    (hZ : Nat.card ↥(Subgroup.center ↥L₁) = 3) : False := by
  have hDY : D ≤ Y := hc.h131.le_G D hD
  have hD₁' : ∀ d ∈ D, ∀ a ∈ L₁, d * a * d⁻¹ ∈ L₁ := by
    intro d hd a ha
    exact ((Subgroup.mem_normalizer_iff.mp (hmem D hD hd)) a).mp ha
  have hmem₂ : D ≤ Subgroup.normalizer (L₂ : Set (LGL 2 V)) := fun d hd =>
    (hL.mem_normalizer_iff (hDY hd)).mp (hmem D hD hd)
  have hD₂' : ∀ d ∈ D, ∀ b ∈ L₂, d * b * d⁻¹ ∈ L₂ := by
    intro d hd b hb
    exact ((Subgroup.mem_normalizer_iff.mp (hmem₂ hd)) b).mp hb
  have hDe : IsElemAbelian 2 D := hc.h131.isElemAb D hD
  have hcent : ∀ d ∈ D, (∀ a ∈ L₁, d * a = a * d) → (∀ b ∈ L₂, d * b = b * d) → d = 1 :=
    fun d hd h₁ h₂ => hL.eq_one_of_isPGroup_cent (hDY hd) (k := 1) (by simpa using hDe.2 d hd) h₁ h₂
  have hc₁ : IsCover3 ↥L₁ := ⟨hL.quasi₁, hZ, hshape⟩
  have hc₂ : IsCover3 ↥L₂ := hL.isCover3_swap hc₁
  have hmod := w183b2_mod_prop_of_quasi hL.quasi₁ hL.quasi₂ hL.comm hD₁' hD₂' hDe
    (hc.h131.quadratic D hD) hcent hD₁ hD₂ hD3 (hc₁.absIrrOverF4 rows.g11cov)
    (hc₂.absIrrOverF4 rows.g11cov)
  have hVA := w183k3_two_VA_inf_fixSub hc.toBr1Base hL hD (hmem D hD) hD₁ hD₂
  exact w183two_two_false_of_mod hc hL.toBase hmem hED hD hDT hVA hmod

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
