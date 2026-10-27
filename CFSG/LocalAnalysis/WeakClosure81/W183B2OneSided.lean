module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Side
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Inner

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt IsSp4)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
  {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}

private theorem w183b2_eight_le_card_of_three_le_mRank {A : Subgroup (LGL 2 V)}
    (h : 3 ≤ mRank A) : 8 ≤ Nat.card A := by
  have hne : Nat.card A ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1, A.one_mem⟩, inferInstance⟩
  have hlog : 3 ≤ Nat.log 2 (Nat.card A) := by simpa only [mRank] using h
  have hpow : 2 ^ 3 ≤ Nat.card A := Nat.pow_le_of_le_log hne hlog
  simpa using hpow

theorem br2_false_of_one_sided (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (hL : Br2TwoComp Y T L₁ L₂)
    (hmem : ∀ D ∈ Γ, D ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    (hone : ∀ D ∈ Γ, D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ∨
      D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hrk : ∀ D ∈ Γ, 3 ≤ mRank D) (hne : Γ.Nonempty)
    (hshape : IsL3 ↥L₁ 2 ∨ IsAlt ↥L₁ 6 ∨ IsSp4 ↥L₁ 2)
    (h65f : Asch6_5Four) (hL34 : FinG4L34) (hA6 : FinG4A6)
    (h5 : IsSp4 ↥L₁ 2 → ∀ D ∈ Γ, ∀ P : Subgroup (LGL 2 V),
      IsSylowIn 5 P (Y ⊓ Subgroup.normalizer (D : Set (LGL 2 V))) → IsCyclic ↥P)
    (hSp5 : FinSp44Noncyclic5) : False := by
  classical
  rcases hshape with h | h | h
  ·
    refine w183b2_false_of_swap hc.toBr1Base hL (X₀ := innAutOf ↥L₁) ?_ ?_ ?_ ?_
      hone hrk hne
    · rw [← imgOf_psiOf_L hL.core₁]
      exact imgOf_le_range _ L₁
    · intro r x hx
      exact psiOf_conj_mem_innAutOf hL.core₁ r hx
    · intro D hD hDX
      exact w183b2_inner_of_quadratic h65f hL.core₁ h hDX
        (hc.h131.isElemAb D hD) (hc.h131.quadratic D hD) (hrk D hD)
    · exact (hL34 ↥L₁ h).1
  ·
    obtain ⟨hnorm, hall, hgen, hnc, -⟩ := hA6 ↥L₁ h
    obtain ⟨D₀, hD₀, hD₀X₁⟩ := w183b2_exists_type_one hc.h131 hc.sylow.le hL hone hne
    let ψ : ↥(Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) →* MulAut ↥L₁ :=
      psiOf (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) L₁ hL.core₁.normal
    have hD₀Ae : IsElemAbelian 2 (imgOf ψ D₀) :=
      (imgOf_isElemAbelian_iff (psiOf_injective hL.core₁) hD₀X₁).mpr (hc.h131.isElemAb D₀ hD₀)
    have hD₀card : 8 ≤ Nat.card (imgOf ψ D₀) := by
      rw [imgOf_card (psiOf_injective hL.core₁) hD₀X₁]
      exact w183b2_eight_le_card_of_three_le_mRank (hrk D₀ hD₀)
    have hX₀ : autNoDynkin ↥L₁ ≤ ψ.range := by
      rw [← hgen (imgOf ψ D₀) hD₀Ae hD₀card]
      refine sup_le ?_ (imgOf_le_range ψ D₀)
      rw [← imgOf_psiOf_L hL.core₁]
      exact imgOf_le_range ψ L₁
    have hX₀n : ∀ r : ↥(Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))),
        ∀ x ∈ autNoDynkin ↥L₁, ψ r * x * (ψ r)⁻¹ ∈ autNoDynkin ↥L₁ :=
      fun r x hx => hnorm.conj_mem x hx (ψ r)
    have hmem : ∀ D ∈ Γ, D ≤ (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) →
        imgOf ψ D ≤ autNoDynkin ↥L₁ := by
      intro D hD hDX
      refine hall (imgOf ψ D)
        ((imgOf_isElemAbelian_iff (psiOf_injective hL.core₁) hDX).mpr
          (hc.h131.isElemAb D hD)) ?_
      rw [imgOf_card (psiOf_injective hL.core₁) hDX]
      exact w183b2_eight_le_card_of_three_le_mRank (hrk D hD)
    exact w183b2_false_of_swap hc.toBr1Base hL hX₀ hX₀n hmem hnc hone hrk hne
  ·
    obtain ⟨D₀, hD₀⟩ := hne
    exact w183b2_sp44_not_one_sided hc.h131 hc.sylow.le hL h hSp5 (h5 h) hD₀
      (hone D₀ hD₀)

end CFSG.LocalAnalysis.WeakClosure81

end
