module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2NC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
  {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}

theorem br2_false_of_one_A6 (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ) (hL : Br2OneComp Y T L)
    (hshape : IsAlt ↥L 6) (hrk : ∀ D ∈ Γ, 3 ≤ mRank D) (hne : Γ.Nonempty)
    (hfin : FinG4A6) : False := by
  classical
  obtain ⟨hX₀normal, hle, hsup, hnc1, hnc2⟩ := hfin ↥L hshape
  let ψ : ↥Y →* MulAut ↥L := psiOf Y L hL.normal
  have hψinj : Function.Injective ψ := psiOf_injective hL.core
  have hcard_ne : ∀ D ∈ Γ, Nat.card D ≠ 0 := by
    intro D _
    exact Nat.pos_iff_ne_zero.mp (Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩)
  have hcard8 : ∀ D ∈ Γ, 8 ≤ Nat.card (imgOf ψ D) := by
    intro D hD
    rw [imgOf_card hψinj (hc.h131.le_G D hD)]
    have hlog : 3 ≤ Nat.log 2 (Nat.card D) := hrk D hD
    have hpow : 2 ^ 3 ≤ Nat.card D := Nat.pow_le_of_le_log (hcard_ne D hD) hlog
    norm_num at hpow
    exact hpow
  have hmem : ∀ D ∈ Γ, imgOf ψ D ≤ autNoDynkin ↥L := by
    intro D hD
    exact hle (imgOf ψ D)
      ((imgOf_isElemAbelian_iff hψinj (hc.h131.le_G D hD)).mpr (hc.h131.isElemAb D hD))
      (hcard8 D hD)
  have hX₀ : autNoDynkin ↥L ≤ ψ.range := by
    obtain ⟨D₀, hD₀⟩ := hne
    have hsup₀ : innAutOf ↥L ⊔ imgOf ψ D₀ = autNoDynkin ↥L :=
      hsup (imgOf ψ D₀)
        ((imgOf_isElemAbelian_iff hψinj (hc.h131.le_G D₀ hD₀)).mpr (hc.h131.isElemAb D₀ hD₀))
        (hcard8 D₀ hD₀)
    rw [← hsup₀]
    refine sup_le ?_ (imgOf_le_range ψ D₀)
    rw [show innAutOf ↥L = imgOf ψ L from (imgOf_psiOf_L hL.core).symm]
    exact imgOf_le_range ψ L
  have hX₀n : ∀ r : ↥Y, ∀ x ∈ autNoDynkin ↥L,
      ψ r * x * (ψ r)⁻¹ ∈ autNoDynkin ↥L :=
    fun r x hx => hX₀normal.conj_mem x hx (ψ r)
  exact w183b2_false_of_dynkin hc.toBr1Base hL hX₀ hX₀n hmem hnc1 hnc2 hrk hne

end CFSG.LocalAnalysis.WeakClosure81

end
