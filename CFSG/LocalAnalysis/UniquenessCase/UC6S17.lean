module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Z
public import CFSG.LocalAnalysis.UniquenessCase.UC6Pgrp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.Yardstones.Mf4cdcdf2e013 (TheoremCAt)

variable {G : Type} [Group G] [Finite G]

structure Data614 (M : Subgroup G) (r : ℕ) (R E : Subgroup G) : Prop where
  maxLocal : uniqueFourIsMaxTwoLocal M
  prime : r.Prime
  odd : r ≠ 2
  sylow : IsSylowOf r R M
  E_le : E ≤ R ⊓ centralizer (R : Set G)
  E_el : IsElemAbelian r E
  E_card : Nat.card E = r ^ 2
  E_gamma : rankThreeGamma 1 r E ≤ M

namespace Data614

variable {M R E : Subgroup G} {r : ℕ} (d : Data614 M r R E) (hC : TheoremCAt M)
include d hC

theorem E_le_M : E ≤ M := fun x hx => d.sylow.le (d.E_le hx).1

theorem inU_of_le {X : Subgroup G} (hXE : X ≤ E) (hX1 : X ≠ ⊥) : InU M X := by
  haveI : Fact r.Prime := ⟨d.prime⟩
  have hMself := normalizer_eq_of_isMaxTwoLocal d.maxLocal
  have hEM : E ≤ M := d.E_le_M hC
  have hEU : InU M E :=
    inU_of_theoremC d.maxLocal hC d.prime d.odd hEM d.E_el d.E_card d.E_gamma
  have hXp : IsPGroup r X := (IsElemAbelian.isPGroup d.E_el).to_le hXE
  have hNX : ∀ w, w ∈ normalizer (X : Set G) → w ∈ M := fun w hw =>
    d.E_gamma (CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 r E X hXE
      (one_le_pRank_of_ne_bot d.prime hXp hX1) hw)
  rw [inU_iff_fixed hMself]
  refine ⟨hXE.trans hEM, fun g hg => ?_⟩
  have hYM : uniqueFourConj g X ≤ M := fun y hy => by
    rw [mem_uniqueFourConj_iff] at hy
    have := hg _ hy
    simpa [mul_assoc] using this
  obtain ⟨k, hkM, hk⟩ := exists_conj_le_of_isSylowOf d.sylow hYM (isPGroup_uniqueFourConj hXp g)
  have hEcent : ∀ e ∈ E, (g * k) * e * (g * k)⁻¹ ∈ M := by
    intro e he
    have hmem : (g * k) * e * (g * k)⁻¹ ∈ centralizer (X : Set G) := by
      rw [mem_centralizer_iff]
      intro x hx
      have hw : k⁻¹ * (g⁻¹ * x * g) * k ∈ R := by
        refine hk _ ?_
        rw [mem_uniqueFourConj_iff]
        simpa [mul_assoc] using hx
      have hcomm := mem_centralizer_iff.1 (d.E_le he).2 _ hw
      calc x * ((g * k) * e * (g * k)⁻¹)
          = (g * k) * ((k⁻¹ * (g⁻¹ * x * g) * k) * e) * (g * k)⁻¹ := by group
        _ = (g * k) * (e * (k⁻¹ * (g⁻¹ * x * g) * k)) * (g * k)⁻¹ := by rw [hcomm]
        _ = ((g * k) * e * (g * k)⁻¹) * x := by group
    exact hNX _ ((Subgroup.centralizer_le_normalizer (X : Set G)) hmem)
  have hfix := ((inU_iff_fixed hMself).1 hEU).2 (g * k)⁻¹ fun e he => by
    simpa using hEcent e he
  have hgk : g * k ∈ M := inv_mem_iff.1 hfix
  have := M.mul_mem hgk (M.inv_mem hkM)
  simpa using this

theorem inU_of_le_pGroup {X S : Subgroup G} (hXE : X ≤ E) (hX1 : X ≠ ⊥) (hXS : X ≤ S)
    (hS : IsPGroup r S) : InU M S :=
  InU.of_subnormal (normalizer_eq_of_isMaxTwoLocal d.maxLocal)
    (isSubnormal_of_isPGroup d.prime hS hXS) (d.inU_of_le hC hXE hX1)

theorem normalizer_le_of_le_pGroup {X S : Subgroup G} (hXE : X ≤ E) (hX1 : X ≠ ⊥)
    (hXS : X ≤ S) (hS : IsPGroup r S) : normalizer (S : Set G) ≤ M :=
  (d.inU_of_le_pGroup hC hXE hX1 hXS hS).normalizer_le (normalizer_eq_of_isMaxTwoLocal d.maxLocal)

end Data614

end CFSG.LocalAnalysis.UniquenessCase.UC6
