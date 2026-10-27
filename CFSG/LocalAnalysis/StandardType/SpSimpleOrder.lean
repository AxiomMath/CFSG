module

public import CFSG.LieType.Universal.Symplectic
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
public import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure

public section

namespace CFSG.StandardType

namespace SpFixed

open CFSG.Open (StatedSp)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}

theorem isSimpleGroup_statedSp (hm : 3 ≤ m) : IsSimpleGroup (StatedSp m F) := by
  have hF : (Infinite F ∨ 4 ≤ Nat.card F) ∨ (Nat.card F = 3 ∧ 2 ≤ m) ∨
      (Nat.card F = 2 ∧ 3 ≤ m) := by
    letI : Fintype F := Fintype.ofFinite F
    obtain ⟨k, -, hk⟩ := FiniteField.card F 2
    have hcard : Nat.card F = 2 ^ (k : ℕ) := by
      rw [Nat.card_eq_fintype_card, hk]
    rcases Nat.lt_or_ge (k : ℕ) 2 with hklo | hkge
    · right; right
      have hk1 : (k : ℕ) = 1 := by
        have hle : (k : ℕ) ≤ 1 := Nat.le_of_lt_succ hklo
        have hge : 1 ≤ (k : ℕ) := Nat.succ_le_of_lt k.2
        exact le_antisymm hle hge
      exact ⟨by rw [hcard, hk1, pow_one], hm⟩
    · left; right
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k : ℕ) := Nat.pow_le_pow_right (by norm_num) hkge
        _ = Nat.card F := hcard.symm
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LieType.Universal.Symplectic.isQuasisimple m F (by omega) hF
  have hcenter : Subgroup.center (StatedSp m F) = ⊥ := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq m F,
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := m) (K := F)]
  let e : StatedSp m F ⧸ Subgroup.center (StatedSp m F) ≃* StatedSp m F :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  haveI := hsimple
  exact e.symm.isSimpleGroup

theorem twentySeven_dvd_card_statedSp (hm : 3 ≤ m) : 27 ∣ Nat.card (StatedSp m F) := by
  obtain ⟨⟨A, -, hcardA⟩, -⟩ :=
    CFSG.LieType.unique_even_symplectic_prime_field_three_rank (K := F) (n := m) (by omega)
  have hdiv : 3 ^ m ∣ Nat.card (StatedSp m F) := by
    rw [← hcardA]
    exact (Subgroup.card_subgroup_dvd_card A).trans
      (Subgroup.card_quotient_dvd_card
        ((CFSG.Open.StatedScalars (Fin m ⊕ Fin m) F).subgroupOf (StatedSp m F)))
  exact (dvd_trans (by norm_num : 27 ∣ 3 ^ 3) (pow_dvd_pow 3 hm)).trans hdiv

end SpFixed

end CFSG.StandardType
