module

import CFSG.RankThree.PartTwo.Sec21.Item2119End6ProofQTools
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

namespace Item2119End7Proof

section Fixed

theorem cube_comm {H : Type*} [CommGroup H] (h3 : ∀ x : H, x ^ 3 = 1) (q r x : H) :
    ((x⁻¹ * q)⁻¹ * (q⁻¹ * r))⁻¹ * ((q⁻¹ * r)⁻¹ * (r⁻¹ * x)) = 1 := by
  have e : ((x⁻¹ * q)⁻¹ * (q⁻¹ * r))⁻¹ * ((q⁻¹ * r)⁻¹ * (r⁻¹ * x)) =
      (q * q * q) * (r * r * r)⁻¹ * (x⁻¹ * x) := by
    simp only [mul_inv_rev, inv_inv]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  rw [e, inv_mul_cancel, mul_one, ← pow_three', h3, ← pow_three', h3, inv_one, one_mul]

theorem card_ker_comp_le {H : Type*} [Group H] [Finite H] (ψ χ : H →* H) :
    Nat.card (χ.comp ψ).ker ≤ Nat.card ψ.ker * Nat.card χ.ker := by
  set K := (χ.comp ψ).ker with hK
  let ψ' : K →* χ.ker := (ψ.comp K.subtype).codRestrict χ.ker (fun k => k.2)
  have h1 := Item2119End6Proof.card_eq_card_ker_mul_card_range ψ'
  have h2 : Nat.card ψ'.ker ≤ Nat.card ψ.ker := by
    refine Nat.card_le_card_of_injective (fun k => ⟨((k : K) : H), ?_⟩) ?_
    · have hk : ψ' (k : K) = 1 := k.2
      exact congrArg Subtype.val hk
    · intro k₁ k₂ h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ψ.ker => (z : H)) h
  have h3 : Nat.card ψ'.range ≤ Nat.card χ.ker := Subgroup.card_le_card_group _
  rw [h1]
  exact Nat.mul_le_mul h2 h3

variable {G : Type} [Group G] [Finite G]

end Fixed

end Item2119End7Proof

open Item2119End7Proof

end CFSG.RankThree.PartTwo.Sec21
