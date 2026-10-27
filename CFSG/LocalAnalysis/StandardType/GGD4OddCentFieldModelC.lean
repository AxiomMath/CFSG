module

public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthD4Stab
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthD4

section ModelC


theorem gdc_ggAutFixedSubgroup_eq_entrywiseFixedGroup {K : Type} [Field K] (σ : K ≃+* K) :
    ggAutFixedSubgroup (entrywiseAdjointAut Tag.D4 σ) =
      (entrywiseFixedGroup Tag.D4 σ).subgroupOf (adjointGroup Tag.D4 K) := by
  ext u
  change entrywiseAdjointAut Tag.D4 σ u = u ↔
    (u : ModGL Tag.D4 K) ∈ entrywiseFixedGroup Tag.D4 σ
  rw [mem_entrywiseFixedGroup]
  constructor
  · intro h
    refine ⟨u.2, ?_⟩
    exact (coe_entrywiseAdjointAut (τ := Tag.D4) (K := K) σ u).symm.trans
      (congrArg Subtype.val h)
  · rintro ⟨-, h⟩
    exact Subtype.ext ((coe_entrywiseAdjointAut (τ := Tag.D4) (K := K) σ u).trans h)

theorem orderOf_entrywiseAdjointAut_D4 {K : Type} [Field K] [Finite K] (τ : K ≃+* K) :
    orderOf (entrywiseAdjointAut Tag.D4 τ) = orderOf τ :=
  CFSG.RankThree.Chevalley.SteinbergBT.orderOf_entrywiseAdjointAut (τ := Tag.D4) (K := K)
    (by decide) τ

theorem d4C_fixed_data {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {τ : K ≃+* K} (hτ : orderOf τ = 3) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (n' : ℕ), Nat.card k = 2 ^ n' ∧ n = 3 * n' ∧
      Nonempty (adjointGroup Tag.D4 k ≃*
        ↥(ggAutFixedSubgroup (entrywiseAdjointAut Tag.D4 τ))) ∧
      ∀ β : MulAut (adjointGroup Tag.D4 K),
        (∀ x ∈ ggAutFixedSubgroup (entrywiseAdjointAut Tag.D4 τ), β x = x) →
          β ∈ Subgroup.zpowers (entrywiseAdjointAut Tag.D4 τ) := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst hn0
      rw [Nat.pow_zero] at hK
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact hn
  haveI : Fintype K := Fintype.ofFinite K
  have hcharP : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hchar : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨hdvd, hcard⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield (p := 2) (f := n)
      Nat.prime_two hn hK τ
  have hcard' : Nat.card ↥(fixSubfield τ) = 2 ^ (n / 3) := by
    simpa [hτ] using hcard
  have hn3 : n = 3 * (n / 3) := (Nat.mul_div_cancel' (by simpa [hτ] using hdvd)).symm
  have hfix : ggAutFixedSubgroup (entrywiseAdjointAut Tag.D4 τ) =
      (fixedFieldImage Tag.D4 τ).subgroupOf (adjointGroup Tag.D4 K) := by
    rw [gdc_ggAutFixedSubgroup_eq_entrywiseFixedGroup τ,
      entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two (τ := Tag.D4)
        (Or.inr (Or.inr (Or.inl rfl))) hchar τ]
  have hJC : fixedFieldImage Tag.D4 τ ≤ adjointGroup Tag.D4 K :=
    fun x hx => (fixedFieldImage_le hx).1
  let e : adjointGroup Tag.D4 ↥(fixSubfield τ) ≃*
      ↥(ggAutFixedSubgroup (entrywiseAdjointAut Tag.D4 τ)) :=
    (fixedFieldImageEquiv (τ := Tag.D4) τ).trans
      ((Subgroup.subgroupOfEquivOfLe hJC).symm.trans (MulEquiv.subgroupCongr hfix.symm))
  refine ⟨↥(fixSubfield τ), inferInstance, inferInstance, n / 3, hcard', hn3, ⟨e⟩, ?_⟩
  intro β hβ
  refine mem_zpowers_of_forall_fixedFieldImage (K := K) τ ?_
  intro j hj
  exact hβ j (by rw [hfix, Subgroup.mem_subgroupOf]; exact hj)

end ModelC

end CFSG.StandardType
