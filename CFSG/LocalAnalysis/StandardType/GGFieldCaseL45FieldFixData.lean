module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Fixed

theorem gff_ggAutFixedSubgroup_eq_entrywiseFixedGroup (τ : Tag) {K : Type} [Field K]
    (σ : K ≃+* K) :
    ggAutFixedSubgroup (entrywiseAdjointAut τ σ) =
      (entrywiseFixedGroup τ σ).subgroupOf (adjointGroup τ K) := by
  ext u
  change entrywiseAdjointAut τ σ u = u ↔ (u : ModGL τ K) ∈ entrywiseFixedGroup τ σ
  rw [mem_entrywiseFixedGroup]
  constructor
  · intro h
    refine ⟨u.2, ?_⟩
    exact (coe_entrywiseAdjointAut (τ := τ) (K := K) σ u).symm.trans (congrArg Subtype.val h)
  · rintro ⟨-, h⟩
    exact Subtype.ext ((coe_entrywiseAdjointAut (τ := τ) (K := K) σ u).trans h)

theorem gff_fixed_data {τ : Tag} (hτ : τ = .F4 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {σ : K ≃+* K} {p : ℕ} (hp : 0 < p)
    (hσ : orderOf σ = p) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (n' : ℕ), Nat.card k = 2 ^ n' ∧ n = p * n' ∧
      1 ≤ n' ∧ Nonempty (adjointGroup τ k ≃* ↥(ggAutFixedSubgroup (entrywiseAdjointAut τ σ))) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcharP : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hchar : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨hdvd, hcard⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield (p := 2) (f := n)
      Nat.prime_two hn hK σ
  rw [hσ] at hdvd hcard
  obtain ⟨n', hn'⟩ := hdvd
  have hdiv : n / p = n' := by rw [hn']; exact Nat.mul_div_cancel_left n' hp
  rw [hdiv] at hcard
  have hn'1 : 1 ≤ n' := by
    rcases Nat.eq_zero_or_pos n' with h | h
    · rw [h, Nat.mul_zero] at hn'
      omega
    · exact h
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have hfix : ggAutFixedSubgroup (entrywiseAdjointAut τ σ) =
      (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) := by
    rw [gff_ggAutFixedSubgroup_eq_entrywiseFixedGroup τ σ,
      entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two hτ' hchar σ]
  have hJC : fixedFieldImage τ σ ≤ adjointGroup τ K :=
    fun x hx => (fixedFieldImage_le hx).1
  let e : adjointGroup τ ↥(fixSubfield σ) ≃*
      ↥(ggAutFixedSubgroup (entrywiseAdjointAut τ σ)) :=
    (fixedFieldImageEquiv (τ := τ) σ).trans
      ((Subgroup.subgroupOfEquivOfLe hJC).symm.trans (MulEquiv.subgroupCongr hfix.symm))
  exact ⟨↥(fixSubfield σ), inferInstance, inferInstance, n', hcard, hn', hn'1, ⟨e⟩⟩

end Fixed

end CFSG.StandardType
