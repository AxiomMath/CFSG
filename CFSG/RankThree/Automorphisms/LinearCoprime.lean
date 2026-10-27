module

public import CFSG.RankThree.Automorphisms.LinearHigherCoprime
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder

public section

namespace CFSG.RankThree.Automorphisms

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem linear_two_coprime_odd_prime_automorphism_subgroups_cyclic {K : Type} [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hpT : ¬ p ∣ Nat.card (projectiveSL 2 K)) :
    ∀ P : Subgroup (MulAut (projectiveSL 2 K)), IsPGroup p P → IsCyclic P := by
  have : Fact p.Prime := ⟨hp⟩
  let eT : projectiveSL 2 K ≃* coordinateG K :=
    (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 2 K)).trans (pslEquivCoordinateG K)
  have hDG : Nat.card (CoordinateQuotientDG K) ∣ 2 := by
    rw [← Nat.card_congr (pglQuotientEquivCoordinateDG K).toEquiv]
    exact (card_pgl_quotient_psl_dvd K).trans (Nat.gcd_dvd_left 2 _)
  have hGcop : Nat.Coprime (Nat.card ((coordinateG K).subgroupOf (coordinateD K))) p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (coordinateG_le_D K)).toEquiv,
      ← Nat.card_congr eT.toEquiv]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hpT).symm
  have hDcop : Nat.Coprime (Nat.card ((coordinateD K).subgroupOf (coordinateE K))) p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (coordinateD_le_E K)).toEquiv,
      ((coordinateG K).subgroupOf (coordinateD K)).card_eq_card_quotient_mul_card_subgroup]
    exact Nat.Coprime.mul_left
      (Nat.Coprime.coprime_dvd_left hDG (Nat.coprime_two_left.2 hodd)) hGcop
  have : IsCyclic (CoordinateQuotientED K) := coordinateED_isCyclic K
  have hE : ∀ Q : Subgroup (coordinateE K), IsPGroup p Q → IsCyclic Q := fun Q hQ =>
    isCyclic_of_injective _ (injective_comp_of_isPGroup
      (QuotientGroup.mk' ((coordinateD K).subgroupOf (coordinateE K)))
      (by rw [QuotientGroup.ker_mk']; exact hDcop) hQ)
  have hG : ∀ P : Subgroup (MulAut (coordinateG K)), IsPGroup p P → IsCyclic P := by
    intro P hP
    have hinj : Function.Injective
        ((coordinateConjugationEquiv K).symm.toMonoidHom.comp P.subtype) :=
      (coordinateConjugationEquiv K).symm.injective.comp Subtype.val_injective
    have := hE _ (hP.map (coordinateConjugationEquiv K).symm.toMonoidHom)
    exact isCyclic_of_injective_comp_of_isCyclic_map _ P hinj
  exact fun P hP => isCyclic_of_isPGroup_of_mulEquiv eT hG hP

theorem linear_coprime_odd_prime_automorphism_subgroups_cyclic {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 2 ≤ n) {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hpT : ¬ p ∣ Nat.card (projectiveSL n K)) :
    (∀ P : Subgroup (MulAut (projectiveSL n K)), IsPGroup p P → IsCyclic P) ∧
    ∀ (E : Type*) [Group E] [IsElementaryAbelian p E], Nat.card E = p ^ 2 →
      ∀ α : E →* MulAut (projectiveSL n K), p ≤ Nat.card α.ker := by
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
  · have hcyc := linear_two_coprime_odd_prime_automorphism_subgroups_cyclic hp hodd hpT
    exact ⟨hcyc, fun E _ _ hE α => le_card_ker_of_isElementaryAbelian hp hcyc hE α⟩
  · exact higher_linear_coprime_odd_prime_automorphism_subgroups_cyclic hn3 hp hodd hpT

end CFSG.RankThree.Automorphisms
