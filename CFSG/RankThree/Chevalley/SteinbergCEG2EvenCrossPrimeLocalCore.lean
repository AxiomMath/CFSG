module

public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenLocalCoreIntersection

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
open scoped Pointwise

open EvenG2

theorem even_G2_cross_prime_local_core_product_odd {f : ℕ} (hf : 2 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (B : Subgroup (MulAut (adjointGroup .G2 K)))
    (hB : (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ≤ B)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) (t : B)
    (htE : t ∈ E) (ht1 : t ≠ 1) :
    thetaT p E = ⊥ ∧
    Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ :
      Subgroup B)) ∧
    ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ : Subgroup B) :
        Set B) * (thetaT p E : Set B) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ ⊔ thetaT p E :
        Subgroup B) : Set B) ∧
    Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ ⊔
      thetaT p E)) ∧
    ((t : MulAut (adjointGroup .G2 K)) ∉
        (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range →
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}) = ⊥ ∧
      ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ : Subgroup B) :
          Set B) * (thetaT p E : Set B) = {1}) := by
  have hIB := even_G2_thetaT_eq_bot hf K hK hp hp3 B hB E hE hEcard
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  have hEpow : ∀ a ∈ E, a ^ p = 1 := fun a ha => by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p E) ⟨a, ha⟩
    simpa using congrArg Subtype.val h
  have htp : orderOf t = p := orderOf_eq_prime (hEpow t htE) ht1
  have hnon : (t : MulAut (adjointGroup .G2 K)) ∉
      (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range →
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}) = ⊥ := fun htinn =>
    localCore_eq_bot_of_noninner hf hK hp hB htinn htp
  have hodd : Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p)
      (Subgroup.centralizer {t}), E⁆ : Subgroup B)) := by
    by_cases htinn : (t : MulAut (adjointGroup .G2 K)) ∈
        (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range
    · exact even_G2_odd_card_commutator_inner hf K hK hp hp3 B hB E hE t htE ht1 htinn
    · rw [hnon htinn, Subgroup.commutator_bot_left, Subgroup.card_bot]
      exact odd_one
  refine ⟨hIB, hodd, ?_, ?_, fun htinn => ⟨hnon htinn, ?_⟩⟩
  · rw [hIB, sup_bot_eq, Subgroup.coe_bot, Set.mul_singleton]
    simp
  · rw [hIB, sup_bot_eq]
    exact hodd
  · rw [hnon htinn, Subgroup.commutator_bot_left, hIB, Subgroup.coe_bot,
      Set.singleton_mul_singleton, one_mul]

end CFSG.RankThree.Chevalley
