module

public import CFSG.Open.LocalVocabulary
import CFSG.HardMathSupport.Curtis.Proving.CentralizerMono
import CFSG.GroupTheory.PRankBound
import TauCeti.RepresentationTheory.CharacterTable.Solvable

public section

namespace CFSG.Permutation

open Equiv Equiv.Perm

theorem card_support_eq_three_or_six_or_nine {σ : Equiv.Perm (Fin 11)} (hσ : orderOf σ = 3) :
    σ.support.card = 3 ∨ σ.support.card = 6 ∨ σ.support.card = 9 := by
  have hσ3 : σ ^ 3 = 1 := by
    rw [← hσ]
    exact pow_orderOf_eq_one σ
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hct : σ.cycleType = Multiset.replicate σ.cycleType.card 3 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hσ3
  have hne : σ.cycleType ≠ 0 := by
    intro h
    have h1 : σ = 1 := Equiv.Perm.cycleType_eq_zero.mp h
    rw [h1] at hσ
    simp at hσ
  have hpos : 0 < σ.cycleType.card := Multiset.card_pos.mpr hne
  have hsum : σ.support.card = σ.cycleType.card * 3 := by
    rw [← Equiv.Perm.sum_cycleType, hct, Multiset.sum_replicate, Multiset.card_replicate]
    simp
  have hle : σ.cycleType.card ≤ 3 := by
    have h := Equiv.Perm.sum_cycleType_le σ
    rw [hct, Multiset.sum_replicate, Fintype.card_fin] at h
    simp at h
    omega
  omega

theorem card_centralizer_of_card_support_eq_nine {σ : Equiv.Perm (Fin 11)}
    (hσ : orderOf σ = 3) (hs : σ.support.card = 9) :
    Nat.card ↥(Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 11)))) = 324 := by
  have hσ3 : σ ^ 3 = 1 := by
    rw [← hσ]
    exact pow_orderOf_eq_one σ
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hct : σ.cycleType = Multiset.replicate 3 3 := by
    have h := Equiv.Perm.cycleType_of_pow_prime_eq_one hσ3
    have hsum : σ.cycleType.sum = 9 := by
      rw [Equiv.Perm.sum_cycleType, hs]
    rw [h, Multiset.sum_replicate] at hsum
    simp at hsum
    have hcard : σ.cycleType.card = 3 := by omega
    simpa [hcard] using h
  rw [Equiv.Perm.nat_card_centralizer, hct]
  decide

theorem isSolvable_centralizer_alternatingGroup_of_card_support_eq_nine
    {σ : alternatingGroup (Fin 11)} (hσ : orderOf σ = 3)
    (hs : (σ : Equiv.Perm (Fin 11)).support.card = 9) :
    IsSolvable ↥(Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11)))) := by
  have hσ' : orderOf (σ : Equiv.Perm (Fin 11)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hσ
  have hdvd :
      Nat.card ↥(Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11)))) ∣ 324 := by
    rw [← card_centralizer_of_card_support_eq_nine hσ' hs]
    exact CFSG.HardMathSupport.Curtis.Proving.card_centralizer_subtype_dvd σ.2
  refine TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow (a := 2) (b := 4)
    Nat.prime_two Nat.prime_three ?_
  calc Nat.card ↥(Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))))
      ∣ 324 := hdvd
    _ = 2 ^ 2 * 3 ^ 4 := by norm_num

theorem not_sq_dvd_card_centralizer_of_orderOf_eq_three {n : ℕ} (hn : n ≤ 11) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {y : Equiv.Perm (Fin n)} (hy : orderOf y = 3) :
    ¬ p ^ 2 ∣ Nat.card ↥(Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin n)))) := by
  intro hdiv
  have hy3 : y ^ 3 = 1 := by
    rw [← hy]
    exact pow_orderOf_eq_one y
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hct : y.cycleType = Multiset.replicate y.cycleType.card 3 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hy3
  have hy1 : y ≠ 1 := by
    rintro rfl
    simp at hy
  have hne : y.cycleType ≠ 0 := fun h => hy1 (Equiv.Perm.cycleType_eq_zero.mp h)
  have hkpos : 0 < y.cycleType.card := Multiset.card_pos.mpr hne
  have hk3 : y.cycleType.card ≤ 3 := by
    have h := Equiv.Perm.sum_cycleType_le y
    rw [hct, Multiset.sum_replicate, Fintype.card_fin] at h
    simp at h
    omega
  have hm8 : n - y.cycleType.card * 3 ≤ 8 := by omega
  have hcard : Nat.card ↥(Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin n)))) =
      (n - y.cycleType.card * 3).factorial * 3 ^ y.cycleType.card *
        y.cycleType.card.factorial := by
    rw [Equiv.Perm.nat_card_centralizer, hct]
    simp [Multiset.sum_replicate, Multiset.prod_replicate, Multiset.toFinset_replicate,
      Multiset.count_replicate_self, hkpos.ne', Finset.prod_singleton, nsmul_eq_mul]
  rw [hcard, mul_assoc] at hdiv
  have hpk : ¬ p ∣ 3 ^ y.cycleType.card * y.cycleType.card.factorial := by
    intro h
    rcases hp.dvd_mul.mp h with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)) (by omega)
    · have := hp.dvd_factorial.mp h
      omega
  have hcop : Nat.Coprime (p ^ 2) (3 ^ y.cycleType.card * y.cycleType.card.factorial) :=
    Nat.Coprime.pow_left 2 (hp.coprime_iff_not_dvd.mpr hpk)
  have hpm : p ^ 2 ∣ (n - y.cycleType.card * 3).factorial :=
    hcop.dvd_of_dvd_mul_right hdiv
  have h8 : p ^ 2 ∣ Nat.factorial 8 := hpm.trans (Nat.factorial_dvd_factorial hm8)
  have hp8 : p ≤ 8 :=
    hp.dvd_factorial.mp ((dvd_pow_self p (n := 2) (by norm_num)).trans h8)
  have hp67 : p = 5 ∨ p = 7 := by
    have h6 : p ≠ 6 := by
      rintro rfl
      norm_num at hp
    have h8' : p ≠ 8 := by
      rintro rfl
      norm_num at hp
    omega
  rcases hp67 with rfl | rfl <;> norm_num at h8

theorem pRank_centralizer_le_one_of_orderOf_eq_three {n : ℕ} (hn : n ≤ 11) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {y : Equiv.Perm (Fin n)} (hy : orderOf y = 3) :
    CFSG.Open.pRank p (Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin n)))) ≤ 1 :=
  CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ hp
    (by simpa using not_sq_dvd_card_centralizer_of_orderOf_eq_three hn hp hp5 hy)

theorem pRank_centralizer_alternatingGroup_le_one_of_orderOf_eq_three {n : ℕ} (hn : n ≤ 11)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {y : alternatingGroup (Fin n)}
    (hy : orderOf y = 3) :
    CFSG.Open.pRank p (Subgroup.centralizer ({y} : Set (alternatingGroup (Fin n)))) ≤ 1 := by
  have hy' : orderOf (y : Equiv.Perm (Fin n)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hy
  refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ hp ?_
  intro hA
  exact not_sq_dvd_card_centralizer_of_orderOf_eq_three hn hp hp5 hy'
    (hA.trans (CFSG.HardMathSupport.Curtis.Proving.card_centralizer_subtype_dvd y.2))

end CFSG.Permutation
