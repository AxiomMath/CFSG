module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SCrit

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

variable {S : Type} [Group S] [Finite S]

theorem exists_sylow_le (h81 : ¬ 81 ∣ Nat.card S) {s : S} {K : Subgroup S} (hs3 : orderOf s = 3)
    (hsK : s ∈ K) (hKs : K ≤ Subgroup.centralizer {s}) (hKq : IsQuasisimple K)
    (hT : IsType425 (K ⧸ aschbacherSolvableCore 3 K)) :
    ∃ P : Sylow 3 S, (P : Subgroup S) ≤ K ∧ s ∈ (P : Subgroup S) ∧
      (P : Subgroup S) ≤ Subgroup.centralizer {s} := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h27K : 27 ∣ Nat.card K :=
    (twentySeven_dvd_card_of_isType425 (isQuasisimple_theta_quot hKq) hT).trans
      (card_theta_quot_dvd K)
  set k : K := ⟨s, hsK⟩ with hk
  have hk3 : IsPGroup 3 (Subgroup.zpowers k) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hk, Subgroup.orderOf_mk, hs3, pow_one])
  obtain ⟨Q, hQ⟩ := hk3.exists_le_sylow
  have hkQ : k ∈ (Q : Subgroup K) := hQ (Subgroup.mem_zpowers k)
  have h27Q : 27 ∣ Nat.card (Q : Subgroup K) :=
    Q.pow_dvd_card_of_pow_dvd_card (n := 3) (by norm_num; exact h27K)
  have hQ3 : IsPGroup 3 ((Q : Subgroup K).map K.subtype) := Q.isPGroup'.map _
  obtain ⟨P, hP⟩ := hQ3.exists_le_sylow
  have hPcard : Nat.card (P : Subgroup S) ≤ 27 := by
    rw [P.card_eq_multiplicity]
    by_contra hlt
    push Not at hlt
    have h4 : 4 ≤ (Nat.card S).factorization 3 := by
      by_contra h
      push Not at h
      have : 3 ^ (Nat.card S).factorization 3 ≤ 3 ^ 3 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    apply h81
    have : 3 ^ 4 ∣ 3 ^ (Nat.card S).factorization 3 := Nat.pow_dvd_pow 3 h4
    exact (by norm_num : (81 : ℕ) = 3 ^ 4) ▸
      this.trans (Nat.ordProj_dvd (Nat.card S) 3)
  have hmapcard : Nat.card ((Q : Subgroup K).map K.subtype) = Nat.card (Q : Subgroup K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hge : 27 ≤ Nat.card ((Q : Subgroup K).map K.subtype) := by
    rw [hmapcard]
    exact Nat.le_of_dvd Nat.card_pos h27Q
  have hPeq : (Q : Subgroup K).map K.subtype = (P : Subgroup S) :=
    Subgroup.eq_of_le_of_card_ge hP (by omega)
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [← hPeq]
    exact Subgroup.map_subtype_le _
  · rw [← hPeq]
    exact ⟨k, hkQ, rfl⟩
  · rw [← hPeq]
    exact (Subgroup.map_subtype_le _).trans hKs

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
