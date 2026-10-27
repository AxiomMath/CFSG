module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofSylow
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarSylow

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG.Open (ordTrialityD4)

namespace Item1120V0Bar

theorem isCyclic_sylow_three_sl2 {F : Type} [Field F] [Finite F] (h2 : ringChar F = 2)
    (P : Sylow 3 (Matrix.SpecialLinearGroup (Fin 2) F)) : IsCyclic P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI hchar : CharP F 2 := by
    rw [← h2]
    exact ringChar.charP F
  have hneg : (-1 : F) = 1 := CharTwo.neg_eq 1
  have hcenter : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) = 1 :=
    CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one hneg
  have hN : ¬ 3 ∣ Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    rw [hcenter]
    norm_num
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have hcard : Nat.card F = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hn]
  rcases Nat.lt_or_ge (Nat.card F) 4 with hlt | h4
  ·
    have hn1 : (n : ℕ) = 1 := by
      by_contra hne
      have hn2 : 2 ≤ (n : ℕ) := by
        have := n.pos
        omega
      have h4le : 4 ≤ 2 ^ (n : ℕ) := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) hn2
      omega
    have hF2 : Nat.card F = 2 := by
      rw [hcard, hn1, pow_one]
    have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 6 := by
      rw [CFSG.BenderSuzuki.External.huppert614_card_specialLinearGroup, hF2] <;> norm_num
    exact CFSG.RankThree.PartTwo.Sec11.KS11LieProof.isCyclic_sylow_three_of_not_nine_dvd
      (by rw [hSL]; norm_num) P
  ·
    refine CFSG.RankThree.PartTwo.Sec11.KS11LieProof.isCyclic_sylow_of_quotient
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) hN ?_ P
    intro S
    exact CFSG.RankThree.PartTwo.KFacts.isCyclic_sylow_three_psl2
      (by rw [h2]; norm_num) h4 S

theorem exists_big_elt_of_cyclic_sylow {Z : Type} [Group Z] [Finite Z] {M : Subgroup Z}
    (hM : ∀ P : Sylow 3 M, IsCyclic P) {z : Z} (hzM : z ∈ M) (hz3 : z ^ 3 = 1) :
    ∃ ζ ∈ M, z * ζ = ζ * z ∧ (∃ k : ℕ, ζ ^ 3 ^ k = 1) ∧
      orderOf ζ = 3 ^ (Nat.card M).factorization 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzP : IsPGroup 3 (Subgroup.zpowers z) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hz3
  obtain ⟨T, hT, hzT⟩ := exists_isSylowOf_ge (Subgroup.zpowers_le.mpr hzM) hzP
  have hTM : T ≤ M := hT.le
  have hTp : IsPGroup 3 ↥T := hT.isPGroup
  have hTcard : Nat.card ↥T = 3 ^ (Nat.card M).factorization 3 := hT.card_eq
  obtain ⟨Q, hQ⟩ := hT
  have Φ : ↥T ≃* ↥(Q : Subgroup ↥M) :=
    (MulEquiv.subgroupCongr hQ.symm).trans
      (Subgroup.equivMapOfInjective (Q : Subgroup ↥M) M.subtype M.subtype_injective).symm
  haveI : IsCyclic ↥T := (MulEquiv.isCyclic Φ).mpr (hM Q)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥T)
  have hzg : (⟨z, hzT (Subgroup.mem_zpowers z)⟩ : ↥T) ∈ Subgroup.zpowers g := hg _
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hzg
  have hzm : (g : Z) ^ m = z := by
    have h2 := congrArg Subtype.val hm
    simpa using h2
  refine ⟨(g : Z), hTM g.2, ?_, ?_, ?_⟩
  · rw [← hzm]
    exact (Commute.refl (g : Z)).zpow_left m
  · obtain ⟨k, hk⟩ := hTp g
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · have h1 : orderOf (g : Z) = orderOf g :=
      orderOf_injective T.subtype Subtype.coe_injective g
    rw [h1, orderOf_eq_card_of_forall_mem_zpowers hg]
    exact hTcard

theorem three_dvd_sq_sub_one_of_not_dvd {q : ℕ} (hq3 : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  have hmod : q % 3 = 1 ∨ q % 3 = 2 := by omega
  have hsq : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod]
    rcases hmod with h | h <;> simp [h]
  omega

theorem q8_q4_mod_nine {q : ℕ} (hq3 : ¬ 3 ∣ q) : (q ^ 8 + q ^ 4 + 1) % 9 = 3 := by
  have hm : Nat.ModEq 9 q (q % 9) := (Nat.mod_modEq q 9).symm
  have hn : (q ^ 8 + q ^ 4 + 1) % 9 = ((q % 9) ^ 8 + (q % 9) ^ 4 + 1) % 9 :=
    ((hm.pow 8).add (hm.pow 4)).add_right 1
  have h9 : q % 9 = 1 ∨ q % 9 = 2 ∨ q % 9 = 4 ∨ q % 9 = 5 ∨ q % 9 = 7 ∨ q % 9 = 8 := by
    omega
  rw [hn]
  rcases h9 with h | h | h | h | h | h <;> rw [h] <;> norm_num

theorem factorization_sixth_sub_one {q : ℕ} (hq2 : 2 ≤ q) (hq3 : ¬ 3 ∣ q) :
    (q ^ 6 - 1).factorization 3 = (q ^ 2 - 1).factorization 3 + 1 := by
  have hq : 0 < q := by omega
  have hq2sq : 4 ≤ q ^ 2 := by nlinarith
  have hdvd : 3 ∣ q ^ 2 - 1 := three_dvd_sq_sub_one_of_not_dvd hq3
  have hndvd2 : ¬ 3 ∣ q ^ 2 := fun h => hq3 (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
  have hodd3 : Odd (3 : ℕ) := ⟨1, by norm_num⟩
  have h6 : (q ^ 2) ^ 3 = q ^ 6 := by ring
  have hL : padicValNat 3 ((q ^ 2) ^ 3 - 1 ^ 3) = padicValNat 3 (q ^ 2 - 1) + padicValNat 3 3 :=
    padicValNat.pow_sub_pow hodd3 (by omega) hdvd hndvd2 (by norm_num)
  have h33 : padicValNat 3 3 = 1 := padicValNat_self
  rw [h6, one_pow, h33] at hL
  rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three, hL]

theorem factorization_q8_q4_one {q : ℕ} (hq3 : ¬ 3 ∣ q) :
    (q ^ 8 + q ^ 4 + 1).factorization 3 = 1 := by
  have hmod := q8_q4_mod_nine hq3
  have hn : q ^ 8 + q ^ 4 + 1 ≠ 0 := by omega
  have h1 : 3 ^ 1 ∣ q ^ 8 + q ^ 4 + 1 := by
    rw [pow_one]
    omega
  have h2 : ¬ 3 ^ 2 ∣ q ^ 8 + q ^ 4 + 1 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
    omega
  have a1 := (Nat.prime_three.pow_dvd_iff_le_factorization hn).1 h1
  have a2 : ¬ 2 ≤ (q ^ 8 + q ^ 4 + 1).factorization 3 := fun h =>
    h2 ((Nat.prime_three.pow_dvd_iff_le_factorization hn).2 h)
  omega

theorem factorization_ordTrialityD4 {q : ℕ} (hq2 : 2 ≤ q) (hq3 : ¬ 3 ∣ q) :
    (ordTrialityD4 q).factorization 3 = 2 * (q ^ 2 - 1).factorization 3 + 2 := by
  have hq : 0 < q := by omega
  have hq2sq : 4 ≤ q ^ 2 := by nlinarith
  have hq6le : q ^ 2 ≤ q ^ 6 := Nat.pow_le_pow_right hq (by norm_num)
  have hA : q ^ 12 ≠ 0 := pow_ne_zero 12 hq.ne'
  have hB : q ^ 8 + q ^ 4 + 1 ≠ 0 := by omega
  have hC : q ^ 6 - 1 ≠ 0 := by omega
  have hD : q ^ 2 - 1 ≠ 0 := by omega
  have e12 : (q ^ 12).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => hq3 (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h))
  have e8 := factorization_q8_q4_one hq3
  have e6 := factorization_sixth_sub_one hq2 hq3
  unfold ordTrialityD4
  rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero hA hB) hC) hD,
    Nat.factorization_mul (mul_ne_zero hA hB) hC, Nat.factorization_mul hA hB,
    Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply, e12, e8, e6]
  omega

theorem factorization_card_SL2_cube {q : ℕ} (hq2 : 2 ≤ q) (hq3 : ¬ 3 ∣ q) :
    ((q ^ 3) * ((q ^ 3) ^ 2 - 1)).factorization 3 = (q ^ 2 - 1).factorization 3 + 1 := by
  have hq : 0 < q := by omega
  have hq2sq : 4 ≤ q ^ 2 := by nlinarith
  have hq6le : q ^ 2 ≤ q ^ 6 := Nat.pow_le_pow_right hq (by norm_num)
  have h6 : (q ^ 3) ^ 2 = q ^ 6 := by ring
  have hA : q ^ 3 ≠ 0 := pow_ne_zero 3 hq.ne'
  have hB : q ^ 6 - 1 ≠ 0 := by omega
  have e3 : (q ^ 3).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => hq3 (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h))
  have e6 := factorization_sixth_sub_one hq2 hq3
  rw [h6, Nat.factorization_mul hA hB, Finsupp.add_apply, e3, e6, zero_add]

end Item1120V0Bar

end CFSG.RankThree.PartTwo.Sec11

end
