module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Defs
public import CFSG.Quasithin.EmptyFaithful.A38c12FieldOne
public import CFSG.Quasithin.EmptyFaithful.S146zXGOrder

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.GoldS146R

namespace F146Field

section Bounds

private theorem sq_ge {q : ℕ} (hq : 4 ≤ q) : 16 ≤ q ^ 2 := by nlinarith

private theorem cube_ge {q : ℕ} (hq : 4 ≤ q) : 64 ≤ q ^ 3 := by nlinarith [sq_ge hq]

private theorem fourth_ge {q : ℕ} (hq : 4 ≤ q) : 256 ≤ q ^ 4 := by nlinarith [sq_ge hq]

theorem lt_ordA_two {q : ℕ} (hq : 4 ≤ q) : 360 < ordA 2 q := by
  rw [ordA_two_eq]
  have hg : Nat.gcd 3 (q - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hX : 1083 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    have h2 := sq_ge hq
    have h3 := cube_ge hq
    calc 1083 ≤ 64 * (15 * 63) := by norm_num
      _ ≤ _ := Nat.mul_le_mul h3 (Nat.mul_le_mul (by omega) (by omega))
  calc 360 < 1083 / 3 := by norm_num
    _ ≤ (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) / 3 := Nat.div_le_div_right hX
    _ ≤ _ := Nat.div_le_div_left hg (by norm_num)

theorem lt_ordTwistedA_two {q : ℕ} (hq : 4 ≤ q) : 360 < ordTwistedA 2 q := by
  rw [ordTwistedA_two_eq' q (by omega)]
  have hg : Nat.gcd 3 (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hX : 1083 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    have h2 := sq_ge hq
    have h3 := cube_ge hq
    calc 1083 ≤ 64 * (15 * 65) := by norm_num
      _ ≤ _ := Nat.mul_le_mul h3 (Nat.mul_le_mul (by omega) (by omega))
  calc 360 < 1083 / 3 := by norm_num
    _ ≤ (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) / 3 := Nat.div_le_div_right hX
    _ ≤ _ := Nat.div_le_div_left hg (by norm_num)

theorem lt_ordBC_two {q : ℕ} (hq : 4 ≤ q) (hodd : Odd (q - 1)) : 360 < ordBC 2 q := by
  have hg : Nat.gcd 2 (q - 1) = 1 := Nat.coprime_two_left.mpr hodd
  unfold ordBC
  rw [hg, Nat.div_one, show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  have h2 := sq_ge hq
  have h4 := fourth_ge hq
  calc 360 < 16 * 15 * 255 := by norm_num
    _ ≤ q ^ (2 * 2) * ((q ^ (2 * 1) - 1) * (q ^ (2 * 2) - 1)) := by
      have e1 : q ^ (2 * 1) = q ^ 2 := by norm_num
      have e2 : q ^ (2 * 2) = q ^ 4 := by norm_num
      rw [e1, e2]
      rw [show 16 * 15 * 255 = 16 * (15 * 255) by norm_num]
      refine Nat.mul_le_mul ?_ (Nat.mul_le_mul (by omega) (by omega))
      omega

theorem lt_ordSuzuki {q : ℕ} (hq : 4 ≤ q) : 360 < ordSuzuki q := by
  rw [ordSuzuki_eq]
  have h2 := sq_ge hq
  calc 360 < 16 * (17 * 3) := by norm_num
    _ ≤ q ^ 2 * ((q ^ 2 + 1) * (q - 1)) :=
      Nat.mul_le_mul h2 (Nat.mul_le_mul (by omega) (by omega))

end Bounds

section Profile

variable {X : Type} [Group X] {n : ℕ}

theorem profile_psl_two (hn : 2 ≤ n) (h : IsPSL 2 2 n X) :
    SrcProfile (Nat.card X) ∧ Nat.card X ≠ 168 ∧ Nat.card X ≠ 360 := by
  have hc : Nat.card X = ordL2 n := card_isPSL_two_two h
  rw [hc]
  exact ⟨srcProfile_ordL2 hn, (ordL2_ne n hn).1, (ordL2_ne n hn).2⟩

theorem profile_sz (hn : 2 ≤ n) (h : IsSz n X) :
    SrcProfile (Nat.card X) ∧ Nat.card X ≠ 168 ∧ Nat.card X ≠ 360 := by
  obtain ⟨-, -, -, hc⟩ := S146zX.card_isSz h
  have hc' : Nat.card X = ordSuzuki (2 ^ n) := by
    rw [hc, ordSuzuki]
    ring
  have h4 := four_le_two_pow hn
  have hlt := lt_ordSuzuki h4
  rw [hc']
  exact ⟨srcProfile_ordSuzuki hn, by omega, by omega⟩

theorem profile_psu_three (hn : 2 ≤ n) (h : IsPSU 3 2 n X) :
    SrcProfile (Nat.card X) ∧ Nat.card X ≠ 168 ∧ Nat.card X ≠ 360 := by
  have hc : Nat.card X = ordTwistedA 2 (2 ^ n) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.1 rfl
  have h4 := four_le_two_pow hn
  have hlt := lt_ordTwistedA_two h4
  rw [hc]
  exact ⟨srcProfile_ordTwistedA_two hn, by omega, by omega⟩

theorem profile_psl_three (hn : 2 ≤ n) (h : IsPSL 3 2 n X) :
    SrcProfile (Nat.card X) ∧ Nat.card X ≠ 168 ∧ Nat.card X ≠ 360 := by
  have hc : Nat.card X = ordA 2 (2 ^ n) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
  have h4 := four_le_two_pow hn
  have hlt := lt_ordA_two h4
  rw [hc]
  exact ⟨srcProfile_ordA_two (by omega), by omega, by omega⟩

theorem profile_sp_four (hn : 2 ≤ n) (h : E2.IsSp4Prime n X) :
    SrcProfile (Nat.card X) ∧ Nat.card X ≠ 168 ∧ Nat.card X ≠ 360 := by
  have h1 : IsPSp4 2 n X := by
    have hn1 : n ≠ 1 := by omega
    simpa [E2.IsSp4Prime, hn1] using h
  have hc : Nat.card X = ordBC 2 (2 ^ n) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two h1).2.2.1 rfl
  have h4 := four_le_two_pow hn
  have hodd : Odd (2 ^ n - 1) := by
    have h5 := odd_two_pow_pow_sub_one' (n := n) (k := 1) (by omega) le_rfl
    simpa using h5
  have hlt := lt_ordBC_two h4 hodd
  rw [hc]
  exact ⟨srcProfile_ordBC_two hn, by omega, by omega⟩

end Profile

section Field

variable {Γ : Type} [Group Γ]

theorem profile_of_field {H T M K : Subgroup Γ} {n : ℕ} (hn : 2 ≤ n)
    (h : A38c12.E22Field H T M K n) :
    SrcProfile (Nat.card ↥(E2.star M H K)) ∧ Nat.card ↥(E2.star M H K) ≠ 168 ∧
      Nat.card ↥(E2.star M H K) ≠ 360 := by
  unfold A38c12.E22Field at h
  rcases h with ⟨-, h | h, -⟩ | ⟨⟨-, h | h | h⟩, -⟩ | ⟨-, h | h, -⟩
  · exact profile_psl_two hn h
  · exact profile_sz hn h
  · exact profile_psl_two hn h
  · exact profile_sz hn h
  · exact profile_psu_three hn h
  · exact profile_psl_three hn h
  · exact profile_sp_four hn h

end Field

section Cases

variable {Γ : Type} [Group Γ]

theorem e22CasesBig_of_field (hA : ArithAll) {H T M K : Subgroup Γ} {n : ℕ} (hn : 2 ≤ n)
    (hF : A38c12.E22Field H T M K n) (hc : E2.E22CasesNoN H T M K) : E22CasesBig H T M K := by
  obtain ⟨hprof, h168, h360⟩ := profile_of_field hn hF
  unfold E2.E22CasesNoN at hc
  dsimp only at hc
  unfold E22CasesBig
  dsimp only
  rcases hc with ⟨hker, t, ht, hne, hMeq, h1⟩ | ⟨hTN, hker2, h2⟩
  · left
    rcases h1 with ⟨m, hm2, hty, hB⟩ | ⟨p, hp, hp8, hPSL, -, -⟩
    · exact ⟨hker, ⟨t, ht, hne, hMeq⟩, m, hm2, hty, hB⟩
    · exfalso
      have hp3 : 3 < p := by
        have := hp.two_le
        omega
      have hT1 : IsT1 p 1 := ⟨hp, hp3, Or.inl rfl, by simpa using hp8⟩
      exact h168 (hA.t1 _ p 1 hprof hT1 _ hPSL rfl).1
  · right
    refine ⟨hTN, hker2, ?_⟩
    rcases h2 with ⟨m, hBen, hBor⟩ | ⟨m, hm1, hshape, hdiag, hBor⟩ |
        ⟨p, e, hp, hp3, he, h8, hPSL, -, -⟩ | ⟨p, hp, -, hcase, -⟩
    · exact Or.inl ⟨m, hBen, hBor⟩
    · by_cases hm : m = 1
      · subst hm
        exfalso
        rcases card_of_shape_two_b hshape with h5 | h5
        · exact h168 h5
        · exact h360 h5
      · exact Or.inr ⟨m, by omega, hshape, hdiag, hBor⟩
    · exfalso
      have hT1 : IsT1 p e := ⟨hp, hp3, he, h8⟩
      exact h168 (hA.t1 _ p e hprof hT1 _ hPSL rfl).1
    · exfalso
      rcases hcase with ⟨h4, hPSU⟩ | ⟨h4, hPSL, -⟩
      · exact hA.t2 _ p hprof hp h4 _ hPSU rfl
      · exact hA.t3 _ p hprof hp h4 _ hPSL rfl

end Cases

end F146Field

end CFSG.Quasithin
