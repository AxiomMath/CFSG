module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryTwoRank
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU4FieldOuter
public import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Lem55Even
public import CFSG.Models.PGL
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryU4Arith
public import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders
public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGenTools
public import CFSG.RankThree.PartTwo.KFacts.K71OddChar

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Facts

variable {k : ℕ}

theorem center_projSU_four (hk : 1 ≤ k) : Subgroup.center (projSU 4 2 k) = ⊥ :=
  Sec4.RonanK432.center_projSU_four_two_eq_bot hk

theorem two_mul_le_twoRank_projSU_four (hk : 1 ≤ k) :
    2 * k ≤ CFSG.Open.twoRank (projSU 4 2 k) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (2 * k)) = (2 ^ k) ^ 2 := by
    rw [GaloisField.card 2 (2 * k) (by omega), ← pow_mul, mul_comm]
  have h := CFSG.GH74.GLS.Stage1.Thm3.Sec5.Lem55.two_mul_le_pRank_psu_even hK
  rw [CFSG.GH74.twoRank_eq_of_mulEquiv (Sec4.projSUEquivStatedProj 4 2 k)]
  exact h

@[expose] def ordU4 (k : ℕ) : ℕ :=
  (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1))

theorem card_projSU_four_eq_ordU4 (hk : 1 ≤ k) : Nat.card (projSU 4 2 k) = ordU4 k :=
  Sec4.RonanK432.card_projSU_four_two_eq hk

theorem ordU4_eq (hk : 1 ≤ k) : ordU4 k = 2 ^ (6 * k) *
    (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) := by
  rw [ordU4, ← pow_mul, mul_comm k 6]

theorem odd_ordU4_part (hk : 1 ≤ k) :
    Odd (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) :=
  ((Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)).mul
    (Timmesfeld.Orders.odd_pow_add_one (by omega) (by norm_num))).mul
      (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))

theorem ordU4_ne_card_SU3 (hk : 1 ≤ k) {m : ℕ} (hm : 1 ≤ m) :
    ordU4 k ≠ 2 ^ (3 * m) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1)) := by
  intro h
  rw [ordU4_eq hk] at h
  have hodd2 : Odd (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1)) :=
    (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)).mul
      (Timmesfeld.Orders.odd_pow_add_one (by omega) (by norm_num))
  have h6 := Sec4.HeringUnitary.two_pow_mul_eq_of_odd_mul (odd_ordU4_part hk) hodd2 h
  have hm2 : m = 2 * k := by omega
  subst hm2
  have e : 2 ^ (6 * k) = (2 ^ k) ^ 6 := by rw [← pow_mul, mul_comm]
  rw [show 3 * (2 * k) = 6 * k by ring] at h
  set s := 2 ^ k with hs
  have h2 : 2 ≤ s := by
    rw [hs]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hp2 : 2 ^ (2 * k) = s ^ 2 := by rw [hs, ← pow_mul, mul_comm]
  rw [hp2, e] at h
  have h4 : 1 ≤ s ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h2' : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h6' : 1 ≤ (s ^ 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3' : 1 ≤ s ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hpos : 0 < s ^ 6 * (s ^ 4 - 1) := by
    have : 1 < s ^ 4 := by nlinarith [pow_pos (by omega : 0 < s) 4, Nat.pow_le_pow_left h2 4]
    exact Nat.mul_pos (pow_pos (by omega) 6) (Nat.sub_pos_of_lt this)
  have key : s ^ 6 * (s ^ 4 - 1) * ((s ^ 2 - 1) * (s ^ 3 + 1)) =
      s ^ 6 * (s ^ 4 - 1) * (s ^ 6 + 1) := by
    zify [h4, h2', h6'] at h ⊢
    nlinarith [h]
  have := Nat.eq_of_mul_eq_mul_left hpos key
  zify [h2'] at this
  nlinarith [Nat.pow_le_pow_left h2 5, Nat.pow_le_pow_left h2 2, Nat.pow_le_pow_left h2 3]

theorem ordU4_ne_card_SL3 (hk : 1 ≤ k) {n : ℕ} (hn : 1 ≤ n) :
    ordU4 k ≠ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
  intro h0
  have hodd2 : Odd (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
    (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)).mul
      (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))
  have e3 : (2 ^ n) ^ 3 = 2 ^ (3 * n) := by rw [← pow_mul, mul_comm]
  have h : 2 ^ (6 * k) * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) =
      2 ^ (3 * n) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
    rw [← ordU4_eq hk, h0, e3]
  have h6 := Sec4.HeringUnitary.two_pow_mul_eq_of_odd_mul (odd_ordU4_part hk) hodd2 h
  have hn2 : n = 2 * k := by omega
  subst hn2
  rw [← e3] at h
  have e : 2 ^ (6 * k) = (2 ^ k) ^ 6 := by rw [← pow_mul, mul_comm]
  set s := 2 ^ k with hs
  have h2 : 2 ≤ s := by
    rw [hs]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hp2 : 2 ^ (2 * k) = s ^ 2 := by rw [hs, ← pow_mul, mul_comm]
  rw [hp2, e] at h
  have h4 : 1 ≤ s ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h2' : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h6' : 1 ≤ (s ^ 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3' : 1 ≤ s ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h66 : 1 ≤ (s ^ 2) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hpos : 0 < s ^ 6 * (s ^ 4 - 1) := by
    have : 1 < s ^ 4 := by nlinarith [pow_pos (by omega : 0 < s) 4, Nat.pow_le_pow_left h2 4]
    exact Nat.mul_pos (pow_pos (by omega) 6) (Nat.sub_pos_of_lt this)
  have h7 : 1 ≤ s ^ 6 := Nat.one_le_pow _ _ (by omega)
  have key : s ^ 6 * (s ^ 4 - 1) * ((s ^ 2 - 1) * (s ^ 3 + 1)) =
      s ^ 6 * (s ^ 4 - 1) * (s ^ 6 - 1) := by
    zify [h4, h2', h6', h66, h7] at h ⊢
    nlinarith [h]
  have := Nat.eq_of_mul_eq_mul_left hpos key
  zify [h2', h7] at this
  nlinarith [Nat.pow_le_pow_left h2 5, Nat.pow_le_pow_left h2 2, Nat.pow_le_pow_left h2 3,
    Nat.pow_le_pow_left h2 4]

theorem ordU4_ne_card_L2 (hk : 1 ≤ k) {m : ℕ} (hm : 1 ≤ m) :
    ordU4 k ≠ 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  intro h
  rw [ordU4_eq hk] at h
  have hodd2 : Odd ((2 ^ m) ^ 2 - 1) := Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)
  have h6 := Sec4.HeringUnitary.two_pow_mul_eq_of_odd_mul (odd_ordU4_part hk) hodd2 h
  have hm2 : m = 6 * k := by omega
  subst hm2
  have e : 2 ^ (6 * k) = (2 ^ k) ^ 6 := by rw [← pow_mul, mul_comm]
  set s := 2 ^ k with hs
  have h2 : 2 ≤ s := by
    rw [hs]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rw [e] at h
  have hpos : 0 < s ^ 6 := pow_pos (by omega) 6
  have key := Nat.eq_of_mul_eq_mul_left hpos h
  have h2' : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ s ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h12 : 1 ≤ (s ^ 6) ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h2', h4, h12] at key
  nlinarith [Nat.pow_le_pow_left h2 2, Nat.pow_le_pow_left h2 3, Nat.pow_le_pow_left h2 4,
    Nat.pow_le_pow_left h2 5, Nat.pow_le_pow_left h2 6, Nat.pow_le_pow_left h2 9,
    Nat.pow_le_pow_left h2 12]

end Facts

section Models

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

variable {X : Type} [Group X] {k : ℕ}

theorem card_projSU_four_eq_ordTwistedA (hk : 1 ≤ k) :
    Nat.card (projSU 4 2 k) = CFSG.Open.ordTwistedA 3 (2 ^ k) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm : StatedLieAdmissible .PSU 4 2 k :=
    ⟨Nat.prime_two, hk, by norm_num, fun h => absurd (Prod.mk.inj h).1 (by norm_num)⟩
  have hc := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm
    (MulEquiv.refl (projSU 4 2 k))
  exact (CFSG.Timmesfeld.card_statedClassicalModel_two hc).2.1 rfl

theorem card_eq_ordU4 (hk : 1 ≤ k) (e : X ≃* projSU 4 2 k) : Nat.card X = ordU4 k :=
  (Nat.card_congr e.toEquiv).trans (card_projSU_four_eq_ordU4 hk)

theorem thousand_lt_ordU4 (hk : 3 ≤ k) : 1000 < ordU4 k := by
  have h8 : 8 ≤ 2 ^ k := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hodd := odd_ordU4_part (by omega : 1 ≤ k)
  rw [ordU4_eq (by omega : 1 ≤ k)]
  have hpos : 1 ≤ ((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1) := hodd.pos
  have h6 : 2 ^ 18 ≤ 2 ^ (6 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 1000 < 2 ^ 18 := by norm_num
    _ ≤ 2 ^ (6 * k) := h6
    _ ≤ 2 ^ (6 * k) * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) :=
      Nat.le_mul_of_pos_right _ hpos

theorem ordU4_ne_of_mem (hk : 1 ≤ k) {m : ℕ}
    (hm : m ∈ CFSG.Timmesfeld.evenOrdersExceptUnitarySp4) : m ≠ ordU4 k := by
  intro h
  refine (CFSG.Timmesfeld.evenOrdersExceptUnitarySp4_ne hm).1 3 k (by norm_num) hk ?_
  rw [h, ← card_projSU_four_eq_ordU4 hk, card_projSU_four_eq_ordTwistedA hk]

theorem false_of_ordA {n : ℕ} (hk : 1 ≤ k) (e : X ≃* projSU 4 2 k) {i : ℕ} (hi : 1 ≤ i)
    (hne : (i, n) ≠ (1, 1)) (hn : 1 ≤ n) (hc : Nat.card X = CFSG.Open.ordA i (2 ^ n)) : False :=
  ordU4_ne_of_mem hk (m := CFSG.Open.ordA i (2 ^ n)) (Or.inl ⟨n, hn, Or.inl ⟨i, hi, hne, rfl⟩⟩)
    ((card_eq_ordU4 hk e).symm.trans hc).symm

theorem false_L3 (hk : 1 ≤ k) (e : X ≃* projSU 4 2 k) {n : ℕ} (hn : 1 ≤ n)
    (φ : X ≃* projSL 3 (GaloisField 2 n)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm : StatedLieAdmissible .PSL 3 2 n :=
    ⟨Nat.prime_two, hn, by norm_num, fun h => absurd (Prod.mk.inj h).1 (by norm_num),
      fun h => absurd (Prod.mk.inj h).1 (by norm_num)⟩
  have hc := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm φ
  exact false_of_ordA hk e (i := 2) (by norm_num) (by simp) hn
    ((CFSG.Timmesfeld.card_statedClassicalModel_two hc).1 rfl)

theorem false_L2 (hk : 1 ≤ k) (e : X ≃* projSU 4 2 k) {m : ℕ} (hm : 1 ≤ m)
    (φ : X ≃* projSL 2 (GaloisField 2 m)) : False := by
  have h1 : Nat.card X = 2 ^ m * ((2 ^ m) ^ 2 - 1) :=
    (Nat.card_congr φ.toEquiv).trans (Item812Res2.card_projSL_two hm)
  exact ordU4_ne_card_L2 hk hm ((card_eq_ordU4 hk e).symm.trans h1)

theorem false_SU3 (hk : 1 ≤ k) (e : X ≃* projSU 4 2 k) {m : ℕ} (hm : 1 ≤ m) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = (2 ^ m) ^ 2) (φ : X ≃* StatedSU 3 (2 ^ m) F) :
    False := by
  have h1 : Nat.card X = 2 ^ (3 * m) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1)) :=
    (Nat.card_congr φ.toEquiv).trans (Item87Proof.card_statedSU_three_two hF)
  exact ordU4_ne_card_SU3 hk hm ((card_eq_ordU4 hk e).symm.trans h1)

theorem false_SL3 (hk : 1 ≤ k) (e : X ≃* projSU 4 2 k) {n : ℕ} (hn : 1 ≤ n) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2 ^ n) (φ : X ≃* StatedSL 3 F) : False := by
  have h1 : Nat.card X = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
    rw [Nat.card_congr φ.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three, hF]
  exact ordU4_ne_card_SL3 hk hn ((card_eq_ordU4 hk e).symm.trans h1)

theorem false_U3 (hk : 3 ≤ k) (e : X ≃* projSU 4 2 k) {m : ℕ} (hm : 1 ≤ m)
    (φ : X ≃* projSU 3 2 m) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hm1 : m = 1
  · subst hm1
    have h72 : Nat.card X = 72 := by
      rw [Nat.card_congr φ.toEquiv, KFacts.card_projSU_three_two (le_refl 1)]
      decide
    have := thousand_lt_ordU4 hk
    rw [← card_eq_ordU4 (by omega) e, h72] at this
    omega
  · have hadm3 : StatedLieAdmissible .PSU 3 2 m :=
      ⟨Nat.prime_two, hm, by norm_num, fun h => by
        have := (Prod.mk.inj h).2
        have h2m : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega⟩
    have hadm4 : StatedLieAdmissible .PSU 4 2 k :=
      ⟨Nat.prime_two, by omega, by norm_num, fun h => absurd (Prod.mk.inj h).1 (by norm_num)⟩
    have hmod3 := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm3 φ
    have hmod4 : LieModel X .PSU 4 2 k :=
      Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm4 e⟩
    have := ((CFSG.RankThree.PartOne.S12K.lieRigidity3 X .PSU 4 k (Or.inl hmod4)).1) m hmod3
    exact absurd this.2.1 (by norm_num)

theorem false_Sp4 (hk : 3 ≤ k) (e : X ≃* projSU 4 2 k) {n : ℕ} (hn : 1 ≤ n)
    (φ : X ≃* projSp 2 (GaloisField 2 n)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hn1 : n = 1
  · subst hn1
    have h720 : Nat.card X = 720 := by
      rw [Nat.card_congr φ.toEquiv, Item812Res2.card_projSp_two_one]
    have := thousand_lt_ordU4 hk
    rw [← card_eq_ordU4 (by omega) e, h720] at this
    omega
  · have hadm2 : StatedLieAdmissible .PSp 2 2 n :=
      ⟨Nat.prime_two, hn, le_refl 2, fun h => by
        have := (Prod.mk.inj h).2
        have h2m : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega⟩
    have hadm4 : StatedLieAdmissible .PSU 4 2 k :=
      ⟨Nat.prime_two, by omega, by norm_num, fun h => absurd (Prod.mk.inj h).1 (by norm_num)⟩
    have hmod2 := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSp hadm2 φ
    have hmod4 : LieModel X .PSU 4 2 k :=
      Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm4 e⟩
    have := ((CFSG.RankThree.PartOne.S12K.lieRigidity3 X .PSU 4 k (Or.inl hmod4)).2.1) n hmod2
    exact absurd this.1 (by decide)

theorem mem_even_Sz {n : ℕ} (hodd : Odd n) (h3 : 3 ≤ n) :
    CFSG.Open.ordSuzuki (2 ^ n) ∈ CFSG.Timmesfeld.evenOrdersExceptUnitarySp4 := by
  refine Or.inl ⟨n, by omega, ?_⟩
  iterate 10 right
  exact ⟨hodd, h3, Or.inl rfl⟩

theorem mem_even_F4 {n : ℕ} (hodd : Odd n) (h3 : 3 ≤ n) :
    CFSG.Open.ordTwistedF4 (2 ^ n) ∈ CFSG.Timmesfeld.evenOrdersExceptUnitarySp4 := by
  refine Or.inl ⟨n, by omega, ?_⟩
  iterate 10 right
  exact ⟨hodd, h3, Or.inr rfl⟩

theorem false_Sz (hk : 1 ≤ k) (e : X ≃* projSU 4 2 k) {n : ℕ} (h : SuzukiModel X 2 n) :
    False := by
  have hL : LieModel X .twistedB2 0 2 n := Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩))
  obtain ⟨hadm, hc⟩ := CFSG.RankThree.PartOne.S12K.card_of_lieModel_two hL
  obtain ⟨-, hn1, -, -, hodd, h3⟩ := hadm
  exact ordU4_ne_of_mem hk (m := CFSG.Open.ordSuzuki (2 ^ n)) (mem_even_Sz hodd h3)
    ((card_eq_ordU4 hk e).symm.trans hc).symm

theorem false_F4 (hk : 1 ≤ k) (e : X ≃* projSU 4 2 k) {n : ℕ}
    (h : ReeTitsModel X .twistedF4 2 n) : False := by
  have hL : LieModel X .twistedF4 0 2 n := Or.inr (Or.inr (Or.inl ⟨rfl, by decide, h⟩))
  obtain ⟨hadm, hc⟩ := CFSG.RankThree.PartOne.S12K.card_of_lieModel_two hL
  obtain ⟨-, hn1, -, -, hodd, h3⟩ := hadm
  exact ordU4_ne_of_mem hk (m := CFSG.Open.ordTwistedF4 (2 ^ n)) (mem_even_F4 hodd h3)
    ((card_eq_ordU4 hk e).symm.trans hc).symm

theorem false_G2 (hk : 1 ≤ k) (e : X ≃* projSU 4 2 k) {n : ℕ}
    (h : ChevalleyExceptionalModel X .G2 2 n) : False := by
  obtain ⟨⟨-, hn1, -, h3⟩, -⟩ := id h
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have : n = 1 := by omega
    subst this
    omega
  exact ordU4_ne_of_mem hk (m := CFSG.Open.ordG2 (2 ^ n))
    (Or.inl ⟨n, hn1, Or.inr (Or.inr (Or.inr (Or.inl ⟨hn2, rfl⟩)))⟩)
    ((card_eq_ordU4 hk e).symm.trans (CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h)).symm

theorem false_D4 (hk : 1 ≤ k) (e : X ≃* projSU 4 2 k) {n : ℕ}
    (h : ChevalleyExceptionalModel X .trialityD4 2 n) : False := by
  obtain ⟨⟨-, hn1, -⟩, -⟩ := id h
  exact ordU4_ne_of_mem hk (m := CFSG.Open.ordTrialityD4 (2 ^ n))
    (Or.inl ⟨n, hn1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩)
    ((card_eq_ordU4 hk e).symm.trans (CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h)).symm

theorem false_oddL2 [Finite X] (hk : 3 ≤ k) (e : X ≃* projSU 4 2 k) {p e' : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (he : 1 ≤ e') (φ : X ≃* projSL 2 (GaloisField p e')) (h3 : p ^ e' ≠ 3) :
    False := by
  have h1 := Sec4.HeringUnitary.twoRank_le_two_of_projSL_two hp2 he h3 φ
  have h2 := two_mul_le_twoRank_projSU_four (by omega : 1 ≤ k)
  rw [CFSG.GH74.twoRank_eq_of_mulEquiv e] at h1
  omega

theorem false_oddL3 [Finite X] (hk : 3 ≤ k) (e : X ≃* projSU 4 2 k) {p e' : ℕ} [hpf : Fact p.Prime]
    (hp3 : 3 < p) (he1 : 1 ≤ e')
    (hX : Sec4.IsSLThreePiAt X (p ^ e') ∨ Sec4.IsoLThreePi X p e') : False := by
  have h2 := two_mul_le_twoRank_projSU_four (by omega : 1 ≤ k)
  rcases hX with ⟨F, _, _, (⟨hF, -, ⟨φ⟩⟩ | ⟨hF, -, ⟨φ⟩⟩)⟩ | (⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩)
  · have h2F : (2 : F) ≠ 0 :=
      CFSG.GH74.Filter.two_ne_zero_of_card_eq hpf.out (by omega) (m := e') hF
    have h1 := Sec4.HeringUnitary.twoRank_le_two_of_det_one h2F (StatedSL 3 F)
      (fun x hx => CFSG.SectionRank.OddCover.det_eq_one_of_mem_statedSL hx)
    rw [← CFSG.GH74.twoRank_eq_of_mulEquiv φ, CFSG.GH74.twoRank_eq_of_mulEquiv e] at h1
    omega
  · have h2F : (2 : F) ≠ 0 :=
      CFSG.GH74.Filter.two_ne_zero_of_card_eq hpf.out (by omega) (m := e' * 2)
        (by rw [hF, pow_mul])
    have h1 := Sec4.HeringUnitary.twoRank_le_two_of_det_one h2F (StatedSU 3 (p ^ e') F)
      (fun x hx => CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU hx)
    rw [← CFSG.GH74.twoRank_eq_of_mulEquiv φ, CFSG.GH74.twoRank_eq_of_mulEquiv e] at h1
    omega
  · have h1 := Sec4.HeringUnitary.twoRank_le_two_of_projSL_three (by omega) he1 φ
    rw [CFSG.GH74.twoRank_eq_of_mulEquiv e] at h1
    omega
  · have h1 := Sec4.HeringUnitary.twoRank_le_two_of_projSU_three (by omega) he1 φ
    rw [CFSG.GH74.twoRank_eq_of_mulEquiv e] at h1
    omega

theorem not_alt47 {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G}
    (hk : 3 ≤ k) (e : L ⧸ aschbacherSolvableCore 3 L ≃* projSU 4 2 k) : ¬ Sec4.Alt47 L x := by
  intro h
  have hk1 : 1 ≤ k := by omega
  rcases h with h1 | h2 | h3 | h4 | h5
  · obtain ⟨p, e', hp, hp2, he, ⟨φ⟩, -⟩ := h1
    refine false_oddL2 hk e hp2 (by omega) φ ?_
    intro hq
    have := (Nat.Prime.pow_eq_iff Nat.prime_three).mp hq
    omega
  · obtain ⟨p, e', hp, hp3, he1, he2, hX, -⟩ := h2
    exact false_oddL3 hk e hp3 he1 hX
  · obtain ⟨hlist, -⟩ := h3
    rcases hlist with ⟨m, hm, hm'⟩ | ⟨n, hodd, hn'⟩
    · rcases hm' with hA | ⟨F, _, _, hF, ⟨φ⟩⟩ | hC | ⟨F, _, _, hF, ⟨φ⟩⟩
      · obtain ⟨φ⟩ := hA
        exact false_L2 hk1 e hm φ
      · exact false_SU3 hk1 e hm hF φ
      · obtain ⟨φ⟩ := hC
        exact false_U3 hk e hm φ
      · exact false_SL3 hk1 e (by omega : 1 ≤ 2 * m) hF φ
    · have hn1 : 1 ≤ n := hodd.pos
      rcases hn' with hSz | hL3 | hSp | hG2 | hF4
      · exact false_Sz hk1 e hSz
      · obtain ⟨φ⟩ := hL3
        exact false_L3 hk1 e hn1 φ
      · obtain ⟨φ⟩ := hSp
        exact false_Sp4 hk e hn1 φ
      · exact false_G2 hk1 e hG2
      · exact false_F4 hk1 e hF4
  · obtain ⟨n, hn, hX, -⟩ := h4
    rcases hX with ⟨F, _, _, (⟨hF, -, ⟨φ⟩⟩ | ⟨hF, -, ⟨φ⟩⟩)⟩ | (⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩)
    · exact false_SL3 hk1 e hn hF φ
    · exact false_SU3 hk1 e hn hF φ
    · exact false_L3 hk1 e hn φ
    · exact false_U3 hk e hn φ
  · obtain ⟨n, hodd, hD4, -⟩ := h5
    exact false_D4 hk1 e hD4

end Models

end CFSG.RankThree.PartTwo.Sec8.Hering418
