module

public import CFSG.Quasithin.Background.SmithC27RHat6Coord
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.EmptyFaithful.SBc11List

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL)

private theorem eq_of_two_pow_mul_odd'' {a b u w : ℕ} (hu : Odd u) (hw : Odd w)
    (h : 2 ^ a * u = 2 ^ b * w) : a = b := by
  have hv := congrArg (padicValNat 2) h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (by positivity) (by rintro rfl; exact Nat.not_odd_zero hu),
    padicValNat.mul (by positivity) (by rintro rfl; exact Nat.not_odd_zero hw),
    padicValNat.prime_pow, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (fun hd => by have := Nat.odd_iff.mp hu; omega),
    padicValNat.eq_zero_of_not_dvd (fun hd => by have := Nat.odd_iff.mp hw; omega)] at hv
  omega

private theorem two_pow_mul_ne {a n k u w c : ℕ} (hu : Odd u) (hw : Odd w) (hc : Odd c)
    (hab : a ≠ k * n) : 2 ^ a * u ≠ (2 ^ n) ^ k * w * c := fun h =>
  hab (eq_of_two_pow_mul_odd'' hu (hw.mul hc) (by rw [h, ← pow_mul', mul_assoc]))

private theorem odd_two_pow_pow_sub_one {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    Odd ((2 ^ n) ^ k - 1) := by
  rw [← pow_mul]
  have h2 : Even (2 ^ (n * k)) :=
    (Nat.even_pow' (Nat.mul_ne_zero (by omega) (by omega))).mpr even_two
  exact Nat.Even.sub_odd Nat.one_le_two_pow h2 odd_one

private theorem odd_sl3 {m : ℕ} (hm : 1 ≤ m) : Odd (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) :=
  (odd_two_pow_pow_sub_one hm (by norm_num)).mul (odd_two_pow_pow_sub_one hm (by norm_num))

private theorem sl3_eq {m : ℕ} :
    (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) =
      2 ^ (3 * m) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) := by
  rw [pow_mul']

private theorem sl3_zero : (2 ^ 0) ^ 3 * (((2 ^ 0) ^ 2 - 1) * ((2 ^ 0) ^ 3 - 1)) = 0 := by
  norm_num

private theorem sl3_ne_sp4_mul {m n c : ℕ} (hn : 1 ≤ n) (hc : Odd c) :
    (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ≠
      (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) * c := by
  intro h
  have hB : Odd (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) :=
    (odd_two_pow_pow_sub_one hn (by norm_num)).mul (odd_two_pow_pow_sub_one hn (by norm_num))
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hpos : 0 < (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) * c :=
      Nat.mul_pos (Nat.mul_pos (by positivity) hB.pos) hc.pos
    have h0 := sl3_zero
    omega
  have h1 : 3 * m = 4 * n := by
    refine eq_of_two_pow_mul_odd'' (odd_sl3 hm) (hB.mul hc) ?_
    rw [← sl3_eq, h, pow_mul' 2 4 n, mul_assoc]
  obtain ⟨j, rfl, rfl⟩ : ∃ j, m = 4 * j ∧ n = 3 * j := ⟨n / 3, by omega, by omega⟩
  have hb : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_mul', pow_mul' 2 3 j] at h
  set b := 2 ^ j with hbdef
  have e1 : 1 ≤ (b ^ 4) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have e2 : 1 ≤ (b ^ 4) ^ 3 := Nat.one_le_pow _ _ (by positivity)
  have e3 : 1 ≤ (b ^ 3) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have e4 : 1 ≤ (b ^ 3) ^ 4 := Nat.one_le_pow _ _ (by positivity)
  zify [e1, e2, e3, e4] at h
  have hb' : (2 : ℤ) ≤ b := by exact_mod_cast hb
  set x : ℤ := (b : ℤ) with hx
  have hx12 : x ^ 12 * (x ^ 12 - 1) ≠ 0 := by
    have : (4096 : ℤ) ≤ x ^ 12 := by
      calc (4096 : ℤ) = 2 ^ 12 := by norm_num
        _ ≤ x ^ 12 := pow_le_pow_left₀ (by norm_num) hb' 12
    exact mul_ne_zero (by positivity) (by linarith)
  have key : (x ^ 8 - 1) * (x ^ 12 * (x ^ 12 - 1)) =
      ((x ^ 6 - 1) * c) * (x ^ 12 * (x ^ 12 - 1)) := by
    linear_combination h
  have k2 := mul_right_cancel₀ hx12 key
  have hx2 : (4 : ℤ) ≤ x ^ 2 := by nlinarith
  have hx4 : (16 : ℤ) ≤ x ^ 4 := by nlinarith
  have hx6 : x ^ 2 < x ^ 6 := by nlinarith
  have hx61 : (0 : ℤ) ≤ x ^ 6 - 1 := by nlinarith
  rcases le_or_gt (c : ℤ) (x ^ 2) with hc' | hc'
  · nlinarith [mul_nonneg hx61 (show (0 : ℤ) ≤ x ^ 2 - c by linarith)]
  · nlinarith [mul_nonneg hx61 (show (0 : ℤ) ≤ c - x ^ 2 - 1 by linarith)]

private theorem sl3_ne_g2_mul {m n c : ℕ} (hn : 1 ≤ n) (hc : Odd c) (hc3 : c ≤ 3) :
    (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ≠
      (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) * c := by
  intro h
  have hB : Odd (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) :=
    (odd_two_pow_pow_sub_one hn (by norm_num)).mul (odd_two_pow_pow_sub_one hn (by norm_num))
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hpos : 0 < (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) * c :=
      Nat.mul_pos (Nat.mul_pos (by positivity) hB.pos) hc.pos
    have h0 := sl3_zero
    omega
  have h1 : 3 * m = 6 * n := by
    refine eq_of_two_pow_mul_odd'' (odd_sl3 hm) (hB.mul hc) ?_
    rw [← sl3_eq, h, pow_mul' 2 6 n, mul_assoc]
  obtain rfl : m = 2 * n := by omega
  have hb : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [pow_mul'] at h
  set b := 2 ^ n with hbdef
  have e1 : 1 ≤ (b ^ 2) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have e2 : 1 ≤ (b ^ 2) ^ 3 := Nat.one_le_pow _ _ (by positivity)
  have e3 : 1 ≤ b ^ 6 := Nat.one_le_pow _ _ (by positivity)
  have e4 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ (by positivity)
  zify [e1, e2, e3, e4] at h
  have hb' : (2 : ℤ) ≤ b := by exact_mod_cast hb
  set x : ℤ := (b : ℤ) with hx
  have hc' : (c : ℤ) ≤ 3 := by exact_mod_cast hc3
  have hx6 : x ^ 6 * (x ^ 6 - 1) ≠ 0 := by
    have : (64 : ℤ) ≤ x ^ 6 := by
      calc (64 : ℤ) = 2 ^ 6 := by norm_num
        _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) hb' 6
    exact mul_ne_zero (by positivity) (by linarith)
  have key : (x ^ 4 - 1) * (x ^ 6 * (x ^ 6 - 1)) =
      ((x ^ 2 - 1) * c) * (x ^ 6 * (x ^ 6 - 1)) := by
    linear_combination h
  have k2 := mul_right_cancel₀ hx6 key
  have hx2 : (4 : ℤ) ≤ x ^ 2 := by nlinarith
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ x ^ 2 - 1 by linarith) (show (0 : ℤ) ≤ 3 - c by linarith)]

private theorem eq_one_of_sl3_eq {m u c : ℕ} (hu : Odd u) (hc : Odd c)
    (h : (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) = 2 ^ 3 * u * c) : m = 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 := sl3_zero
    have : 0 < 2 ^ 3 * u * c := Nat.mul_pos (Nat.mul_pos (by norm_num) hu.pos) hc.pos
    omega
  have h1 : 3 * m = 3 := by
    refine eq_of_two_pow_mul_odd'' (odd_sl3 hm) (hu.mul hc) ?_
    rw [← sl3_eq, h, mul_assoc]
  omega

private theorem sl3_ne_360_mul {m c : ℕ} (hc : Odd c) :
    (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ≠ 360 * c := by
  intro h
  obtain rfl := eq_one_of_sl3_eq (u := 45) (by decide) hc (by rw [h]; ring)
  norm_num at h
  omega

private theorem sl3_ne_1080_mul {m c : ℕ} (hc : Odd c) :
    (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ≠ 1080 * c := by
  intro h
  obtain rfl := eq_one_of_sl3_eq (u := 135) (by decide) hc (by rw [h]; ring)
  norm_num at h
  omega

theorem card_statedSL_three' {F : Type} [Field F] [Finite F] :
    Nat.card ↥(Assembly.LowTwoRank.StatedSL 3 F) =
      Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) :=
  CFSG.Open.StatedAPI.card_statedSL_three F

theorem card_center_statedSL_three_le {F : Type} [Field F] :
    Nat.card ↥(Subgroup.center ↥(Assembly.LowTwoRank.StatedSL 3 F)) ≤ 3 := by
  rw [← Nat.card_congr (Subgroup.centerCongr (specialLinearGroupEquivStatedSL 3 F)).toEquiv,
    Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity).toEquiv,
    show max (Fintype.card (Fin 3)) 1 = 3 by simp]
  exact card_rootsOfUnity F 3

theorem card_statedSp_two' {F : Type} [Field F] [Finite F] :
    Nat.card ↥(Assembly.LowTwoRank.StatedSp 2 F) =
      Nat.card F ^ 4 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1)) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
    show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  norm_num

theorem card_quasithinG2' {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Nat.card ↥(quasithinG2 F) =
      Nat.card F ^ 6 * ((Nat.card F ^ 6 - 1) * (Nat.card F ^ 2 - 1)) := by
  have := FFC.charP_two_of_card_pow hF
  rw [Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]
  exact Vol2.KGNat.card_cayleyGroup

theorem odd_card_of_le_center {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.pCore 2 Q = ⊥)
    {N : Subgroup Q} (hN : N ≤ Subgroup.center Q) : Odd (Nat.card N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 h2
  have hzle : Subgroup.zpowers (z : Q) ≤ Subgroup.center Q :=
    (Subgroup.zpowers_le).2 (hN z.2)
  have hnorm : (Subgroup.zpowers (z : Q)).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_center_iff.1 (hzle hx) g, mul_inv_cancel_right]
    exact hx⟩
  have hz2 : (z : Q) ^ 2 ^ 1 = 1 := by
    rw [pow_one, ← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
  have hle : Subgroup.zpowers (z : Q) ≤ CFSG.pCore 2 Q :=
    le_sSup ⟨hnorm, isPGroup_zpowers_of_pow_eq_one hz2⟩
  rw [hQ] at hle
  have h1 : (z : Q) = 1 := Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers _))
  have h1' : z = 1 := Subtype.ext h1
  rw [h1', orderOf_one] at hz
  exact absurd hz (by norm_num)

variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

theorem StarHyp.exists_card_quot_eq (hs : StarHyp R K V) :
    ∃ c : ℕ, Odd c ∧ c ∣ Nat.card ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ∧
      Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = Nat.card ↥(autOn K V) * c := by
  have hKV := hs.K_le_normalizer_V
  have hle := InternalSec.pCore_le_ker_autOnHom hKV hs.pCore_K_eq_bot
  let ρ : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥(autOn K V) := QuotientGroup.lift _ _ hle
  have hρ : Function.Surjective ρ := by
    intro y
    obtain ⟨l, rfl⟩ := InternalSec.autOnHom_surjective hKV y
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hker : ρ.ker ≤ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    intro p hp
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective p
    have h1 : InternalSec.autOnHom hKV l = 1 := hp
    have h2 : (l : G) ∈ Subgroup.centralizer (V : Set G) :=
      (InternalSec.mem_ker_autOnHom hKV l).1 h1
    exact mk_mem_center_of_mem_oTwoZIn (hs.inf_centralizer_le ⟨l.2, h2⟩)
  refine ⟨Nat.card ρ.ker, odd_card_of_le_center (pCore_two_quotient_pCore_two _) hker,
    Subgroup.card_dvd_of_le hker, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv]

omit [Finite G] in
theorem card_quot_of_isModO2Surj {m : ℕ} {F : Type} [Field F] [Fintype F]
    {α : ↥K →* ↥(Assembly.LowTwoRank.StatedSL 3 F)} (hF : Fintype.card F = 2 ^ m)
    (hα : IsModO2Surj K α) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) =
        (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ∧
      Nat.card ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ≤ 3 := by
  let e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(Assembly.LowTwoRank.StatedSL 3 F) :=
    (QuotientGroup.quotientMulEquivOfEq hα.2.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα.1)
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, card_statedSL_three', Nat.card_eq_fintype_card, hF]
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact card_center_statedSL_three_le

theorem blocks_of_statedSp (hs : StarHyp R K V) {n : ℕ} {F : Type} [Field F] [Fintype F]
    (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (e : ↥(autOn K V) ≃* ↥(Assembly.LowTwoRank.StatedSp 2 F))
    (hc : IsG2Block K ∨ IsAltBlockType K 6 ∨ IsSp4Block K ∨ IsHatA6Block K ∨
      ∃ (m : ℕ) (F' : Type) (_ : Field F') (_ : Fintype F')
        (α : ↥K →* ↥(Assembly.LowTwoRank.StatedSL 3 F')),
        Fintype.card F' = 2 ^ m ∧ IsModO2Surj K α) :
    IsAltBlockType K 6 ∨ IsSp4Block K := by
  obtain ⟨c, hco, hcZ, hN⟩ := hs.exists_card_quot_eq
  have hk : Nat.card ↥(autOn K V) = (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) := by
    rw [Nat.card_congr e.toEquiv, card_statedSp_two', Nat.card_eq_fintype_card, hF]
  have hB : Odd (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) :=
    (odd_two_pow_pow_sub_one (by omega) (by norm_num)).mul
      (odd_two_pow_pow_sub_one (by omega) (by norm_num))
  rw [hk] at hN
  rcases hc with hb | hb | hb | hb | ⟨m, F', _, _, α, hF', hα⟩
  · rw [SBc11.card_of_isPSU_three_three hb.2.1] at hN
    exact absurd (by rw [← hN]; norm_num) (two_pow_mul_ne (a := 5) (u := 189) (by decide) hB hco
      (by omega))
  · exact Or.inl hb
  · exact Or.inr hb
  · rw [card_of_isHat_alt6 hb.2.1] at hN
    exact absurd (by rw [← hN]; norm_num) (two_pow_mul_ne (a := 3) (u := 135) (by decide) hB hco
      (by omega))
  · rw [(card_quot_of_isModO2Surj hF' hα).1] at hN
    exact absurd hN (sl3_ne_sp4_mul (by omega) hco)

theorem blocks_of_quasithinG2 (hs : StarHyp R K V) {n : ℕ} {F : Type} [Field F] [Fintype F]
    (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n) (e : ↥(autOn K V) ≃* ↥(quasithinG2 F))
    (hc : IsG2Block K ∨ IsAltBlockType K 6 ∨ IsSp4Block K ∨ IsHatA6Block K ∨
      ∃ (m : ℕ) (F' : Type) (_ : Field F') (_ : Fintype F')
        (α : ↥K →* ↥(Assembly.LowTwoRank.StatedSL 3 F')),
        Fintype.card F' = 2 ^ m ∧ IsModO2Surj K α) :
    IsAltBlockType K 6 ∨ IsSp4Block K := by
  obtain ⟨c, hco, hcZ, hN⟩ := hs.exists_card_quot_eq
  have hF2 : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have hk : Nat.card ↥(autOn K V) = (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) := by
    rw [Nat.card_congr e.toEquiv, card_quasithinG2' hF2, hF2]
  have hB : Odd (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) :=
    (odd_two_pow_pow_sub_one (by omega) (by norm_num)).mul
      (odd_two_pow_pow_sub_one (by omega) (by norm_num))
  rw [hk] at hN
  rcases hc with hb | hb | hb | hb | ⟨m, F', _, _, α, hF', hα⟩
  · rw [SBc11.card_of_isPSU_three_three hb.2.1] at hN
    exact absurd (by rw [← hN]; norm_num) (two_pow_mul_ne (a := 5) (u := 189) (by decide) hB hco
      (by omega))
  · exact Or.inl hb
  · exact Or.inr hb
  · rw [card_of_isHat_alt6 hb.2.1] at hN
    exact absurd (by rw [← hN]; norm_num) (two_pow_mul_ne (a := 3) (u := 135) (by decide) hB hco
      (by omega))
  · obtain ⟨hcard, hZ⟩ := card_quot_of_isModO2Surj hF' hα
    rw [hcard] at hN
    have hc3 : c ≤ 3 := (Nat.le_of_dvd Nat.card_pos hcZ).trans hZ
    exact absurd hN (sl3_ne_g2_mul (by omega) hco hc3)

theorem blocks_of_alt6 (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (e : ↥(autOn K V) ≃* ↥(alternatingGroup (Fin 6)))
    (hc : IsG2Block K ∨ IsAltBlockType K 6 ∨ IsSp4Block K ∨ IsHatA6Block K ∨
      ∃ (m : ℕ) (F' : Type) (_ : Field F') (_ : Fintype F')
        (α : ↥K →* ↥(Assembly.LowTwoRank.StatedSL 3 F')),
        Fintype.card F' = 2 ^ m ∧ IsModO2Surj K α) :
    IsAltBlockType K 6 ∨ IsSp4Block K := by
  obtain ⟨c, hco, -, hN⟩ := hs.exists_card_quot_eq
  have hk : Nat.card ↥(autOn K V) = 360 := by
    rw [Nat.card_congr e.toEquiv, CFSG.QuasithinUnique.Setup.X3.card_alt6]
  rcases hc with hb | hb | hb | hb | ⟨m, F', _, _, α, hF', hα⟩
  · rw [SBc11.card_of_isPSU_three_three hb.2.1, hk] at hN
    omega
  · exact Or.inl hb
  · exact Or.inr hb
  · have := card_autOn_of_hatA6 h hs hb
    omega
  · rw [(card_quot_of_isModO2Surj hF' hα).1, hk] at hN
    exact absurd hN (sl3_ne_360_mul hco)

theorem blocks_of_isHat_alt6 (hs : StarHyp R K V)
    (hhat : IsHat ↥(autOn K V) ↥(alternatingGroup (Fin 6)))
    (hc : IsG2Block K ∨ IsAltBlockType K 6 ∨ IsSp4Block K ∨ IsHatA6Block K ∨
      ∃ (m : ℕ) (F' : Type) (_ : Field F') (_ : Fintype F')
        (α : ↥K →* ↥(Assembly.LowTwoRank.StatedSL 3 F')),
        Fintype.card F' = 2 ^ m ∧ IsModO2Surj K α) :
    (IsAltBlockType K 6 ∨ IsSp4Block K) ∨ IsHatA6Block K := by
  obtain ⟨c, hco, -, hN⟩ := hs.exists_card_quot_eq
  rw [card_of_isHat_alt6 hhat] at hN
  rcases hc with hb | hb | hb | hb | ⟨m, F', _, _, α, hF', hα⟩
  · rw [SBc11.card_of_isPSU_three_three hb.2.1] at hN
    omega
  · exact Or.inl (Or.inl hb)
  · exact Or.inl (Or.inr hb)
  · exact Or.inr hb
  · rw [(card_quot_of_isModO2Surj hF' hα).1] at hN
    exact absurd hN (sl3_ne_1080_mul hco)

end CFSG.Quasithin.SmithC27
