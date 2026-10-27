module

public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114Excl
public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114Orders
public import CFSG.GH74.Orders.LieType
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13

public section

namespace CFSG.Quasithin.H13.Sec1214Orders

open CFSG.Open (ordA quasithinG2)
open CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix CFSG.Quasithin.H13.L34Orders

theorem eq_of_two_pow_mul_odd {a b u v : ℕ} (hu : Odd u) (hv : Odd v)
    (h : 2 ^ a * u = 2 ^ b * v) : a = b := by
  have h1 := congrArg (fun x => x.factorization 2) h
  rw [Nat.factorization_mul (by positivity) hu.pos.ne',
    Nat.factorization_mul (by positivity) hv.pos.ne'] at h1
  simp only [Finsupp.coe_add, Pi.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same] at h1
  rw [Nat.factorization_eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hu)),
    Nat.factorization_eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hv))] at h1
  omega

theorem odd_eq_of_two_pow_mul_odd {a b u v : ℕ} (hu : Odd u) (hv : Odd v)
    (h : 2 ^ a * u = 2 ^ b * v) : u = v := by
  rw [eq_of_two_pow_mul_odd hu hv h] at h
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h

theorem odd_pow_sub_one {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) : Odd ((2 ^ n) ^ k - 1) := by
  rw [← pow_mul]
  exact Nat.Even.sub_odd Nat.one_le_two_pow
    ((Nat.even_pow' (Nat.mul_ne_zero hn hk)).mpr even_two) odd_one

theorem odd_pow_add_one {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) : Odd ((2 ^ n) ^ k + 1) := by
  rw [← pow_mul]
  exact ((Nat.even_pow' (Nat.mul_ne_zero hn hk)).mpr even_two).add_one

theorem two_pow_mul_ne {c n a u v : ℕ} (hu : Odd u) (hv : Odd v) (h : c * n ≠ a) :
    (2 ^ n) ^ c * u ≠ 2 ^ a * v := fun he =>
  h (eq_of_two_pow_mul_odd hu hv (by rw [← he, ← pow_mul, mul_comm n c]))

theorem ordA_one_two_pow {n : ℕ} (hn : n ≠ 0) : ordA 1 (2 ^ n) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 :=
    Nat.coprime_two_left.mpr (by simpa using odd_pow_sub_one (k := 1) hn one_ne_zero)
  simp only [ordA, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, pow_one, Finset.Icc_self,
    Finset.prod_singleton, hg, Nat.div_one]

structure OrderFacts (N : ℕ) : Prop where
  sl3 : ∀ n : ℕ, (2 ^ n) ^ 3 * (((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1)) ≠ N
  sp4 : ∀ n : ℕ, (2 ^ n) ^ (2 ^ 2) * (((2 ^ n) ^ (2 * 1) - 1) * ((2 ^ n) ^ (2 * 2) - 1)) ≠ N
  l2 : ∀ n : ℕ, ordA 1 (2 ^ n) ≠ N
  l3 : ∀ n : ℕ, ordA 2 (2 ^ n) ≠ N
  g2 : ¬ N ∣ 12096
  g2' : ∀ n : ℕ, 2 ≤ n → (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) ≠ N
  su3 : ∀ n : ℕ, (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) ≠ N
  three : 3 ∣ N
  small : N ≠ 60 ∧ N ≠ 168 ∧ N ≠ 360 ∧ N ≠ 1080 ∧ N ≠ 2520 ∧ N ≠ 20160 ∧ N ≠ 9999360
  pow : ∀ k : ℕ, N * 2 ^ k ≠ 2520 ∧ N * 2 ^ k ≠ 20160 ∧ N * 2 ^ k ≠ 9999360
  m12 : ∀ k : ℕ, ¬ 95040 ∣ N * 2 ^ k
  m22 : ¬ 443520 ∣ N
  m23 : ¬ 23 ∣ N

theorem OrderFacts.of_two_part {N a u : ℕ} (hN : N = 2 ^ a * u) (hu : Odd u) (ha : a = 4 ∨ a = 10)
    (hl2 : u ≠ 2 ^ (2 * a) - 1) (hsp : N ≠ 720) (hg2 : ¬ N ∣ 12096) (h3 : 3 ∣ N)
    (hsmall : N ≠ 60 ∧ N ≠ 168 ∧ N ≠ 360 ∧ N ≠ 1080 ∧ N ≠ 2520 ∧ N ≠ 20160 ∧ N ≠ 9999360)
    (hpow : u ≠ 315 ∧ u ≠ 9765) (hm12 : ¬ 1485 ∣ u) (hm22 : ¬ 443520 ∣ N) (hm23 : ¬ 23 ∣ N) :
    OrderFacts N := by
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact mul_ne_zero (by positivity) hu.pos.ne'
  refine ⟨fun n h => ?_, fun n h => ?_, fun n h => ?_, fun n h => ?_, hg2, fun n hn h => ?_,
    fun n h => ?_, h3, hsmall, fun k => ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩, fun k h => ?_,
    hm22, hm23⟩
  ·
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hN0 (by simpa using h.symm)
    · exact two_pow_mul_ne ((odd_pow_sub_one hn.ne' (by norm_num)).mul
        (odd_pow_sub_one hn.ne' (by norm_num))) hu (by omega) (h.trans hN)
  ·
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hN0 (by simpa using h.symm)
    · by_cases hc : 4 * n = a
      · obtain rfl : n = 1 := by omega
        exact hsp (by simpa using h.symm)
      · exact two_pow_mul_ne ((odd_pow_sub_one hn.ne' (by norm_num)).mul
          (odd_pow_sub_one hn.ne' (by norm_num))) hu (by norm_num; omega) (h.trans hN)
  ·
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hN0 (by simpa [ordA] using h.symm)
    · rw [ordA_one_two_pow hn.ne', hN] at h
      have hodd := odd_pow_sub_one (k := 2) hn.ne' (by norm_num)
      obtain rfl := eq_of_two_pow_mul_odd hodd hu h
      exact hl2 ((odd_eq_of_two_pow_mul_odd hodd hu h).symm.trans (by rw [← pow_mul, mul_comm]))
  ·
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hN0 (by simpa [ordA] using h.symm)
    · set q := 2 ^ n with hq
      have hP : ordA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := by
        simp only [ordA]
        rw [show Finset.Icc 2 (2 + 1) = {2, 3} by rfl, Finset.prod_pair (by norm_num)]
      set g := Nat.gcd 3 (q - 1) with hg
      have hgd : g ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
        refine Dvd.dvd.mul_left (Dvd.dvd.mul_left ?_ _) _
        have := Nat.sub_dvd_pow_sub_pow q 1 3
        rw [one_pow] at this
        exact (Nat.gcd_dvd_right 3 (q - 1)).trans this
      have hgo : Odd g := Odd.of_dvd_nat (by norm_num) (Nat.gcd_dvd_left 3 (q - 1))
      rw [hP] at h
      have h' : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) = 2 ^ a * (u * g) := by
        rw [← mul_assoc (2 ^ a), ← hN, ← h, Nat.div_mul_cancel hgd]
      exact two_pow_mul_ne ((odd_pow_sub_one hn.ne' (by norm_num)).mul
        (odd_pow_sub_one hn.ne' (by norm_num))) (hu.mul hgo) (by omega) h'
  ·
    exact two_pow_mul_ne ((odd_pow_sub_one (by omega) (by norm_num)).mul
      (odd_pow_sub_one (by omega) (by norm_num))) hu (by omega) (h.trans hN)
  ·
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hN0 (by simpa using h.symm)
    · rw [mul_assoc] at h
      exact two_pow_mul_ne ((odd_pow_sub_one hn.ne' (by norm_num)).mul
        (odd_pow_add_one hn.ne' (by norm_num))) hu (by omega) (h.trans hN)
  ·
    rw [hN, mul_right_comm, ← pow_add, show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num] at h
    exact hpow.1 (odd_eq_of_two_pow_mul_odd hu (by decide) h)
  ·
    rw [hN, mul_right_comm, ← pow_add, show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num] at h
    exact hpow.1 (odd_eq_of_two_pow_mul_odd hu (by decide) h)
  ·
    rw [hN, mul_right_comm, ← pow_add, show (9999360 : ℕ) = 2 ^ 10 * 9765 by norm_num] at h
    exact hpow.2 (odd_eq_of_two_pow_mul_odd hu (by decide) h)
  ·
    rw [hN, mul_right_comm, ← pow_add] at h
    have h1 : 1485 ∣ 2 ^ (a + k) * u := (Dvd.intro_left 64 rfl).trans h
    exact hm12 ((Nat.Coprime.pow_right _ (by norm_num : Nat.Coprime 1485 2)).dvd_of_dvd_mul_left h1)

theorem orderFacts_5616 : OrderFacts 5616 :=
  OrderFacts.of_two_part (a := 4) (u := 351) (by norm_num) (by decide) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem orderFacts_7920 : OrderFacts 7920 :=
  OrderFacts.of_two_part (a := 4) (u := 495) (by norm_num) (by decide) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem orderFacts_he : OrderFacts 4030387200 :=
  OrderFacts.of_two_part (a := 10) (u := 3935925) (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

variable {N : ℕ}

theorem OrderFacts.card_SL3_ne (hN : OrderFacts N) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : Nat.card (SpecialLinearGroup (Fin 3) F) ≠ N := by
  rw [card_SL3, hF]
  exact hN.sl3 n

theorem OrderFacts.card_statedSL3_ne (hN : OrderFacts N) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : Nat.card (StatedSL 3 F) ≠ N := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv]
  exact hN.card_SL3_ne hF

theorem OrderFacts.card_statedSp_ne (hN : OrderFacts N) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : Nat.card (StatedSp 2 F) ≠ N := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF,
    show Finset.Icc 1 2 = {1, 2} by rfl, Finset.prod_pair (by norm_num)]
  exact hN.sp4 n

theorem OrderFacts.card_PSL2_ne (hN : OrderFacts N) {X : Type} [Group X] {n : ℕ}
    (hl : LieModel X .PSL 2 2 n) : Nat.card X ≠ N := by
  rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) hl]
  exact hN.l2 n

theorem OrderFacts.card_PSL3_ne (hN : OrderFacts N) {X : Type} [Group X] {n : ℕ}
    (hl : LieModel X .PSL 3 2 n) : Nat.card X ≠ N := by
  rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) hl]
  exact hN.l3 n

theorem OrderFacts.card_G2_derived_ne (hN : OrderFacts N) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : Nat.card ↥⁅quasithinG2 F, quasithinG2 F⁆ ≠ N := by
  rcases n with _ | _ | n
  · exfalso
    have := Finite.one_lt_card (α := F)
    rw [hF] at this
    norm_num at this
  · have : CharP F 2 := Vol2.KGNat.charP_two_of_card (n := 1) one_ne_zero hF
    have hG : Nat.card ↥(quasithinG2 F) = 12096 := by
      rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
        Vol2.KGNat.card_cayleyGroup, hF]
      norm_num
    intro h
    apply hN.g2
    rw [← h, ← hG]
    exact Subgroup.card_dvd_of_le (Subgroup.commutator_le_self (quasithinG2 F))
  · rw [Vol2.KGNat.factG2DerivedOrder_holds F (n + 2) (by omega) hF]
    exact hN.g2' (n + 2) (by omega)

theorem OrderFacts.card_statedSU_ne (hN : OrderFacts N) {F : Type} [Field F] [Finite F]
    [CharP F 2] {n : ℕ} (hF : Nat.card F = (2 ^ n) ^ 2) : Nat.card (StatedSU 3 (2 ^ n) F) ≠ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.OddCover.card_statedSU_three hF]
  exact hN.su3 n

theorem dvd_card_mulAut_M12 :
    95040 ∣ Nat.card (MulAut ↥NativeSporadic.M12) := by
  have hs : IsSimpleGroup ↥NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  set a : ↥NativeSporadic.M12 := ⟨m12A, m12A_mem⟩ with ha
  set y : ↥NativeSporadic.M12 := ⟨m12A * m12B, Subgroup.mul_mem _ m12A_mem m12B_mem⟩ with hy
  have hc : Subgroup.center ↥NativeSporadic.M12 = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥NativeSporadic.M12) with h | h
    · exact h
    · exfalso
      have hyc : y ∈ Subgroup.center _ := h ▸ Subgroup.mem_top y
      have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hyc a)
      simp only [Subgroup.coe_mul, ha, hy] at h2
      apply m12AB_not_comm
      rw [← h2]
      group
  rw [← CFSG.Sporadic.Mathieu.card_M12]
  refine Subgroup.card_dvd_of_injective MulAut.conj fun g h hgh => ?_
  have hz : h⁻¹ * g ∈ Subgroup.center ↥NativeSporadic.M12 := Subgroup.mem_center_iff.mpr fun x => by
    have h1 := congrArg (fun φ : MulAut ↥NativeSporadic.M12 => φ x) hgh
    simp only [MulAut.conj_apply] at h1
    calc x * (h⁻¹ * g) = h⁻¹ * (h * x * h⁻¹) * g := by group
      _ = h⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
      _ = h⁻¹ * g * x := by group
  rw [hc, Subgroup.mem_bot, inv_mul_eq_one] at hz
  exact hz.symm

theorem simple_card_L33 {Q : Type} [Group Q] (h : StatedClassicalModel Q .PSL 3 3 1) :
    IsSimpleGroup Q ∧ Nat.card Q = 5616 := by
  refine ⟨?_, ?_⟩
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
    have hs := CFSG.BenderSuzuki.External.huppert_II_6_13 (K := F) 3 (by norm_num)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact (e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).isSimpleGroup
  · rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) (Or.inl ⟨by decide, h⟩)]
    decide

theorem center_SL3_three : Subgroup.center (SpecialLinearGroup (Fin 3) (ZMod 3)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have key : ∀ s : ZMod 3, s ^ 3 = 1 → s = 1 := by decide
  obtain rfl := key r (by simpa using hr)
  rw [Subgroup.mem_bot]
  exact Subtype.ext (by rw [← hA, map_one]; rfl)

theorem isSimpleGroup_SL3_three : IsSimpleGroup (SpecialLinearGroup (Fin 3) (ZMod 3)) := by
  have hs := CFSG.BenderSuzuki.External.huppert_II_6_13 (K := ZMod 3) 3 (by norm_num)
    (Or.inl (by norm_num)) (Or.inl (by norm_num))
  exact ((QuotientGroup.quotientMulEquivOfEq center_SL3_three).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

theorem simple_card_SL33 {Q : Type} [Group Q] (e : Q ≃* ↥(StatedSL 3 (ZMod 3))) :
    IsSimpleGroup Q ∧ Nat.card Q = 5616 := by
  have e' := e.trans (specialLinearGroupEquivStatedSL 3 (ZMod 3)).symm
  have hs := isSimpleGroup_SL3_three
  refine ⟨e'.isSimpleGroup, ?_⟩
  rw [Nat.card_congr e'.toEquiv, card_SL3, Nat.card_zmod]
  norm_num

theorem simple_card_M11 {Q : Type} [Group Q]
    (e : Q ≃* NativeSporadic.Carrier .M11) : IsSimpleGroup Q ∧ Nat.card Q = 7920 := by
  have hs : IsSimpleGroup (NativeSporadic.Carrier .M11) :=
    CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
  exact ⟨e.isSimpleGroup, (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M11⟩

theorem simple_card_He {Q : Type} [Group Q]
    (e : Q ≃* NativeSporadic.Carrier .He) : IsSimpleGroup Q ∧ Nat.card Q = 4030387200 := by
  have hs : IsSimpleGroup (NativeSporadic.Carrier .He) := CFSG.Sporadic.He.isSimpleGroup_He
  exact ⟨e.isSimpleGroup, (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.He.card_He⟩

end CFSG.Quasithin.H13.Sec1214Orders
