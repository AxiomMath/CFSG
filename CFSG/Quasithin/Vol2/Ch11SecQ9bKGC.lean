module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGB
import CFSG.Adapters.StatedSmallProjOrders
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint SecS CFSG.Assembly.LowTwoRank

@[expose] def Fact3D4Order : Prop :=
  ∀ (X : Type) [Group X] (n : ℕ), 1 ≤ n → Is3D4 2 n X →
    Nat.card X = (2 ^ n) ^ 12 * (((2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1) *
      (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)))

@[expose] def FactA7SectionCent : Prop :=
  ∀ (X : Type) [Group X] [Finite X], (IsAlt 7 X ∨ IsHat X (alternatingGroup (Fin 7))) →
    ∀ B : Subgroup X, (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
      ∀ x : X, orderOf x = 3 → x ∈ sectionCentralizer B (pCoreOf 2 B) → x ∈ Subgroup.center X

namespace C11P9B

theorem ordSU3_mono {a b : ℕ} (h : a ≤ b) :
    a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 + 1)) ≤ b ^ 3 * ((b ^ 2 - 1) * (b ^ 3 + 1)) :=
  Nat.mul_le_mul (Nat.pow_le_pow_left h 3) (Nat.mul_le_mul
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)
    (Nat.add_le_add_right (Nat.pow_le_pow_left h 3) 1))

theorem window_L {N q d a b : ℕ} (hd1 : 1 ≤ d) (hd3 : d ≤ 3)
    (h : N * d = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)))
    (ha : a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 - 1)) < N)
    (hb : 3 * N < (b + 1) ^ 3 * (((b + 1) ^ 2 - 1) * ((b + 1) ^ 3 - 1))) : a < q ∧ q ≤ b := by
  have h1 : N ≤ N * d := Nat.le_mul_of_pos_right N hd1
  have h2 : N * d ≤ 3 * N := by
    rw [mul_comm 3 N]
    exact Nat.mul_le_mul_left N hd3
  constructor
  · by_contra hq
    have := ordSL3_mono (not_lt.mp hq)
    omega
  · by_contra hq
    have := ordSL3_mono (show b + 1 ≤ q by omega)
    omega

theorem window_U {N q d a b : ℕ} (hd1 : 1 ≤ d) (hd3 : d ≤ 3)
    (h : N * d = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)))
    (ha : a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 + 1)) < N)
    (hb : 3 * N < (b + 1) ^ 3 * (((b + 1) ^ 2 - 1) * ((b + 1) ^ 3 + 1))) : a < q ∧ q ≤ b := by
  have h1 : N ≤ N * d := Nat.le_mul_of_pos_right N hd1
  have h2 : N * d ≤ 3 * N := by
    rw [mul_comm 3 N]
    exact Nat.mul_le_mul_left N hd3
  constructor
  · by_contra hq
    have := ordSU3_mono (not_lt.mp hq)
    omega
  · by_contra hq
    have := ordSU3_mono (show b + 1 ≤ q by omega)
    omega

theorem eq_two_two_of_pow_eq_four {p e : ℕ} (hp : p.Prime) (h : p ^ e = 4) : p = 2 ∧ e = 2 := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at h
  have hp2 : p = 2 := by
    have h4 : p ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← h]
      exact dvd_pow_self p he
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4)
  subst hp2
  exact ⟨rfl, Nat.pow_right_injective le_rfl (h.trans (by norm_num))⟩

theorem card_mul_gcd_of_isPSL3' {X : Type} [Group X] {p e : ℕ} (h : IsPSL 3 p e X) :
    Nat.card X * Nat.gcd 3 (p ^ e - 1) = (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) := by
  obtain ⟨⟨hp, -⟩, K, _, _, hK, ⟨φ⟩⟩ := h
  rw [Nat.card_congr φ.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL
    (n := 3) (by norm_num), hK, show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide,
    Finset.prod_pair (by norm_num), show (3 * (3 - 1) / 2 : ℕ) = 3 from rfl]
  refine Nat.div_mul_cancel ((Nat.gcd_dvd_right 3 (p ^ e - 1)).trans ?_)
  refine Dvd.dvd.mul_left (Dvd.dvd.mul_left ?_ _) _
  rw [pow_three_sub_one (p ^ e) (Nat.one_le_pow _ _ hp.pos)]
  exact Dvd.intro _ rfl

theorem card_mul_gcd_of_isPSU3 {X : Type} [Group X] {p e : ℕ} (h : IsPSU 3 p e X) :
    Nat.card X * Nat.gcd 3 (p ^ e + 1) = (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) :=
  CFSG.Open.StatedAPI.card_mul_gcd_of_statedClassicalModel_psu_three h

theorem card_hypSU_three' {p f : ℕ} {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K) :
    Nat.card (CFSG.ClassicalGroups.UnitaryFlag.hypSU h 1 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
  have h1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ h.prime.pos)
  obtain ⟨-, -, -, -, -, hS, -⟩ :=
    CFSG.ClassicalGroups.UnitaryFlag.unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  have hI : Finset.Icc 2 (2 * 1 + 1) = {2, 3} := by decide
  rw [hI, Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3)] at hS
  have hZ : (Nat.card (CFSG.ClassicalGroups.UnitaryFlag.hypSU h 1 1) : ℤ) =
      (((p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) : ℕ) : ℤ) := by
    rw [hS]
    push_cast [h1]
    norm_num
  exact_mod_cast hZ

theorem card_of_isSU3 {X : Type} [Group X] {q : ℕ} (h : IsSU3 q X) :
    Nat.card X = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h
  have := Fintype.ofFinite K
  obtain ⟨m, hp, hm⟩ := FiniteField.card K (ringChar K)
  rw [← Nat.card_eq_fintype_card, hK] at hm
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp (⟨q, by rw [← hm, sq]⟩ : q ∣ _)
  have h2k : 2 * k = m := by
    rw [← pow_mul, mul_comm] at hm
    exact Nat.pow_right_injective hp.two_le hm
  have hk1 : 1 ≤ k := by
    have := m.pos
    omega
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData (ringChar K) k K :=
    ⟨hp, hk1, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := CFSG.ClassicalGroups.UnitaryFlag.exists_isHypTransport hU (r := 1) (ε := 1)
  rw [Nat.card_congr (φ.trans (CFSG.ClassicalGroups.UnitaryFlag.hypTransport hU hR).symm).toEquiv]
  exact card_hypSU_three' hU

theorem card_of_list2 (hG2 : FactG2AdjointOrder) (h3D4 : Fact3D4Order) {X : Type} [Group X]
    (hX : List11_1_1Two X 2) :
    Nat.card X = 60480 ∨ Nat.card X = 20160 ∨ Nat.card X = 979200 ∨
      Nat.card X = 251596800 ∨ Nat.card X = 67802350642790400 := by
  rcases hX with h | h | h | h | h | h | ⟨h3, -⟩
  · left
    rw [card_of_isSL3 h]
    norm_num
  · exact Or.inr (Or.inl (card_of_isPSL_three_two_two h))
  · right; right; left
    rw [(card_of_isPSp4 h).2]
    norm_num
  · right; right; right; left
    obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := h
    rw [Nat.card_congr φ.toEquiv, hG2 K 2 (by norm_num) hK]
    norm_num
  · exfalso
    obtain ⟨-, a, ha, -⟩ := h
    omega
  · right; right; right; right
    rw [h3D4 X 2 (by norm_num) h]
    norm_num
  · exfalso
    omega

end C11P9B

open C11P9B

theorem factList2PSL3_of (hG2 : FactG2AdjointOrder) (h3D4 : Fact3D4Order) : FactList2PSL3 := by
  intro X _ _ hX s p e hp he hS
  have hN := card_of_list2 hG2 h3D4 hX
  cases s
  · exfalso
    have h := card_mul_gcd_of_isPSU3 hS
    generalize p ^ e = q at h
    have hd1 : 1 ≤ Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hd3 : Nat.gcd 3 (q + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    rcases hN with hN | hN | hN | hN | hN <;> rw [hN] at h
    · obtain ⟨h1, h2⟩ := window_U hd1 hd3 h (a := 3) (b := 4) (by norm_num) (by norm_num)
      interval_cases q
      norm_num at h
    · obtain ⟨h1, h2⟩ := window_U hd1 hd3 h (a := 3) (b := 3) (by norm_num) (by norm_num)
      omega
    · obtain ⟨h1, h2⟩ := window_U hd1 hd3 h (a := 5) (b := 6) (by norm_num) (by norm_num)
      interval_cases q
      norm_num at h
    · obtain ⟨h1, h2⟩ := window_U hd1 hd3 h (a := 11) (b := 12) (by norm_num) (by norm_num)
      interval_cases q
      norm_num at h
    · obtain ⟨h1, h2⟩ := window_U hd1 hd3 h (a := 127) (b := 145) (by norm_num) (by norm_num)
      interval_cases q <;> norm_num at h
  · have h := card_mul_gcd_of_isPSL3' hS
    generalize hq : p ^ e = q at h
    have hd1 : 1 ≤ Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hd3 : Nat.gcd 3 (q - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    rcases hN with hN | hN | hN | hN | hN <;> rw [hN] at h
    · obtain ⟨h1, h2⟩ := window_L hd1 hd3 h (a := 3) (b := 4) (by norm_num) (by norm_num)
      interval_cases q
      norm_num at h
    · obtain ⟨h1, h2⟩ := window_L hd1 hd3 h (a := 3) (b := 4) (by norm_num) (by norm_num)
      interval_cases q
      exact ⟨rfl, eq_two_two_of_pow_eq_four hp hq⟩
    · obtain ⟨h1, h2⟩ := window_L hd1 hd3 h (a := 5) (b := 6) (by norm_num) (by norm_num)
      interval_cases q
      norm_num at h
    · obtain ⟨h1, h2⟩ := window_L hd1 hd3 h (a := 11) (b := 12) (by norm_num) (by norm_num)
      interval_cases q
      norm_num at h
    · obtain ⟨h1, h2⟩ := window_L hd1 hd3 h (a := 127) (b := 145) (by norm_num) (by norm_num)
      interval_cases q <;> norm_num at h

theorem factA7Cent_of (h7 : FactA7SectionCent) : FactA7Cent := by
  intro X _ _ hX
  have hN : Nat.card X = 2520 ∨ Nat.card X = 7560 := by
    rcases hX with hA | ⟨-, hZ, ⟨φ⟩⟩
    · obtain ⟨φ⟩ := (hA : Nonempty (X ≃* alternatingGroup (Fin 7)))
      left
      rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      rfl
    · right
      rw [(Subgroup.center X).card_eq_card_quotient_mul_card_subgroup, Nat.card_congr φ.toEquiv,
        hZ, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      rfl
  refine ⟨h7 X hX, fun s q hS => ?_, fun s p e hS => ?_⟩
  · cases s
    · have h : Nat.card X * 1 = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
        rw [mul_one]
        exact card_of_isSU3 hS
      rcases hN with hN | hN <;> rw [hN] at h
      · obtain ⟨h1, h2⟩ := window_U le_rfl (by norm_num) h (a := 2) (b := 3) (by norm_num)
          (by norm_num)
        interval_cases q
        norm_num at h
      · obtain ⟨h1, h2⟩ := window_U le_rfl (by norm_num) h (a := 3) (b := 3) (by norm_num)
          (by norm_num)
        omega
    · have h : Nat.card X * 1 = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
        rw [mul_one]
        exact card_of_isSL3 hS
      rcases hN with hN | hN <;> rw [hN] at h
      · obtain ⟨h1, h2⟩ := window_L le_rfl (by norm_num) h (a := 2) (b := 3) (by norm_num)
          (by norm_num)
        interval_cases q
        norm_num at h
      · obtain ⟨h1, h2⟩ := window_L le_rfl (by norm_num) h (a := 3) (b := 3) (by norm_num)
          (by norm_num)
        omega
  · cases s
    · have h := card_mul_gcd_of_isPSU3 hS
      generalize p ^ e = q at h
      have hd1 : 1 ≤ Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
      have hd3 : Nat.gcd 3 (q + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
      rcases hN with hN | hN <;> rw [hN] at h
      · obtain ⟨h1, h2⟩ := window_U hd1 hd3 h (a := 2) (b := 3) (by norm_num) (by norm_num)
        interval_cases q
        norm_num at h
      · obtain ⟨h1, h2⟩ := window_U hd1 hd3 h (a := 3) (b := 3) (by norm_num) (by norm_num)
        omega
    · have h := card_mul_gcd_of_isPSL3' hS
      generalize p ^ e = q at h
      have hd1 : 1 ≤ Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
      have hd3 : Nat.gcd 3 (q - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
      rcases hN with hN | hN <;> rw [hN] at h
      · obtain ⟨h1, h2⟩ := window_L hd1 hd3 h (a := 2) (b := 3) (by norm_num) (by norm_num)
        interval_cases q
        norm_num at h
      · obtain ⟨h1, h2⟩ := window_L hd1 hd3 h (a := 3) (b := 3) (by norm_num) (by norm_num)
        omega

end CFSG.Quasithin.Vol2.Ch11.SecA
