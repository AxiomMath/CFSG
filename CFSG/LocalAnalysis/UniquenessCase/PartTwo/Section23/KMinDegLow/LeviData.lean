module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Timmesfeld.Orders.Bang
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.Rep
import all CFSG.Timmesfeld.Orders.Distinct
import CFSG.Timmesfeld.Orders.Classical
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
import CFSG.GH74.QTGen4.U42.L28Nine
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCaseTwoCMArith

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow

open CFSG.Timmesfeld Matrix
open CFSG.Timmesfeld.Orders CFSG.Open

structure LeviData (T : Type) [Group T] (n : ℕ) : Prop where
  simple : IsSimpleGroup T
  nonab : ∃ a b : T, a * b ≠ b * a
  bound : ∃ m, 2 ≤ m ∧ (3 ∣ Nat.card T ∨ m = 4) ∧
    (∃ t : T, ∀ (d : ℕ) (g : GL (Fin d) (ZMod 2)), orderOf g = orderOf t → m * n ≤ d) ∧
    (m * n ≠ 6 → ∃ p, IsPrimitivePrimeDivisor p (m * n) ∧ p ∣ Nat.card T)

private theorem isPrimitivePrimeDivisor_three_two : IsPrimitivePrimeDivisor 3 2 := by
  refine ⟨Nat.prime_three, by norm_num, fun j hj hj2 => ?_⟩
  interval_cases j
  norm_num

private theorem nonab_of_pow_two_dvd {T : Type} [Group T] [Finite T] (hT : IsSimpleGroup T)
    {n : ℕ} (hn : 2 < n) (h : 2 ^ n ∣ Nat.card T) : ∃ a b : T, a * b ≠ b * a := by
  haveI := hT.toNontrivial
  have hpos : 0 < Nat.card T := Nat.card_pos
  have hle : 2 ^ n ≤ Nat.card T := Nat.le_of_dvd hpos h
  have h2lt : 2 < 2 ^ n := by
    have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : 1 < n)
    simpa using this
  have h2 : 2 ∣ Nat.card T := (dvd_pow_self 2 (by omega : n ≠ 0)).trans h
  by_contra hnab
  have hcomm : ∀ a b : T, a * b = b * a := fun a b => by
    by_contra hab
    exact hnab ⟨a, b, hab⟩
  haveI : IsMulCommutative T := IsMulCommutative.mk (Std.Commutative.mk hcomm)
  exact Nat.not_prime_of_dvd_of_lt h2 (by norm_num) (h2lt.trans_le hle)
    (Group.is_simple_iff_prime_card.mp hT)

private theorem exists_ppd_dvd_of_profile {T : Type} [Group T] [Finite T] {N N₀ k : ℕ}
    {Z : ℕ → Prop} (hcard : Nat.card T = N) (hprof : Profile N N₀ Z)
    (hk2 : 2 ≤ k) (hk6 : k ≠ 6) (hZ : Z k) :
    ∃ p, IsPrimitivePrimeDivisor p k ∧ p ∣ Nat.card T := by
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor hk2 hk6
  exact ⟨p, hp, hcard.symm ▸ (hprof.prim p k hp (by omega)).mpr hZ⟩

private theorem exists_orderOf_of_profile {T : Type} [Group T] [Finite T] {N N₀ k : ℕ}
    {Z : ℕ → Prop} (hcard : Nat.card T = N) (hprof : Profile N N₀ Z)
    (hk2 : 2 ≤ k) (hk6 : k ≠ 6) (hZ : Z k) :
    ∃ t : T, ∀ (d : ℕ) (g : GL (Fin d) (ZMod 2)), orderOf g = orderOf t → k ≤ d := by
  obtain ⟨p, hp, hdvd⟩ := exists_ppd_dvd_of_profile hcard hprof hk2 hk6 hZ
  haveI : Fact p.Prime := ⟨hp.prime⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact ⟨t, fun d g hg => le_of_orderOf_eq_ppd hp (by omega) g (hg.trans ht)⟩

private theorem three_dvd_of_profile {N N₀ : ℕ} {Z : ℕ → Prop} (hprof : Profile N N₀ Z)
    (hZ : Z 2) : 3 ∣ N :=
  (hprof.prim 3 2 isPrimitivePrimeDivisor_three_two (by norm_num)).mpr hZ

private theorem isPrimitivePrimeDivisor_nineteen_eighteen : IsPrimitivePrimeDivisor 19 18 := by
  refine ⟨by norm_num, by norm_num, fun j hj hj18 => ?_⟩
  interval_cases j <;> norm_num

theorem leviData_l2 {T : Type} [Group T] [Finite T] {n : ℕ} (h : IsL2 T n) (hn : 2 < n) :
    LeviData T n := by
  have hB : CFSG.Blueprint.LieModel T .PSL 2 2 n := h
  haveI := uc22p22r_lieModel_isSimple_classical (Or.inl rfl) hB
  have hX := CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hB
  have hcard : Nat.card T = ordA 1 (2 ^ n) := (card_statedClassicalModel_two hX).1 rfl
  have hprof := profile_ordA (n := 1) (f := n) (by norm_num) (by omega)
  have hq : 2 ^ n ∣ Nat.card T := by
    rw [hcard]
    have h := CFSG.AGLEmbedding.pow_dvd_ordA 1 (2 ^ n) (by norm_num)
    rwa [show 1 * (1 + 1) / 2 = 1 by norm_num, pow_one] at h
  have h3 : 3 ∣ Nat.card T := by
    rw [hcard]
    exact three_dvd_of_profile hprof (by
      unfold zA
      exact ⟨2, by norm_num, dvd_mul_left 2 n⟩)
  have hz : zA 1 n (2 * n) := by
    unfold zA
    exact ⟨2, by norm_num, ⟨1, by ring⟩⟩
  refine ⟨‹IsSimpleGroup T›, nonab_of_pow_two_dvd ‹IsSimpleGroup T› hn hq, ?_⟩
  refine ⟨2, by norm_num, Or.inl h3, ?_, ?_⟩
  · by_cases hn3 : n = 3
    · subst hn3
      obtain ⟨t, ht⟩ :=
        CFSG.GH74.QTGen4.U42.L28Nine.exists_orderOf_nine_of_lieModel_psl2_three hB
      exact ⟨t, fun d g hg => by
        have h6 := six_le_of_orderOf_eq_nine g (hg.trans ht)
        omega⟩
    · exact exists_orderOf_of_profile hcard hprof (by omega) (by omega) hz
  · intro h6
    exact exists_ppd_dvd_of_profile hcard hprof (by omega) h6 hz

theorem leviData_l3 {T : Type} [Group T] [Finite T] {n : ℕ} (h : IsL3 T n) (hn : 2 < n) :
    LeviData T n := by
  have hB : CFSG.Blueprint.LieModel T .PSL 3 2 n := h
  haveI := uc22p22r_lieModel_isSimple_classical (Or.inl rfl) hB
  have hX := CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hB
  have hcard : Nat.card T = ordA 2 (2 ^ n) := (card_statedClassicalModel_two hX).1 rfl
  have hprof := profile_ordA (n := 2) (f := n) (by norm_num) (by omega)
  have hq3 : (2 ^ n) ^ 3 ∣ Nat.card T := by
    rw [hcard]
    have h := CFSG.AGLEmbedding.pow_dvd_ordA 2 (2 ^ n) (by norm_num)
    rwa [show 2 * (2 + 1) / 2 = 3 by norm_num] at h
  have hq : 2 ^ n ∣ Nat.card T :=
    (dvd_pow_self (2 ^ n) (by norm_num : (3 : ℕ) ≠ 0)).trans hq3
  have h3 : 3 ∣ Nat.card T := by
    rw [hcard]
    exact three_dvd_of_profile hprof (by
      unfold zA
      exact ⟨2, by norm_num, dvd_mul_left 2 n⟩)
  have hz : zA 2 n (3 * n) := by
    unfold zA
    exact ⟨3, by norm_num, ⟨1, by ring⟩⟩
  refine ⟨‹IsSimpleGroup T›, nonab_of_pow_two_dvd ‹IsSimpleGroup T› hn hq, ?_⟩
  refine ⟨3, by norm_num, Or.inl h3, ?_, ?_⟩
  · exact exists_orderOf_of_profile hcard hprof (by omega) (by omega) hz
  · intro h6
    exact exists_ppd_dvd_of_profile hcard hprof (by omega) (by omega) hz

theorem leviData_u3 {T : Type} [Group T] [Finite T] {n : ℕ} (h : IsU3 T n) (hn : 2 < n) :
    LeviData T n := by
  have hB : CFSG.Blueprint.LieModel T .PSU 3 2 n := h
  haveI := uc22p22r_lieModel_isSimple_classical (Or.inr (Or.inl rfl)) hB
  have hX := CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hB
  have hcard : Nat.card T = ordTwistedA 2 (2 ^ n) := (card_statedClassicalModel_two hX).2.1 rfl
  have hprof := profile_ordTwistedA (n := 2) (g := n) (by norm_num) (by omega)
  have hq3 : (2 ^ n) ^ 3 ∣ Nat.card T := by
    rw [hcard]
    have h := CFSG.AGLEmbedding.pow_dvd_ordTwistedA 2 (2 ^ n) (by norm_num) Nat.one_le_two_pow
    rwa [show 2 * (2 + 1) / 2 = 3 by norm_num] at h
  have hq : 2 ^ n ∣ Nat.card T :=
    (dvd_pow_self (2 ^ n) (by norm_num : (3 : ℕ) ≠ 0)).trans hq3
  have h3 : 3 ∣ Nat.card T := by
    rw [hcard]
    exact three_dvd_of_profile hprof (by
      unfold zU
      exact ⟨2, by norm_num, Or.inl ⟨by norm_num, dvd_mul_left 2 n⟩⟩)
  have hz : zU 2 n (6 * n) := by
    unfold zU
    refine ⟨3, by norm_num, Or.inr ⟨by norm_num, ?_, ?_⟩⟩
    · exact ⟨1, by ring⟩
    · intro hdvd
      have hle := Nat.le_of_dvd (by positivity : 0 < n * 3) hdvd
      omega
  refine ⟨‹IsSimpleGroup T›, nonab_of_pow_two_dvd ‹IsSimpleGroup T› hn hq, ?_⟩
  refine ⟨6, by norm_num, Or.inl h3, ?_, ?_⟩
  · exact exists_orderOf_of_profile hcard hprof (by omega) (by omega) hz
  · intro h6
    exact exists_ppd_dvd_of_profile hcard hprof (by omega) (by omega) hz

theorem leviData_sp4 {T : Type} [Group T] [Finite T] {n : ℕ} (h : IsSp4 T n) (hn : 2 < n) :
    LeviData T n := by
  have hB : CFSG.Blueprint.LieModel T .PSp 2 2 n := h
  haveI := uc22p22r_lieModel_isSimple_classical (Or.inr (Or.inr (Or.inl rfl))) hB
  have hX := CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hB
  have hcard : Nat.card T = ordBC 2 (2 ^ n) := (card_statedClassicalModel_two hX).2.2.1 rfl
  have hprof := profile_ordBC (n := 2) (f := n) (by omega)
  have hq4 : (2 ^ n) ^ 4 ∣ Nat.card T := by
    rw [hcard]
    have h := CFSG.AGLEmbedding.pow_dvd_ordBC 2 (2 ^ n) (by norm_num)
    rwa [show 2 * 2 = 4 by norm_num] at h
  have hq : 2 ^ n ∣ Nat.card T :=
    (dvd_pow_self (2 ^ n) (by norm_num : (4 : ℕ) ≠ 0)).trans hq4
  have hz : zBC 2 n (4 * n) := by
    unfold zBC
    exact ⟨2, by norm_num, ⟨1, by ring⟩⟩
  refine ⟨‹IsSimpleGroup T›, nonab_of_pow_two_dvd ‹IsSimpleGroup T› hn hq, ?_⟩
  refine ⟨4, by norm_num, Or.inr rfl, ?_, ?_⟩
  · exact exists_orderOf_of_profile hcard hprof (by omega) (by omega) hz
  · intro h6
    exact exists_ppd_dvd_of_profile hcard hprof (by omega) (by omega) hz

theorem leviData_sz
    (hSz : ∀ (X : Type) [Group X] (f : ℕ), IsSz X f → Nat.card X = CFSG.Open.ordSuzuki (2 ^ f))
    {T : Type} [Group T] [Finite T] {n : ℕ} (h : IsSz T n) (hn : 2 < n) : LeviData T n := by
  have hB : CFSG.Blueprint.LieModel T .twistedB2 0 2 n := h
  haveI := uc22p22r_lieModel_isSimple_twistedB2 hB
  have hcard : Nat.card T = CFSG.Open.ordSuzuki (2 ^ n) := hSz T n h
  have hprof := profile_ordSuzuki (f := n) (by omega)
  have hq2 : (2 ^ n) ^ 2 ∣ Nat.card T := by
    rw [hcard]
    unfold CFSG.Open.ordSuzuki
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hq : 2 ^ n ∣ Nat.card T :=
    (dvd_pow_self (2 ^ n) (by norm_num : (2 : ℕ) ≠ 0)).trans hq2
  have hz : zSz n (4 * n) := by
    unfold zSz
    refine Or.inl ⟨?_, ?_⟩
    · exact ⟨1, by ring⟩
    · intro hdvd
      have hle := Nat.le_of_dvd (by positivity : 0 < n * 2) hdvd
      omega
  refine ⟨‹IsSimpleGroup T›, nonab_of_pow_two_dvd ‹IsSimpleGroup T› hn hq, ?_⟩
  refine ⟨4, by norm_num, Or.inr rfl, ?_, ?_⟩
  · exact exists_orderOf_of_profile hcard hprof (by omega) (by omega) hz
  · intro h6
    exact exists_ppd_dvd_of_profile hcard hprof (by omega) (by omega) hz

theorem exists_orderOf_u3_three {T : Type} [Group T] [Finite T] (h : IsU3 T 3) :
    ∃ t : T, ∀ (d : ℕ) (g : GL (Fin d) (ZMod 2)), orderOf g = orderOf t → 18 ≤ d := by
  have hB : CFSG.Blueprint.LieModel T .PSU 3 2 3 := h
  have hX := CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hB
  have hcard : Nat.card T = ordTwistedA 2 (2 ^ 3) := (card_statedClassicalModel_two hX).2.1 rfl
  have hprof := profile_ordTwistedA (n := 2) (g := 3) (by norm_num) (by norm_num)
  have hz : zU 2 3 18 := by
    unfold zU
    refine ⟨3, by norm_num, Or.inr ⟨by norm_num, ?_, ?_⟩⟩
    · exact ⟨1, by norm_num⟩
    · intro hdvd
      have hle := Nat.le_of_dvd (by norm_num : 0 < 3 * 3) hdvd
      omega
  have hdvd : 19 ∣ Nat.card T := by
    rw [hcard]
    exact (hprof.prim 19 18 isPrimitivePrimeDivisor_nineteen_eighteen (by norm_num)).mpr hz
  haveI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 19 hdvd
  exact ⟨t, fun d g hg => le_of_orderOf_eq_ppd isPrimitivePrimeDivisor_nineteen_eighteen
    (by norm_num) g (hg.trans ht)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow
