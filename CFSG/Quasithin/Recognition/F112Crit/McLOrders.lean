module

public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K64Types

public section

namespace CFSG.Quasithin.F112Crit.McLOrd

open CFSG.Timmesfeld CFSG.Open CFSG.HardMathSupport.Solomon
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K64

@[expose] def McLArith (w : ℕ) : Prop :=
  0 < w ∧ 3 ∣ w ∧
    (∀ j p : ℕ, 4 ≤ j → IsPrimitivePrimeDivisor p (2 * j) → p ∣ w → 2 ^ (j + 2) ∣ w) ∧
    w ≠ 504 ∧ w ≠ 1008

theorem primDiv_lt {p k : ℕ} (h : IsPrimitivePrimeDivisor p k) (hk : 0 < k) : k < p := by
  have hp := h.prime
  have hcop : Nat.Coprime 2 p :=
    (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm (h.ne_two hk))
  have hmod : 2 ^ Nat.totient p ≡ 1 [MOD p] := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime hp] at hmod
  have hf : p ∣ 2 ^ (p - 1) - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmod.symm
  have h2 := hp.two_le
  have h1 := Nat.le_of_dvd (by omega) ((h.dvd_sub_one_iff hk (p - 1)).mp hf)
  omega

theorem le_of_two_pow_dvd {a b r : ℕ} (hr : Odd r) (h : 2 ^ a ∣ 2 ^ b * r) : a ≤ b := by
  have hc : Nat.Coprime (2 ^ a) r := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hr)
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hc.dvd_of_dvd_mul_right h)

theorem two_pow_dvd_factorial {j n : ℕ} (hj : 4 ≤ j) (hn : 2 * j ≤ n) :
    2 ^ (j + 2) ∣ n.factorial := by
  refine dvd_trans ?_ (Nat.factorial_dvd_factorial hn)
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [show 2 * (i + 1) = (2 * i + 1) + 1 by ring, Nat.factorial_eq_mul_doubleFactorial,
    show 2 * i + 1 + 1 = 2 * (i + 1) by ring, Nat.doubleFactorial_two_mul, pow_add, mul_assoc]
  refine mul_dvd_mul_left _ (dvd_mul_of_dvd_left ?_ _)
  exact dvd_trans (by decide : 2 ^ 2 ∣ Nat.factorial 4) (Nat.factorial_dvd_factorial (by omega))

theorem dvd_of_dvd_two_pow_mul {p a x : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 2 ^ a * x) :
    p ∣ x := by
  rcases hp.dvd_mul.mp h with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)) hp2
  · exact h

theorem two_pow_sub_one_pos {k : ℕ} (hk : 0 < k) : 0 < 2 ^ k - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))

theorem false_of_top {w s j r c p : ℕ} (hw : McLArith w) (hc : c = 1 ∨ c = 2)
    (hws : w = c * s) (hs : s ∣ 2 ^ j * r) (hr : Odd r) (hj : 4 ≤ j)
    (hp : IsPrimitivePrimeDivisor p (2 * j)) (hps : p ∣ s) : False := by
  have h := hw.2.2.1 j p hj hp (hws ▸ dvd_mul_of_dvd_right hps c)
  have h2 : 2 ^ (j + 2) ∣ 2 ^ (j + 1) * r := by
    refine h.trans ?_
    rw [hws]
    refine (mul_dvd_mul_left c hs).trans ?_
    rcases hc with rfl | rfl
    · rw [one_mul]
      exact mul_dvd_mul_right (Nat.pow_dvd_pow 2 (by omega)) r
    · rw [← mul_assoc, ← pow_succ']
  have := le_of_two_pow_dvd hr h2
  omega

theorem card_statedSL_zmod_two {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (StatedSL n (ZMod 2)) = 2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) := by
  rw [CFSG.Open.StatedAPI.card_statedSL,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq hn, Nat.card_zmod]

theorem mcLArith_SL {n : ℕ} (hn : 2 ≤ n) :
    McLArith (2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1)) := by
  have hmem : 2 ∈ Finset.Icc 2 n := Finset.mem_Icc.mpr ⟨le_rfl, hn⟩
  refine ⟨Nat.mul_pos (Nat.two_pow_pos _) (Finset.prod_pos fun j hj => ?_), ?_, ?_, ?_⟩
  · exact two_pow_sub_one_pos (by have := (Finset.mem_Icc.mp hj).1; omega)
  · exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun j => 2 ^ j - 1) hmem) _
  · intro j p hj hp hpw
    have hk : 0 < 2 * j := by omega
    obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hp.prime.prime _).mp
      (dvd_of_dvd_two_pow_mul hp.prime (hp.ne_two hk) hpw)
    have hi' := Finset.mem_Icc.mp hi
    have h2j : 2 * j ≤ n :=
      (Nat.le_of_dvd (by omega) ((hp.dvd_sub_one_iff hk i).mp hpi)).trans hi'.2
    refine dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 ?_) _
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have h8 : 8 * m ≤ (m + 1) * m := Nat.mul_le_mul_right m (by omega)
    apply (Nat.le_div_iff_mul_le (by norm_num)).mpr
    generalize (m + 1) * m = X at h8 ⊢
    omega
  · rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
    · decide
    · decide
    · have h32 : 2 ^ 5 ∣ 2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) := by
        refine dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 ?_) _
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [Nat.add_sub_cancel]
        have h4' : 4 * m ≤ (m + 1) * m := Nat.mul_le_mul_right m (by omega)
        apply (Nat.le_div_iff_mul_le (by norm_num)).mpr
        generalize (m + 1) * m = X at h4' ⊢
        omega
      constructor <;> intro h <;> rw [h] at h32 <;> norm_num at h32

theorem card_statedSp_zmod_two (n : ℕ) :
    Nat.card (StatedSp n (ZMod 2)) = 2 ^ (n ^ 2) * ∏ j ∈ Finset.Icc 1 n, (2 ^ (2 * j) - 1) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod]

theorem mcLArith_Sp {n : ℕ} (hn : 2 ≤ n) :
    McLArith (2 ^ (n ^ 2) * ∏ j ∈ Finset.Icc 1 n, (2 ^ (2 * j) - 1)) := by
  have hmem : 1 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  refine ⟨Nat.mul_pos (Nat.two_pow_pos _) (Finset.prod_pos fun j hj => ?_), ?_, ?_, ?_⟩
  · exact two_pow_sub_one_pos (by have := (Finset.mem_Icc.mp hj).1; omega)
  · exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun j => 2 ^ (2 * j) - 1) hmem) _
  · intro j p hj hp hpw
    have hk : 0 < 2 * j := by omega
    obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hp.prime.prime _).mp
      (dvd_of_dvd_two_pow_mul hp.prime (hp.ne_two hk) hpw)
    have hi' := Finset.mem_Icc.mp hi
    have hji : j ≤ i := by
      have := Nat.le_of_dvd (by omega) ((hp.dvd_sub_one_iff hk (2 * i)).mp hpi)
      omega
    refine dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 ?_) _
    have h4 : 4 * n ≤ n ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right n (by omega)
    generalize n ^ 2 = X at h4 ⊢
    omega
  · rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
    · decide
    · have h32 : 2 ^ 5 ∣ 2 ^ (n ^ 2) * ∏ j ∈ Finset.Icc 1 n, (2 ^ (2 * j) - 1) := by
        refine dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 ?_) _
        have h3' : 3 * n ≤ n ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right n h3
        generalize n ^ 2 = X at h3' ⊢
        omega
      constructor <;> intro h <;> rw [h] at h32 <;> norm_num at h32

theorem cast_two_pow_sub_one (a : ℕ) : ((2 ^ a - 1 : ℕ) : ℤ) = 2 ^ a - 1 := by
  rw [Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  ring

theorem card_glaPlus_zmod_two (m : ℕ) :
    Nat.card ↥(GLAOrthGroup (GLAQPlus (ZMod 2) (m + 1))) =
      2 * 2 ^ (m * (m + 1)) * (2 ^ (m + 1) - 1) * ∏ i ∈ Finset.Icc 1 m, (2 ^ (2 * i) - 1) := by
  rw [card_glaPlus]
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadPlus (K := ZMod 2) m
  rw [Nat.card_zmod] at h
  apply Nat.cast_injective (R := ℤ)
  rw [h, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_prod]
  simp only [cast_two_pow_sub_one]
  push_cast
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [pow_mul]
  norm_num

theorem card_glaMinus_zmod_two (n : ℕ) :
    Nat.card ↥(GLAOrthGroup (GLAQMinus n (1 : ZMod 2) 1)) =
      2 * 2 ^ (n * (n + 1)) * (2 ^ (n + 1) + 1) * ∏ i ∈ Finset.Icc 1 n, (2 ^ (2 * i) - 1) := by
  rw [card_glaMinus]
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus (K := ZMod 2)
    CFSG.HardMathSupport.Solomon.Coordinator.mcltf_irr n
  rw [Nat.card_zmod] at h
  apply Nat.cast_injective (R := ℤ)
  rw [h, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_prod]
  simp only [cast_two_pow_sub_one]
  push_cast
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [pow_mul]
  norm_num

theorem mcLArith_OPlus {m : ℕ} (hm : 1 ≤ m) :
    McLArith (2 * 2 ^ (m * (m + 1)) * (2 ^ (m + 1) - 1) *
      ∏ i ∈ Finset.Icc 1 m, (2 ^ (2 * i) - 1)) := by
  have hmem : 1 ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨le_rfl, hm⟩
  have hw : 2 * 2 ^ (m * (m + 1)) * (2 ^ (m + 1) - 1) * ∏ i ∈ Finset.Icc 1 m, (2 ^ (2 * i) - 1) =
      2 ^ (m * (m + 1) + 1) * ((2 ^ (m + 1) - 1) * ∏ i ∈ Finset.Icc 1 m, (2 ^ (2 * i) - 1)) := by
    ring
  rw [hw]
  refine ⟨Nat.mul_pos (Nat.two_pow_pos _) (Nat.mul_pos (two_pow_sub_one_pos (by omega))
    (Finset.prod_pos fun i hi => ?_)), ?_, ?_, ?_⟩
  · exact two_pow_sub_one_pos (by have := (Finset.mem_Icc.mp hi).1; omega)
  · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right
      (Finset.dvd_prod_of_mem (fun i => 2 ^ (2 * i) - 1) hmem) _) _
  · intro j p hj hp hpw
    have hk : 0 < 2 * j := by omega
    have hjm : j ≤ m := by
      rcases hp.prime.dvd_mul.mp (dvd_of_dvd_two_pow_mul hp.prime (hp.ne_two hk) hpw) with h | h
      · have := Nat.le_of_dvd (by omega) ((hp.dvd_sub_one_iff hk (m + 1)).mp h)
        omega
      · obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hp.prime.prime _).mp h
        have hi' := Finset.mem_Icc.mp hi
        have := Nat.le_of_dvd (by omega) ((hp.dvd_sub_one_iff hk (2 * i)).mp hpi)
        omega
    refine dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 ?_) _
    have h1 : m + 1 ≤ m * (m + 1) := Nat.le_mul_of_pos_left (m + 1) (by omega)
    generalize m * (m + 1) = X at h1 ⊢
    omega
  · rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | h2
    · decide
    · have h32 : 2 ^ 5 ∣ 2 ^ (m * (m + 1) + 1) *
          ((2 ^ (m + 1) - 1) * ∏ i ∈ Finset.Icc 1 m, (2 ^ (2 * i) - 1)) := by
        refine dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 ?_) _
        have h3 : 2 * 3 ≤ m * (m + 1) := Nat.mul_le_mul h2 (by omega)
        generalize m * (m + 1) = X at h3 ⊢
        omega
      constructor <;> intro h <;> rw [h] at h32 <;> norm_num at h32

theorem mcLArith_OMinus {n : ℕ} (hn : 1 ≤ n) :
    McLArith (2 * 2 ^ (n * (n + 1)) * (2 ^ (n + 1) + 1) *
      ∏ i ∈ Finset.Icc 1 n, (2 ^ (2 * i) - 1)) := by
  have hmem : 1 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨le_rfl, hn⟩
  have hw : 2 * 2 ^ (n * (n + 1)) * (2 ^ (n + 1) + 1) * ∏ i ∈ Finset.Icc 1 n, (2 ^ (2 * i) - 1) =
      2 ^ (n * (n + 1) + 1) * ((2 ^ (n + 1) + 1) * ∏ i ∈ Finset.Icc 1 n, (2 ^ (2 * i) - 1)) := by
    ring
  rw [hw]
  refine ⟨Nat.mul_pos (Nat.two_pow_pos _) (Nat.mul_pos (by positivity)
    (Finset.prod_pos fun i hi => ?_)), ?_, ?_, ?_⟩
  · exact two_pow_sub_one_pos (by have := (Finset.mem_Icc.mp hi).1; omega)
  · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right
      (Finset.dvd_prod_of_mem (fun i => 2 ^ (2 * i) - 1) hmem) _) _
  · intro j p hj hp hpw
    have hk : 0 < 2 * j := by omega
    have hjn : j ≤ n + 1 := by
      rcases hp.prime.dvd_mul.mp (dvd_of_dvd_two_pow_mul hp.prime (hp.ne_two hk) hpw) with h | h
      · have := Nat.le_of_dvd (by omega) ((hp.dvd_add_one_iff hk (n + 1)).mp h).1
        omega
      · obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hp.prime.prime _).mp h
        have hi' := Finset.mem_Icc.mp hi
        have := Nat.le_of_dvd (by omega) ((hp.dvd_sub_one_iff hk (2 * i)).mp hpi)
        omega
    refine dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 ?_) _
    have h3 : 3 * (n + 1) ≤ n * (n + 1) := Nat.mul_le_mul_right (n + 1) (by omega)
    generalize n * (n + 1) = X at h3 ⊢
    omega
  · rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | h2
    · decide
    · have h32 : 2 ^ 5 ∣ 2 ^ (n * (n + 1) + 1) *
          ((2 ^ (n + 1) + 1) * ∏ i ∈ Finset.Icc 1 n, (2 ^ (2 * i) - 1)) := by
        refine dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 ?_) _
        have h3 : 2 * 3 ≤ n * (n + 1) := Nat.mul_le_mul h2 (by omega)
        generalize n * (n + 1) = X at h3 ⊢
        omega
      constructor <;> intro h <;> rw [h] at h32 <;> norm_num at h32

theorem mcLArith_perm {n : ℕ} (hn : 5 ≤ n) : McLArith n.factorial := by
  refine ⟨Nat.factorial_pos n, Nat.dvd_factorial (by norm_num) (by omega), ?_, ?_⟩
  · intro j p hj hp hpw
    have hpn : p ≤ n := (Nat.Prime.dvd_factorial hp.prime).mp hpw
    have := primDiv_lt hp (by omega)
    exact two_pow_dvd_factorial hj (by omega)
  · rcases (show n = 5 ∨ n = 6 ∨ 7 ≤ n by omega) with rfl | rfl | h7
    · decide
    · decide
    · have h1 : Nat.factorial 7 ≤ n.factorial := Nat.factorial_le h7
      have h2 : Nat.factorial 7 = 5040 := by decide
      omega

theorem mcLArith_of_isMcLaughlinGroup {W : Type} [Group W]
    (h : UniquenessMaximal.IsMcLaughlinGroup W) : McLArith (Nat.card W) := by
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, card_statedSL_zmod_two (by omega)]
    exact mcLArith_SL hn
  · rw [Nat.card_congr e.toEquiv, card_statedSp_zmod_two]
    exact mcLArith_Sp hn
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.card_congr e.toEquiv, card_glaPlus_zmod_two]
    exact mcLArith_OPlus (by omega)
  · rw [Nat.card_congr e.toEquiv, card_glaMinus_zmod_two]
    exact mcLArith_OMinus hn
  · rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact mcLArith_perm hn

end CFSG.Quasithin.F112Crit.McLOrd

end
