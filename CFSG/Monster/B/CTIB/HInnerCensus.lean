module

public import CFSG.Monster.B.CTIB.HInnerCert
public import CFSG.Monster.B.CTIB.FourClasses
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import Certificates.Certificate3011
public import Certificates.Certificate3013
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate16022
public import Certificates.Certificate3027
public import Certificates.Certificate16951

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Bin
  CFSG.Monster.B.Short CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.CTIB.Native (censusRecs censusAct qmul gArr natBfs orbitOK)

attribute [local instance] kvLeft

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

@[expose] def innerPts (k : ℕ) : Array ℕ :=
  (natBfs censusAct 2 (censusRecs.getD k (0, 0)).1 ((censusRecs.getD k (0, 0)).2 + 1)).1

theorem censusRecs_length : censusRecs.length = 5 := rfl

theorem censusRecs_getD_mem {k : ℕ} (hk : k < 5) : censusRecs.getD k (0, 0) ∈ censusRecs := by
  rw [List.getD_eq_getElem censusRecs (0, 0) (by rw [censusRecs_length]; exact hk)]
  exact List.getElem_mem _

theorem jOrbit_eq_innerPts
    {k : ℕ} (hk : k < 5) :
    jOrbit (qS (censusRecs.getD k (0, 0)).1) =
      (fun i => vecW (innerPts k)[i]!) '' {i | i < (innerPts k).size} ∧
    ∀ i < (innerPts k).size, censusValid (innerPts k)[i]! = true := by
  have ho := innerOrbOK_eq_true
  simp only [innerOrbOK, List.all_eq_true, List.mem_range] at ho
  obtain ⟨hc, -, -⟩ := orbitOK_parts (ho k hk)
  have h := TwoA.Census.orbit_of_natCertOK hc census_hact
  refine ⟨?_, fun i hi => TwoA.Census.natCertOK_valid hc hi⟩
  rw [jOrbit_code]
  exact h

theorem innerTab_pts
    {k : ℕ} (hk : k < 5) {i : ℕ} (hi : i < (innerPts k).size) :
    innerTab[(innerPts k)[i]!]! = k + 1 := by
  have h := innerTabOK_eq_true
  simp only [innerTabOK, List.all_eq_true, List.mem_range, Array.all_eq_true, beq_iff_eq] at h
  rw [getElem!_pos (innerPts k) i hi]
  exact h k hk i hi

theorem innerTab_spec
    {w : ℕ} (hw : censusValid w = true) :
    ∃ k < 5, innerTab[w]! = k + 1 ∧ vecW w ∈ jOrbit (qS (censusRecs.getD k (0, 0)).1) := by
  obtain ⟨r, hr, hmem⟩ := census_cover (vecW_ne_zero hw)
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
  have hk5 : k < 5 := by rw [censusRecs_length] at hk; exact hk
  rw [← List.getD_eq_getElem censusRecs (0, 0) hk] at hmem
  refine ⟨k, hk5, ?_, hmem⟩
  obtain ⟨horb, hval⟩ := jOrbit_eq_innerPts hk5
  rw [horb] at hmem
  obtain ⟨i, hi, hiw⟩ := hmem
  rw [← census_inj _ _ (hval i hi) hw hiw]
  exact innerTab_pts hk5 hi

theorem psiS_qS_mod (n : ℕ) : psiS (qS n) = vecW (n % 2 ^ 22) :=
  psiS_qS_congr (bvec_mod n).symm

theorem innerTy_spec
    {n : ℕ} (hn : n < 2 ^ 23) :
    (n = 0 ∧ innerTy innerTab n = 0) ∨ (n = 2 ^ 22 ∧ innerTy innerTab n = 6) ∨
      ∃ k < 5, innerTy innerTab n = k + 1 ∧
        psiS (qS n) ∈ jOrbit (qS (censusRecs.getD k (0, 0)).1) := by
  by_cases h0 : n % 2 ^ 22 = 0
  · have hn' : n = 0 ∨ n = 2 ^ 22 := by omega
    rcases hn' with rfl | rfl
    · exact .inl ⟨rfl, by simp [innerTy]⟩
    · exact .inr (.inl ⟨rfl, by simp [innerTy]⟩)
  · have hw : censusValid (n % 2 ^ 22) = true := by
      simp only [censusValid, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨Nat.pos_of_ne_zero h0, Nat.mod_lt _ (by norm_num)⟩
    obtain ⟨k, hk, ht, hmem⟩ := innerTab_spec hw
    refine .inr (.inr ⟨k, hk, ?_, by rwa [psiS_qS_mod]⟩)
    rw [innerTy, ite_eq_right h0, ht]

theorem rank_beta_one :
    ((βr (1 : Sbp)) - 1).rank = 0 := by
  rw [map_one, Units.val_one, sub_self, Matrix.rank_zero]

theorem rank_of_conj_rs
    {y : Sbp} {i : ℕ} (hi : i < 14) (h : IsConj y (rs i)) :
    ((βr y) - 1).rank = Native.repRanks.getD i 0 := by
  rw [rank_beta_conj h, rank_rs hi]

theorem innerRank_spec
    {n : ℕ} (hn : n < 2 ^ 23) :
    (innerTyRank (innerTy innerTab n) = 0 ↔ n = 0) ∧
    (innerTyRank (innerTy innerTab n) = 1 → qS n * qS n = xs) ∧
    (innerTyRank (innerTy innerTab n) ≠ 1 →
      qS n * qS n = 1 ∧ ((βr (qS n)) - 1).rank = innerTyRank (innerTy innerTab n)) := by
  rcases innerTy_spec hn with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨k, hk, ht, hmem⟩
  · rw [ht]
    refine ⟨by simp [innerTyRank], fun h => absurd h (by decide), fun _ => ?_⟩
    rw [qS_zero, mul_one, rank_beta_one]
    exact ⟨rfl, rfl⟩
  · rw [ht, qS_two_pow_22]
    refine ⟨by simp [innerTyRank], fun h => absurd h (by decide), fun _ => ⟨xs_mul_self, ?_⟩⟩
    rw [← rs0_eq, rank_four.2.1]
    rfl
  · have hn0 : n ≠ 0 := by
      rintro rfl
      rw [qS_zero, psiS_one] at hmem
      exact ne_zero_of_mem_census (censusRecs_getD_mem hk) hmem rfl
    rw [ht]
    interval_cases k
    · change psiS (qS n) ∈ jOrbit (qS 1) at hmem
      have hc := isConj_of_mem_jClass (mem_jClass_of (by decide) (qS_mem n) hmem)
      refine ⟨by simp [innerTyRank, hn0], fun h => absurd h (by decide), fun _ =>
        ⟨sq_one_of_mem (qS_mem n) (.inl (.inl hmem)), ?_⟩⟩
      rw [← rs1_eq] at hc
      rw [rank_of_conj_rs (by norm_num) hc]
      rfl
    · change psiS (qS n) ∈ jOrbit (qS 3) at hmem
      have hc := isConj_of_mem_jClass (mem_jClass_of (by decide) (qS_mem n) hmem)
      refine ⟨by simp [innerTyRank, hn0], fun h => absurd h (by decide), fun _ =>
        ⟨sq_one_of_mem (qS_mem n) (.inl (.inr hmem)), ?_⟩⟩
      rw [← rs2_eq] at hc
      rw [rank_of_conj_rs (by norm_num) hc]
      rfl
    · change psiS (qS n) ∈ jOrbit (qS 7) at hmem
      have hc := isConj_of_mem_jClass (mem_jClass_of (by decide) (qS_mem n) hmem)
      refine ⟨by simp [innerTyRank, hn0], fun h => absurd h (by decide), fun _ =>
        ⟨sq_one_of_mem (qS_mem n) (.inr hmem), ?_⟩⟩
      rw [← rs3_eq] at hc
      rw [rank_of_conj_rs (by norm_num) hc]
      rfl
    · change psiS (qS n) ∈ jOrbit (qS 17) at hmem
      exact ⟨by simp [innerTyRank, hn0], fun _ => sq_x_of_mem (qS_mem n) (.inl hmem),
        fun h => absurd rfl h⟩
    · change psiS (qS n) ∈ jOrbit (qS 19) at hmem
      exact ⟨by simp [innerTyRank, hn0], fun _ => sq_x_of_mem (qS_mem n) (.inr hmem),
        fun h => absurd rfl h⟩

theorem innerPairIdx_ne_zero (a b : ℕ) : innerPairIdx a b ≠ 0 := by
  unfold innerPairIdx
  split_ifs <;> decide

theorem innerPairIdx_eq_six_iff {a b : ℕ} : innerPairIdx a b = 6 ↔ a = 1 := by
  unfold innerPairIdx
  split_ifs <;> omega

theorem innerPairIdx_one {a b : ℕ} : innerPairIdx a b = 1 ↔ a = 2048 ∧ b = 1860 := by
  unfold innerPairIdx
  split_ifs <;> omega

theorem innerPairIdx_two {a b : ℕ} : innerPairIdx a b = 2 ↔ a = 1860 ∧ b = 2048 := by
  unfold innerPairIdx
  split_ifs <;> omega

theorem innerPairIdx_three {a b : ℕ} : innerPairIdx a b = 3 ↔ a = 2048 ∧ b = 2168 := by
  unfold innerPairIdx
  split_ifs <;> omega

theorem innerPairIdx_four {a b : ℕ} : innerPairIdx a b = 4 ↔ a = 2168 ∧ b = 2048 := by
  unfold innerPairIdx
  split_ifs <;> omega

theorem innerPairIdx_five {a b : ℕ} : innerPairIdx a b = 5 ↔ a = 2168 ∧ b = 2168 := by
  unfold innerPairIdx
  split_ifs <;> omega

theorem innerPairIdx_cases {a b : ℕ} (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hb0 : b ≠ 0)
    (h9 : innerPairIdx a b ≠ 9) :
    (a = 2048 ∧ b = 1860) ∨ (a = 1860 ∧ b = 2048) ∨ (a = 2048 ∧ b = 2168) ∨
      (a = 2168 ∧ b = 2048) ∨ (a = 2168 ∧ b = 2168) := by
  unfold innerPairIdx at h9
  split_ifs at h9 <;> omega

theorem innerKey_eq_zero_iff (n : ℕ) :
    innerKey innerTab n = 0 ↔ qmul gArr n 1 ≠ qmul gArr 1 n := by
  unfold innerKey
  split_ifs with h
  · exact ⟨fun h' => absurd h' (innerPairIdx_ne_zero _ _), fun h' => absurd h h'⟩
  · exact ⟨fun _ => h, fun _ => rfl⟩

theorem innerKey_of_comm {n : ℕ} (h : qmul gArr n 1 = qmul gArr 1 n) :
    innerKey innerTab n = innerPairIdx (innerTyRank (innerTy innerTab n))
      (innerTyRank (innerTy innerTab (qmul gArr 1 n))) := by
  rw [innerKey, ite_eq_left h]

theorem fold_modify_spec (key : ℕ → ℕ) (sz : ℕ) : ∀ N : ℕ,
    (Nat.fold N (fun n _ h => h.modify (key n) (· + 1)) (Array.replicate sz 0)).size = sz ∧
    ∀ i < sz, (Nat.fold N (fun n _ h => h.modify (key n) (· + 1)) (Array.replicate sz 0))[i]! =
      ((Finset.range N).filter (fun n => key n = i)).card
  | 0 => by
    refine ⟨by simp, fun i hi => ?_⟩
    rw [Nat.fold_zero, getElem!_pos _ i (by simpa using hi), Array.getElem_replicate]
    simp
  | N + 1 => by
    obtain ⟨hs, hc⟩ := fold_modify_spec key sz N
    rw [Nat.fold_succ]
    refine ⟨by rw [Array.size_modify]; exact hs, fun i hi => ?_⟩
    have hi' : i < (Nat.fold N (fun n _ h => h.modify (key n) (· + 1))
        (Array.replicate sz 0)).size := by rw [hs]; exact hi
    rw [getElem!_pos _ i (by rw [Array.size_modify]; exact hi'), Array.getElem_modify,
      ← getElem!_pos _ i hi', hc i hi, Finset.range_add_one, Finset.filter_insert]
    by_cases hk : key N = i
    · rw [ite_eq_left hk, ite_eq_left hk, Finset.card_insert_of_notMem (by simp)]
    · rw [ite_eq_right hk, ite_eq_right hk]

theorem ncard_eq_hist (i : ℕ) (hi : i < 10) :
    {n | n < 2 ^ 23 ∧ innerKey innerTab n = i}.ncard = (innerHist innerTab)[i]! := by
  rw [innerHist, (fold_modify_spec (innerKey innerTab) 10 (2 ^ 23)).2 i hi]
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n
  simp

theorem ncard_innerKey (i : ℕ) (hi : i < 10) :
    {n | n < 2 ^ 23 ∧ innerKey innerTab n = i}.ncard =
      [4194304, 1783, 1783, 49896, 49896, 1995840, 2095104, 1, 1, 0].getD i 0 := by
  rw [ncard_eq_hist i hi, innerHist_eq]
  interval_cases i <;> rfl

theorem mem_centQ_iff
    {y : Sbp} :
    (y ∈ Qs ∧ y * qS 1 = qS 1 * y) ↔
      ∃ n < 2 ^ 23, qS n = y ∧ qmul gArr n 1 = qmul gArr 1 n := by
  constructor
  · rintro ⟨hy, hc⟩
    obtain ⟨n, hn, rfl⟩ := exists_qS hy
    refine ⟨n, hn, rfl, qS_injOn (qmul_lt _ _) (qmul_lt _ _) ?_⟩
    rw [← qS_mul, ← qS_mul, hc]
  · rintro ⟨n, -, rfl, hc⟩
    exact ⟨qS_mem n, by rw [qS_mul, qS_mul, hc]⟩

theorem centSet_eq_image
    (P : Sbp → Sbp → Prop) (p : ℕ → Prop)
    (hp : ∀ n < 2 ^ 23, qmul gArr n 1 = qmul gArr 1 n → (P (qS n) (qS (qmul gArr 1 n)) ↔ p n)) :
    {y | y ∈ Qs ∧ y * qS 1 = qS 1 * y ∧ P y (qS 1 * y)} =
      qS '' {n | n < 2 ^ 23 ∧ qmul gArr n 1 = qmul gArr 1 n ∧ p n} := by
  ext y
  constructor
  · rintro ⟨hy, hc, hP⟩
    obtain ⟨n, hn, rfl, hcn⟩ := mem_centQ_iff.1 ⟨hy, hc⟩
    rw [qS_mul] at hP
    exact ⟨n, ⟨hn, hcn, (hp n hn hcn).1 hP⟩, rfl⟩
  · rintro ⟨n, ⟨hn, hcn, hpn⟩, rfl⟩
    obtain ⟨hy, hc⟩ := mem_centQ_iff.2 ⟨n, hn, rfl, hcn⟩
    exact ⟨hy, hc, by rw [qS_mul]; exact (hp n hn hcn).2 hpn⟩

theorem ncard_image_qS
    {T : Set ℕ} (hT : ∀ n ∈ T, n < 2 ^ 23) : (qS '' T).ncard = T.ncard :=
  Set.InjOn.ncard_image (qS_injOn.mono fun n hn => hT n hn)

theorem ncard_centSet_key
    (P : Sbp → Sbp → Prop) {i : ℕ} (hi0 : i ≠ 0) (hi : i < 10)
    (hp : ∀ n < 2 ^ 23, qmul gArr n 1 = qmul gArr 1 n →
      (P (qS n) (qS (qmul gArr 1 n)) ↔ innerKey innerTab n = i)) :
    {y | y ∈ Qs ∧ y * qS 1 = qS 1 * y ∧ P y (qS 1 * y)}.ncard =
      [4194304, 1783, 1783, 49896, 49896, 1995840, 2095104, 1, 1, 0].getD i 0 := by
  rw [centSet_eq_image P _ hp, ncard_image_qS fun n hn => hn.1, ← ncard_innerKey i hi]
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hn, -, hk⟩
    exact ⟨hn, hk⟩
  · rintro ⟨hn, hk⟩
    refine ⟨hn, ?_, hk⟩
    by_contra hc
    exact hi0 (hk ▸ (innerKey_eq_zero_iff n).2 hc)

theorem sq_mul_of_comm {c y : Sbp} (hc : c * c = 1) (h : y * c = c * y) :
    c * y * (c * y) = y * y := by
  calc c * y * (c * y) = c * (y * c) * y := by group
    _ = c * (c * y) * y := by rw [h]
    _ = y * y := by rw [← mul_assoc, hc, one_mul]

theorem qS_one_mul_self :
    qS 1 * qS 1 = 1 := sq_qS_one (.inl rfl)

theorem xs_ne_one' : xs ≠ (1 : Sbp) := xs_ne_one

theorem pair_iff
    {n : ℕ} (hn : n < 2 ^ 23) (hcn : qmul gArr n 1 = qmul gArr 1 n) {a b : ℕ}
    (ha : a ≠ 1) (hb : b ≠ 1) :
    (qS n * qS n = 1 ∧ ((βr (qS n)) - 1).rank = a ∧ ((βr (qS (qmul gArr 1 n))) - 1).rank = b) ↔
      (innerTyRank (innerTy innerTab n) = a ∧
        innerTyRank (innerTy innerTab (qmul gArr 1 n)) = b) := by
  obtain ⟨-, h1, h2⟩ := innerRank_spec hn
  obtain ⟨-, h1', h2'⟩ := innerRank_spec (qmul_lt 1 n)
  have hc : qS n * qS 1 = qS 1 * qS n := by rw [qS_mul, qS_mul, hcn]
  have hsq : qS n * qS n = 1 → qS (qmul gArr 1 n) * qS (qmul gArr 1 n) = 1 := fun h => by
    rw [← qS_mul, sq_mul_of_comm qS_one_mul_self hc, h]
  constructor
  · rintro ⟨hsq1, hra, hrb⟩
    have hA : innerTyRank (innerTy innerTab n) ≠ 1 := fun h =>
      xs_ne_one' ((h1 h).symm.trans hsq1)
    have hB : innerTyRank (innerTy innerTab (qmul gArr 1 n)) ≠ 1 := fun h =>
      xs_ne_one' ((h1' h).symm.trans (hsq hsq1))
    exact ⟨(h2 hA).2.symm.trans hra, (h2' hB).2.symm.trans hrb⟩
  · rintro ⟨hA, hB⟩
    obtain ⟨hsq1, hra⟩ := h2 (hA ▸ ha)
    obtain ⟨-, hrb⟩ := h2' (hB ▸ hb)
    exact ⟨hsq1, hra.trans hA, hrb.trans hB⟩

theorem census_pair_q1
    {a b i : ℕ} (ha : a ≠ 1) (hb : b ≠ 1) (hi0 : i ≠ 0) (hi : i < 10)
    (hidx : ∀ a' b', innerPairIdx a' b' = i ↔ a' = a ∧ b' = b) :
    {y | y ∈ Qs ∧ y * qS 1 = qS 1 * y ∧
      (y * y = 1 ∧ ((βr y) - 1).rank = a ∧ ((βr (qS 1 * y)) - 1).rank = b)}.ncard =
      [4194304, 1783, 1783, 49896, 49896, 1995840, 2095104, 1, 1, 0].getD i 0 := by
  refine ncard_centSet_key (fun y z => y * y = 1 ∧ ((βr y) - 1).rank = a ∧
    ((βr z) - 1).rank = b) hi0 hi fun n hn hcn => ?_
  rw [pair_iff hn hcn ha hb, innerKey_of_comm hcn, hidx]

theorem census_q1 :
    {y | y ∈ Qs ∧ y * qS 1 = qS 1 * y}.ncard = 2 ^ 22 ∧
    (∀ y ∈ Qs, y * qS 1 = qS 1 * y → y * y = 1 → y ≠ 1 → y ≠ qS 1 →
      ((((βr y) - 1).rank = 2048 ∧ ((βr (qS 1 * y)) - 1).rank = 1860) ∨
        (((βr y) - 1).rank = 1860 ∧ ((βr (qS 1 * y)) - 1).rank = 2048) ∨
        (((βr y) - 1).rank = 2048 ∧ ((βr (qS 1 * y)) - 1).rank = 2168) ∨
        (((βr y) - 1).rank = 2168 ∧ ((βr (qS 1 * y)) - 1).rank = 2048) ∨
        (((βr y) - 1).rank = 2168 ∧ ((βr (qS 1 * y)) - 1).rank = 2168))) ∧
    {y | y ∈ Qs ∧ y * qS 1 = qS 1 * y ∧ (y * y = 1 ∧ ((βr y) - 1).rank = 2048 ∧
      ((βr (qS 1 * y)) - 1).rank = 1860)}.ncard = 1783 ∧
    {y | y ∈ Qs ∧ y * qS 1 = qS 1 * y ∧ (y * y = 1 ∧ ((βr y) - 1).rank = 1860 ∧
      ((βr (qS 1 * y)) - 1).rank = 2048)}.ncard = 1783 ∧
    {y | y ∈ Qs ∧ y * qS 1 = qS 1 * y ∧ (y * y = 1 ∧ ((βr y) - 1).rank = 2048 ∧
      ((βr (qS 1 * y)) - 1).rank = 2168)}.ncard = 49896 ∧
    {y | y ∈ Qs ∧ y * qS 1 = qS 1 * y ∧ (y * y = 1 ∧ ((βr y) - 1).rank = 2168 ∧
      ((βr (qS 1 * y)) - 1).rank = 2048)}.ncard = 49896 ∧
    {y | y ∈ Qs ∧ y * qS 1 = qS 1 * y ∧ (y * y = 1 ∧ ((βr y) - 1).rank = 2168 ∧
      ((βr (qS 1 * y)) - 1).rank = 2168)}.ncard = 1995840 ∧
    {y | y ∈ Qs ∧ y * qS 1 = qS 1 * y ∧ y * y ≠ 1}.ncard = 2095104 ∧
    (∀ y ∈ Qs, y * qS 1 = qS 1 * y → y * y ≠ 1 → y * y = xs) := by
  refine ⟨?_, ?_, census_pair_q1 (by decide) (by decide) (by decide) (by decide)
      fun _ _ => innerPairIdx_one,
    census_pair_q1 (by decide) (by decide) (by decide) (by decide) fun _ _ => innerPairIdx_two,
    census_pair_q1 (by decide) (by decide) (by decide) (by decide) fun _ _ => innerPairIdx_three,
    census_pair_q1 (by decide) (by decide) (by decide) (by decide) fun _ _ => innerPairIdx_four,
    census_pair_q1 (by decide) (by decide) (by decide) (by decide) fun _ _ => innerPairIdx_five,
    ?_, ?_⟩
  ·
    have e : {y | y ∈ Qs ∧ y * qS 1 = qS 1 * y} =
        qS '' {n | n < 2 ^ 23 ∧ qmul gArr n 1 = qmul gArr 1 n ∧ True} := by
      have := centSet_eq_image (fun _ _ => True) (fun _ => True) (fun _ _ _ => Iff.rfl)
      simpa using this
    rw [e, ncard_image_qS fun n hn => hn.1]
    have h0 := ncard_innerKey 0 (by norm_num)
    have hsplit : {n | n < 2 ^ 23 ∧ qmul gArr n 1 = qmul gArr 1 n ∧ True}.ncard +
        {n | n < 2 ^ 23 ∧ innerKey innerTab n = 0}.ncard = 2 ^ 23 := by
      have hu : {n | n < 2 ^ 23 ∧ qmul gArr n 1 = qmul gArr 1 n ∧ True} ∪
          {n | n < 2 ^ 23 ∧ innerKey innerTab n = 0} = Set.Iio (2 ^ 23) := by
        ext n
        simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_Iio, and_true, innerKey_eq_zero_iff]
        tauto
      have hd : Disjoint {n | n < 2 ^ 23 ∧ qmul gArr n 1 = qmul gArr 1 n ∧ True}
          {n | n < 2 ^ 23 ∧ innerKey innerTab n = 0} := by
        rw [Set.disjoint_left]
        rintro n ⟨-, hc, -⟩ ⟨-, hk⟩
        exact (innerKey_eq_zero_iff n).1 hk hc
      rw [← Set.ncard_union_eq hd ((Set.finite_Iio _).subset fun n hn => hn.1)
        ((Set.finite_Iio _).subset fun n hn => hn.1), hu, Set.ncard_Iio, Nat.card_Iio]
    have h0' : {n | n < 2 ^ 23 ∧ innerKey innerTab n = 0}.ncard = 4194304 := h0
    rw [h0'] at hsplit
    generalize {n | n < 2 ^ 23 ∧ qmul gArr n 1 = qmul gArr 1 n ∧ True}.ncard = A at hsplit ⊢
    norm_num at hsplit ⊢
    omega
  · intro y hy hc hsq h1 hq
    obtain ⟨n, hn, rfl, hcn⟩ := mem_centQ_iff.1 ⟨hy, hc⟩
    obtain ⟨hA0, hA1, hA2⟩ := innerRank_spec hn
    obtain ⟨hB0, hB1, hB2⟩ := innerRank_spec (qmul_lt 1 n)
    have hcq : qS n * qS 1 = qS 1 * qS n := by rw [qS_mul, qS_mul, hcn]
    have hA : innerTyRank (innerTy innerTab n) ≠ 1 := fun h => xs_ne_one' ((hA1 h).symm.trans hsq)
    have hsq' : qS (qmul gArr 1 n) * qS (qmul gArr 1 n) = 1 := by
      rw [← qS_mul, sq_mul_of_comm qS_one_mul_self hcq, hsq]
    have hB : innerTyRank (innerTy innerTab (qmul gArr 1 n)) ≠ 1 := fun h =>
      xs_ne_one' ((hB1 h).symm.trans hsq')
    have hn0 : n ≠ 0 := by rintro rfl; exact h1 qS_zero
    have hm0 : qmul gArr 1 n ≠ 0 := by
      intro h
      apply hq
      have e : qS 1 * qS n = 1 := by rw [qS_mul, h, qS_zero]
      calc qS n = qS 1 * (qS 1 * qS n) := by rw [← mul_assoc, qS_one_mul_self, one_mul]
        _ = qS 1 := by rw [e, mul_one]
    have h9 : innerKey innerTab n ≠ 9 := by
      intro h9
      have hpos : 0 < {n | n < 2 ^ 23 ∧ innerKey innerTab n = 9}.ncard :=
        Set.ncard_pos ((Set.finite_Iio _).subset fun n hn => hn.1) |>.2 ⟨n, hn, h9⟩
      rw [ncard_innerKey 9 (by norm_num)] at hpos
      exact absurd hpos (by decide)
    rw [innerKey_of_comm hcn] at h9
    rw [qS_mul, (hA2 hA).2, (hB2 hB).2]
    exact innerPairIdx_cases (fun h => hn0 (hA0.1 h)) hA (fun h => hm0 (hB0.1 h)) h9
  · refine ncard_centSet_key (i := 6) (fun y _ => y * y ≠ 1) (by decide) (by decide)
      fun n hn hcn => ?_
    rw [innerKey_of_comm hcn, innerPairIdx_eq_six_iff]
    obtain ⟨-, h1, h2⟩ := innerRank_spec hn
    constructor
    · intro hsq
      by_contra hne
      exact hsq (h2 hne).1
    · intro h hsq
      exact xs_ne_one' ((h1 h).symm.trans hsq)
  · intro y hy hc hsq
    obtain ⟨n, hn, rfl, -⟩ := mem_centQ_iff.1 ⟨hy, hc⟩
    obtain ⟨-, h1, h2⟩ := innerRank_spec hn
    by_cases h : innerTyRank (innerTy innerTab n) = 1
    · exact h1 h
    · exact absurd (h2 h).1 hsq

theorem conj_mul_conj (g a b : Sbp) : g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by
  group

theorem conj_injective (g : Sbp) : Function.Injective fun y : Sbp => g⁻¹ * y * g :=
  fun a b h => by simpa using h

theorem conj_mem_Qs_iff {g y : Sbp} (hg : g ∈ Jbar.op) : g⁻¹ * y * g ∈ Qs ↔ y ∈ Qs := by
  refine ⟨fun h => ?_, conj_mem_Qs hg⟩
  have h' := conj_mem_Qs (g := g⁻¹) (Jbar.op.inv_mem hg) h
  rwa [show g⁻¹⁻¹ * (g⁻¹ * y * g) * g⁻¹ = y by group] at h'

theorem rank_conj
    (g y : Sbp) : ((βr (g⁻¹ * y * g)) - 1).rank = ((βr y) - 1).rank :=
  rank_beta_conj (isConj_iff.2 ⟨g, by group⟩)

theorem conj_sq_eq_one_iff (g y : Sbp) : g⁻¹ * y * g * (g⁻¹ * y * g) = 1 ↔ y * y = 1 := by
  rw [conj_mul_conj]
  constructor
  · intro h
    calc y * y = g * (g⁻¹ * (y * y) * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  · intro h
    rw [h]
    group

theorem conj_comm_iff (g y c : Sbp) :
    g⁻¹ * y * g * (g⁻¹ * c * g) = g⁻¹ * c * g * (g⁻¹ * y * g) ↔ y * c = c * y := by
  rw [conj_mul_conj, conj_mul_conj]
  exact ⟨fun h => conj_injective g h, fun h => by rw [h]⟩

theorem centSet_conj {g : Sbp} (hg : g ∈ Jbar.op) (c : Sbp) (F : Sbp → Sbp → Prop)
    (hF : ∀ y z, F (g⁻¹ * y * g) (g⁻¹ * z * g) ↔ F y z) :
    {y | y ∈ Qs ∧ y * (g⁻¹ * c * g) = g⁻¹ * c * g * y ∧ F y (g⁻¹ * c * g * y)} =
      (fun y => g⁻¹ * y * g) '' {y | y ∈ Qs ∧ y * c = c * y ∧ F y (c * y)} := by
  ext z
  constructor
  · rintro ⟨hz, hc, hF'⟩
    have hz' : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [hz'] at hz hc hF'
    rw [conj_mul_conj] at hF'
    refine ⟨g * z * g⁻¹, ⟨(conj_mem_Qs_iff hg).1 hz, (conj_comm_iff g _ c).1 hc,
      (hF _ _).1 hF'⟩, hz'.symm⟩
  · rintro ⟨y, ⟨hy, hc, hF'⟩, rfl⟩
    refine ⟨(conj_mem_Qs_iff hg).2 hy, (conj_comm_iff g y c).2 hc, ?_⟩
    rw [conj_mul_conj]
    exact (hF _ _).2 hF'

theorem ncard_centSet_conj
    {g : Sbp} (hg : g ∈ Jbar.op) (c : Sbp) (F : Sbp → Sbp → Prop)
    (hF : ∀ y z, F (g⁻¹ * y * g) (g⁻¹ * z * g) ↔ F y z) :
    {y | y ∈ Qs ∧ y * (g⁻¹ * c * g) = g⁻¹ * c * g * y ∧ F y (g⁻¹ * c * g * y)}.ncard =
      {y | y ∈ Qs ∧ y * c = c * y ∧ F y (c * y)}.ncard := by
  rw [centSet_conj hg c F hF, Set.ncard_image_of_injective _ (conj_injective g)]

theorem pairF_conj
    (g : Sbp) (a b : ℕ) (y z : Sbp) :
    (g⁻¹ * y * g * (g⁻¹ * y * g) = 1 ∧ ((βr (g⁻¹ * y * g)) - 1).rank = a ∧
      ((βr (g⁻¹ * z * g)) - 1).rank = b) ↔
      (y * y = 1 ∧ ((βr y) - 1).rank = a ∧ ((βr z) - 1).rank = b) := by
  rw [conj_sq_eq_one_iff, rank_conj, rank_conj]

theorem mem_jClass_of_isConj_labelS
    {c : Sbp} (hc : c ∈ Qs) (hcl : IsConj c labelS) :
    c ∈ jClass (qS 1) := by
  have hl : IsConj labelS (qS 1) := isConj_of_mem_jClass labelS_mem_jClass
  have hq : IsConj c (rs 1) := by rw [rs1_eq]; exact hcl.trans hl
  have hsq : c * c = 1 := by
    obtain ⟨k, hk⟩ := isConj_iff.1 hq
    rw [rs1_eq] at hk
    calc c * c = k⁻¹ * (k * c * k⁻¹ * (k * c * k⁻¹)) * k := by group
      _ = 1 := by rw [hk, qS_one_mul_self]; group
  have hne : c ≠ 1 := by
    rintro rfl
    have := isConj_one_right.1 hq
    rw [rs1_eq] at this
    exact qS_ne_one (by decide) this
  have hmem : c ∈ {t | t ∈ Qs ∧ t * t = 1 ∧ t ≠ 1} := ⟨hc, hsq, hne⟩
  rw [invs_eq] at hmem
  have hr := rank_beta_conj hq
  obtain ⟨h1, h0, -, h3⟩ := rank_four
  rcases hmem with ((h | h) | h) | h
  · have := rank_beta_conj (isConj_of_mem_jClass h)
    omega
  · rwa [rs1_eq] at h
  · have := rank_beta_conj (isConj_of_mem_jClass h)
    rw [rank_rs (by norm_num : 2 < 14)] at this
    have e : Native.repRanks.getD 2 0 = 2048 := rfl
    omega
  · have := rank_beta_conj (isConj_of_mem_jClass h)
    omega

theorem image_centQ_labelS :
    (fun y : Sbp => (toShat y : Dfull)) '' {y | y ∈ Qs ∧ y * labelS = labelS * y} = N1 := by
  have key : ∀ y : Sbp, y * labelS = labelS * y ↔ iotaD y.unop * cQ = cQ * iotaD y.unop := by
    intro y
    rw [← iotaD_labelS, ← map_mul, ← map_mul, iotaD_injective.eq_iff]
    constructor
    · intro h
      have := congrArg MulOpposite.unop h
      rw [unop_mul, unop_mul] at this
      exact this.symm
    · intro h
      apply MulOpposite.unop_injective
      rw [unop_mul, unop_mul]
      exact h.symm
  ext d
  constructor
  · rintro ⟨y, ⟨hy, hc⟩, rfl⟩
    exact ⟨⟨y.unop, hy, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ((key y).1 hc)⟩
  · rintro ⟨⟨e, he, rfl⟩, hc⟩
    exact ⟨op e, ⟨he, (key (op e)).2 (Subgroup.mem_centralizer_singleton_iff.1 hc)⟩, rfl⟩

theorem native_inner_involution_census
    {c : Sbp} (hc : c ∈ Qs) (hcl : IsConj c labelS) :
    {y | y ∈ Qs ∧ y * c = c * y}.ncard = 2 ^ 22 ∧
    (∀ y ∈ Qs, y * c = c * y → y * y = 1 → y ≠ 1 → y ≠ c →
      ((((βr y) - 1).rank = 2048 ∧ ((βr (c * y)) - 1).rank = 1860) ∨
        (((βr y) - 1).rank = 1860 ∧ ((βr (c * y)) - 1).rank = 2048) ∨
        (((βr y) - 1).rank = 2048 ∧ ((βr (c * y)) - 1).rank = 2168) ∨
        (((βr y) - 1).rank = 2168 ∧ ((βr (c * y)) - 1).rank = 2048) ∨
        (((βr y) - 1).rank = 2168 ∧ ((βr (c * y)) - 1).rank = 2168))) ∧
    {y | y ∈ Qs ∧ y * c = c * y ∧ (y * y = 1 ∧ ((βr y) - 1).rank = 2048 ∧
      ((βr (c * y)) - 1).rank = 1860)}.ncard = 1783 ∧
    {y | y ∈ Qs ∧ y * c = c * y ∧ (y * y = 1 ∧ ((βr y) - 1).rank = 1860 ∧
      ((βr (c * y)) - 1).rank = 2048)}.ncard = 1783 ∧
    {y | y ∈ Qs ∧ y * c = c * y ∧ (y * y = 1 ∧ ((βr y) - 1).rank = 2048 ∧
      ((βr (c * y)) - 1).rank = 2168)}.ncard = 49896 ∧
    {y | y ∈ Qs ∧ y * c = c * y ∧ (y * y = 1 ∧ ((βr y) - 1).rank = 2168 ∧
      ((βr (c * y)) - 1).rank = 2048)}.ncard = 49896 ∧
    {y | y ∈ Qs ∧ y * c = c * y ∧ (y * y = 1 ∧ ((βr y) - 1).rank = 2168 ∧
      ((βr (c * y)) - 1).rank = 2168)}.ncard = 1995840 ∧
    {y | y ∈ Qs ∧ y * c = c * y ∧ y * y ≠ 1}.ncard = 2095104 ∧
    (∀ y ∈ Qs, y * c = c * y → y * y ≠ 1 → y * y = xs) ∧
    (fun y : Sbp => (toShat y : Dfull)) '' {y | y ∈ Qs ∧ y * labelS = labelS * y} = N1 := by
  obtain ⟨g, hg, rfl⟩ := mem_jClass_of_isConj_labelS hc hcl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := census_q1
  have hpair : ∀ a b, (∀ y z, (g⁻¹ * y * g * (g⁻¹ * y * g) = 1 ∧
      ((βr (g⁻¹ * y * g)) - 1).rank = a ∧ ((βr (g⁻¹ * z * g)) - 1).rank = b) ↔
      (y * y = 1 ∧ ((βr y) - 1).rank = a ∧ ((βr z) - 1).rank = b)) :=
    fun a b y z => pairF_conj g a b y z
  have hback : ∀ y, y ∈ Qs → y * (g⁻¹ * qS 1 * g) = g⁻¹ * qS 1 * g * y →
      (g * y * g⁻¹ ∈ Qs ∧ g * y * g⁻¹ * qS 1 = qS 1 * (g * y * g⁻¹)) ∧
      y = g⁻¹ * (g * y * g⁻¹) * g := by
    intro y hy hcy
    have hy' : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    refine ⟨⟨(conj_mem_Qs_iff hg).1 (hy' ▸ hy), ?_⟩, hy'⟩
    rw [hy'] at hcy
    exact (conj_comm_iff g _ _).1 hcy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, image_centQ_labelS⟩
  · have e := ncard_centSet_conj hg (qS 1) (fun _ _ => True) (fun _ _ => Iff.rfl)
    simp only [and_true] at e
    rw [e, h1]
  · intro y hy hcy hsq hne1 hnec
    obtain ⟨⟨hy', hcy'⟩, hyy⟩ := hback y hy hcy
    have hsq' : g * y * g⁻¹ * (g * y * g⁻¹) = 1 := by
      rw [hyy, conj_sq_eq_one_iff] at hsq
      exact hsq
    have hne1' : g * y * g⁻¹ ≠ 1 := fun h => hne1 (by rw [hyy, h]; group)
    have hnec' : g * y * g⁻¹ ≠ qS 1 := fun h => hnec (by rw [hyy, h])
    have hr := h2 _ hy' hcy' hsq' hne1' hnec'
    rw [hyy, conj_mul_conj, rank_conj, rank_conj]
    exact hr
  · exact (ncard_centSet_conj hg (qS 1) (fun y z => y * y = 1 ∧ ((βr y) - 1).rank = 2048 ∧
      ((βr z) - 1).rank = 1860) (hpair 2048 1860)).trans h3
  · exact (ncard_centSet_conj hg (qS 1) (fun y z => y * y = 1 ∧ ((βr y) - 1).rank = 1860 ∧
      ((βr z) - 1).rank = 2048) (hpair 1860 2048)).trans h4
  · exact (ncard_centSet_conj hg (qS 1) (fun y z => y * y = 1 ∧ ((βr y) - 1).rank = 2048 ∧
      ((βr z) - 1).rank = 2168) (hpair 2048 2168)).trans h5
  · exact (ncard_centSet_conj hg (qS 1) (fun y z => y * y = 1 ∧ ((βr y) - 1).rank = 2168 ∧
      ((βr z) - 1).rank = 2048) (hpair 2168 2048)).trans h6
  · exact (ncard_centSet_conj hg (qS 1) (fun y z => y * y = 1 ∧ ((βr y) - 1).rank = 2168 ∧
      ((βr z) - 1).rank = 2168) (hpair 2168 2168)).trans h7
  · have hF : ∀ y z : Sbp, (fun y (_ : Sbp) => y * y ≠ 1) (g⁻¹ * y * g) (g⁻¹ * z * g) ↔
        (fun y (_ : Sbp) => y * y ≠ 1) y z := fun y _ => not_congr (conj_sq_eq_one_iff g y)
    exact (ncard_centSet_conj hg (qS 1) (fun y _ => y * y ≠ 1) hF).trans h8
  · intro y hy hcy hsq
    obtain ⟨⟨hy', hcy'⟩, hyy⟩ := hback y hy hcy
    have hsq' : g * y * g⁻¹ * (g * y * g⁻¹) ≠ 1 := by
      rw [hyy, Ne, conj_sq_eq_one_iff] at hsq
      exact hsq
    rw [hyy, conj_mul_conj, h9 _ hy' hcy' hsq']
    exact conj_xs hg

end CFSG.Monster.B.CTIB
