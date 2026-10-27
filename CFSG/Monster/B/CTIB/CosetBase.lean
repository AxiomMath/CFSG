module

public import CFSG.Monster.B.CTIB.Action
public import Certificates.Data.CFSGNative.CTIB.Coset
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3098
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3027

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Bin Native

abbrev IsRank (k : ℕ) : Prop := k = 6 ∨ k = 8 ∨ k = 10

@[expose] noncomputable def cosetInv
    (k : ℕ) : Set Sbp :=
  {t | (∃ q ∈ Qs, t = hs k * q) ∧ t * t = 1}

@[expose] noncomputable def cosetElt
    (k n : ℕ) : Sbp := hs k * qS n

theorem qmul_lt (a b : ℕ) : qmul gArr a b < 2 ^ 23 := by
  rw [qmul]
  have h1 : (a ^^^ b) % 2 ^ 22 < 2 ^ 22 := Nat.mod_lt _ (by norm_num)
  split_ifs
  · rw [Nat.or_two_pow_eq_add_of_lt h1]; omega
  · rw [Nat.or_zero]; omega

theorem qS_eq_one_iff
    {n : ℕ} (hn : n < 2 ^ 23) : qS n = 1 ↔ n = 0 := by
  constructor
  · intro h
    rw [← qS_zero] at h
    exact qS_injOn hn (show (0 : ℕ) < 2 ^ 23 by norm_num) h
  · rintro rfl
    exact qS_zero

theorem hs_sq_code
    {k : ℕ} (hk : IsRank k) : hs k * hs k = qS (sqCode k) := by
  rw [← sq]
  rcases hk with rfl | rfl | rfl
  · rw [hs6_sq, sqCode, ite_eq_right (by decide), qS_two_pow_22]
  · rw [hs8_sq, sqCode, ite_eq_left rfl, qS_zero]
  · rw [hs10_sq, sqCode, ite_eq_right (by decide), qS_two_pow_22]

theorem liftImgsK_getD (k i : ℕ) : (liftImgsK k).toArray.getD i 0 = (liftImgsK k).getD i 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

theorem conj_hs_qS
    {k : ℕ} (hk : IsRank k) (n : ℕ) :
    (hs k)⁻¹ * qS n * hs k = qS (autApply gArr (liftImgsK k).toArray n) :=
  conj_qS (hs_mem_Jbar hk) (fun i hi => by rw [liftImgsK_getD]; exact conj_hs hk hi) n

theorem cosetElt_sq
    {k : ℕ} (hk : IsRank k) (n : ℕ) :
    cosetElt k n * cosetElt k n =
      qS (qmul gArr (sqCode k) (qmul gArr (autApply gArr (liftImgsK k).toArray n) n)) := by
  rw [← qS_mul, ← qS_mul, ← conj_hs_qS hk, ← hs_sq_code hk, cosetElt]
  group

theorem cosetElt_sq_eq_one_iff
    {k : ℕ} (hk : IsRank k) {n : ℕ} :
    cosetElt k n * cosetElt k n = 1 ↔
      isInv gArr (liftImgsK k).toArray (sqCode k) n = true := by
  rw [cosetElt_sq hk, qS_eq_one_iff (qmul_lt _ _), isInv, beq_iff_eq]

theorem bvec_qmul (a b : ℕ) : Code.bvec 22 (qmul gArr a b) = Code.bvec 22 a + Code.bvec 22 b := by
  funext i
  rw [Code.bvec_apply, Pi.add_apply, Code.bvec_apply, Code.bvec_apply, testBit_qmul_low a b i.2]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem bvec_autApplyN (A : Array ℕ) (n : ℕ) : ∀ m, Code.bvec 22 (autApplyN gArr A n m) =
    ∑ j ∈ Finset.range m, if n.testBit j then Code.bvec 22 (A.getD j 0) else 0
  | 0 => by
    rw [Finset.range_zero, Finset.sum_empty, show autApplyN gArr A n 0 =
      if n.testBit 22 then 2 ^ 22 else 0 from rfl]
    funext i
    have h0 : (if n.testBit 22 then 2 ^ 22 else 0 : ℕ).testBit i = false := by
      split_ifs
      · rw [Nat.testBit_two_pow]
        have : ¬ (22 = (i : ℕ)) := by omega
        simp [this]
      · exact Nat.zero_testBit _
    rw [Code.bvec_apply, Pi.zero_apply, h0]
    rfl
  | m + 1 => by
    rw [autApplyN_succ, Finset.sum_range_succ, ← bvec_autApplyN A n m]
    split_ifs
    · rw [bvec_qmul]
    · rw [add_zero]

theorem bvec_mod (n : ℕ) : Code.bvec 22 (n % 2 ^ 22) = Code.bvec 22 n := by
  funext i
  rw [Code.bvec_apply, Code.bvec_apply, Nat.testBit_mod_two_pow, decide_eq_true i.2, Bool.true_and]

theorem actGo_lt (rows : Array ℕ) (hr : ∀ i < 22, rows[i]! < 2 ^ 22) (v : ℕ) :
    ∀ m, m ≤ 22 → ∀ acc, acc < 2 ^ 22 → CFSG.Monster.VisCert.Native.actGo rows v m acc < 2 ^ 22
  | 0, _, _, h => h
  | m + 1, hm, acc, h => by
    rw [CFSG.Monster.VisCert.Native.actGo]
    refine actGo_lt rows hr v m (by omega) _ ?_
    split_ifs
    · exact Nat.xor_lt_two_pow h (hr m (by omega))
    · exact h

theorem isInvF_eq {k : ℕ} (hk : IsRank k) (n : ℕ) :
    isInvF gArr (liftImgsK k).toArray (liftRowsK k).toArray (sqCode k) n =
      isInv gArr (liftImgsK k).toArray (sqCode k) n := by
  rw [isInvF]
  by_cases h : isInv gArr (liftImgsK k).toArray (sqCode k) n = true
  · rw [h, Bool.and_true, beq_iff_eq]
    have hrows := lift_rows hk
    have hlt := lift_lt hk
    rw [isInv, beq_iff_eq] at h
    have hb := congrArg (Code.bvec 22) h
    rw [bvec_qmul, bvec_qmul, Code.bvec_zero] at hb
    have hw : Code.bvec 22 (sqCode k) = 0 := by
      rw [← bvec_mod, sqCode]
      split_ifs <;> simp [Code.bvec_zero]
    rw [hw, zero_add] at hb
    have ha : Code.bvec 22 (autApply gArr (liftImgsK k).toArray n) = Code.bvec 22 n := by
      have := congrArg (· + Code.bvec 22 n) hb
      simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] at this
      exact this
    apply Max2.bvec_injective22
    · exact actGo_lt _ hlt _ 22 le_rfl 0 (by norm_num)
    · exact Nat.mod_lt _ (by norm_num)
    · have hL : ∀ i < 22, Code.bvec 22 (liftRowsK k).toArray[i]! =
          Code.bvec 22 ((liftImgsK k).toArray.getD i 0) := by
        intro i _
        rw [toArray_getElem!, ← hrows, liftImgsK_getD,
          show (0 : ℕ) = 0 % 2 ^ 22 from rfl, List.getD_map, bvec_mod, Nat.zero_mod]
      rw [Max2.Native.act22, Max2.bvec_actGo, Code.bvec_zero, zero_add, bvec_mod, ← ha, autApply,
        bvec_autApplyN]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      rw [Nat.testBit_mod_two_pow, decide_eq_true hi', Bool.true_and, hL i hi']
  · rw [Bool.not_eq_true] at h
    rw [h, Bool.and_false]

theorem countBelow_eq (p : ℕ → Bool) :
    ∀ m acc, countBelow p m acc = acc + ((Finset.range m).filter fun i => p i = true).card
  | 0, acc => by simp [countBelow]
  | m + 1, acc => by
    rw [countBelow, countBelow_eq p m, Finset.range_add_one, Finset.filter_insert]
    have hm : m ∉ (Finset.range m).filter fun i => p i = true := by simp
    split_ifs with h
    · rw [Finset.card_insert_of_notMem hm]; omega
    · rfl

theorem cosetInv_eq
    {k : ℕ} (hk : IsRank k) :
    cosetInv k = cosetElt k '' {n | n < 2 ^ 23 ∧
      isInv gArr (liftImgsK k).toArray (sqCode k) n = true} := by
  ext t
  constructor
  · rintro ⟨⟨q, hq, rfl⟩, ht⟩
    obtain ⟨n, hn, rfl⟩ := exists_qS hq
    exact ⟨n, ⟨hn, (cosetElt_sq_eq_one_iff hk).1 ht⟩, rfl⟩
  · rintro ⟨n, ⟨-, hn⟩, rfl⟩
    exact ⟨⟨qS n, qS_mem n, rfl⟩, (cosetElt_sq_eq_one_iff hk).2 hn⟩

theorem cosetElt_injOn
    (k : ℕ) : Set.InjOn (cosetElt k) (Set.Iio (2 ^ 23)) := by
  intro n hn m hm h
  exact qS_injOn hn hm (mul_left_cancel h)

theorem ncard_cosetInv
    {k : ℕ} (hk : IsRank k) :
    (cosetInv k).ncard =
      countInv gArr (liftImgsK k).toArray (liftRowsK k).toArray (sqCode k) := by
  rw [cosetInv_eq hk, Set.InjOn.ncard_image ((cosetElt_injOn k).mono fun n hn => hn.1), countInv,
    countBelow_eq, zero_add]
  have : {n | n < 2 ^ 23 ∧ isInv gArr (liftImgsK k).toArray (sqCode k) n = true} =
      ↑((Finset.range (2 ^ 23)).filter fun i =>
        isInvF gArr (liftImgsK k).toArray (liftRowsK k).toArray (sqCode k) i = true) := by
    ext n
    simp [isInvF_eq hk]
  rw [this, Set.ncard_coe_finset]

end CFSG.Monster.B.CTIB
