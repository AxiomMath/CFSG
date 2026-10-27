module

public import CFSG.Sporadic.Co1Block.ClassesCheckInputs
public meta import CFSG.Sporadic.Co1Block.XFix
public meta import CFSG.Sporadic.Co1Block.Iota
public meta import CFSG.Sporadic.Co1Block.IotaData
public meta import CFSG.Sporadic.Co1Block.PermData
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import Certificates.Kernel.Co1B.Fix2041
public import CFSG.Certificates.Kernel.Co1BTrSound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1B

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KD.Co1B CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Enum
  CertificateChecks.KernelCo1Cover

@[expose] def cntN (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => if p n = true then cntN p n + 1 else cntN p n

theorem countBelow_cnt (p : Nat → Bool) : ∀ n acc,
    CFSG.Sporadic.Co1.InvNative.countBelow p n acc = acc + cntN p n
  | 0, acc => by simp [CFSG.Sporadic.Co1.InvNative.countBelow, cntN]
  | n + 1, acc => by
    simp only [CFSG.Sporadic.Co1.InvNative.countBelow, cntN]
    rw [countBelow_cnt p n]
    by_cases h : p n = true
    · simp only [h, ↓reduceIte]
      omega
    · simp [h]

theorem cntN_add (p : Nat → Bool) (a : Nat) : ∀ b,
    cntN p (a + b) = cntN p a + cntN (fun k => p (a + k)) b
  | 0 => rfl
  | b + 1 => by
    rw [← Nat.add_assoc]
    simp only [cntN]
    rw [cntN_add p a b]
    by_cases h : p (a + b) = true
    · simp only [h, ↓reduceIte]
      omega
    · simp [h]

@[expose] def bsum (p : Nat → Bool) (n : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => cntN (fun k => p (n * m + k)) n + bsum p n m

theorem cntN_blocks (p : Nat → Bool) (n : Nat) : ∀ m, cntN p (n * m) = bsum p n m
  | 0 => by simp [cntN, bsum]
  | m + 1 => by
    rw [Nat.mul_succ, cntN_add, cntN_blocks p n m, bsum, Nat.add_comm]

theorem cntN_congr {p q : Nat → Bool} : ∀ n, (∀ i < n, p i = q i) → cntN p n = cntN q n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [cntN]
    rw [cntN_congr n fun i hi => h i (by omega), h n (by omega)]

theorem fixChunk_eq (T P : Nat) : fixChunkK T P = cntN (fun k =>
    Nat.beq (vmF 24 T (pg 24 (CFSG.KS.mask 24) P k)) (pg 24 (CFSG.KS.mask 24) P k)) 840 := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) 0 (fun k acc => (fun v => Bool.rec
      (motive := fun _ => Nat) acc (Nat.succ acc) (Nat.beq (vmF 24 T v) v))
      (pg 24 (CFSG.KS.mask 24) P k)) n : Nat) = cntN (fun k =>
      Nat.beq (vmF 24 T (pg 24 (CFSG.KS.mask 24) P k)) (pg 24 (CFSG.KS.mask 24) P k)) n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [cntN]
      rw [← ih]
      by_cases h : Nat.beq (vmF 24 T (pg 24 (CFSG.KS.mask 24) P n)) (pg 24 (CFSG.KS.mask 24) P n) = true
      · simp only [h, ↓reduceIte]
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
  unfold fixChunkK
  exact key 840

theorem fixTab_eq (T : Nat) (F : Nat → Nat) : ∀ m,
    fixTabK T F m = Nat.rec (motive := fun _ => Nat) 0 (fun j acc => fixChunkK T (F j) + acc) m
  | 0 => rfl
  | m + 1 => by
    change fixChunkK T (F m) + fixTabK T F m = _
    rw [fixTab_eq T F m]

theorem certVecs_get {j k : Nat} (hj : j < 117) (hk : k < 840) :
    CFSG.Sporadic.Co1Block.certVecs[840 * j + k]! = pg 24 (CFSG.KS.mask 24) (CV.F j) k := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound CV.all j hj
  rw [← CV.eq] at h
  have e1 : CFSG.Sporadic.Co1Block.certVecs[840 * j + k]! =
      (CFSG.Monster.B.Co2.Native.hexTable 6 840 (840 * j) CFSG.Sporadic.Co1Block.certVecHex)[k]! := by
    unfold CFSG.Sporadic.Co1Block.certVecs
    rw [getElem!_pos _ _ (by simp [CFSG.Monster.B.Co2.Native.hexTable]; omega),
      getElem!_pos _ _ (by simp [CFSG.Monster.B.Co2.Native.hexTable]; omega)]
    simp only [CFSG.Monster.B.Co2.Native.hexTable, Array.getElem_ofFn, Nat.zero_add]
  rw [e1, h, getElem!_pos _ _ (by simp [CFSG.KS.Raw.unpack]; omega)]
  simp [CFSG.KS.Raw.unpack]

theorem beq_nat (a b : Nat) : (a == b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff]
  simp [Nat.beq_eq]

theorem xFix_eq {M T : Nat} (hT : trK 24 M = T) :
    CFSG.Sporadic.Co1Block.xFixCount CFSG.Sporadic.Co1Block.certVecs (unpackR 24 M) =
      fixTabK T CV.F 117 := by
  rw [CFSG.Sporadic.Co1Block.xFixCount, countBelow_cnt, Nat.zero_add]
  have h98 : (98280 : Nat) = 840 * 117 := rfl
  rw [h98, cntN_blocks, fixTab_eq]
  have key : ∀ m ≤ 117, bsum (fun i => CFSG.Sporadic.Co1Schreier.Native.act (unpackR 24 M)
      CFSG.Sporadic.Co1Block.certVecs[i]! == CFSG.Sporadic.Co1Block.certVecs[i]!) 840 m =
      Nat.rec (motive := fun _ => Nat) 0 (fun j acc => fixChunkK T (CV.F j) + acc) m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [bsum, ih (by omega)]
      change _ = fixChunkK T (CV.F m) + _
      rw [fixChunk_eq]
      congr 1
      refine cntN_congr 840 fun k hk => ?_
      rw [certVecs_get (by omega) hk, CFSG.KC.F2W.act_unpackR hT, beq_nat]
  exact key 117 le_rfl

theorem sq_eq {X : Nat} (h : Nat.beq (mulWK X X) oneK = true) :
    (CFSG.Sporadic.Co1Schreier.Native.mul (unpackR 24 X) (unpackR 24 X) ==
      CFSG.Sporadic.Co1Schreier.Native.one) = true := by
  rw [CFSG.KC.F2W.mul_unpackW, ← one_eq]
  change (unpackR 24 (mulWK X X) == unpackR 24 oneK) = true
  rw [Nat.eq_of_beq_eq_true h, beq_self_eq_true]

open Certificates in
open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier.Native in
open CFSG.Sporadic.Co1.InvNative in
theorem c2041 : classCheckOf certVecs iotaARows iotaCRows aR = true := by
  have hs := sq_chk
  have hn := ne_chk
  simp only [andB_eq_and, Bool.and_eq_true] at hs hn
  unfold CFSG.Sporadic.Co1Block.classCheckOf
  rw [iotaA_eq, iotaC_eq, aR_eq, xFix_eq (Nat.eq_of_beq_eq_true trA_chk),
    xFix_eq (Nat.eq_of_beq_eq_true trC_chk), xFix_eq (Nat.eq_of_beq_eq_true tr1_chk),
    Nat.eq_of_beq_eq_true fixA_chk, Nat.eq_of_beq_eq_true fixC_chk, Nat.eq_of_beq_eq_true fix1_chk]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sq_eq hs.1, sq_eq hs.2.1, sq_eq hs.2.2, validRows_unpackR, validRows_unpackR, validRows_unpackR,
    ← one_eq, hn.1, hn.2.1, hn.2.2]
  rfl

end CertificateChecks.KernelCo1B

end
