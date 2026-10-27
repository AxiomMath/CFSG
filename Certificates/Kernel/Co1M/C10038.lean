module

public import CFSG.Monster.GMS.S365Root
public import CFSG.Monster.GMS.S365CosetSpec
public import CFSG.Monster.GMS.S365USpec
public import Certificates.Data.CFSGNative.Co1.S365CentRoot
public import CFSG.Monster.GMS.S365CentRootSpecInputs
public import Certificates.Kernel.Co1M.C10041
public import Certificates.Kernel.Co1M.Data10038
public import CFSG.Sporadic.Co1.Module.InvSpec
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Certificate10042Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1F2 CFSG.KC.Co1M CFSG.KC.VecK CFSG.KD.Co1M CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.Co1.S365Native
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.S365UNative CFSG.Sporadic.Co1.S365CentNative
  CFSG.Monster.GMS.S365

@[expose] noncomputable def rootPK (x : Nat) : Bool :=
  orthAllN rootGs x && (if x = 0 then 0 else if parity24N (vecMulN 24 qRows x &&& x) then 2
    else if orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 x then 3 else 1) == 3

theorem rootP_eq (x : Nat) :
    rootP qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 rootGs x =
      rootPK x := by
  have e : inPtsN (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 x =
      orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 x :=
    cm_orb_inPts x
  rw [rootP, tyLabN, e, rootPK]

theorem tl_rootP : TL.all rootPK = true := by quickRfl

theorem tl_lt : TL.all (fun x => decide (x < 16777216)) = true := by decide +kernel

theorem tl_nodup : TL.Nodup := by decide +kernel

theorem tl_len : TL.length = 120 := by decide +kernel

theorem mem_TL {x : Nat}
    (hx : rootP qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 rootGs x =
      true) : x ∈ TL := by
  unfold rootP at hx
  rw [Bool.and_eq_true, beq_iff_eq] at hx
  obtain ⟨hor, hty⟩ := hx
  have hin : inPtsN (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 x = true := by
    unfold tyLabN at hty
    split_ifs at hty with h1 h2 h3 <;> first | exact h3 | omega
  unfold inPtsN at hin
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hin
  obtain ⟨hi, hpx⟩ := hin
  have e : (orbitOf 2 98280).pts[((posTable 24 (orbitOf 2 98280).pts)[x]!).toNat]! =
      lk CertificateChecks.KernelVec.Co1.Pt 32 ((posTable 24 (orbitOf 2 98280).pts)[x]!).toNat :=
    cm_orb_twin.2.1 _ hi
  have hlx : lk CertificateChecks.KernelVec.Co1.Pt 32
      ((posTable 24 (orbitOf 2 98280).pts)[x]!).toNat = x := e.symm.trans hpx
  have hc := cov44All _ hi
  unfold covF44 at hc
  rw [hlx] at hc
  have ho : orthAll rootGs x = true := hor
  rw [ho, Bool.not_true, Bool.false_or, List.contains_iff_mem] at hc
  exact hc

theorem filter_rootP :
    ((Finset.range 16777216).filter fun i => rootP qRows (orbitOf 2 98280).pts
      (posTable 24 (orbitOf 2 98280).pts) 98280 rootGs i = true) = TL.toFinset := by
  ext x
  rw [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
  constructor
  · rintro ⟨-, hx⟩
    exact mem_TL hx
  · intro hx
    refine ⟨?_, ?_⟩
    · have h := List.all_eq_true.1 tl_lt x hx
      exact of_decide_eq_true h
    · rw [rootP_eq]
      exact List.all_eq_true.1 tl_rootP x hx

theorem imBasis_eq : imBasis (unpackR 24 (trK 24 SA)) = List.zip IBA IBB := by decide +kernel

theorem tl_pre : TL.all (hasPreN (List.zip IBA IBB) (unpackR 24 (trK 24 SA))) = true := by
  quickRfl

theorem countBelow_zero (p : Nat → Bool) (n : Nat) :
    countBelow p n 0 = ((Finset.range n).filter fun i => p i = true).card := by
  rw [countBelow_eq, Nat.zero_add]

theorem count1 : countBelow (rootP qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts)
    98280 rootGs) 16777216 0 = 120 := by
  refine (countBelow_zero _ _).trans ?_
  exact (congrArg Finset.card filter_rootP).trans
    ((List.toFinset_card_of_nodup tl_nodup).trans tl_len)

theorem pre_of_rootP {x : Nat}
    (h1 : rootP qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 rootGs x =
      true) : hasPreN (imBasis (unpackR 24 (trK 24 SA))) (unpackR 24 (trK 24 SA)) x = true := by
  rw [imBasis_eq]
  exact List.all_eq_true.1 tl_pre x (mem_TL h1)

theorem count2 : countBelow (fun x => rootP qRows (orbitOf 2 98280).pts
    (posTable 24 (orbitOf 2 98280).pts) 98280 rootGs x &&
      !hasPreN (imBasis (unpackR 24 (trK 24 SA))) (unpackR 24 (trK 24 SA)) x) 16777216 0 = 0 := by
  refine (countBelow_zero _ _).trans ?_
  refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun x _ h => ?_)
  have h' := Eq.mp (Bool.and_eq_true _ _) h
  have hp := pre_of_rootP h'.1
  have h2 := h'.2
  rw [hp] at h2
  exact Bool.noConfusion h2

theorem rcount {Mt : Array Nat} (hMt : Mt = unpackR 24 (trK 24 SA)) :
    rootCountNB (imBasis Mt) qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280
      rootGs Mt 120 = true := by
  subst hMt
  exact Eq.mpr (Bool.and_eq_true _ _) ⟨beq_iff_eq.2 count1, beq_iff_eq.2 count2⟩

theorem c10038_count : rootCount120 = true := by
  unfold rootCount120 rootCountN
  exact rcount (Mt := transposeRows 24 rowsSA) (by rw [rowsSA_eq, trU41])

theorem c10038_fix : rootFixOK = true := by
  unfold rootFixOK
  rw [rowsSA_eq]
  quickRfl

theorem c10038_neg :
    (!rootPK (lk CertificateChecks.KernelVec.Co1.Pt 32 0) && !rootPK 24) = true := by
  quickRfl

open Certificates in
open CFSG.Monster.GMS.S365 in
theorem c10038 :
    (rootCount120 = true)
    ∧ (rootFixOK = true) := ⟨c10038_count, c10038_fix⟩

end CertificateChecks.KernelCo1M

end
