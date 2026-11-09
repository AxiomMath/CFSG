module

public import Certificates.Data.Kernel.GammaUList
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.IdxChunks

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

open Certificates.Kernel.GammaUList CFSG.GammaU.Native

@[expose] noncomputable def gHead (i : Nat) : Bool :=
  ((resConj i).map Array.toList).all (fun c => invOK c (invL c)) &&
    (compOfL i).all (fun x => x.length == 12)

#kc_each gHead 0 2

@[expose] noncomputable def gPc0 (j : Nat) : Bool :=
  nlOKAtL (spanList d0) (compOfL 0)
    (((((resConj 0).map Array.toList).map fun c => (c, invL c)).drop (j * 10)).take 10)

#kc_each gPc0 0 5

@[expose] noncomputable def gPc1 (j : Nat) : Bool :=
  nlOKAtL (spanList d0) (compOfL 1)
    (((((resConj 1).map Array.toList).map fun c => (c, invL c)).drop (j * 10)).take 10)

#kc_each gPc1 0 3

theorem gPart0 : (((resConj 0).map Array.toList).all (fun c => invOK c (invL c)) &&
    (compOfL 0).all (fun x => x.length == 12) &&
      nlOKAtL (spanList d0) (compOfL 0) (((resConj 0).map Array.toList).map fun c => (c, invL c))) =
    true := by
  rw [Bool.and_eq_true]
  refine ⟨gHead0, ?_⟩
  unfold nlOKAtL
  refine CFSG.KC.IdxChunks.all_chunks_of _ 10 5 _ (by decide +kernel) fun j hj => ?_
  match j, hj with
  | 0, _ => exact gPc00
  | 1, _ => exact gPc01
  | 2, _ => exact gPc02
  | 3, _ => exact gPc03
  | 4, _ => exact gPc04
  | k + 5, h => exact absurd h (by omega)

theorem gPart1 : (((resConj 1).map Array.toList).all (fun c => invOK c (invL c)) &&
    (compOfL 1).all (fun x => x.length == 12) &&
      nlOKAtL (spanList d0) (compOfL 1) (((resConj 1).map Array.toList).map fun c => (c, invL c))) =
    true := by
  rw [Bool.and_eq_true]
  refine ⟨gHead1, ?_⟩
  unfold nlOKAtL
  refine CFSG.KC.IdxChunks.all_chunks_of _ 10 3 _ (by decide +kernel) fun j hj => ?_
  match j, hj with
  | 0, _ => exact gPc10
  | 1, _ => exact gPc11
  | 2, _ => exact gPc12
  | k + 3, h => exact absurd h (by omega)

theorem resConjCheckL_eq : Certificates.Kernel.GammaUList.resConjCheckL = true := by
  unfold resConjCheckL
  rw [List.all_eq_true]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact gPart0
  · exact gPart1

end CertificateChecks.KernelCensus
