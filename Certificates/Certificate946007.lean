module

public import Certificates.Data.ParrottSpinA
import Certificates.Data.ParrottSpin
import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelInputs
import CFSG.GH74.KGroups.Generic

public section

namespace Certificates

open CFSG.RankThree.GF2n.Parrott
open CFSG.ComponentClassification.CatFactsSmall.PSp43

structure SpinAFacts : Prop where
  f_sq : f45 * f45 = 1
  f_not_mem_Q : ¬ (QP45.sift f45 0 = true)
  f_conj_x : CFSG.Certificates.schreierPermEq (f45 * x45 * f45)
    (CFSG.GH74.KGroups.evalW x45 y45 conjWordX) = true
  f_conj_y : CFSG.Certificates.schreierPermEq (f45 * y45 * f45)
    (CFSG.GH74.KGroups.evalW x45 y45 conjWordY) = true
  f_conj_x_sift : QP45.sift (f45 * x45 * f45) 0 = true
  f_conj_y_sift : QP45.sift (f45 * y45 * f45) 0 = true
  Mf_sq : ∀ e : Fin 8, bitSq Mf (1 <<< (e : Nat)) = 1 <<< (e : Nat)
  Mf_conj_Mx : ∀ e : Fin 8, bitConj Mf Mx (1 <<< (e : Nat)) =
    bitWord (toSpinWord conjWordX) (1 <<< (e : Nat))
  Mf_conj_My : ∀ e : Fin 8, bitConj Mf My (1 <<< (e : Nat)) =
    bitWord (toSpinWord conjWordY) (1 <<< (e : Nat))

end Certificates

public section

namespace Certificates

open Certificates

open CFSG.RankThree.GF2n.Parrott

set_option maxHeartbeats 0 in
open CFSG.RankThree.GF2n.Parrott in
open CFSG.ComponentClassification.CatFactsSmall.PSp43 in
theorem certificate946007 : SpinAFacts := {
    f_sq := by decide +kernel
    f_not_mem_Q := by decide +kernel
    f_conj_x := by decide +kernel
    f_conj_y := by decide +kernel
    f_conj_x_sift := by decide +kernel
    f_conj_y_sift := by decide +kernel
    Mf_sq := by decide +kernel
    Mf_conj_Mx := by decide +kernel
    Mf_conj_My := by decide +kernel }

end Certificates
