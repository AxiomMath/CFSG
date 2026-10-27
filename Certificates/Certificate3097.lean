module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.FendelDataInputs
import Certificates.Kernel.LocalComp.FendelRest

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.SympSix CFSG.Sporadic.Schreier.Co3 CFSG.Monster.B.Co2.Native
    CFSG.Sporadic.Schreier.Co3.Native CFSG.GH74.M12.Hyp in
theorem certificate3097 : (∀ x : Fin 128 × Fin 4 × Fin 2, fendelWitOK x.1 x.2.1 x.2.2 = true)
    ∧ ((co3TLevels[0]!).pts.size = 128 ∧ (co3TLevels[1]!).pts.size = 4 ∧
       (co3TLevels[2]!).pts.size = 2)
    ∧ (∀ x ∈ fendelMElts, isInvA 276 x (invCand 276 x) = true ∧
       siftA 276 co3MLevels co3MBaseArr 0 x = true)
    ∧ (eqA 276 (compA 276 fendelAArr fendelAArr) (idA 276) = true ∧
       eqA 276 fendelAArr (idA 276) = false ∧ eqA 276 co3TtArr co3ZArr = false)
    ∧ (eqA 276 (compA 276 fendelCArr co3TtArr) (compA 276 (compA 276 co3ZArr co3TtArr) fendelCArr)
       = true)
    ∧ (commutesA 276 fendelKArr co3TtArr = true ∧
       eqA 276 (compA 276 fendelKArr fendelKArr) co3ZArr = true)
    ∧ (fendelKTbl co3ZArr = JT)
    ∧ (commutesA 276 fendelYArr co3TtArr = true ∧
       eqA 276 (compA 276 fendelYHArr fendelYArr) (compA 276 fendelAArr fendelYHArr) = true ∧
       fendelKTbl fendelYArr ∈ QT ∧ fendelKTbl fendelYArr ≠ JT)
    ∧ (commutesA 276 fendelY'Arr co3TtArr = true ∧
       eqA 276 (compA 276 fendelY'HArr fendelY'Arr) (compA 276 fendelAArr fendelY'HArr) = true ∧
       eqA 276 (compA 276 fendelY'ZHArr (compA 276 co3ZArr fendelY'Arr))
         (compA 276 fendelAArr fendelY'ZHArr) = true)
    ∧ (∀ i < 4, commutesA 276 (fendelGArr i) co3TtArr = true ∧
       eqA 276 (compA 276 (fendelGHArr i) (fendelGArr i)) (compA 276 fendelAArr (fendelGHArr i))
         = true)
    ∧ (fendelGWords.map fendelGWordTbl = gensT ∧
       ∀ u ∈ fendelGWords, ∀ i ∈ u, 1 ≤ i ∧ i ≤ 4)
    ∧ (commutesA 276 fendelK2Arr co3TtArr = true ∧
       eqA 276 (compA 276 (compA 276 (compA 276 (fendelGArr 0) fendelK2Arr)
         (invCand 276 (fendelGArr 0))) (invCand 276 fendelK2Arr)) co3ZArr = true)
    ∧ (∀ t ∈ BT, (∀ u ∈ BT, tmul t u = tmul u t) → t = tid ∨ t = JT) := KernelLC.Fendel.facts

end Certificates
