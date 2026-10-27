module

public import CFSG.Sporadic.J4.QTOutCommNative
import Certificates.Kernel.J4Q.C4021
public import CFSG.Sporadic.J4.QTOutObsNative
public import CFSG.Sporadic.J4.QTRankWitNative

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
open CFSG.Sporadic.J4.Native in
theorem certificate4021 : (kEdges.length = 6)
    ∧ ((∀ c ∈ kCols, c.1 < 6 ∧ c.2 < 112) ∧ (∀ c ∈ fCols, c.1 < 2 ∧ c.2 < 112))
    ∧ (∀ e ∈ kEdges, e.1 < 111)
    ∧ (eqRows (mulRows pInv CFSG.Sporadic.J4.QT.pRows) idRows = true ∧
          eqRows (mulRows CFSG.Sporadic.J4.QT.pRows pInv) idRows = true)
    ∧ (eqRows (mulRows bkRows (phiOf edgeMats kCols)) (psiRows 4) = true ∧
          eqRows (mulRows (invRows bkRows) bkRows) idRows = true)
    ∧ (eqRows (mulRows bfRows (phiOf mgps fCols)) (psiRows 2) = true ∧
          eqRows (mulRows (invRows bfRows) bfRows) idRows = true)
    ∧ (∀ e < 6, (frApply (frTable (edgeMat e)) v0Vec).beq V2.zero = true)
    ∧ (∀ g < 2, (frApply (frTable (rg g)) v0Vec).beq
          ((frApply (frTable (mg g)) v1Vec).xor v1Vec) = true)
    ∧ (∀ i < 4, ∀ g < 2,
          (frApply (frTable (mgp g)) (u1s[i]!)).beq (frApply (frTable (rg g)) (bkRows[i]!)) = true)
    ∧ (∀ b0 b1 b2 b3 d0 d1 : Bool,
          eqRows (tcomb b0 b1 b2 b3 d0 d1) idRows = true ∨
            (wfRows (powBin (mulRows (jword (witWords.getD (combIdx b0 b1 b2 b3 d0 d1) []))
              (tcomb b0 b1 b2 b3 d0 d1)) 86775571046077562880) = true ∧
            eqRows (powBin (mulRows (jword (witWords.getD (combIdx b0 b1 b2 b3 d0 d1) []))
              (tcomb b0 b1 b2 b3 d0 d1)) 86775571046077562880) idRows = false))
    ∧ (eqRows (mulRows (mulRows yRows (wordRowsOf mWord0)) yRows)
            (mulRows (etaR mConjC0) (wordRowsOf mConjW0)) = true ∧
          eqRows (mulRows (mulRows yRows (wordRowsOf mWord1)) yRows)
            (mulRows (etaR mConjC1) (wordRowsOf mConjW1)) = true)
    ∧ ((∀ ℓ ∈ mWord0, ℓ ∈ CFSG.Sporadic.J4.QT.letters) ∧ (∀ ℓ ∈ mWord1, ℓ ∈ CFSG.Sporadic.J4.QT.letters) ∧
          (∀ ℓ ∈ mConjW0, ℓ ∈ CFSG.Sporadic.J4.QT.letters) ∧ (∀ ℓ ∈ mConjW1, ℓ ∈ CFSG.Sporadic.J4.QT.letters) ∧ mConjC0 < 2 ^ 11 ∧
          mConjC1 < 2 ^ 11)
    ∧ (((List.range 2048).any fun c => actT (wordT wObs) c != c) = true) := KernelJ4Q.c4021

end Certificates
