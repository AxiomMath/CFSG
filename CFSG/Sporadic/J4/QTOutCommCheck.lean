module

public import CFSG.Sporadic.J4.QTOutCommNative
public meta import CFSG.Sporadic.J4.QTOutCommNative
public import Certificates.Certificate4021
public meta import CFSG.Sporadic.J4.QTOutObsNative
public meta import CFSG.Sporadic.J4.QTRankWitNative

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4.Native

theorem comm_kEdges_length : kEdges.length = 6 :=
  Certificates.certificate4021.1

theorem comm_cols :
    (∀ c ∈ kCols, c.1 < 6 ∧ c.2 < 112) ∧ (∀ c ∈ fCols, c.1 < 2 ∧ c.2 < 112) :=
  Certificates.certificate4021.2.1

theorem comm_edges_lt : ∀ e ∈ kEdges, e.1 < 111 :=
  Certificates.certificate4021.2.2.1

theorem comm_pinv : eqRows (mulRows pInv pRows) idRows = true ∧
    eqRows (mulRows pRows pInv) idRows = true :=
  Certificates.certificate4021.2.2.2.1

theorem comm_K :
    eqRows (mulRows bkRows (phiOf edgeMats kCols)) (psiRows 4) = true ∧
    eqRows (mulRows (invRows bkRows) bkRows) idRows = true :=
  Certificates.certificate4021.2.2.2.2.1

theorem comm_F :
    eqRows (mulRows bfRows (phiOf mgps fCols)) (psiRows 2) = true ∧
    eqRows (mulRows (invRows bfRows) bfRows) idRows = true :=
  Certificates.certificate4021.2.2.2.2.2.1

theorem comm_rel :
    ∀ e < 6, (frApply (frTable (edgeMat e)) v0Vec).beq V2.zero = true :=
  Certificates.certificate4021.2.2.2.2.2.2.1

theorem comm_rg : ∀ g < 2, (frApply (frTable (rg g)) v0Vec).beq
    ((frApply (frTable (mg g)) v1Vec).xor v1Vec) = true :=
  Certificates.certificate4021.2.2.2.2.2.2.2.1

theorem comm_u1 : ∀ i < 4, ∀ g < 2,
    (frApply (frTable (mgp g)) (u1s[i]!)).beq (frApply (frTable (rg g)) (bkRows[i]!)) = true :=
  Certificates.certificate4021.2.2.2.2.2.2.2.2.1

theorem comm_excl : ∀ b0 b1 b2 b3 d0 d1 : Bool,
    eqRows (tcomb b0 b1 b2 b3 d0 d1) idRows = true ∨
      (wfRows (powBin (mulRows (jword (witWords.getD (combIdx b0 b1 b2 b3 d0 d1) []))
        (tcomb b0 b1 b2 b3 d0 d1)) 86775571046077562880) = true ∧
      eqRows (powBin (mulRows (jword (witWords.getD (combIdx b0 b1 b2 b3 d0 d1) []))
        (tcomb b0 b1 b2 b3 d0 d1)) 86775571046077562880) idRows = false) :=
  Certificates.certificate4021.2.2.2.2.2.2.2.2.2.1

theorem comm_conj :
    eqRows (mulRows (mulRows yRows (wordRowsOf mWord0)) yRows)
      (mulRows (etaR mConjC0) (wordRowsOf mConjW0)) = true ∧
    eqRows (mulRows (mulRows yRows (wordRowsOf mWord1)) yRows)
      (mulRows (etaR mConjC1) (wordRowsOf mConjW1)) = true :=
  Certificates.certificate4021.2.2.2.2.2.2.2.2.2.2.1

theorem comm_conj_data :
    (∀ ℓ ∈ mWord0, ℓ ∈ letters) ∧ (∀ ℓ ∈ mWord1, ℓ ∈ letters) ∧
    (∀ ℓ ∈ mConjW0, ℓ ∈ letters) ∧ (∀ ℓ ∈ mConjW1, ℓ ∈ letters) ∧ mConjC0 < 2 ^ 11 ∧
    mConjC1 < 2 ^ 11 :=
  Certificates.certificate4021.2.2.2.2.2.2.2.2.2.2.2.1

theorem comm_y_out :
    ((List.range 2048).any fun c => actT (wordT wObs) c != c) = true :=
  Certificates.certificate4021.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.Sporadic.J4.QT
