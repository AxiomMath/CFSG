module

public import Certificates.Data.Kernel.G2Three.Sec1T3C

public section

namespace CFSG.KD.G2Three.Sec1T3

open CFSG.KC.Loop

@[expose] noncomputable def q8modK (P V r s N : Nat) : Bool :=
  strictB N fun N => allBelow 64 1 fun uv => (fun u v =>
      hasB N (mulE P (atR V (d8I P r s (q8M u v))) (mulE P (d8I P r s u) (d8I P r s v))))
    (Nat.shiftRight uv 3) (Nat.land uv 7)

@[expose] noncomputable def q8U (P r s N : Nat) : Nat :=
  strictN N fun N => Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => Nat.lor acc (imgR (rowT P (d8I P r s k)) N)) 8

@[expose] noncomputable def q8q8modK (P C V X N r1 s1 r2 s2 : Nat) : Bool :=
  strictB X fun X => strictB N fun N =>
  bAnd(subM N X, bAnd(normM P C V X N, bAnd(q8modK P V r1 s1 N, bAnd(q8modK P V r2 s2 N,
  strictB (q8U P r1 s1 N) fun U1 => strictB (q8U P r2 s2 N) fun U2 =>
  bAnd(Nat.beq (pop U1) (Nat.mul 8 (pop N)), bAnd(Nat.beq (pop U2) (Nat.mul 8 (pop N)),
  bAnd(subM U1 X, bAnd(subM U2 X,
  bAnd(allBelow 64 1 (fun uv => hasB N (commE P C V (d8I P r1 s1 (Nat.shiftRight uv 3))
    (d8I P r2 s2 (Nat.land uv 7)))),
  bAnd(Nat.beq (prodM C U1 U2) X, Nat.beq (pop (Nat.land U1 U2)) (Nat.mul 2 (pop N))))))))))))

@[expose] noncomputable def jrU (P C V Q L RG m X N : Nat) : Nat :=
  strictN N fun N => strictN (jC P C V L RG m X N) fun Cm =>
    strictN (maxBelow m 7 fun k => nIf(hasB Cm k, omN Q (entL L k) N, 0)) fun mx =>
      orBelow m 7 fun k => nIf(hasB Cm k, strictN (entL L k) fun K =>
        nIf(Nat.beq (omN Q K N) mx, K, 0), 0)

@[expose] noncomputable def abBoundK (P C V L RG m b : Nat) : Bool :=
  allBelow m 7 fun k => bIf(abR P C V (rgAt RG k) 1, Nat.ble (pop (entL L k)) b, true)

@[expose] noncomputable def f15aK (P C V Q L m a1 b1 a2 b2 h0 sg kA kBs r1 s1 r2 s2 R : Nat) : Bool :=
  (fun gs gs6 gB b1b2 z => bAnd(closOK C gs R, bAnd(closOK C gs6 R, bAnd(closOK C gB R,
  bAnd(closOK C [z] R, bAnd(closOK C [a1, b1, a2, b2] R,
  bAnd(closOK C [b1b2, mulE P (mulE P a1 b1) a2, z] R, bAnd(closOK C [mulE P a1 a2, b1b2, z] R,
  bAnd(closOK C [sg] R, bAnd(closOK C [mulE P a1 a2, b1, b2, h0, sg] R,
  strictB (closK C gs R) fun S => strictB (closK C gs6 R) fun Ss =>
  strictB (closK C [z] R) fun Zm => strictB (cenE P C S b1b2) fun Bm =>
  strictB (cenS P C Bm gB) fun ZB => strictB (closK C [a1, b1, a2, b2] R) fun A =>
  strictB (prodM C (closK C [b1b2, mulE P (mulE P a1 b1) a2, z] R)
    (closK C [mulE P a1 a2, b1b2, z] R)) fun EF =>
  strictB (closK C [sg] R) fun Sg => strictB (closK C [mulE P a1 a2, b1, b2, h0, sg] R) fun Bs =>
  bAnd(Nat.beq Bm (closK C gB R), bAnd(Nat.beq (cenS P C Ss gs6) Zm,
  bAnd(Nat.beq (upS P C V Ss Zm gs6) ZB, bAnd(Nat.beq (upS P C V Ss ZB gs6) EF,
  bAnd(secEK P C V Q Ss EF 8, bAnd(normM P C V Ss ZB, bAnd(eaMaxK Q L m Ss ZB kA kBs,
  bAnd(Nat.beq (entL L kA) A, bAnd(Nat.beq (entL L kBs) Bs, bAnd(Nat.beq (prodM C Bm Sg) Bs,
  bAnd(permB P C Bm Sg, q8q8modK P C V Bs Zm r1 s1 r2 s2)))))))))))))))))))))
    [a1, b1, a2, b2, h0] [a1, b1, a2, b2, h0, sg] [mulE P a1 a2, b1, b2, h0] (mulE P b1 b2)
    (atR Q b1)

@[expose] noncomputable def f15bK (P C V Q L RG m a1 b1 a2 b2 h0 sg kF kFs R : Nat) : Bool :=
  (fun gs gs6 b1b2 z => bAnd(closOK C gs R, bAnd(closOK C gs6 R, bAnd(closOK C [z] R,
  bAnd(closOK C [a1, b1, a2, b2] R, bAnd(closOK C [mulE P a1 a2, b1b2, z] R,
  bAnd(closOK C [sg] R, bAnd(closOK C [mulE P a1 a2, b1b2, z, sg] R,
  strictB (closK C gs R) fun S => strictB (closK C gs6 R) fun Ss =>
  strictB (closK C [z] R) fun Zm => strictB (closK C [a1, b1, a2, b2] R) fun A =>
  strictB (closK C [mulE P a1 a2, b1b2, z] R) fun F => strictB (closK C [sg] R) fun Sg =>
  strictB (closK C [mulE P a1 a2, b1b2, z, sg] R) fun Fs =>
  bAnd(normM P C V Ss Zm, bAnd(joinK C (jrU P C V Q L RG m Ss Zm) R A,
  bAnd(Nat.beq (prodM C F Sg) Fs, bAnd(permB P C F Sg, bAnd(joinK C (jrU P C V Q L RG m Ss 1) R Fs,
  bAnd(elemAbK P C Q Fs, bAnd(Nat.beq (pop Fs) 16,
  bAnd(Nat.beq (entL L kF) F, bAnd(Nat.beq (entL L kFs) Fs, bAnd(Bool.not' (Nat.beq kF kFs),
  strictB (maxIdx L (secC Q L m S 1) m) fun MxS =>
  bAnd(hasB MxS kF, Nat.beq (maxIdx L (secC Q L m Ss 1) m)
    (Nat.lor (Nat.sub MxS (Nat.shiftLeft 1 kF)) (Nat.shiftLeft 1 kFs)))))))))))))))))))))
    [a1, b1, a2, b2, h0] [a1, b1, a2, b2, h0, sg] (mulE P b1 b2) (atR Q b1)

@[expose] noncomputable def f15cK (P C V Q L RG m a1 b1 a2 b2 h0 sg R : Nat) : Bool :=
  bAnd(closOK C [a1, b1, a2, b2, h0, sg] R, bAnd(closOK C [a1, b1, a2, b2] R,
  bAnd(closOK C [atR Q b1] R, bAnd(abBoundK P C V L RG m 16,
  bAnd(Nat.beq (pRankK Q L m (closK C [a1, b1, a2, b2, h0, sg] R)) 16,
    secEK P C V Q (closK C [a1, b1, a2, b2] R) (closK C [atR Q b1] R) 16)))))

end CFSG.KD.G2Three.Sec1T3
