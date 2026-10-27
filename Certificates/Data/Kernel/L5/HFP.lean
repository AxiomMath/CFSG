module

public import Certificates.Data.Kernel.L5.HFC

public section

namespace CFSG.Certificates.Kernel.L5H

open Equiv Perm CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.L5S
  CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.HF CFSG.GH74.GLS.C3.Layer2.Model

@[expose] def g72N (E : Nat) : List Nat := (List.range 72).map fun k => fld 80 E k

@[expose] noncomputable def idxN (GN : List Nat) (x : CV 16) : Nat := GN.idxOf x.1

@[expose] def mulN (MP a b : Nat) : Nat := fld 7 MP (a * 72 + b)

@[expose] noncomputable def covIdxN (GN : List Nat) (MP i : Nat) : Bool :=
  let M := closG 72 (mulN MP) (idxN GN 1) [idxN GN yC, idxN GN wC, i] 8
  n24C.all fun a => M.testBit (idxN GN a)

@[expose] noncomputable def covN (GN : List Nat) (MP : Nat) (x : CV 16) : Bool :=
  if x.1 ∈ GN then covIdxN GN MP (idxN GN x) else n24CovC (closureList [yC, wC, x] 8) false

@[expose] noncomputable def n24TailN (GN : List Nat) (MP : Nat) (x : CV 16) (o : List Nat) : Bool :=
  (imgN x (pN Ppl) == pN Ppl) &&
    (((fam0L.all fun F => decide (pN F ∈ o)) && covN GN MP x) ||
       ((fam1L.all fun F => decide (pN F ∈ o)) && covN GN MP (twC⁻¹ * x * twC)))

@[expose] noncomputable def n24ChkN (GN : List Nat) (MP : Nat) (x : CV 16) : Bool :=
  decide ((orbListN [yC, wC, x] 3).length = 5) ||
    (let o := orbListN [yC, wC, x] 6
     decide (5 ≤ o.dedup.length) || n24TailN GN MP x o)

@[expose] noncomputable def n24EntryN (GN : List Nat) (MP : Nat) (x : CV 16) : Bool :=
  !(n24PreC x) || n24ChkN GN MP x

@[expose] noncomputable def cHatN (GN : List Nat) (MP : Nat) (x : CV 16) : Bool :=
  if x.1 ∈ GN then
    (closG 72 (mulN MP) (idxN GN 1) [idxN GN wC, idxN GN (n24C.getD 6 1), idxN GN x] 8).testBit
      (idxN GN cHC)
  else decide (cHC ∈ closureList [wC, n24C.getD 6 1, x] 8)

@[expose] noncomputable def famEntryN (GN : List Nat) (MP : Nat) (x : CV 16) : Bool :=
  let f0 := fam0ChkL (ev x)
  let f1 := fam1ChkL (ev x)
  (!(f0 || f1) || (imgN x (pN Ppl) == pN Ppl)) && (!f0 || decide (x.1 ∈ GN)) &&
    (!f0 || decide (x ∈ n24C) || cHatN GN MP x)

@[expose] noncomputable def g72PinChk (GN : List Nat) (MP : Nat) : Bool :=
  (G72C.map Subtype.val == GN) && Nat.beq mulGP MP

end CFSG.Certificates.Kernel.L5H

end
