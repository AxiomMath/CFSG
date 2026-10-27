module

public import Certificates.Data.HuppertU38.Model

public section

namespace CFSG.Certificates.Kernel.U38

open CFSG.RankThree.PartTwo.Sec4.Item434U38 GF64

@[expose] def c8L : List Nat := (List.range 64).map fun x => (conj8 (ofNat' x)).toNat

@[expose] def c8 (a : GF64) : GF64 := ofNat' (c8L.getD a.toNat 0)

@[expose] def isoB (a b c : GF64) : Bool := c8 a * c + c8 b * b + c8 c * a == 0

@[expose] def genMatN (k : Nat) : Fin 3 → Fin 3 → GF64 :=
  if h : k < 7 then genMat ⟨k, h⟩ else weylMat

@[expose] def codesL : List Nat := (List.range 513).map fun i => vcode (ptsVn i)

@[expose] def ptsChk (x0 n : Nat) : Bool :=
  (List.range' x0 n).all fun x => (List.range 64).all fun y => (List.range 64).all fun z =>
    (ofNat' x == 0 && ofNat' y == 0 && ofNat' z == 0) || !isoB (ofNat' x) (ofNat' y) (ofNat' z) ||
      codesL.contains (vcode (normV3 (ofNat' x) (ofNat' y) (ofNat' z)))

end CFSG.Certificates.Kernel.U38

end
