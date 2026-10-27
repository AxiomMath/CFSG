module

public import Certificates.Data.Kernel.Census.Packed

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum

structure ExcRefP where
  node : Nat
  w : Nat
deriving Inhabited

section Checks

variable (n w : Nat)

@[expose] noncomputable def pexcOK (ps : List Nat) (inW : Nat → Bool) (e0 : Array Nat)
    (cN : Array ArrCertP) (excs : List ExcRefP) (i : Nat) : Bool :=
  penumOK n w e0 ps (pmaskCert n w e0) && excs.any fun r => Nat.beq r.node i &&
    pvalid n w r.w && inW r.w &&
    ((List.range e0.size).all fun j => pmem cN[i]! (pconj n w r.w e0[j]!)) &&
    Nat.beq (pmaskCert n w e0).pts.size cN[i]!.pts.size

@[expose] noncomputable def pchildrenOK (cS : ArrCertP) (nodes : Array NodeP) (cN : Array ArrCertP)
    (i : Nat) : Bool :=
  walkAll (fun u c =>
    !(Nat.beq (pc n w u u) (pid n w)) ||
      !((List.range nodes[i]!.basis.size).all fun k => pcommA n w u nodes[i]!.basis[k]!) ||
      pmem cN[i]! u || pchildOK n w nodes cN i u c) cS.pts.toList nodes[i]!.children.toList

@[expose] noncomputable def pnodeExcOK (ps : List Nat) (inX outX inW : Nat → Bool)
    (allowPW allowInX allowU : Bool) (cS : ArrCertP) (nodes : Array NodeP)
    (cN : Array ArrCertP) (wcs : Array (Array ArrCertP)) (e0 : Array Nat) (excs : List ExcRefP)
    (i : Nat) : Bool :=
  pnodeOK n w ps inX outX allowPW allowInX allowU cS nodes cN wcs i ||
    (penumOK n w nodes[i]!.basis ps cN[i]! && pexcOK n w ps inW e0 cN excs i &&
      pchildrenOK n w cS nodes cN i)

end Checks

end CFSG.KC.Census
