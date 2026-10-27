module

public import CFSG.RankThree.Asc83Table.MatCertDefs

public section

namespace CFSG.RankThree.PartOne.CTP.Fus

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

structure Gen where
  reg : Nat
  ord : Nat
  u : Word
  w : Word
  tu : Nat
deriving Inhabited

structure Spec where
  p : Nat
  rA : Nat
  oA : Nat
  rB : Nat
  oB : Nat
  rx : Nat
  ry : Nat
  tx : Nat
  gens : List Gen
  wA : Word
  wB : Word
deriving Inhabited

@[expose] def Spec.facts (D : Spec) : List MFact :=
  [.ord D.rA D.oA, .ord D.rB D.oB, .ord D.rx D.p, .ord D.ry D.p,
    .eq [(D.rx, 1), (D.ry, 1)] [(D.ry, 1), (D.rx, 1)], .ne [(D.rx, 1)] [] D.tx] ++
  D.gens.flatMap (fun g => [MFact.ord g.reg g.ord, MFact.conj g.reg g.u g.w,
    MFact.ne g.u [] g.tu]) ++
  [.eq [(D.rA, 1)] D.wA, .eq [(D.rB, 1)] D.wB]

@[expose] def Spec.wf (D : Spec) : Bool :=
  decide (2 ≤ D.p) &&
  D.gens.all (fun g => (g.u ++ g.w).all fun q => q.1 == D.rx || q.1 == D.ry) &&
  (D.wA ++ D.wB).all (fun q => D.gens.any fun g => g.reg == q.1)

@[expose] def fusCheck {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (nregs : Nat)
    (prog : List Op) (D : Spec) : Bool :=
  mcertCheck O sA sB ⟨nregs, prog, D.facts⟩ &&
  decide (D.rA < nregs) && decide (D.rB < nregs) &&
  O.eq (O.regsOf sA sB nregs prog)[D.rA]! (O.decode sA) &&
  O.eq (O.regsOf sA sB nregs prog)[D.rB]! (O.decode sB) && D.wf

end CFSG.RankThree.PartOne.CTP.Fus
