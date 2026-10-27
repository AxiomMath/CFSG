module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.DerDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.ONanJ4Nine

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3

structure FGen where
  reg : Nat
  ord : Nat
  u : Word
  tu : Nat
deriving Inhabited

structure Cj where
  reg : Nat
  ord : Nat
  wz : Word
  wx : Word
deriving Inhabited

structure FixSpec where
  rA : Nat
  oA : Nat
  rB : Nat
  oB : Nat
  rx : Nat
  ry : Nat
  rz : Nat
  tz : Nat
  rxy : Nat
  rxy2 : Nat
  gens : List FGen
  ders : List Der
  wA : Word
  wB : Word
  c1 : Cj
  c2 : Cj
  c3 : Cj
deriving Inhabited

@[expose] def Cj.facts (D : FixSpec) (c : Cj) : List MFact :=
  [.ord c.reg c.ord, .conj c.reg [(D.rz, 1)] c.wz, .conj c.reg [(D.rx, 1)] c.wx]

@[expose] def FixSpec.facts (D : FixSpec) : List MFact :=
  [.ord D.rA D.oA, .ord D.rB D.oB, .ord D.rx 3, .ord D.ry 3, .ord D.rz 3, .ord D.rxy 3,
    .ord D.rxy2 3,
    .eq [(D.rz, 1)] [(D.rx, 1), (D.ry, 1), (D.rx, 2), (D.ry, 2)],
    .eq [(D.rz, 1), (D.rx, 1)] [(D.rx, 1), (D.rz, 1)],
    .eq [(D.rz, 1), (D.ry, 1)] [(D.ry, 1), (D.rz, 1)], .ne [(D.rz, 1)] [] D.tz,
    .eq [(D.rxy, 1)] [(D.rx, 1), (D.ry, 1)], .eq [(D.rxy2, 1)] [(D.rx, 1), (D.ry, 2)]] ++
  D.gens.flatMap (fun g => [MFact.ord g.reg g.ord, MFact.conj g.reg g.u g.u,
    MFact.ne g.u [] g.tu]) ++
  D.ders.flatMap Der.facts ++ [.eq [(D.rA, 1)] D.wA, .eq [(D.rB, 1)] D.wB] ++
  Cj.facts D D.c1 ++ Cj.facts D D.c2 ++ Cj.facts D D.c3

@[expose] def FixSpec.genRegs (D : FixSpec) : List Nat := D.gens.map (·.reg)

@[expose] def FixSpec.avRegs (D : FixSpec) : List Nat := D.ders.map (·.reg) ++ D.genRegs

@[expose] def Cj.wf (D : FixSpec) (r : Nat) (c : Cj) : Bool :=
  (c.wz ++ c.wx).all fun q => q.1 == D.rz || q.1 == r

@[expose] def FixSpec.wf (D : FixSpec) : Bool :=
  D.gens.all (fun g => decide (g.ord % 3 ≠ 0) &&
    g.u.all fun q => q.1 == D.rz || q.1 == D.rx) &&
  derWf D.genRegs D.ders &&
  (D.wA ++ D.wB).all (fun q => D.avRegs.contains q.1) &&
  Cj.wf D D.rxy2 D.c1 && Cj.wf D D.rxy D.c2 && Cj.wf D D.ry D.c3

@[expose] def fixCheck {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (nregs : Nat)
    (prog : List Op) (D : FixSpec) : Bool :=
  mcertCheck O sA sB ⟨nregs, prog, D.facts⟩ && decide (D.rA < nregs) && decide (D.rB < nregs) &&
  O.eq (O.regsOf sA sB nregs prog)[D.rA]! (O.decode sA) &&
  O.eq (O.regsOf sA sB nregs prog)[D.rB]! (O.decode sB) && D.wf

end CFSG.RankThree.PartTwo.Sec4.ONanJ4Nine
