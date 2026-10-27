module

public import CFSG.RankThree.Asc83Table.MatCertDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.DerDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3

structure GenItem where
  reg : Nat
  ord : Nat
  fixes : List Nat
deriving Inhabited

structure GenData where
  nregs : Nat
  prog : List Op
  oA : Nat
  oB : Nat
  fixOrd : List (Nat × Nat)
  gens : List GenItem
  der : List Der
  wA : Word
  wB : Word
  extra : List MFact

@[expose] def GenItem.facts (g : GenItem) : List MFact :=
  .ord g.reg g.ord :: g.fixes.map fun f => .conj g.reg [(f, 1)] [(f, 1)]

@[expose] def GenData.facts (D : GenData) : List MFact :=
  [.ord 0 D.oA, .ord 1 D.oB, .eq [(0, 1)] D.wA, .eq [(1, 1)] D.wB] ++
    D.fixOrd.map (fun q => .ord q.1 q.2) ++ D.gens.flatMap GenItem.facts ++
    D.der.flatMap Der.facts ++ D.extra

@[expose] def GenData.mcert (D : GenData) : MCert := ⟨D.nregs, D.prog, D.facts⟩

@[expose] def genCheck {M V : Type} [Inhabited M] (O : Ops M V) (p : Nat) (sA sB : String)
    (D : GenData) : Bool :=
  let R := O.regsOf sA sB D.nregs D.prog
  mcertCheck O sA sB D.mcert && O.eq R[0]! (O.decode sA) && O.eq R[1]! (O.decode sB) &&
    D.gens.all (fun g => g.ord % p != 0 && g.fixes.all fun f => D.fixOrd.any (·.1 == f)) &&
    derWf (D.gens.map (·.reg)) D.der &&
    (D.wA ++ D.wB).all (fun q => D.gens.any (·.reg == q.1) || D.der.any (·.reg == q.1))

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e
