module

public import CFSG.Sporadic.GLQ.RegisterProgram
public meta import CFSG.Sporadic.GLQ.RegisterProgram
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public meta import Certificates.Data.CFSGNative.SectionRank.F2Fast
public import CFSG.Blueprint.MatrixSeedIdentification
import CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.Bridge.Fi23GPL
public meta import Certificates.Data.CFSGNative.Bridge.Fi23GPL
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Fi23InB

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.Sporadic.GLQ
  CFSG.Sporadic.Bridge.Fi23GPL.Native

@[expose] def slp : List Instr := [
  .mu 1 2 3, .mu 3 2 4, .mu 3 4 5, .mu 3 5 6, .mu 6 3 7, .mu 7 7 6, .mu 6 6 2, .mu 5 5 6,
  .mu 5 6 7, .mu 6 7 5, .mu 5 5 6, .mu 6 6 1, .mu 4 4 5, .mu 5 5 6, .mu 6 6 5, .mu 4 5 6,
  .iv 6 7, .mu 7 2 5, .mu 5 6 2, .mu 3 3 4, .mu 3 4 5, .mu 4 5 6, .mu 6 6 5, .iv 5 6,
  .mu 6 1 4, .mu 4 5 1]

@[expose] def nreg : ℕ := 8

@[expose] def regsN : Array (Array ℕ × Array ℕ) :=
  runProgN (ops2fr 4370) (initRegsN (ops2fr 4370) nreg
    ((ops2fr 4370).decode NativeSporadic.BSeed1, (ops2fr 4370).decode NativeSporadic.BSeed1)
    ((ops2fr 4370).decode NativeSporadic.BSeed2,
      (ops2fr 4370).pow ((ops2fr 4370).decode NativeSporadic.BSeed2) 2)) slp

@[expose] def imgN (k : ℕ) : Array ℕ := signedWordN (ops2fr 4370) regsN[1]! regsN[2]! imgWords[k]!

@[expose] def imgsN : Array (Array ℕ) := Array.ofFn (n := 10) fun i => imgN i.val

@[expose] def wordN (imgs : Array (Array ℕ)) (w : List (ℕ × Bool)) : Array ℕ :=
  w.foldr (fun l acc => (ops2fr 4370).mul imgs[l.1]! acc) (ops2fr 4370).one

@[expose] def powOK (X : Array ℕ) (e : ℕ) : Bool :=
  (ops2fr 4370).eq ((ops2fr 4370).pow X e) (ops2fr 4370).one

@[expose] def fi23InBCheck : Bool :=
  slp.all (Instr.lt nreg) &&
    powOK ((ops2fr 4370).decode NativeSporadic.BSeed1) 2 &&
    powOK ((ops2fr 4370).decode NativeSporadic.BSeed2) 3 &&
    (imgWords.size == 10) &&
    rels.all (fun r => r.all fun l => decide (l.1 < 10)) &&
    (List.range 10).all (fun k => powOK imgsN[k]! 2) &&
    rels.all (fun r => (ops2fr 4370).eq (wordN imgsN r) (ops2fr 4370).one) &&
    (ops2fr 4370).vne ((ops2fr 4370).vmul ((ops2fr 4370).unit 0) imgsN[0]!) ((ops2fr 4370).unit 0)

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Fi23InB
