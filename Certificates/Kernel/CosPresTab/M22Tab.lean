module

public import Certificates.Data.Kernel.TabWordK
public import CFSG.CGT.T75JM.M22PDInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Sec5One
public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.CGT.Timmesfeld75.SolvableCentral
public import CFSG.CGT.Timmesfeld75.StrongClosureCentral
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 200

namespace CFSG.KC.TabWord.M22

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.CGT.T75JM CFSG.Sporadic.Mathieu.Native

@[expose] noncomputable def idn : Nat := pidn 22 5

@[expose] noncomputable def PA : Nat := packU 5 (m22Data ()).tA.toList

@[expose] noncomputable def PB : Nat := packU 5 (m22Data ()).tB.toList

@[expose] noncomputable def BL (z : Int) : Nat := if z = 1 then PA else if z = 2 then PB else idn

@[expose] noncomputable def TP (k : Nat) : Nat := wordK 22 5 idn BL (m22GenWord k)

@[expose] noncomputable def VP (k : Nat) : Nat := pinvK 22 5 (TP k)

@[expose] noncomputable def LP (z : Int) : Nat :=
  if z = 1 then TP 0 else if z = 2 then TP 1 else if z = 3 then TP 2 else if z = 4 then TP 3
  else if z = 5 then TP 4 else if z = 6 then TP 5 else if z = 7 then TP 6 else if z = -1 then VP 0
  else if z = -2 then VP 1 else if z = -3 then VP 2 else if z = -4 then VP 3 else if z = -5 then VP 4
  else if z = -6 then VP 5 else VP 6

@[expose] noncomputable def genOk (k : Nat) : Bool :=
  allLtK 22 5 (TP k) 22 && allLtK 22 5 (VP k) 22 && Nat.beq (pcomp 22 5 (mask 5) (VP k) (TP k)) idn

@[expose] noncomputable def m22Ok : Bool :=
  allLtK 22 5 PA 22 && allLtK 22 5 PB 22 && (List.range' 0 7).all genOk &&
    m22Rels.all (fun r => Nat.beq (wordK 22 5 idn LP (r.map m22LetterZ)) idn) &&
    Nat.beq (wordK 22 5 idn LP m22SurjA) PA && Nat.beq (wordK 22 5 idn LP m22SurjB) PB

@[expose] noncomputable def thetaOk : Bool :=
  thetaRels.all (fun r => Nat.beq (wordK 22 5 idn LP (r.map m22LetterZ)) idn)

theorem m22_ok : m22Ok = true := by quickRfl

theorem tA_ok : allLtU (2 ^ 5) (m22Data ()).tA.toList = true := by quickRfl

theorem tB_ok : allLtU (2 ^ 5) (m22Data ()).tB.toList = true := by quickRfl

theorem theta_ok : thetaOk = true := by quickRfl

end CFSG.KC.TabWord.M22

end
