module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatFactsK
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24DcInputs
public import CFSG.Quasithin.EmptyFaithful.S151S9TJ2Inputs
public import CFSG.Quasithin.EmptyFaithful.S151S9TM12Inputs
public import CFSG.Quasithin.EmptyFaithful.S151S9TM22Check
public import CFSG.Quasithin.EmptyFaithful.S151S9TM23Inputs
public import CFSG.Quasithin.EmptyFaithful.S151S9TM24Inputs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Inputs
public import CFSG.Quasithin.Background.E2TwoProofSporJ2
public import CFSG.Quasithin.Background.HSporLatMathieu

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.QuasithinUnique.Ch1.SporLat.M24 CFSG.Quasithin.H.MathieuLat
open CFSG.Quasithin.E2P.SporB CFSG.Quasithin.E2P.SporB.J2Lat

@[expose] def j2FactsK : Prop :=
  ∃ D : LatData (List ℕ),
    LatFactsK (codeSetLab 315) 315 j2ta.toArray j2tb.toArray j2Delta
      (CFSG.Sporadic.J2.a : CFSG.Sporadic.J2.J) (CFSG.Sporadic.J2.b : CFSG.Sporadic.J2.J) j2Sg
      j2STabs D ∧
    D.Om.map (fun o => o.lbl.size) = #[1, 3, 9, 15, 3] ∧
    j2Wit.Ok 315 (codeSetAct 315) j2Delta D j2SLP[143]!

@[expose] def m12FactsK : Prop :=
  ∃ D : LatData (List ℕ),
    LatFactsK (codeSetLab 12) 12 m12ta.toArray m12tb.toArray m12Delta
      CFSG.Sporadic.Mathieu.m12a CFSG.Sporadic.Mathieu.m12b m12Sg m12STabs D ∧
    D.Om.map (fun o => o.lbl.size) = #[1, 3, 3] ∧
    m12Wit.Ok 12 (codeSetAct 12) m12Delta D m12SLP[153]!

@[expose] def m22FactsK : Prop :=
  ∃ D : LatData (List ℕ),
    LatFactsK (codeSetLab 22) 22 m22ta.toArray m22tb.toArray m22Delta
      CFSG.Sporadic.Mathieu.m22a CFSG.Sporadic.Mathieu.m22b m22Sg m22STabs D ∧
    D.Om.map (fun o => o.lbl.size) = #[1, 45, 3, 15, 3] ∧
    m22Wit.Ok 22 (codeSetAct 22) m22Delta D m22SLP[163]!

@[expose] def m23MemW : LatData (List ℕ) where
  O := default
  F := default
  sTabs := m23STabs
  mw := A312M23.m23MwLit
  mt := A312M23.m23MwLit.map fun ws => ws.map (wordTabA #[m23ta.toArray, m23tb.toArray] 23)
  Om := #[]
  atoms := #[]
  joins := []

@[expose] def m23CheckK : Prop :=
  m23Wit.Ok 23 (codeSetAct 23) m23Delta m23MemW m23SLP[159]!

end CFSG.Quasithin.S151S9T

end
