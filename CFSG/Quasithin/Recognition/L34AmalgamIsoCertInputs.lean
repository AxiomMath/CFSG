
module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoRefInputs

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94 CFSG.CosetTable

@[expose, irreducible] def a2r : M22 := m22OfWord "babbabababbaBaBabbaB"

@[expose, irreducible] def b2r : M22 := m22OfWord "abaBaBaBaBababbababa"

@[expose] def c2OfWord (s : String) : M22 :=
  s.toList.foldl (fun g c => g * if c = 'a' then a2r else if c = 'b' then b2r else b2r⁻¹) 1

@[expose] def tmul (s t : Array (Fin 22)) : Array (Fin 22) :=
  Array.ofFn fun x : Fin 22 => s.getD (t.getD x.val 0).val 0

@[expose] def tid : Array (Fin 22) := Array.ofFn id

@[expose] def evalT (f g : Fin 5 → Array (Fin 22)) : List (Fin 5 × Bool) → Array (Fin 22)
  | [] => tid
  | x :: w => tmul (cond x.2 (f x.1) (g x.1)) (evalT f g w)

@[expose] def genTL : List (Array (Fin 22)) := [tab bC1, tab bC2, tab bC3, tab bT1, tab bT2]

@[expose] def genTiL : List (Array (Fin 22)) :=
  [tab bC1⁻¹, tab bC2⁻¹, tab bC3⁻¹, tab bT1⁻¹, tab bT2⁻¹]

@[expose] def wtab (gT gTi : List (Array (Fin 22))) (s : String) : Array (Fin 22) :=
  evalT (fun i => gT.getD i tid) (fun i => gTi.getD i tid) (word s)

@[expose] def invW (w : List (Fin 5 × Bool)) : List (Fin 5 × Bool) :=
  (w.map fun x => (x.1, !x.2)).reverse

@[expose] def wtabI (gT gTi : List (Array (Fin 22))) (s : String) : Array (Fin 22) :=
  evalT (fun i => gT.getD i tid) (fun i => gTi.getD i tid) (invW (word s))

@[expose] def fixesF (T : Array (Fin 22)) : Bool := m22HexadL.all fun y => T.getD y.val 0 == y

@[expose] def presF (T : Array (Fin 22)) : Bool :=
  m22HexadL.all fun y => m22HexadL.contains (T.getD y.val 0)

@[expose] def lettersB (s : String) : Bool := (word s).all fun x => decide (x.1.val < 3)

@[expose] def crdTL : List (Array (Fin 22)) := (List.finRange 16).map fun x => tab (crd x)

@[expose] def candT (T₀ T₁ T₂ : Array (Fin 22)) : Fin 5 → Array (Fin 22) :=
  fun i => [T₀, T₁, T₂].getD i tid

@[expose] def relsP1 : List (List (Fin 5 × Bool)) := (rels1 ++ ["u"]).map word

@[expose] def relsP2 : List (List (Fin 5 × Bool)) := (rels2 ++ ["s"]).map word

@[expose] def a2W : List String :=
  ["", "p", "Rpr", "qpq", "rpR", "pqpq", "Rqpqr", "qRprq", "qrpRq", "rqpqR", "Rpqpqr", "qpqRpr",
   "qpqrpR", "rpqpqR", "pRpqpqr", "prpqpqR"]

@[expose] def s1W : List (List String) :=
  [["p", "rqR", "R", "s"], ["qrpRq", "Rqr", "R", "qrsR"], ["qRprq", "Rqr", "r", "qRsr"],
   ["prpqpqR", "Rqr", "r", "rqRs"], ["qpqRpr", "q", "r", "qrsR"], ["Rpr", "rqR", "r", "Rqsr"],
   ["prpqpqR", "Rqr", "R", "qs"], ["qrpRq", "Rqr", "r", "rqsR"], ["rqpqR", "Rqr", "r", "qrsR"],
   ["qpq", "Rqr", "R", "Rqrs"], ["rpR", "rqR", "r", "rsR"], ["Rqpqr", "Rqr", "r", "Rqsr"],
   ["rpR", "q", "R", "qrqsR"], ["pRpqpqr", "q", "r", "rqRs"], ["rpR", "rqR", "R", "rqsR"],
   ["qpqRpr", "Rqr", "r", "rsR"], ["p", "q", "r", "s"], ["Rqpqr", "Rqr", "R", "Rsr"],
   ["qpqRpr", "rqR", "r", "qrqsR"], ["qrpRq", "rqR", "R", "qrqsR"], ["Rpr", "q", "r", "qRsr"],
   ["Rpr", "rqR", "R", "qRsr"], ["rqpqR", "q", "R", "qrsR"], ["rqpqR", "rqR", "R", "rsR"],
   ["rpR", "q", "r", "rqsR"], ["qRprq", "q", "r", "Rsr"], ["rqpqR", "rqR", "r", "rqsR"],
   ["Rpr", "q", "R", "Rsr"], ["qpqrpR", "rqR", "R", "Rqsr"], ["qpqRpr", "q", "R", "rsR"],
   ["qpq", "rqR", "r", "Rqrs"], ["Rqpqr", "q", "R", "Rqsr"], ["qrpRq", "rqR", "r", "qrsR"],
   ["pRpqpqr", "Rqr", "r", "Rqrs"], ["qpqrpR", "q", "r", "Rqsr"], ["rqpqR", "Rqr", "R", "rqsR"],
   ["qRprq", "q", "R", "qRsr"], ["Rpr", "Rqr", "r", "Rsr"], ["Rqpqr", "rqR", "r", "Rsr"],
   ["Rqpqr", "q", "r", "qRqsr"], ["prpqpqR", "rqR", "r", "qs"], ["rpR", "Rqr", "r", "qrqsR"],
   ["qrpRq", "q", "r", "qrqsR"], ["qpq", "Rqr", "r", "s"], ["rqpqR", "q", "r", "rsR"],
   ["rpR", "Rqr", "R", "rsR"], ["qpq", "q", "r", "qs"], ["pRpqpqr", "Rqr", "R", "s"],
   ["qpqrpR", "q", "R", "qRqsr"], ["p", "q", "R", "qs"], ["p", "Rqr", "r", "qs"],
   ["qpqrpR", "rqR", "r", "qRsr"], ["qRprq", "rqR", "r", "qRqsr"],
   ["qpqrpR", "Rqr", "r", "qRqsr"], ["qRprq", "rqR", "R", "Rsr"], ["prpqpqR", "q", "r", "Rqrs"],
   ["p", "rqR", "r", "rqRs"], ["qpqRpr", "rqR", "R", "qrsR"], ["qpq", "rqR", "R", "qs"],
   ["Rpr", "Rqr", "R", "Rqsr"], ["pRpqpqr", "q", "R", "Rqrs"], ["qpqrpR", "Rqr", "R", "qRsr"],
   ["qRprq", "Rqr", "R", "qRqsr"], ["qrpRq", "q", "R", "rqsR"], ["pRpqpqr", "rqR", "R", "rqRs"],
   ["qpqRpr", "Rqr", "R", "qrqsR"], ["Rqpqr", "rqR", "R", "qRqsr"],
   ["prpqpqR", "rqR", "R", "Rqrs"], ["prpqpqR", "q", "R", "rqRs"], ["qpq", "q", "R", "s"],
   ["p", "Rqr", "R", "rqRs"], ["pRpqpqr", "rqR", "r", "s"]]

@[expose] def rhW : List (List String) :=
  [["p", "q", "r", "", "u", "p", "q", "r"],
   ["Rpr", "qRpqpqr", "r", "", "rpur", "rpR", "qrpqpqR", "r"],
   ["rpR", "rpqpR", "r", "", "ruR", "Rpr", "Rpqpr", "r"],
   ["p", "prqRp", "R", "", "pup", "p", "rpqpR", "R"]]

@[expose] def witL : List (ℕ × ℕ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
   (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
   (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (2, 10),
   (2, 59), (3, 49), (3, 16), (1, 5), (1, 45), (2, 41), (2, 21), (2, 24), (2, 27), (0, 16),
   (0, 49), (0, 0), (0, 0), (3, 0), (3, 50), (0, 0), (0, 0), (3, 70), (3, 56), (0, 50), (0, 0),
   (1, 37), (1, 14), (0, 56), (0, 70), (0, 0), (0, 0), (1, 20), (1, 12), (0, 0), (0, 0), (2, 5),
   (2, 45), (3, 12), (3, 20), (1, 56), (1, 70), (2, 37), (2, 14), (2, 20), (2, 12), (0, 24),
   (0, 27), (0, 0), (0, 0), (3, 14), (3, 37), (0, 0), (0, 0), (3, 45), (3, 5), (0, 41), (0, 21),
   (1, 50), (1, 0), (0, 10), (0, 59), (0, 0), (0, 0), (1, 16), (1, 49), (0, 0), (0, 0), (2, 26),
   (2, 17), (3, 68), (3, 13), (1, 52), (1, 1), (2, 15), (2, 28), (2, 42), (2, 36), (0, 46),
   (0, 69), (0, 0), (0, 0), (3, 58), (3, 43), (0, 0), (0, 0), (3, 47), (3, 40), (0, 3), (0, 64),
   (1, 53), (1, 57), (0, 71), (0, 6), (0, 0), (0, 0), (1, 39), (1, 22), (0, 0), (0, 0), (2, 56),
   (2, 70), (3, 27), (3, 24), (1, 10), (1, 59), (2, 50), (2, 0), (2, 16), (2, 49), (0, 20),
   (0, 12), (0, 0), (0, 0), (3, 21), (3, 41), (0, 0), (0, 0), (3, 59), (3, 10), (0, 37), (0, 14),
   (1, 41), (1, 21), (0, 5), (0, 45), (0, 0), (0, 0), (1, 24), (1, 27), (0, 0), (0, 0), (0, 0),
   (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
   (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
   (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (2, 51), (2, 65), (3, 29), (3, 34),
   (1, 30), (1, 9), (2, 11), (2, 23), (2, 25), (2, 63), (0, 42), (0, 36), (0, 0), (0, 0), (3, 19),
   (3, 2), (0, 0), (0, 0), (3, 35), (3, 38), (0, 15), (0, 28), (1, 33), (1, 67), (0, 26), (0, 17),
   (0, 0), (0, 0), (1, 55), (1, 60), (0, 0), (0, 0), (2, 38), (2, 35), (3, 63), (3, 25), (1, 71),
   (1, 6), (2, 2), (2, 19), (2, 34), (2, 29), (0, 44), (0, 31), (0, 0), (0, 0), (3, 23), (3, 11),
   (0, 0), (0, 0), (3, 65), (3, 51), (0, 7), (0, 54), (1, 3), (1, 64), (0, 18), (0, 61), (0, 0),
   (0, 0), (1, 46), (1, 69), (0, 0), (0, 0), (2, 30), (2, 9), (3, 48), (3, 4), (1, 18), (1, 61),
   (2, 33), (2, 67), (2, 55), (2, 60), (0, 39), (0, 22), (0, 0), (0, 0), (3, 66), (3, 8), (0, 0),
   (0, 0), (3, 62), (3, 32), (0, 53), (0, 57), (1, 7), (1, 54), (0, 52), (0, 1), (0, 0), (0, 0),
   (1, 44), (1, 31), (0, 0), (0, 0), (2, 71), (2, 6), (3, 31), (3, 44), (1, 32), (1, 62), (2, 3),
   (2, 64), (2, 46), (2, 69), (0, 25), (0, 63), (0, 0), (0, 0), (3, 54), (3, 7), (0, 0), (0, 0),
   (3, 61), (3, 18), (0, 11), (0, 23), (1, 8), (1, 66), (0, 51), (0, 65), (0, 0), (0, 0), (1, 4),
   (1, 48), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
   (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
   (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
   (2, 40), (2, 47), (3, 36), (3, 42), (1, 26), (1, 17), (2, 43), (2, 58), (2, 13), (2, 68),
   (0, 34), (0, 29), (0, 0), (0, 0), (3, 28), (3, 15), (0, 0), (0, 0), (3, 17), (3, 26), (0, 2),
   (0, 19), (1, 15), (1, 28), (0, 38), (0, 35), (0, 0), (0, 0), (1, 42), (1, 36), (0, 0), (0, 0),
   (2, 52), (2, 1), (3, 22), (3, 39), (1, 40), (1, 47), (2, 53), (2, 57), (2, 39), (2, 22),
   (0, 4), (0, 48), (0, 0), (0, 0), (3, 57), (3, 53), (0, 0), (0, 0), (3, 1), (3, 52), (0, 8),
   (0, 66), (1, 43), (1, 58), (0, 32), (0, 62), (0, 0), (0, 0), (1, 13), (1, 68), (0, 0), (0, 0),
   (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
   (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
   (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (2, 18), (2, 61), (3, 69),
   (3, 46), (1, 51), (1, 65), (2, 7), (2, 54), (2, 44), (2, 31), (0, 13), (0, 68), (0, 0), (0, 0),
   (3, 64), (3, 3), (0, 0), (0, 0), (3, 6), (3, 71), (0, 43), (0, 58), (1, 11), (1, 23), (0, 40),
   (0, 47), (0, 0), (0, 0), (1, 25), (1, 63), (0, 0), (0, 0), (2, 32), (2, 62), (3, 60), (3, 55),
   (1, 38), (1, 35), (2, 8), (2, 66), (2, 4), (2, 48), (0, 55), (0, 60), (0, 0), (0, 0), (3, 67),
   (3, 33), (0, 0), (0, 0), (3, 9), (3, 30), (0, 33), (0, 67), (1, 2), (1, 19), (0, 30), (0, 9),
   (0, 0), (0, 0), (1, 34), (1, 29)]

@[expose] def cjW : List String :=
  ["", "", "", "", "", "pR", "qR", "pr", "", "pR", "qr", "", "qR", "pr", "qr", "pqrqp", "",
   "qprpq", "", "p", "prqpR", "qpRpq", "", "qprpq", "p", "pRqpr", "pRqpr", "q", "pqRqp", "",
   "pqrqp", "prqpR", "q", "", "pqRqp", "", "qpRpq", "pqRqpR", "pqpR", "", "", "pqrqpr", "qpqR",
   "", "", "pqpRp", "qRp", "", "qrp", "pqrpR", "pqpr", "", "pqpR", "qRp", "pqRpr", "pqprp", "",
   "qrp", "pRq", "", "pqRpr", "pqprp", "prq", "qpqr", "qpqR", "pqpRp", "pRq", "", "prq", "pqrpR",
   "", "", "pqpr", "pqrqpr", "", "", "qpqr", "pqRqpR", "qrpq", "pqp", "pqpqR", "", "pqrp", "",
   "prqp", "qpq", "", "pqRp", "", "pRqp", "pqrq", "", "pRqpqR", "", "", "", "qp", "pqRq",
   "pRqrpR", "pqpqr", "pqpqR", "pqrq", "pqpqRq", "", "qp", "", "pqRq", "prqp", "", "", "pqpqrp",
   "pqpqRq", "", "qRpq", "qprp", "", "pq", "", "pqpqrp", "qpRp", "pRqpqR", "qprp", "pq", "", "",
   "pRqrpR", "", "qpRp", "qrpq", "", "pqRp", "", "", "pqpqr", "pqp", "qRpq", "", "pqrp", "", "",
   "qpq", "pRqp", "pqR", "pqpq", "", "qpR", "qrpR", "qRprq", "pRqpq", "qrpqp", "pqr", "pRqr", "",
   "qrpR", "", "qpqrp", "pqprq", "qRprq", "pRqrp", "qRpr", "", "", "prqR", "pqR", "", "qpqrp",
   "qRpr", "qRpqp", "", "prqpq", "pRqrp", "qpr", "", "prqR", "", "pRqr", "qpR", "pqprq", "qrpqp",
   "", "pqpq", "qRpqp", "pqr", "prqpq", "pRqpq", "qpr", "", "", "", "", "", ""]

@[expose] def a2Check (gT gTi : List (Array (Fin 22))) : Bool :=
  decide ((a2W.map (wtab gT gTi)).Nodup) && decide (a2W.length = 16) &&
    a2W.all fun s => lettersB s && fixesF (wtab gT gTi s)

@[expose] def pqCheck (gT gTi crdT : List (Array (Fin 22))) : Bool :=
  fixesF (gT.getD 0 tid) && !crdT.contains (gT.getD 0 tid) && crdT.contains (gT.getD 1 tid) &&
    !fixesF (gT.getD 1 tid) &&
    !presF (tmul (tmul (gT.getD 3 tid) (gT.getD 0 tid)) (gTi.getD 3 tid)) &&
    !((tmul (tmul (gT.getD 4 tid) (gT.getD 1 tid)) (gTi.getD 4 tid)).getD 1 0 == 1)

@[expose] def invCheck (gT gTi crdT : List (Array (Fin 22))) : Bool :=
  bWords.all fun s => let T := wtab gT gTi s
    !(tmul T T == tid) || crdT.contains T || fixesF T

@[expose] def conjCheck (gT gTi : List (Array (Fin 22))) : Bool :=
  (List.range 192).all fun i => let T := wtab gT gTi (bWords.getD i "")
    T == tid || !(tmul T (tmul T T) == tid) ||
      (lettersB (cjW.getD i "") &&
        (let U := tmul (tmul (wtab gT gTi (cjW.getD i "")) T) (wtabI gT gTi (cjW.getD i ""))
         U == gT.getD 2 tid || U == gTi.getD 2 tid))

@[expose] def s1Check (gT gTi : List (Array (Fin 22))) : Bool :=
  s1W.all fun σ => lettersB (σ.getD 0 "") && lettersB (σ.getD 1 "") && lettersB (σ.getD 2 "") &&
    (word (σ.getD 3 "")).all (fun x => decide (x.1 ≠ 4)) && decide (σ.getD 4 "" = "") &&
    !presF (wtab gT gTi (σ.getD 3 "")) &&
    relsP1.all fun w => evalT (fun i => wtab gT gTi (σ.getD i ""))
      (fun i => wtabI gT gTi (σ.getD i "")) w == tid

@[expose] def rhCheck (gT gTi : List (Array (Fin 22))) : Bool :=
  rhW.all fun ρ => lettersB (ρ.getD 0 "") && lettersB (ρ.getD 1 "") && lettersB (ρ.getD 2 "") &&
    decide (ρ.getD 3 "" = "") && (word (ρ.getD 4 "")).all (fun x => decide (x.1 ≠ 3)) &&
    !((wtab gT gTi (ρ.getD 4 "")).getD 1 0 == 1) &&
    (relsP2.all fun w => evalT (fun i => wtab gT gTi (ρ.getD i ""))
      (fun i => wtabI gT gTi (ρ.getD i "")) w == tid) &&
    (List.range 3).all fun x => lettersB (ρ.getD (x + 5) "") &&
      evalT (fun i => wtab gT gTi (ρ.getD i "")) (fun i => wtabI gT gTi (ρ.getD i ""))
        (word (ρ.getD (x + 5) "")) == gT.getD x tid

@[expose] def glueCheck (gT gTi crdT : List (Array (Fin 22))) : Bool :=
  (List.range 16).all fun i => (List.range 16).all fun j => (List.range 2).all fun e =>
    let Tp := wtab gT gTi (a2W.getD i "")
    let Tq := crdT.getD j tid
    let Tr := if e = 0 then gT.getD 2 tid else gTi.getD 2 tid
    let TR := if e = 0 then gTi.getD 2 tid else gT.getD 2 tid
    crdT.contains Tp || fixesF Tq ||
      (let w := witL.getD ((16 * i + j) * 2 + e) (0, 0)
       decide (w.1 < rhW.length) && decide (w.2 < s1W.length) &&
         (List.range 3).all fun x =>
           evalT (candT Tp Tq Tr) (candT Tp Tq TR) (word ((s1W.getD w.2 []).getD x "")) ==
             wtab gT gTi ((rhW.getD w.1 []).getD x ""))

end CFSG.Quasithin.L34Amalgam
