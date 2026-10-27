module

public import Certificates.Data.GrSLitL34FactsRealBCheck

public section

namespace CFSG.OddStandard.ChengHeldData

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real

inductive Tm : Type
  | var : ℕ → Tm
  | one : Tm
  | mul : Tm → Tm → Tm
  | inv : Tm → Tm

namespace Tm

@[expose] def evalM (σ : ℕ → MElt) : Tm → MElt
  | var i => σ i
  | one => oneM
  | mul a b => mulM (evalM σ a) (evalM σ b)
  | inv a => invM (evalM σ a)

@[expose] def pw (a : Tm) : ℕ → Tm
  | 0 => one
  | n + 1 => mul (pw a n) a

@[expose] def cj (a b : Tm) : Tm := mul (mul (inv b) a) b

@[expose] def cm (a b : Tm) : Tm := mul (mul (mul (inv a) (inv b)) a) b

@[expose] def prod : List Tm → Tm
  | [] => one
  | [a] => a
  | a :: l => mul a (prod l)

end Tm

open Tm

@[expose] def vt : Tm := var 0
@[expose] def vpi : Tm := var 1
@[expose] def vtau : Tm := var 2
@[expose] def vmu : Tm := var 3
@[expose] def vlam : Tm := var 4
@[expose] def vze : Tm := var 5
@[expose] def vxi : Tm := var 6

@[expose] def frM (α : ℕ) : ℕ → MElt
  | 0 => if α = 1 then (0, 0, 3) else (0, 0, 1)
  | 1 => if α = 0 then (4, 0, 3) else if α = 1 then (4, 0, 3) else (4, 0, 1)
  | 2 => if α = 0 then (8, 0, 3) else if α = 1 then (8, 0, 1) else (8, 0, 1)
  | 3 => (3, 0, 0)
  | 4 => (2, 0, 0)
  | 5 => (24, 0, 0)
  | _ => (16, 0, 0)

@[expose] def frame4Rels (α : ℕ) : List (Tm × Tm) :=
  [(pw vt 4, one), (pw vpi 2, one), (pw vtau 4, one), (pw vmu 2, one), (pw vlam 2, one),
    (pw vze 2, one), (pw vxi 2, one), (pw vtau 2, pw vt 2), (cm vpi vtau, one),
    (cj vpi vmu, mul (pw vt 2) vpi), (cj vpi vlam, mul (pw vt 2) vpi),
    (cj vpi vze, mul (pw vt 2) vpi), (cj vpi (mul vmu vlam), vpi), (cj vpi vxi, vpi),
    (cj vtau vxi, mul (pw vt 2) vtau), (cj vtau vlam, mul (pw vt 2) vtau),
    (cj vtau vze, mul (pw vt 2) vtau), (cm vtau vmu, one), (cm vmu vlam, one),
    (cm vze vxi, one), (cm vmu vxi, mul vpi vtau), (cm vmu vze, mul vt vpi),
    (cm vlam vxi, vtau), (cm vlam vze, mul (mul (mul vt (pw vt (2 * α))) vpi) vtau)]

@[expose] def frame2Rels : List (Tm × Tm) :=
  [(pw vt 2, one), (pw vpi 2, one), (pw vtau 2, one), (pw vmu 2, one), (pw vlam 2, one),
    (pw vze 2, one), (pw vxi 2, one),
    (mul vt vpi, mul vpi vt), (mul vt vtau, mul vtau vt), (mul vt vmu, mul vmu vt),
    (mul vt vlam, mul vlam vt), (mul vt vze, mul vze vt), (mul vt vxi, mul vxi vt),
    (mul vpi vtau, mul vtau vpi), (mul vpi vmu, mul vmu vpi), (mul vpi vlam, mul vlam vpi),
    (mul vtau vmu, mul vmu vtau), (mul vtau vlam, mul vlam vtau), (mul vmu vlam, mul vlam vmu),
    (mul vpi vze, mul vze vpi), (mul vpi vxi, mul vxi vpi), (mul vtau vze, mul vze vtau),
    (mul vtau vxi, mul vxi vtau), (mul vze vxi, mul vxi vze),
    (cm vmu vxi, mul vpi vtau), (cm vlam vxi, vtau), (cm vmu vze, mul vt vpi),
    (cm vlam vze, mul (mul vt vpi) vtau)]

@[expose] def actRels (α k : ℕ) : List (ℕ × Tm) :=
  if k = 0 then
    if α = 0 then
      [(0, vt), (1, vpi), (2, mul vpi vtau), (3, mul (pw vt 2) vlam), (4, mul (pw vt 2) vmu),
        (5, mul vze vxi), (6, vxi)]
    else
      [(0, inv vt), (1, vpi), (2, mul vpi vtau), (3, mul (pw vt 2) vlam),
        (4, mul (pw vt 2) vmu), (5, mul (mul (pw vt 2) vze) vxi), (6, vxi)]
  else if k = 1 then
    if α = 0 then
      [(0, inv vt), (1, vpi), (2, inv vtau), (3, mul (mul (pw vt 2) vze) vxi), (4, vze),
        (5, vlam), (6, mul (mul (pw vt 2) vmu) vlam)]
    else
      [(0, vt), (1, vpi), (2, vtau), (3, mul vze vxi), (4, vze), (5, vlam), (6, mul vmu vlam)]
  else
    if α = 0 then
      [(0, inv vt), (1, vpi), (2, mul vpi (inv vtau)), (3, mul (pw vt 2) vze),
        (4, mul vze vxi), (5, mul (pw vt 2) vmu), (6, mul (mul (pw vt 2) vmu) vlam)]
    else
      [(0, inv vt), (1, vpi), (2, mul vpi vtau), (3, mul (pw vt 2) vze),
        (4, mul (mul (pw vt 2) vze) vxi), (5, mul (pw vt 2) vmu), (6, mul vmu vlam)]

@[expose] def act2Rels (k : ℕ) : List (ℕ × Tm) :=
  if k = 0 then
    [(0, vt), (1, vpi), (2, mul vpi vtau), (3, vlam), (4, vmu), (5, mul vze vxi), (6, vxi)]
  else if k = 1 then
    [(0, vt), (1, vpi), (2, vtau), (3, mul vze vxi), (4, vze), (5, vlam), (6, mul vmu vlam)]
  else
    [(0, vt), (1, vpi), (2, mul vpi vtau), (3, vze), (4, mul vze vxi), (5, vmu),
      (6, mul vmu vlam)]

@[expose] def gRels (α : ℕ) : List (ℕ × Tm) :=
  if α = 0 then
    [(0, vt), (1, Tm.prod [vtau, vpi, pw vt 3]), (2, Tm.prod [vpi, vt]),
      (3, Tm.prod [vlam, vmu, pw vt 2]), (4, Tm.prod [vmu, pw vt 2]), (5, Tm.prod [vxi, vze]),
      (6, vze)]
  else if α = 1 then
    [(0, vt), (1, Tm.prod [vtau, vpi, vt]), (2, Tm.prod [vpi, vt]), (3, Tm.prod [vlam, vmu]),
      (4, Tm.prod [vmu, pw vt 2]), (5, Tm.prod [vxi, vze, pw vt 2]), (6, vze)]
  else
    [(0, vt), (1, Tm.prod [vtau, vpi, vt]), (2, Tm.prod [vpi, vt]), (3, Tm.prod [vlam, vmu]),
      (4, vmu), (5, Tm.prod [vxi, vze]), (6, vze)]

@[expose] def eqN2 (x y : MElt) : Bool := x.1 == y.1 && ((x.2.2 - y.2.2).val % 2 == 0)

@[expose] def relsOK (eqf : MElt → MElt → Bool) (σ : ℕ → MElt) (rels : List (Tm × Tm)) : Bool :=
  rels.all fun e => eqf (e.1.evalM σ) (e.2.evalM σ)

@[expose] def actOK (eqf : MElt → MElt → Bool) (σ : ℕ → MElt) (i : ℕ) (rels : List (ℕ × Tm)) :
    Bool :=
  rels.all fun e => eqf (betaRepM i (σ e.1)) (e.2.evalM σ)

@[expose] def kapOf (α : ℕ) : ZMod 4 × ZMod 4 := if α = 0 then (1, 2) else (1, 0)

@[expose] def frame4OK : Bool :=
  [0, 1].all fun α => relsOK (eqKM (kapOf α)) (frM α) (frame4Rels α)

@[expose] def act4OK : Bool :=
  [0, 1].all fun α => [0, 1, 2].all fun k =>
    actOK (eqKM (kapOf α)) (frM α) (k + 1) (actRels α k)

@[expose] def frame2OK : Bool := relsOK eqN2 (frM 2) frame2Rels

@[expose] def act2OK : Bool :=
  [0, 1, 2].all fun k => actOK eqN2 (frM 2) (k + 1) (act2Rels k)

@[expose] def frIdx : List ℕ := [4, 8, 3, 2, 24, 16]

@[expose] def frTg : List (List ℕ) := frIdx.map tg

@[noinline, expose] def genT0OK : Bool :=
  enumOK 42 (wordTabs frTg) (enumBFS 42 (wordTabs frTg) 64) &&
    (enumBFS 42 (wordTabs frTg) 64).tabs.size == 64

@[expose] def allPairs : List (ZMod 4 × ZMod 4) :=
  (List.finRange 4).flatMap fun a => (List.finRange 4).map fun b => ((a : ZMod 4), (b : ZMod 4))

@[expose] def mact (i : ℕ) (x : ZMod 4 × ZMod 4) : ZMod 4 × ZMod 4 :=
  (x.1 * ((alphaEntry i 64).2.1 : ZMod 4) + x.2 * ((alphaEntry i 65).2.1 : ZMod 4),
    x.1 * ((alphaEntry i 64).2.2.1 : ZMod 4) + x.2 * ((alphaEntry i 65).2.2.1 : ZMod 4))

@[expose] def kapStd : List (ZMod 4 × ZMod 4) := [(1, 2), (1, 0)]

@[expose] def twistOK : Bool :=
  kGensC.all fun κ => [0, 4, 5].any fun i => kapStd.any fun κs =>
    allPairs.all fun x => decide (inKC κ (mact i x).1 (mact i x).2 ↔ inKC κs x.1 x.2)

@[expose] def kappaFGOK : Bool :=
  kGensC.all fun κ => !(liftsK κ 1 || liftsK κ 2) || kapStd.contains κ

@[expose] def inN2 (ab : ZMod 4 × ZMod 4) (x : ZMod 4 × ZMod 4) : Bool :=
  (ab.1 * x.1 + ab.2 * x.2).val % 2 == 0

@[expose] def kap2Gens : List (ZMod 4 × ZMod 4) := [(1, 0), (0, 1), (1, 1)]

@[expose] def lifts2 (ab : ZMod 4 × ZMod 4) (i : ℕ) : Bool :=
  allPairs.all fun x => !inN2 ab x || inN2 ab (mact i x)

@[expose] def twist2OK : Bool :=
  kap2Gens.all fun ab => [0, 4, 5].any fun i =>
    allPairs.all fun x => inN2 ab (mact i x) == inN2 (0, 1) x

@[expose] def kappa2FGOK : Bool :=
  kap2Gens.all fun ab => !(lifts2 ab 1 || lifts2 ab 2) || ab == (0, 1)

@[noinline, expose] def commOK : Bool :=
  [4, 5].all fun i => comp 42 (repTab i) (repTab 3) == comp 42 (repTab 3) (repTab i)

@[expose] def gTrivialOK : Bool := allPairs.all fun x => mact 31 x == x

@[expose] def gActOK : Bool :=
  [0, 1].all (fun α => actOK (eqKM (kapOf α)) (frM α) 31 (gRels α)) &&
    actOK eqN2 (frM 2) 31 (gRels 2) && gTrivialOK

@[noinline, expose] def chCoverOK : Bool :=
  frame4OK && act4OK && frame2OK && act2OK && genT0OK && twistOK && kappaFGOK &&
    twist2OK && kappa2FGOK && commOK && gActOK

end CFSG.OddStandard.ChengHeldData
