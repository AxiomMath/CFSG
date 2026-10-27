module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchKillC
public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernelSylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Coord
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParLin
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CFSG.KC.SBCls

open CFSG.EvenSmallLie.OmegaEight.SpBranch

@[expose] noncomputable def strictT {α : Type} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

variable (mul : ℕ → ℕ → ℕ) (inv : ℕ → ℕ) (gens : List ℕ)

@[expose] noncomputable def bfsAdd (o w : ℕ) (acc : List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ) (g : ℕ) :
    List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ :=
  strictT (cconj mul inv g o) fun v =>
    if acc.2.2.testBit v then acc
    else strictT (mul g w) fun w' => strictT (acc.2.2 ||| 2 ^ v) fun M =>
      ((v, w') :: acc.1, (v, w') :: acc.2.1, M)

@[expose] noncomputable def bfsPop (o w : ℕ) (q : List (ℕ × ℕ))
    (acc : List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ) :
    List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ :=
  (fun a => (a.1, q, a.2.1, a.2.2)) (gens.foldl (bfsAdd mul inv o w) acc)

@[expose] noncomputable def bfsStep (st : List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ) :
    List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ :=
  match st.2.1 with
  | (o, w) :: q => bfsPop mul inv gens o w q (st.1, st.2.2.1, st.2.2.2)
  | [] =>
    match st.2.2.1.reverse with
    | (o, w) :: q => bfsPop mul inv gens o w q (st.1, [], st.2.2.2)
    | [] => st

@[expose] noncomputable def bfsRun (u : ℕ) : List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ :=
  (List.range 130).foldl (fun st _ => bfsStep mul inv gens st) ([(u, 0)], [(u, 0)], [], 2 ^ u)

@[expose] noncomputable def clsChk (N : ℕ) (r : ℕ × ℕ) : Bool :=
  (fun st : List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ =>
    decide (r.1 < N) && mul r.1 r.1 == 0 && r.1 != 0 && st.2.1.isEmpty && st.2.2.1.isEmpty &&
      st.1.length == r.2 && (st.1.all fun p => decide (r.1 ≤ p.1)) && orbOKM mul inv N r.1 st.1)
    (bfsRun mul inv gens r.1)

end CFSG.KC.SBCls

end
