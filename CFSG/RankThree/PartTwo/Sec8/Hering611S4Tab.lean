module

public import CFSG.Assembly.Defs
public import CFSG.Sporadic.SmallOddCore.J3CheckInputs

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611.J3T

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

abbrev Gp : Type := Equiv.Perm (Fin 6156)

@[expose] def prodT (R : Array Table) (l : List ℕ) : Table :=
  l.foldl (fun T i => compT 6156 T R[i]!) (idT 6156)

@[expose] def prodG (Rg : ℕ → Gp) (l : List ℕ) : Gp := (l.map Rg).prod

@[expose] def Ksub (Rg : ℕ → Gp) (gi : List ℕ) : Subgroup Gp :=
  closure (Rg '' {r | r ∈ gi})

inductive TFact where
  | eqP (l₁ l₂ : List ℕ)
  | neP (l₁ l₂ : List ℕ)
  | memE (e : ℕ) (l : List ℕ)
  | inP (l : List ℕ)
  | notInP (l : List ℕ)
  | ordEq (i m : ℕ)
  deriving DecidableEq

@[expose] def idxOK (R : Array Table) (l : List ℕ) : Bool := l.all fun i => decide (i < R.size)

@[expose] def TFact.ok (R : Array Table) (Es : Array (Array Table)) : TFact → Bool
  | .eqP l₁ l₂ => idxOK R l₁ && idxOK R l₂ && tblEq 6156 (prodT R l₁) (prodT R l₂)
  | .neP l₁ l₂ => idxOK R l₁ && idxOK R l₂ && !tblEq 6156 (prodT R l₁) (prodT R l₂)
  | .memE e l => decide (e < Es.size) && idxOK R l && memT 6156 Es[e]! (prodT R l)
  | .inP l => idxOK R l && j3Sift (prodT R l)
  | .notInP l => idxOK R l && !j3Sift (prodT R l)
  | .ordEq i m => decide (i < R.size) && decide (0 < m) && ordTest 6156 m R[i]!

@[expose] noncomputable def TFact.sem (Rg : ℕ → Gp) (K : ℕ → Subgroup Gp) : TFact → Prop
  | .eqP l₁ l₂ => prodG Rg l₁ = prodG Rg l₂
  | .neP l₁ l₂ => prodG Rg l₁ ≠ prodG Rg l₂
  | .memE e l => prodG Rg l ∈ K e
  | .inP l => prodG Rg l ∈ j3P
  | .notInP l => prodG Rg l ∉ j3P
  | .ordEq i m => orderOf (Rg i) = m

inductive Cond where
  | comm (r : ℕ)
  | commM (w r : ℕ)
  | memConj (e r : ℕ)
  | memSelf (e : ℕ)
  | not (c : Cond)
  | and (c d : Cond)
  | imp (c d : Cond)
  deriving DecidableEq

@[expose] def Cond.wfB (nR nE : ℕ) : Cond → Bool
  | .comm r => decide (r < nR)
  | .commM w r => decide (w < nR) && decide (r < nR)
  | .memConj e r => decide (e < nE) && decide (r < nR)
  | .memSelf e => decide (e < nE)
  | .not c => c.wfB nR nE
  | .and c d => c.wfB nR nE && d.wfB nR nE
  | .imp c d => c.wfB nR nE && d.wfB nR nE

@[expose] def Cond.eval (R : Array Table) (Es : Array (Array Table)) (T Ti : Table) :
    Cond → Bool
  | .comm r => commTT 6156 T R[r]!
  | .commM w r => commTT 6156 (compT 6156 T R[w]!) R[r]!
  | .memConj e r => memT 6156 Es[e]! (compT 6156 (compT 6156 T R[r]!) Ti)
  | .memSelf e => memT 6156 Es[e]! T
  | .not c => !(c.eval R Es T Ti)
  | .and c d => c.eval R Es T Ti && d.eval R Es T Ti
  | .imp c d => !(c.eval R Es T Ti) || d.eval R Es T Ti

@[expose] noncomputable def Cond.sem (Rg : ℕ → Gp) (K : ℕ → Subgroup Gp) (x : Gp) : Cond → Prop
  | .comm r => x * Rg r = Rg r * x
  | .commM w r => (x * Rg w) * Rg r = Rg r * (x * Rg w)
  | .memConj e r => x * Rg r * x⁻¹ ∈ K e
  | .memSelf e => x ∈ K e
  | .not c => ¬ c.sem Rg K x
  | .and c d => c.sem Rg K x ∧ d.sem Rg K x
  | .imp c d => c.sem Rg K x → d.sem Rg K x

inductive TLoop where
  | allE (e : ℕ) (c : Cond)
  | countEq (e : ℕ) (c : Cond) (b : ℕ)
  | countLe (e : ℕ) (c : Cond) (b : ℕ)
  | exE (e : ℕ) (c : Cond)
  deriving DecidableEq

@[expose] def loopCount (R : Array Table) (Es : Array (Array Table)) (e : ℕ) (c : Cond) : ℕ :=
  ((List.range Es[e]!.size).filter fun k =>
    c.eval R Es (Es[e]!)[k]! (invT 6156 (Es[e]!)[k]!)).length

@[expose] def TLoop.ok (R : Array Table) (Es : Array (Array Table)) : TLoop → Bool
  | .allE e c => decide (e < Es.size) && c.wfB R.size Es.size &&
      decide (loopCount R Es e c = Es[e]!.size)
  | .countEq e c b => decide (e < Es.size) && c.wfB R.size Es.size &&
      decide (loopCount R Es e c = b)
  | .countLe e c b => decide (e < Es.size) && c.wfB R.size Es.size &&
      decide (loopCount R Es e c ≤ b)
  | .exE e c => decide (e < Es.size) && c.wfB R.size Es.size && decide (0 < loopCount R Es e c)

@[expose] noncomputable def TLoop.sem (Rg : ℕ → Gp) (K : ℕ → Subgroup Gp) : TLoop → Prop
  | .allE e c => ∀ x ∈ K e, c.sem Rg K x
  | .countEq e c b => Set.ncard {x | x ∈ K e ∧ c.sem Rg K x} = b
  | .countLe e c b => Set.ncard {x | x ∈ K e ∧ c.sem Rg K x} ≤ b
  | .exE e c => ∃ x ∈ K e, c.sem Rg K x

structure TData where
  prog : List Instr
  enums : List (List ℕ × ℕ)
  facts : List TFact
  loops : List TLoop
  fixedBelow : ℕ

structure TSem (initG Rg : ℕ → Gp) (D : TData) : Prop where
  fixed : ∀ r < D.fixedBelow, Rg r = initG r
  card : ∀ e (he : e < D.enums.length), Nat.card (Ksub Rg D.enums[e].1) = D.enums[e].2
  fact : ∀ f ∈ D.facts, f.sem Rg (fun e => Ksub Rg (D.enums[e]!).1)
  loop : ∀ l ∈ D.loops, l.sem Rg (fun e => Ksub Rg (D.enums[e]!).1)

theorem TSem.fact_get {initG Rg : ℕ → Gp} {D : TData} (h : TSem initG Rg D) (k : ℕ)
    (hk : k < D.facts.length) : D.facts[k].sem Rg (fun e => Ksub Rg (D.enums[e]!).1) :=
  h.fact _ (List.getElem_mem hk)

theorem TSem.loop_get {initG Rg : ℕ → Gp} {D : TData} (h : TSem initG Rg D) (k : ℕ)
    (hk : k < D.loops.length) : D.loops[k].sem Rg (fun e => Ksub Rg (D.enums[e]!).1) :=
  h.loop _ (List.getElem_mem hk)

end CFSG.RankThree.PartTwo.Sec8.Hering611.J3T
