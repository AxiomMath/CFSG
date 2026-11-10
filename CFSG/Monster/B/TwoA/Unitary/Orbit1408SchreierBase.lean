
module

public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Base
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408Base
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Bridge
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs
public import CFSG.Monster.B.TwoA.Unitary.OrbitInputs
public import CFSG.Monster.B.TwoA.Unitary.WStabInputs
public import CFSG.Monster.B.TwoA.Unitary.Stab891Inputs
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Inputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census

attribute [local instance] wLeftAction

structure UsigIdxAct
    (N : ℕ) where
  f : Usig → Fin N → Fin N
  mul : ∀ a b x, f (a * b) x = f b (f a x)
  one : ∀ x, f 1 x = x

namespace UsigIdxAct

variable {N : ℕ} (A : UsigIdxAct N)

theorem inv_f (a : Usig) (x : Fin N) : A.f a⁻¹ (A.f a x) = x := by
  rw [← A.mul, mul_inv_cancel, A.one]

theorem f_inv (a : Usig) (x : Fin N) : A.f a (A.f a⁻¹ x) = x := by
  rw [← A.mul, inv_mul_cancel, A.one]

def partStab (part : Array ℕ) : Subgroup Usig where
  carrier := {u | ∀ x : Fin N, part[(A.f u x : ℕ)]! = part[(x : ℕ)]!}
  one_mem' x := by rw [A.one]
  mul_mem' {a b} ha hb x := by
    have ha' : ∀ x : Fin N, part[(A.f a x : ℕ)]! = part[(x : ℕ)]! := ha
    have hb' : ∀ x : Fin N, part[(A.f b x : ℕ)]! = part[(x : ℕ)]! := hb
    rw [A.mul, hb', ha']
  inv_mem' {a} ha x := by
    have ha' : ∀ x : Fin N, part[(A.f a x : ℕ)]! = part[(x : ℕ)]! := ha
    have h := ha' (A.f a⁻¹ x)
    rw [A.f_inv] at h
    exact h.symm

end UsigIdxAct

abbrev tauEdge (i k : ℕ) : ℕ := (tauCert.edges[i]!)[k]!

def transArr (gen : Array (Array ℕ)) (N : ℕ) : Array (Array ℕ) :=
  (List.range 1408).foldl (fun acc i => acc.push (if i = 0 then (List.range N).toArray else
    (acc[tauPar i]!).map fun x => (gen[tauLab i]!)[x]!)) #[]

def invPermArr (p : Array ℕ) : Array ℕ :=
  (List.range p.size).foldl (fun acc x => acc.set! p[x]! x) (Array.replicate p.size 0)

def treeOK (gen T I : Array (Array ℕ)) (N : ℕ) : Bool :=
  (List.range N).all (fun x => (T[0]!)[x]! == x) &&
  (List.range 1408).all fun i => (List.range N).all fun x =>
    decide ((T[i]!)[x]! < N) && decide ((I[i]!)[x]! < N) && (T[i]!)[(I[i]!)[x]!]! == x &&
      (i == 0 || (T[i]!)[x]! == (gen[tauLab i]!)[(T[tauPar i]!)[x]!]!)

def schreierOK (gen T I : Array (Array ℕ)) (part : Array ℕ) (N : ℕ) : Bool :=
  (List.range 1408).all fun i => (List.range 17).all fun k => (List.range N).all fun x =>
    part[(I[tauEdge i k]!)[(gen[k]!)[(T[i]!)[x]!]!]!]! == part[x]!

def selAct (gen T I : Array (Array ℕ)) (sel : Array (ℕ × ℕ)) (r x : ℕ) : ℕ :=
  (I[tauEdge sel[r]!.1 sel[r]!.2]!)[(gen[sel[r]!.2]!)[(T[sel[r]!.1]!)[x]!]!]!

section Tree

variable {N : ℕ} {gen T I : Array (Array ℕ)}

theorem treeOK_zero (h : treeOK gen T I N = true) {x : ℕ} (hx : x < N) : (T[0]!)[x]! = x := by
  simp only [treeOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h.1 x hx

theorem treeOK_spec (h : treeOK gen T I N = true) {i x : ℕ} (hi : i < 1408) (hx : x < N) :
    (T[i]!)[x]! < N ∧ (I[i]!)[x]! < N ∧ (T[i]!)[(I[i]!)[x]!]! = x ∧
      (0 < i → (T[i]!)[x]! = (gen[tauLab i]!)[(T[tauPar i]!)[x]!]!) := by
  simp only [treeOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h.2 i hi x hx
  refine ⟨h1, h2, h3, fun h0 => ?_⟩
  rcases h4 with h4 | h4
  · omega
  · exact h4

end Tree

end CFSG.Monster.B.TwoA.Unitary
