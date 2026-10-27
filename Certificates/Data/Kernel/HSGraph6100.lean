module

public import Certificates.Data.Kernel.HSIdent

public section

namespace Certificates.Kernel.HSGraph6100

open CFSG.ComponentClassification.WittDesign CFSG.Monster.B.Classical.Plane
  Certificates.Kernel.HSIdent

@[expose] def rowAux (i : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => rowAux i n ||| (if modelAdjN i n then 2 ^ n else 0)

@[expose] def rowOf (i : Nat) : Nat := rowAux i 100

@[expose] def popK : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, x => if x = 0 then 0 else popK f (x &&& (x - 1)) + 1

@[expose] def srgPair (i j ri rj : Nat) : Bool :=
  if i = j then popK 101 ri == 22
  else if ri.testBit j then popK 101 (ri &&& rj) == 0
  else popK 101 (ri &&& rj) == 6

@[expose] def srgK (row : Nat → Nat) : Bool :=
  allBelow (fun i => allBelow (fun j => srgPair i j (row i) (row j)) 100) 100

@[expose] def distinctK (m : Nat → Nat) : Bool :=
  allBelow (fun k => allBelow (fun l => k == l || m k != m l) 77) 77

@[expose] def psiK (l : List Nat) : Bool :=
  allBelow (fun i => allBelow (fun j =>
    modelAdjN (l.getD i 0 % 100) (l.getD j 0 % 100) == modelAdjN i j) 100) 100

@[expose] def sigN (i : Nat) : Nat :=
  if i = 0 then 0
  else if i ≤ 22 then (sigmaFun ⟨(i - 1) % 22, Nat.mod_lt _ (by decide)⟩).val + 1
  else hexadMasks.idxOf (mask ((hexadList.getD (i - 23) hexad0).image sigmaFun)) + 23

@[expose] def sigK (s : Nat → Nat) : Bool :=
  allBelow (fun k => decide (23 ≤ s (k + 23)) && decide (s (k + 23) < 100) &&
    hexMask (s (k + 23) - 23) == mask ((hexadList.getD k hexad0).image sigmaFun)) 77

@[expose] def sigNF (s : Nat → Nat) (i : Fin 100) : Fin 100 := ⟨s i % 100, Nat.mod_lt _ (by decide)⟩

@[expose] def sigPerm (s : Nat → Nat) (h : ∀ i, sigNF s (sigNF s i) = i) : Equiv.Perm (Fin 100) where
  toFun := sigNF s
  invFun := sigNF s
  left_inv := h
  right_inv := h

end Certificates.Kernel.HSGraph6100
