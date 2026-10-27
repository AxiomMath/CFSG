module

public import Certificates.Data.Kernel.PermCent.CV
public import CFSG.GH74.KGroups.Checks
public import Mathlib

public section

namespace CFSG.Certificates.Kernel.PkCV.KGrp

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups

variable {n : Nat} [Small n]

@[expose] noncomputable def orderIsC (g : CV n) (m : Nat) : Bool :=
  powOneC g m && (List.range m).all fun k => k == 0 || !powOneC g k

@[expose] noncomputable def pairInvC (ws : List (List Bool × ℕ)) (a b : CV n) : Bool :=
  ws.all fun wk => orderIsC (evalW a b wk.1) wk.2

@[expose] noncomputable def centTrivC (L : List (CV n)) (a b : CV n) : Bool :=
  L.all fun σ => !(eq22C σ a a σ && eq22C σ b b σ) || decide (σ = 1)

@[expose] noncomputable def normC (QP : RawSchreierDatum n) (gens : List (CV n)) (a b : CV n) :
    Bool :=
  gens.all fun σ => siftC QP (σ * a * σ⁻¹) 0 && siftC QP (σ * b * σ⁻¹) 0

@[expose] noncomputable def pairCountC (L : List (CV n)) (oa ob : ℕ) (ws : List (List Bool × ℕ)) :
    ℕ :=
  (((L.filter (fun g => orderIsC g oa)) ×ˢ (L.filter (fun g => orderIsC g ob))).filter
    (fun q => pairInvC ws q.1 q.2)).length

@[expose] noncomputable def inner3C (LA : List (CV n)) (QP : RawSchreierDatum n) : Bool :=
  LA.all fun g => bif powOneC g 3 then siftC QP g 0 else true

@[expose] noncomputable def centL (L : List (CV n)) (τ : CV n) : List (CV n) :=
  L.filter fun g => eq22C g τ τ g

@[expose] noncomputable def e9atC (C : List (CV n)) : Bool :=
  C.all fun X => C.all fun Y =>
    bif !decide (X = 1) && powOneC X 3 && powOneC Y 3 && eq22C X Y Y X then
      decide (Y = 1) || decide (Y = X) || decide (Y = X ^ 2) else true

@[expose] noncomputable def e9freeC (L : List (CV n)) : Bool :=
  L.all fun τ => bif powOneC τ 2 && !decide (τ = 1) then e9atC (centL L τ) else true

@[expose] noncomputable def e9allC (L : List (CV n)) : Bool :=
  (L.filter fun g => !decide (g = 1) && powOneC g 3).all fun X =>
    (L.filter fun g => powOneC g 3 && eq22C g X X g).all fun Y =>
      decide (Y = 1) || decide (Y = X) || decide (Y = X ^ 2)

@[expose] noncomputable def e27atC (X : CV n) (C : List (CV n)) : Bool :=
  C.all fun Y => C.all fun Z =>
    !eq22C Y Z Z Y || decide (Y ∈ ([1, X, X ^ 2] : List (CV n))) || decide (Z ∈ pow3list X Y)

@[expose] noncomputable def e27freeC (L : List (CV n)) : Bool :=
  L.all fun X => bif powOneC X 3 && !decide (X = 1) then
    e27atC X (L.filter fun g => powOneC g 3 && eq22C g X X g) else true

@[expose] noncomputable def e27at3 (L : List (CV n)) (X : CV n) : Bool :=
  bif powOneC X 3 && !decide (X = 1) then
    e27atC X ((L.filter fun g => powOneC g 3).filter fun g => eq22C g X X g) else true

@[expose] noncomputable def e27freeF (L : List (CV n)) : Bool := L.all (e27at3 L)

@[expose] noncomputable def e27blk (L : List (CV n)) (c j : Nat) : Bool :=
  ((L.drop (j * c)).take c).all (e27at3 L)

@[expose] noncomputable def pairAll (Lx Ly : List (CV n)) (ws : List (List Bool × ℕ)) (c : ℕ) :
    Bool :=
  Lx.all fun x => (Ly.filter fun y => pairInvC ws x y).length == c

@[expose] noncomputable def cent3atC (x : CV n) (C : List (CV n)) : Bool :=
  C.all fun y =>
    bif powOneC y 3 && !decide (y ∈ ([1, x, x ^ 2] : List (CV n))) then
      C.all fun k => bif eq22C k y y k then decide (k ∈ pow3list x y) else true
    else true

@[expose] noncomputable def cent3C (L : List (CV n)) : Bool :=
  L.all fun x => bif powOneC x 3 && !decide (x = 1) then cent3atC x (centL L x) else true

@[expose] noncomputable def solvC (LA LP : List (CV n)) (goods : List ℕ) : Bool :=
  LA.all fun τ => bif powOneC τ 2 && !decide (τ = 1) then
    decide ((centL LP τ).length ∈ goods) else true

end CFSG.Certificates.Kernel.PkCV.KGrp

end
