module

public import CFSG.Quasithin.Background.F3Paths
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.Map

public section

namespace CFSG.Quasithin.Asc94

open scoped Pointwise

universe u v u' v'

section Paths

variable {V : Type u}

@[expose] def IsPath (Γ : SimpleGraph V) (p : List V) : Prop := p ≠ [] ∧ p.IsChain Γ.Adj

@[expose] def IsCycle (Γ : SimpleGraph V) (p : List V) : Prop :=
  IsPath Γ p ∧ p.head? = p.getLast?

@[expose] def IsNGon (Γ : SimpleGraph V) (n : ℕ) (p : List V) : Prop :=
  IsCycle Γ p ∧ p.length = n + 1 ∧ p.dropLast.Nodup

@[expose] def IsRotation (c d : List V) : Prop :=
  ∃ (l₁ l₂ : List V) (w : V), c = l₁ ++ l₂ ∧ l₁.getLast? = some w ∧ d = w :: (l₂ ++ l₁.tail)

@[expose] def rotRev (C : Set (List V)) : Set (List V) :=
  {d | ∃ c ∈ C, IsRotation c d ∨ IsRotation c.reverse d}

inductive ElemMove (Γ : SimpleGraph V) (C : Set (List V)) : List V → List V → Prop
  | backDel (l₁ l₂ : List V) (w v : V) (h : Γ.Adj w v) :
      ElemMove Γ C (l₁ ++ w :: v :: w :: l₂) (l₁ ++ w :: l₂)
  | backIns (l₁ l₂ : List V) (w v : V) (h : Γ.Adj w v) :
      ElemMove Γ C (l₁ ++ w :: l₂) (l₁ ++ w :: v :: w :: l₂)
  | cycIns (l₁ l₂ c : List V) (w : V) (hc : c ∈ rotRev C) (h₁ : c.head? = some w)
      (h₂ : c.getLast? = some w) : ElemMove Γ C (l₁ ++ w :: l₂) (l₁ ++ c ++ l₂)
  | cycDel (l₁ l₂ c : List V) (w : V) (hc : c ∈ rotRev C) (h₁ : c.head? = some w)
      (h₂ : c.getLast? = some w) : ElemMove Γ C (l₁ ++ c ++ l₂) (l₁ ++ w :: l₂)

abbrev Moves (Γ : SimpleGraph V) (C : Set (List V)) : List V → List V → Prop :=
  Relation.ReflTransGen (ElemMove Γ C)

@[expose] def InClosure (Γ : SimpleGraph V) (C : Set (List V)) (c : List V) : Prop :=
  ∃ w : V, Moves Γ C c [w]

@[expose] def Triangulable (Γ : SimpleGraph V) : Prop :=
  ∀ c : List V, IsCycle Γ c → InClosure Γ {p | IsNGon Γ 3 p} c

end Paths

section Systems

variable {G : Type v} [Group G] {X : Type u} [MulAction G X]

structure IsUniquenessSystem (Γ : SimpleGraph X) (I : Subgroup G) (ΓI : Γ.Subgraph) (x y : X) :
    Prop where
  graphAction : GraphAction G Γ
  trans : ∀ w : X, ∃ g : G, g • x = w
  edgeSet_eq : Γ.edgeSet = Set.range fun g : G => s(g • x, g • y)
  swap : ∃ t ∈ I, t • x = y ∧ t • y = x
  verts_eq : ΓI.verts = (fun i : G => i • x) '' (I : Set G)
  edgeSet_I_eq : ΓI.edgeSet = (fun i : G => s(i • x, i • y)) '' (I : Set G)
  sup_eq_top : MulAction.stabilizer G x ⊔ I = ⊤
  stab_eq : MulAction.stabilizer G x =
    MulAction.stabilizer G x ⊓ MulAction.stabilizer G y ⊔ I ⊓ MulAction.stabilizer G x
  I_eq : I = I ⊓ MulAction.stabilizer G x ⊔ I ⊓ MulAction.stabilizer G ({x, y} : Set X)

@[expose] def IsSubCycle {Γ : SimpleGraph X} (ΓI : Γ.Subgraph) (c : List X) : Prop :=
  IsCycle ΓI.spanningCoe c ∧ ∀ w ∈ c, w ∈ ΓI.verts

variable (G) in
@[expose] def IsBase (Γ : SimpleGraph X) (ΓI : Γ.Subgraph) : Prop :=
  ∀ c : List X, IsCycle Γ c →
    InClosure Γ {d | ∃ (c₀ : List X) (g : G), IsSubCycle ΓI c₀ ∧ d = c₀.map (g • ·)} c

variable {Gb : Type v'} [Group Gb] {Xb : Type u'} [MulAction Gb Xb]

structure IsSimilarity (I : Subgroup G) (x y : X) (Ib : Subgroup Gb) (xb yb : Xb)
    (β : MulAction.stabilizer G x ≃* MulAction.stabilizer Gb xb) (ζ : I ≃* Ib) : Prop where
  map_stab : ((MulAction.stabilizer G x).subgroupOf I).map ζ.toMonoidHom =
    (MulAction.stabilizer Gb xb).subgroupOf Ib
  eq_on : ∀ (i : I) (h : (i : G) ∈ MulAction.stabilizer G x), (β ⟨i, h⟩ : Gb) = ζ i
  map_stab_two : ((MulAction.stabilizer G y).subgroupOf (MulAction.stabilizer G x)).map
      β.toMonoidHom = (MulAction.stabilizer Gb yb).subgroupOf (MulAction.stabilizer Gb xb)
  map_edge : ((MulAction.stabilizer G ({x, y} : Set X)).subgroupOf I).map ζ.toMonoidHom =
    (MulAction.stabilizer Gb ({xb, yb} : Set Xb)).subgroupOf Ib

@[expose] def IsEquivalence (I : Subgroup G) (x y : X) (Ib : Subgroup Gb) (xb yb : Xb)
    (β : MulAction.stabilizer G x ≃* MulAction.stabilizer Gb xb) (ζ : I ≃* Ib) : Prop :=
  IsSimilarity I x y Ib xb yb β ζ ∧
    ∃ t : I, (t : G) • x = y ∧ (t : G) • y = x ∧
      ∀ b c : MulAction.stabilizer G x, (b : G) • y = y → (c : G) = (t : G)⁻¹ * b * t →
        (β c : Gb) = (ζ t : Gb)⁻¹ * β b * ζ t

end Systems

end CFSG.Quasithin.Asc94
