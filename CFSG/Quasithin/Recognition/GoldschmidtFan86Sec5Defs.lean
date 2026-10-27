module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4RankDefs
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TSlide

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Cen (S : Set G) : Set G := {z | z ∈ S ∧ ∀ h ∈ S, h * z = z * h}

namespace Line

@[expose] def fixIdx (ℓ : Line Γ) (g : G) : Set ℤ := {i | g • ℓ.vert i = ℓ.vert i}

@[expose] def edgeStab (ℓ : Line Γ) (i : ℤ) : Subgroup G :=
  MulAction.stabilizer G (ℓ.vert i) ⊓ MulAction.stabilizer G (ℓ.vert (i + 1))

open scoped Classical in
@[expose] noncomputable def edgeCirc (ℓ : Line Γ) (i : ℤ) : Set G :=
  if valence Γ (ℓ.vert i) = 5 then Gcirc Γ G (ℓ.vert i) (ℓ.vert (i + 1))
  else Gcirc Γ G (ℓ.vert (i + 1)) (ℓ.vert i)

@[expose] def Zc (ℓ : Line Γ) : Set G :=
  {z | z * z = 1 ∧ ∃ i, z ∈ Cen (ℓ.edgeCirc i)}

@[expose] def ZZ (ℓ : Line Γ) : Set G :=
  {z | z * z = 1 ∧ ∃ i, z ∈ Cen (ℓ.edgeStab (G := G) i : Set G)}

@[expose] def IsCoreWith (ℓ : Line Γ) (P : ℤ → Prop) (z : G) (a b : ℤ) : Prop :=
  a < b ∧ (∀ i, a ≤ i → i ≤ b → i ∈ ℓ.fixIdx z) ∧ (∀ i, a ≤ i → i < b → P i) ∧
    ¬ (a - 1 ∈ ℓ.fixIdx z ∧ P (a - 1)) ∧ ¬ (b ∈ ℓ.fixIdx z ∧ P b)

@[expose] def IsCoreC (ℓ : Line Γ) (z : G) (a b : ℤ) : Prop :=
  ℓ.IsCoreWith (fun i => z ∈ Cen (ℓ.edgeCirc i)) z a b

@[expose] def IsCore (ℓ : Line Γ) (z : G) (a b : ℤ) : Prop :=
  ℓ.IsCoreWith (fun i => z ∈ Cen (ℓ.edgeStab (G := G) i : Set G)) z a b

structure IsCoreFix (ℓ : Line Γ) (z : G) (a b tL tR : ℤ) : Prop where
  fix : ∀ i, i ∈ ℓ.fixIdx z ↔ tL ≤ i ∧ i ≤ tR
  core : ℓ.IsCore z a b

structure IsCoreCFix (ℓ : Line Γ) (z : G) (a b tL tR : ℤ) : Prop where
  fix : ∀ i, i ∈ ℓ.fixIdx z ↔ tL ≤ i ∧ i ≤ tR
  core : ℓ.IsCoreC z a b

structure InPos (ℓ : Line Γ) (z z' : G) (a b tL tR a' b' tL' tR' : ℤ) : Prop where
  left : ℓ.IsCoreCFix z a b tL tR
  right : ℓ.IsCoreCFix z' a' b' tL' tR'
  pos : ∃ i j : ℤ, (i = 0 ∨ i = 1) ∧ (j = 0 ∨ j = 1) ∧ tR = a' - i ∧ tL' = b + j

structure InPerfectPos (ℓ : Line Γ) (z z' : G) (a b tL tR a' b' tL' tR' : ℤ) : Prop where
  left : ℓ.IsCoreCFix z a b tL tR
  right : ℓ.IsCoreCFix z' a' b' tL' tR'
  pos_left : tR = a'
  pos_right : tL' = b

end Line

@[expose] def Xi (i : ℕ) (T : Track Γ G) : Prop :=
  match i with
  | 1 => InPiStar T
  | 2 => T.HasReflections
  | 3 => HasLenTwoReflection Γ G T
  | _ => False

@[expose] def XiI (i : ℕ) (T : Track Γ G) : Prop :=
  Xi i T ∧ ∀ j : ℕ, 1 ≤ j → j < i → ¬ ∃ T' : Track Γ G, Xi j T'

@[expose] def InXi (T : Track Γ G) : Prop := ∃ i : ℕ, XiI i T

@[expose] def Equiv3 (G : Type*) [Group G] [MulAction G V] (α δ : V) : Prop :=
  ∃ g : G, g • α = δ

@[expose] def Cinv (G : Type*) [Group G] [MulAction G V] (δ : V) : Set G :=
  {w | w ≠ 1 ∧ w * w = 1 ∧ w ∈ Cen (MulAction.stabilizer G δ : Set G)}

@[expose] def Arc.deltaL {k : ℕ} (γ : Arc Γ k) : Set V :=
  Γ.neighborSet (γ.vert 0) \ {γ.vert 1}

@[expose] def Arc.GcircL (G : Type*) [Group G] [MulAction G V] {k : ℕ} (γ : Arc Γ k) : Set G :=
  {g | g ∈ γ.stab G ∧ g * g ∈ fixSet G (Arc.deltaL γ)}

end CFSG.Quasithin.Fan86
