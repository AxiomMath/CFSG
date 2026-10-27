module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Reflect
public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Fix

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V : Type*} (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V]

@[expose] noncomputable def valence (v : V) : ℕ := Nat.card (Γ.neighborSet v)

@[expose] def nbrStab (v : V) : Subgroup G := fixSet G (Γ.neighborSet v)

@[expose] def ballStab (n : ℕ) (v : V) : Subgroup G := fixSet G {w | Γ.dist v w ≤ n}

variable {Γ G}

theorem mem_nbrStab {v : V} {g : G} : g ∈ nbrStab Γ G v ↔ ∀ w, Γ.Adj v w → g • w = w := Iff.rfl

theorem mem_ballStab {n : ℕ} {v : V} {g : G} :
    g ∈ ballStab Γ G n v ↔ ∀ w, Γ.dist v w ≤ n → g • w = w := Iff.rfl

variable (Γ G)

@[expose] def RightSingular (x : ℕ → V) (i k : ℕ) : Prop :=
  ∃ w, Γ.Adj (x k) w ∧ w ≠ x (k - 1) ∧ ∀ g ∈ stabRange G x i k, g • w = w

@[expose] def LeftSingular (x : ℕ → V) (i k : ℕ) : Prop :=
  ∃ w, Γ.Adj (x i) w ∧ w ≠ x (i + 1) ∧ ∀ g ∈ stabRange G x i k, g • w = w

@[expose] def RightTransitive (x : ℕ → V) (i k : ℕ) : Prop :=
  ∀ a b, Γ.Adj (x k) a → a ≠ x (k - 1) → Γ.Adj (x k) b → b ≠ x (k - 1) →
    ∃ g ∈ stabRange G x i k, g • a = b

@[expose] def LeftTransitive (x : ℕ → V) (i k : ℕ) : Prop :=
  ∀ a b, Γ.Adj (x i) a → a ≠ x (i + 1) → Γ.Adj (x i) b → b ≠ x (i + 1) →
    ∃ g ∈ stabRange G x i k, g • a = b

@[expose] def HasRightSingular (k : ℕ) : Prop :=
  ∃ P : Arc Γ k, RightSingular Γ G P.vert 0 k

@[expose] def SingLe (n : ℕ) : Prop := ∃ k, 1 ≤ k ∧ k ≤ n ∧ HasRightSingular Γ G k

@[expose] def SingGe (n : ℕ) : Prop := ∀ k, 1 ≤ k → k < n → ¬ HasRightSingular Γ G k

@[expose] def TransGe (n : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k < n → ∀ P : Arc Γ k, RightTransitive Γ G P.vert 0 k ∧ LeftTransitive Γ G P.vert 0 k

@[expose] def LineSingLe (ℓ : Line Γ) (n : ℕ) : Prop :=
  ∃ (k : ℕ) (a : ℤ), 1 ≤ k ∧ k ≤ n ∧
    (RightSingular Γ G (ℓ.arc a k).vert 0 k ∨ LeftSingular Γ G (ℓ.arc a k).vert 0 k)

@[expose] def PClosed (v : V) : Prop :=
  ∀ x ∈ MulAction.stabilizer G v, orderOf x = valence Γ v →
    ∀ g ∈ MulAction.stabilizer G v, g * x * g⁻¹ ∈ Subgroup.zpowers x

@[expose] def Gcirc (α β : V) : Set G :=
  {g | g ∈ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β ∧ g * g ∈ nbrStab Γ G α}

@[expose] def HasLenTwoReflection (T : Track Γ G) : Prop :=
  ∃ (k : ℤ) (f : G), IsLenTwoReflection T.line k f

variable {Γ G}

theorem singGe_succ_iff (n : ℕ) : SingGe Γ G (n + 1) ↔ ¬ SingLe Γ G n := by
  unfold SingGe SingLe
  constructor
  · rintro h ⟨k, hk1, hk2, hk⟩
    exact h k hk1 (by omega) hk
  · intro h k hk1 hk2 hk
    exact h ⟨k, hk1, by omega, hk⟩

end CFSG.Quasithin.Fan86
