module

public import CFSG.LieType.Chevalley.WeylRoots

public noncomputable section

namespace CFSG.StandardType.GGK0LC

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def hr : (τ : Tag) → Fin τ.rank → ℕ
  | .G2 => ![2, 3]
  | .F4 => ![2, 3, 4, 2]
  | .D4 => ![1, 1, 2, 1]
  | .E6 => ![1, 2, 2, 3, 2, 1]
  | .E7 => ![2, 2, 3, 4, 3, 2, 1]
  | .E8 => ![2, 3, 4, 6, 5, 4, 3, 2]

@[expose] def theta (τ : Tag) : Fin τ.rank → ℤ := fun i => (hr τ i : ℤ)

structure KacPt (τ : Tag) where
  p : ℕ
  p_pos : 0 < p
  s : Fin τ.rank → ℕ
  s0 : ℕ
  weight : s0 + ∑ i, hr τ i * s i = p

abbrev AffPair (τ : Tag) : Type := (Fin τ.rank → ℤ) × ℤ

@[expose] def AffPos {τ : Tag} (a : AffPair τ) : Prop := 0 < a.2 ∨ (a.2 = 0 ∧ 0 < height a.1)

@[expose] def AffNeg {τ : Tag} (a : AffPair τ) : Prop := a.2 < 0 ∨ (a.2 = 0 ∧ height a.1 < 0)

@[expose] def simpleAff {τ : Tag} (j : Fin τ.rank) : AffPair τ := (Pi.single j 1, 0)

@[expose] def extAff (τ : Tag) : AffPair τ := (-theta τ, 1)

namespace KacPt

variable {τ : Tag}

@[expose] def lam (K : KacPt τ) (v : Fin τ.rank → ℤ) : ℤ := ∑ i, (K.s i : ℤ) * v i

@[expose] def stab (K : KacPt τ) : Subgroup (WeylGroup τ) where
  carrier := {w | ∀ v : Fin τ.rank → ℤ, (K.p : ℤ) ∣ K.lam (w • v) - K.lam v}
  one_mem' v := by simp
  mul_mem' {w w'} hw hw' v := by
    have h1 := hw (w' • v)
    have h2 := hw' v
    have : K.lam ((w * w') • v) - K.lam v =
        (K.lam (w • (w' • v)) - K.lam (w' • v)) + (K.lam (w' • v) - K.lam v) := by
      rw [mul_smul]; ring
    rw [this]
    exact dvd_add h1 h2
  inv_mem' {w} hw v := by
    have h1 := hw (w⁻¹ • v)
    rw [smul_inv_smul] at h1
    have : K.lam (w⁻¹ • v) - K.lam v = -(K.lam v - K.lam (w⁻¹ • v)) := by ring
    rw [this]
    exact (dvd_neg).2 h1

@[expose] def kerRoots (K : KacPt τ) : Set (Fin τ.rank → ℤ) :=
  {α | IsRoot τ α ∧ (K.p : ℤ) ∣ K.lam α}

@[expose] def refl (K : KacPt τ) : Subgroup (WeylGroup τ) :=
  Subgroup.closure {r | ∃ (w : WeylGroup τ) (i : Fin τ.rank),
    w • (Pi.single i 1 : Fin τ.rank → ℤ) ∈ K.kerRoots ∧ r = w * simple τ i * w⁻¹}

@[expose] def shift (K : KacPt τ) (z : WeylGroup τ) (γ : Fin τ.rank → ℤ) : ℤ :=
  (K.lam γ - K.lam (z • γ)) / (K.p : ℤ)

@[expose] def act (K : KacPt τ) (z : WeylGroup τ) (a : AffPair τ) : AffPair τ :=
  (z • a.1, a.2 + K.shift z a.1)

@[expose] def inv (K : KacPt τ) (z : WeylGroup τ) : Set (AffPair τ) :=
  {a | IsRoot τ a.1 ∧ AffPos a ∧ AffNeg (K.act z a)}

end KacPt

@[expose] def KacBox (τ : Tag) : Prop :=
  (∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ i, -(hr τ i : ℤ) ≤ γ i ∧ γ i ≤ hr τ i) ∧
    IsRoot τ (theta τ) ∧ ∀ i, 0 < hr τ i

@[expose] def KacCentred (τ : Tag) (d : ℕ) : Prop :=
  ∃ B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ,
    B * (τ.cartan).transpose = (d : ℤ) • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) ∧
      ∀ i, hr τ i = 1 → ∃ k, ¬ ((d : ℤ) ∣ B k i)

end CFSG.StandardType.GGK0LC

end
