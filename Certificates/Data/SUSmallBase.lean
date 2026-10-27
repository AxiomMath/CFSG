module

public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.StandardType.HdRo7SU.Small

abbrev SMV (m : ℕ) : Type := Fin m → ZMod 3

abbrev SMGL (m : ℕ) : Type := SMV m ≃ₗ[ZMod 3] SMV m

@[expose] def SMIsPerm {m : ℕ} (g : SMGL m) : Prop :=
  ∃ σ : Equiv.Perm (Fin m), ∀ (v : SMV m) (i : Fin m), (g v) i = v (σ.symm i)

@[expose] def smOnes (m : ℕ) : SMV m := fun _ => 1

@[expose] def smDot {m : ℕ} (w v : SMV m) : ZMod 3 := ∑ i, w i * v i

@[expose] noncomputable def smDual {m : ℕ} (w : SMV m) : Module.Dual (ZMod 3) (SMV m) :=
  ∑ i, w i • (LinearMap.proj i : SMV m →ₗ[ZMod 3] ZMod 3)

@[expose] def SMRefl {m : ℕ} (r : SMGL m) (u : SMV m) (φ : Module.Dual (ZMod 3) (SMV m)) : Prop :=
  φ u = 2 ∧ ∀ v, r v = v - φ v • u

@[expose] def smRefSet {m : ℕ} (H : Subgroup (SMGL m)) : Set (SMV m × SMV m) :=
  {p | ∃ r ∈ H, SMRefl r p.1 (smDual p.2)}

@[expose] def SMTClass {m : ℕ} (p : SMV m × SMV m) : Prop :=
  ∃ (i j : Fin m) (s : ZMod 3), i ≠ j ∧ (s = 1 ∨ s = -1) ∧
    p.1 = s • (Pi.single i 1 - Pi.single j 1) ∧ p.2 = s • (Pi.single i 1 - Pi.single j 1)

@[expose] def SMClass {m : ℕ} (p q : SMV m × SMV m) : Prop :=
  ∃ (π : Equiv.Perm (Fin m)) (s : ZMod 3), (s = 1 ∨ s = -1) ∧
    ∀ i, p.1 i = s * q.1 (π i) ∧ p.2 i = s * q.2 (π i)

@[expose] def SMRCl {m : ℕ} (R : Set (SMV m × SMV m)) : Prop :=
  (∀ p ∈ R, smDot p.2 p.1 = 2) ∧
  (∀ p ∈ R, ∀ π : Equiv.Perm (Fin m), ((fun i => p.1 (π i), fun i => p.2 (π i)) : SMV m × SMV m) ∈ R) ∧
  (∀ p ∈ R, ((-p.1, -p.2) : SMV m × SMV m) ∈ R) ∧
  (∀ p ∈ R, ∀ q ∈ R,
    ((q.1 - smDot p.2 q.1 • p.1, q.2 - smDot q.2 p.1 • p.2) : SMV m × SMV m) ∈ R) ∧
  (∀ p : SMV m × SMV m, SMTClass p → p ∈ R) ∧
  (∀ p ∈ R, ∀ q ∈ R, smDot p.2 q.1 = 0 ↔ smDot q.2 p.1 = 0) ∧
  (∀ p ∈ R, ∀ q ∈ R, p.1 = q.1 → p.2 = q.2) ∧
  (∀ p ∈ R, ∀ q ∈ R, p.2 = q.2 → p.1 = q.1) ∧
  (∀ p ∈ R, ∑ i, p.2 i = 0 → SMTClass p)

@[expose] def sm7cx : SMV 7 × SMV 7 := (![2, 2, 2, 2, 2, 2, 2], ![1, 1, 1, 1, 1, 1, 1])
@[expose] def sm7A7a : SMV 7 × SMV 7 := (![1, 2, 2, 2, 2, 2, 2], ![2, 0, 0, 0, 0, 0, 0])
@[expose] def sm7A7b : SMV 7 × SMV 7 := (![0, 0, 0, 0, 0, 0, 2], ![2, 2, 2, 2, 2, 2, 1])
@[expose] def sm7D7a : SMV 7 × SMV 7 := (![0, 0, 2, 2, 2, 2, 2], ![0, 0, 2, 2, 2, 2, 2])
@[expose] def sm7D7b : SMV 7 × SMV 7 := (![0, 0, 0, 0, 0, 2, 2], ![0, 0, 0, 0, 0, 2, 2])
@[expose] def sm7B7a : SMV 7 × SMV 7 := (![1, 2, 2, 2, 2, 2, 2], ![2, 1, 1, 1, 1, 1, 1])
@[expose] def sm7B7b : SMV 7 × SMV 7 := (![0, 0, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 0, 0, 1])
@[expose] def sm7E7a : SMV 7 × SMV 7 := (![1, 1, 1, 1, 2, 2, 2], ![2, 2, 2, 2, 0, 0, 0])
@[expose] def sm7E7b : SMV 7 × SMV 7 := (![0, 0, 0, 2, 2, 2, 2], ![2, 2, 2, 1, 1, 1, 1])
@[expose] def sm8cx : SMV 8 × SMV 8 := (![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1])
@[expose] def sm8A8a : SMV 8 × SMV 8 := (![1, 1, 1, 1, 1, 1, 1, 2], ![0, 0, 0, 0, 0, 0, 0, 1])
@[expose] def sm8A8b : SMV 8 × SMV 8 := (![1, 1, 1, 1, 1, 1, 1, 2], ![2, 2, 2, 2, 2, 2, 2, 0])
@[expose] def sm8D8a : SMV 8 × SMV 8 := (![1, 1, 1, 1, 1, 1, 2, 2], ![1, 1, 1, 1, 1, 1, 2, 2])
@[expose] def sm8D8b : SMV 8 × SMV 8 := (![0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 1])
@[expose] def sm8B8a : SMV 8 × SMV 8 := (![0, 2, 2, 2, 2, 2, 2, 2], ![0, 1, 1, 1, 1, 1, 1, 1])
@[expose] def sm8B8b : SMV 8 × SMV 8 := (![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 2])

@[expose] def smAllowed7 : List (List (SMV 7 × SMV 7)) :=
  [[], [sm7B7b, sm7D7b], [sm7D7b], [sm7D7a], [sm7A7b], [sm7E7b, sm7A7a], [sm7A7a],
    [sm7A7b, sm7E7a], [sm7cx], [sm7B7a, sm7D7a], [sm7A7b, sm7A7a, sm7cx]]

@[expose] def smAllowed8 : List (List (SMV 8 × SMV 8)) :=
  [[], [sm8B8b, sm8D8b], [sm8D8b], [sm8B8a, sm8D8a], [sm8A8a], [sm8A8b], [sm8cx], [sm8D8a]]

end CFSG.StandardType.HdRo7SU.Small
