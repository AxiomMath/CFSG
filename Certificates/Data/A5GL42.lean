module

public import Mathlib

public section

open Matrix

namespace Certificates.A5GL42

abbrev Mat4 : Type := Matrix (Fin 4) (Fin 4) (ZMod 2)

abbrev Vec4 : Type := Fin 4 → ZMod 2

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

instance decidableForallVec4 (p : Vec4 → Prop) [DecidablePred p] : Decidable (∀ v : Vec4, p v) :=
  decidable_of_iff (∀ v ∈ (Finset.univ : Finset Vec4), p v) (by simp)

instance decidableExistsVec4 (p : Vec4 → Prop) [DecidablePred p] : Decidable (∃ v : Vec4, p v) :=
  decidable_of_iff (∃ v ∈ (Finset.univ : Finset Vec4), p v) (by simp)

@[expose] def ofCode (c : ℕ) : Mat4 :=
  Matrix.of fun i j => if c.testBit (4 * i.val + j.val) then 1 else 0

@[expose] def aN : Mat4 := !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]

@[expose] def bN : Mat4 := !![0,1,0,0; 1,1,0,0; 0,1,1,1; 1,1,1,0]

@[expose] def aO : Mat4 := !![1,1,1,1; 0,1,0,0; 0,0,0,1; 0,0,1,0]

@[expose] def bO : Mat4 := !![0,0,0,1; 1,0,0,0; 0,0,1,0; 0,1,0,0]

@[expose, irreducible] def codesN : List ℕ := [
  5064, 5083, 5097, 5114, 8580, 8599, 8613, 8630, 12876, 12895, 12909, 12926, 19506, 19582,
  19638, 19706, 24370, 24429, 24471, 24520, 27954, 27999, 28036, 28137, 32306, 32332, 32421,
  32475, 33825, 33901, 33957, 34025, 38689, 38751, 38838, 38856, 42273, 42366, 42372, 42459,
  46625, 46668, 46743, 46842, 51219, 51295, 51351, 51419, 56083, 56190, 56229, 56264, 59667,
  59757, 59780, 59898, 64019, 64076, 64182, 64233]

@[expose, irreducible] def codesO : List ℕ := [
  4680, 4751, 4852, 5167, 5250, 5368, 6180, 6223, 6386, 7976, 8002, 8068, 8527, 8580, 8696, 9240,
  9359, 9457, 10271, 10305, 10484, 12052, 12104, 12161, 16680, 16783, 16882, 16927, 17025, 17144,
  18450, 18479, 18673, 20248, 20257, 20354, 33071, 33090, 33268, 33300, 33359, 33521, 33823,
  33825, 34034, 36626, 36644, 36673, 61732, 61768, 61826, 61976, 62017, 62084, 62482, 62504,
  62593, 63508, 63521, 63554]

@[expose, irreducible] def HN : Finset Mat4 := (codesN.map ofCode).toFinset

@[expose, irreducible] def HO : Finset Mat4 := (codesO.map ofCode).toFinset

@[expose] def fixSet (A : Finset Mat4) : Finset Vec4 :=
  Finset.univ.filter fun v => ∀ a ∈ A, a *ᵥ v = v

@[expose] def commSet (A : Finset Mat4) (S : Finset Vec4) : Finset Vec4 :=
  (A ×ˢ S).image fun p => p.2 - p.1 *ᵥ p.2

@[expose] def vecOfCode (c : ℕ) : Vec4 := fun i => if c.testBit i.val then 1 else 0

@[expose, irreducible] def subspaceCodes : List (List ℕ) := [
  [0], [0, 1], [0, 2], [0, 3], [0, 4], [0, 5], [0, 6], [0, 7], [0, 8], [0, 9], [0, 10], [0, 11],
  [0, 12], [0, 13], [0, 14], [0, 15], [0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 1, 8, 9],
  [0, 1, 10, 11], [0, 1, 12, 13], [0, 1, 14, 15], [0, 2, 4, 6], [0, 2, 5, 7], [0, 2, 8, 10],
  [0, 2, 9, 11], [0, 2, 12, 14], [0, 2, 13, 15], [0, 3, 4, 7], [0, 3, 5, 6], [0, 3, 8, 11],
  [0, 3, 9, 10], [0, 3, 12, 15], [0, 3, 13, 14], [0, 4, 8, 12], [0, 4, 9, 13], [0, 4, 10, 14],
  [0, 4, 11, 15], [0, 5, 8, 13], [0, 5, 9, 12], [0, 5, 10, 15], [0, 5, 11, 14], [0, 6, 8, 14],
  [0, 6, 9, 15], [0, 6, 10, 12], [0, 6, 11, 13], [0, 7, 8, 15], [0, 7, 9, 14], [0, 7, 10, 13],
  [0, 7, 11, 12], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 8, 9, 10, 11],
  [0, 1, 2, 3, 12, 13, 14, 15], [0, 1, 4, 5, 8, 9, 12, 13], [0, 1, 4, 5, 10, 11, 14, 15],
  [0, 1, 6, 7, 8, 9, 14, 15], [0, 1, 6, 7, 10, 11, 12, 13], [0, 2, 4, 6, 8, 10, 12, 14],
  [0, 2, 4, 6, 9, 11, 13, 15], [0, 2, 5, 7, 8, 10, 13, 15], [0, 2, 5, 7, 9, 11, 12, 14],
  [0, 3, 4, 7, 8, 11, 12, 15], [0, 3, 4, 7, 9, 10, 13, 14], [0, 3, 5, 6, 8, 11, 13, 14],
  [0, 3, 5, 6, 9, 10, 12, 15], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]

@[expose, irreducible] def subspaces : Finset (Finset Vec4) :=
  (subspaceCodes.map fun l => (l.map vecOfCode).toFinset).toFinset

@[expose] def SubspacesComplete : Prop :=
  ∀ W : Finset Vec4, 0 ∈ W → (∀ x ∈ W, ∀ y ∈ W, x + y ∈ W) → W ∈ subspaces

set_option synthInstance.maxSize 1024 in
instance : Decidable SubspacesComplete :=
  decidable_of_iff
    (∀ W ∈ (Finset.univ : Finset (Finset Vec4)),
      0 ∈ W → (∀ x ∈ W, ∀ y ∈ W, x + y ∈ W) → W ∈ subspaces) (by simp [SubspacesComplete])

@[expose] def invSubspaces (B : Finset Mat4) : Finset (Finset Vec4) :=
  subspaces.filter fun W => ∀ h ∈ B, ∀ w ∈ W, h *ᵥ w ∈ W

@[expose] def klein (x y : Mat4) : Finset Mat4 := {1, x, y, x * y}

abbrev IsKlein (x y : Mat4) : Prop :=
  x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y ∧ x * x = 1 ∧ y * y = 1 ∧ x * y = y * x

@[expose] def kleinGroups (H : Finset Mat4) : Finset (Finset Mat4) :=
  ((H ×ˢ H).filter fun p => IsKlein p.1 p.2).image fun p => klein p.1 p.2

@[expose] def normSet (H A : Finset Mat4) : Finset Mat4 :=
  H.filter fun h => ∀ a ∈ A, ∃ a' ∈ A, ∀ v : Vec4, h *ᵥ (a *ᵥ v) = a' *ᵥ (h *ᵥ v)

abbrev IsMulSet (A : Finset Mat4) : Prop :=
  1 ∈ A ∧ ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A

abbrev Offender (A : Finset Mat4) : Prop :=
  (∃ a ∈ A, a ≠ 1) ∧
    (∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ v : Vec4, (v - a₁ *ᵥ v) - a₂ *ᵥ (v - a₁ *ᵥ v) = 0) ∧
    16 ≤ (fixSet A).card * A.card

@[expose] def Classify : Prop :=
  ∀ a b : Mat4, a * a = 1 → a ≠ 1 → b ^ 3 = 1 → (a * b) ^ 5 = 1 →
    ∃ g : Mat4, g.det = 1 ∧
      ((g * a = aN * g ∧ g * b = bN * g) ∨ (g * a = aO * g ∧ g * b = bO * g))

@[expose] def GroupFacts (H : Finset Mat4) : Prop :=
  1 ∈ H ∧ (∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) ∧ (∀ x ∈ H, ∃ y ∈ H, x * y = 1) ∧ H.card = 60 ∧
    (∀ x ∈ H, x * x * x * x = 1 → x * x = 1) ∧ invSubspaces H = {{0}, Finset.univ}

set_option synthInstance.maxSize 1024 in
instance (H : Finset Mat4) : Decidable (GroupFacts H) := by unfold GroupFacts; infer_instance

@[expose] def NatSpan (A : Finset Mat4) (F : Finset Vec4) : Prop :=
  0 ∈ F ∧ (∀ u ∈ F, ∀ w ∈ F, u + w ∈ F) ∧ F.card = 4 ∧ F = fixSet A ∧
    ∀ a ∈ A, a ≠ 1 → ∀ v : Vec4, a *ᵥ v = v → v ∈ F

set_option synthInstance.maxSize 1024 in
instance (A : Finset Mat4) (F : Finset Vec4) : Decidable (NatSpan A F) := by
  unfold NatSpan; infer_instance

@[expose] def NatLattice (H A : Finset Mat4) (F : Finset Vec4) : Prop :=
  invSubspaces (normSet H A) = {{0}, F, Finset.univ} ∧
    ∀ A' ∈ A.powerset, IsMulSet A' → Offender A' → A' = A

set_option synthInstance.maxSize 1024 in
instance (H A : Finset Mat4) (F : Finset Vec4) : Decidable (NatLattice H A F) := by
  unfold NatLattice; infer_instance

@[expose] def NatFacts (H A : Finset Mat4) (F : Finset Vec4) : Prop :=
  NatSpan A F ∧ NatLattice H A F

instance (H A : Finset Mat4) (F : Finset Vec4) : Decidable (NatFacts H A F) := by
  unfold NatFacts; infer_instance

@[expose] def OrthSpan (A : Finset Mat4) (F₂ F₁ : Finset Vec4) : Prop :=
  0 ∈ F₂ ∧ (∀ u ∈ F₂, ∀ w ∈ F₂, u + w ∈ F₂) ∧ F₂.card = 8 ∧
  0 ∈ F₁ ∧ (∀ u ∈ F₁, ∀ w ∈ F₁, u + w ∈ F₁) ∧ F₁.card = 2 ∧ F₁ = fixSet A

set_option synthInstance.maxSize 1024 in
instance (A : Finset Mat4) (F₂ F₁ : Finset Vec4) : Decidable (OrthSpan A F₂ F₁) := by
  unfold OrthSpan; infer_instance

@[expose] def OrthLattice (H A : Finset Mat4) (F₂ F₁ : Finset Vec4) : Prop :=
  invSubspaces (normSet H A) = {{0}, F₁, F₂, Finset.univ} ∧
  (∀ d ∈ normSet H A, d ≠ 1 → d * d * d = 1 → ∀ f ∈ F₂, f - d *ᵥ f ∈ F₁ → f ∈ F₁) ∧
  ∀ A' ∈ A.powerset, IsMulSet A' → ¬ Offender A'

set_option synthInstance.maxSize 4096 in
instance (H A : Finset Mat4) (F₂ F₁ : Finset Vec4) : Decidable (OrthLattice H A F₂ F₁) := by
  unfold OrthLattice; infer_instance

@[expose] def OrthFacts (H A : Finset Mat4) (F₂ F₁ : Finset Vec4) : Prop :=
  OrthSpan A F₂ F₁ ∧ OrthLattice H A F₂ F₁

instance (H A : Finset Mat4) (F₂ F₁ : Finset Vec4) : Decidable (OrthFacts H A F₂ F₁) := by
  unfold OrthFacts; infer_instance

@[expose] def FixN : Prop :=
  ∀ h ∈ HN, h ≠ 1 → h * h * h = 1 → ∀ v : Vec4, h *ᵥ v = v → v = 0

set_option synthInstance.maxSize 1024 in
instance : Decidable FixN := by unfold FixN; infer_instance

@[expose] def FixO : Prop :=
  ∀ h ∈ HO, h ≠ 1 → h * h * h = 1 → ∃ v : Vec4, v ≠ 0 ∧ h *ᵥ v = v

set_option synthInstance.maxSize 1024 in
instance : Decidable FixO := by unfold FixO; infer_instance

@[expose] def KleinN : Prop :=
  ∀ A ∈ kleinGroups HN, NatFacts HN A (commSet A Finset.univ)

set_option synthInstance.maxSize 1024 in
instance : Decidable KleinN := by unfold KleinN; infer_instance

@[expose] def KleinO : Prop :=
  ∀ A ∈ kleinGroups HO, OrthFacts HO A (commSet A Finset.univ) (commSet A (commSet A Finset.univ))

set_option synthInstance.maxSize 1024 in
instance : Decidable KleinO := by unfold KleinO; infer_instance

structure Facts : Prop where
  subspaces_complete : SubspacesComplete
  classify : Classify
  groupN : GroupFacts HN
  groupO : GroupFacts HO
  gens : aN ∈ HN ∧ bN ∈ HN ∧ aO ∈ HO ∧ bO ∈ HO
  fixN : FixN
  fixO : FixO
  kleinN : KleinN
  kleinO : KleinO

end Certificates.A5GL42
