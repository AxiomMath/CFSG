module

public import Certificates.Data.A5GL42

public section

open Matrix

namespace Certificates.S3x3GL42

open Certificates.A5GL42 (Mat4 Vec4)

@[expose] def aI : Mat4 := !![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,1]

@[expose] def bI : Mat4 := !![0,1,0,0; 1,1,0,0; 0,0,1,0; 0,0,0,1]

@[expose] def aII : Mat4 := !![0,1,0,0; 1,1,0,0; 0,0,0,1; 0,0,1,1]

@[expose] def bII : Mat4 := !![0,1,0,0; 1,1,0,0; 0,0,1,1; 0,0,1,0]

@[expose] def RelAB (a b : Mat4) : Prop :=
  a * a * a = 1 ∧ a ≠ 1 ∧ b * b * b = 1 ∧ b ≠ 1 ∧ a * b = b * a

@[expose] def RelC (a b c : Mat4) : Prop := c * c = 1 ∧ c * a = a * a * c ∧ c * b = b * c

@[expose] def Rel (a b c : Mat4) : Prop := RelAB a b ∧ RelC a b c

set_option synthInstance.maxSize 1024 in
instance (a b : Mat4) : Decidable (RelAB a b) := by unfold RelAB; infer_instance

set_option synthInstance.maxSize 1024 in
instance (a b c : Mat4) : Decidable (RelC a b c) := by unfold RelC; infer_instance

@[expose] def fixV (a : Mat4) : Finset Vec4 := Finset.univ.filter fun v => a *ᵥ v = v

@[expose] def NonSing (g : Mat4) : Prop := ∀ v : Vec4, g *ᵥ v = 0 → v = 0

instance (g : Mat4) : Decidable (NonSing g) := by unfold NonSing; infer_instance

@[expose] def CentFacts (a b c : Mat4) : Prop :=
  ∃ T : List Mat4, T.length ≤ 6 ∧
    (∀ g : Mat4, g * a = a * g → g * c = c * g → NonSing g → g ∈ T) ∧
    ∀ g ∈ T, g * g * g = 1 → g = 1 ∨ g = b ∨ g = b * b

@[expose] def TypeIFacts (a b c : Mat4) : Prop :=
  (fixV a).card = 4 ∧ (fixV b).card = 4 ∧ (∀ v ∈ fixV a, v ∈ fixV b → v = 0) ∧
    (∀ v ∈ fixV a, c *ᵥ v = v) ∧ ∀ u : Vec4, ∃ x ∈ fixV a, ∃ y ∈ fixV b, u = x + y

set_option synthInstance.maxSize 1024 in
instance (a b c : Mat4) : Decidable (TypeIFacts a b c) := by unfold TypeIFacts; infer_instance

@[expose] def Irr (a b c : Mat4) : Prop :=
  ∀ S : Finset Vec4, 0 ∈ S → (∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) →
    (∀ v ∈ S, a *ᵥ v ∈ S ∧ b *ᵥ v ∈ S ∧ c *ᵥ v ∈ S) → (∃ v ∈ S, v ≠ 0) → S = Finset.univ

@[expose] def TypeIIFacts (a b c : Mat4) : Prop :=
  (∀ v : Vec4, a *ᵥ v = v → v = 0) ∧ (∀ v : Vec4, b *ᵥ v = v → v = 0) ∧ Irr a b c

@[expose] def Classify : Prop :=
  ∀ a b c : Mat4, Rel a b c →
    ∃ g : Mat4, g.det = 1 ∧
      ((g * a = aI * g ∧ g * b = bI * g) ∨ (g * a = aII * g ∧ g * b = bII * g))

@[expose] def StdI : Prop :=
  ∀ c : Mat4, Rel aI bI c → CentFacts aI bI c ∧ TypeIFacts aI bI c

@[expose] def StdII : Prop :=
  ∀ c : Mat4, Rel aII bII c → CentFacts aII bII c ∧ TypeIIFacts aII bII c

structure Facts : Prop where
  classify : Classify
  stdI : StdI
  stdII : StdII

end Certificates.S3x3GL42
