module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Open
open Matrix

@[expose] def fischerMatrixGroup {ι F : Type*} [Fintype ι] [DecidableEq ι] [CommRing F]
    (P : Matrix ι ι F → Prop) : Subgroup (GL ι F) :=
  Subgroup.closure {g | P (g : Matrix ι ι F)}

@[expose] def fischerTransvections {ι F : Type*} [Fintype ι] [DecidableEq ι] [CommRing F]
    (β : (ι → F) → (ι → F) → F) (P : (ι → F) → Prop) : Set (GL ι F) :=
  {g | ∃ v, P v ∧ ∀ x, (g : Matrix ι ι F) *ᵥ x = x + β x v • v}

@[expose] def fischerLinearModel {G : Type*} [Group G] (D : Set G) {ι F : Type*} [Fintype ι]
    [DecidableEq ι] [CommRing F] (H : Subgroup (GL ι F)) (T : Set (GL ι F)) : Prop :=
  ∃ φ : G ≃* H, ∀ g : G, g ∈ D ↔ ((φ g : GL ι F) ∈ T)

@[expose] def fischerCentralQuotientModel {G : Type*} [Group G] (D : Set G) {ι F : Type*} [Fintype ι]
    [DecidableEq ι] [CommRing F] (H : Subgroup (GL ι F)) (T : Set (GL ι F)) : Prop :=
  ∃ φ : G ≃* H ⧸ Subgroup.center H,
    ∀ g : G, g ∈ D ↔
      ∃ h : H, (h : GL ι F) ∈ T ∧ φ g = (QuotientGroup.mk h : H ⧸ Subgroup.center H)

@[expose] noncomputable def fischerHermitianF4 (m : ℕ) (x y : Fin m → GaloisField 2 2) : GaloisField 2 2 :=
  ∑ i, x i * y i ^ 2

end CFSG.Open
