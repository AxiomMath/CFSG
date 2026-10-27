module

public import CFSG.LocalAnalysis.StandardType.GGFixSub
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylClauseFive
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylCompDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOtherTypeDet
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def ggFixDer {R : Type} [Group R] (x : MulAut R) : Subgroup R :=
  ⁅ggFixSub x, ggFixSub x⁆

theorem ggFixDer_map_mem {R : Type} [Group R] {x φ : MulAut R} (h : φ * x = x * φ) {g : R}
    (hg : g ∈ ggFixDer x) : φ g ∈ ggFixDer x := by
  have hC : (ggFixSub x).map (φ : R →* R) ≤ ggFixSub x := by
    rintro _ ⟨a, ha, rfl⟩
    change x (φ a) = φ a
    calc x (φ a) = (x * φ) a := rfl
      _ = (φ * x) a := by rw [h]
      _ = φ (x a) := rfl
      _ = φ a := by rw [show x a = a from ha]
  have h1 : (ggFixDer x).map (φ : R →* R) ≤ ggFixDer x := by
    unfold ggFixDer
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hC hC
  exact h1 ⟨g, hg, rfl⟩

@[expose] def GGFixGeom {R : Type} [Group R] (I : Set (MulAut R)) (x : MulAut R) {R₀ : Type}
    [Group R₀] (I₀ : Set (MulAut R₀)) (θ₀ : ggFixDer x ≃* R₀) : Prop :=
  (∀ φ ∈ I, ∀ hφ : φ * x = x * φ, ∃ φ₀ ∈ I₀, ∀ (g : R) (hg : g ∈ ggFixDer x),
      θ₀ ⟨φ g, ggFixDer_map_mem hφ hg⟩ = φ₀ (θ₀ ⟨g, hg⟩)) ∧
    (∀ φ ∈ I, φ * x = x * φ → (∀ g ∈ ggFixDer x, φ g = g) → φ = 1)

@[expose] def GGFixData (p r : ℕ) {R : Type} [Group R] (I : Set (MulAut R)) (x : MulAut R) :
    Prop :=
  ∃ (R₀ : Type) (_ : Group R₀) (I₀ : Set (MulAut R₀)) (θ₀ : ggFixDer x ≃* R₀),
    IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ GGFixGeom I x I₀ θ₀ ∧
      GGTorusLift p r R₀ ∧ GGTorusNoLine p r R₀ I₀

@[expose] def GGRawFieldFixStd (p : ℕ) (lab₀ : LargeEvenLabel) : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∀ f ∈ F, orderOf f = p →
      LargeEvenRawDatum lab₀ fun R₀ _ I₀ _ => IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧
        ∃ θ₀ : ggFixDer f ≃* R₀, GGFixGeom I f I₀ θ₀

@[expose] def GGRawFieldFix (p : ℕ) (lab₀ : LargeEvenLabel) : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∀ x ∈ Subgroup.closure (I ∪ F), x ∉ I → x ^ p = 1 →
      LargeEvenRawDatum lab₀ fun R₀ _ I₀ _ => IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧
        ∃ θ₀ : ggFixDer x ≃* R₀, GGFixGeom I x I₀ θ₀

@[expose] def GGFieldFixKnown (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
    LargeEvenLabelAll lab (GGRawFieldFixStd p ⟨lab.tag, lab.rank, lab.n / p⟩)

@[expose] def GGNbrWeylRowPlain (p r : ℕ) : LargeEvenRawCont :=
  fun R _ I _ => (∀ g : R, MulAut.conj g ∈ I) ∧ GGTorusLift p r R ∧
    (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGTorusNoLine p r R I)

@[expose] def GGFieldFixRowLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n - 1 ∧
    ((lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∨
      ((lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank) ∨
      (lab.tag = .D ∧ 4 ≤ lab.rank ∧ ¬ (lab.rank = 4 ∧ p = 3)) ∨
      (lab.tag = .twD ∧ 4 ≤ lab.rank) ∨ (lab.tag = .A ∧ 4 ≤ lab.rank) ∨
      (lab.tag = .E6 ∧ p ≠ 3))

@[expose] def ggFieldFixRank (lab : LargeEvenLabel) : ℕ :=
  match lab.tag with
  | .A => lab.rank - 1
  | .B => lab.rank
  | .C => lab.rank
  | .D => lab.rank
  | .twD => lab.rank - 1
  | .F4 => 4
  | .E6 => 6
  | .E7 => 7
  | .E8 => 8
  | _ => 0

@[expose] def GGFieldFixLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ lab.n ∧ GGFieldFixRowLabel p lab

@[expose] def GGFieldFixChevLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGFieldFixLabel p lab ∧ (lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8)

@[expose] def GGFieldFixSpLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGFieldFixLabel p lab ∧ (lab.tag = .B ∨ lab.tag = .C)

@[expose] def GGFieldFixOmegaPlusLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGFieldFixLabel p lab ∧ lab.tag = .D

@[expose] def GGFieldFixTwOmegaLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGFieldFixLabel p lab ∧ lab.tag = .twD

@[expose] def GGFieldFixLinearLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGFieldFixLabel p lab ∧ lab.tag = .A

@[expose] def GGFieldFixE6Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGFieldFixLabel p lab ∧ lab.tag = .E6

theorem GGFieldFixLabel.family {p : ℕ} {lab : LargeEvenLabel} (h : GGFieldFixLabel p lab) :
    GGFieldFixChevLabel p lab ∨ GGFieldFixSpLabel p lab ∨ GGFieldFixOmegaPlusLabel p lab ∨
      GGFieldFixTwOmegaLabel p lab ∨ GGFieldFixLinearLabel p lab ∨ GGFieldFixE6Label p lab := by
  rcases h.2.2 with h' | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩
  · exact Or.inl ⟨h, h'⟩
  · exact Or.inr (Or.inl ⟨h, h'⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, h'⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, h'⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, h'⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, h'⟩))))

end CFSG.StandardType

end
