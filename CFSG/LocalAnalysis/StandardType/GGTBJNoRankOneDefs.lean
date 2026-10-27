module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGFixSub
public import CFSG.LocalAnalysis.StandardType.GGResLeaf

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTBJNoRankOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (n : ℕ),
    GGConfig p B Bs x L D J → 2 ≤ n →
      ¬ GGHasLabel (⟨.A, 1, n⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)

@[expose] def GGRankOneSetup {R : Type} [Group R] (I : Set (MulAut R)) {L' : Type} [Group L']
    (ψ : L' →* R) (p : ℕ) (e : MulAut L') (J : Subgroup L') (n : ℕ) (a : MulAut L') : Prop :=
  p.Prime ∧ p ≠ 2 ∧ e ≠ 1 ∧ e ^ p = 1 ∧ (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) ∧
    IsComponentOf J (ggFixSub e) ∧ 2 ≤ n ∧
    GGHasLabel (⟨.A, 1, n⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) ∧
    a * e = e * a ∧ (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) ∧ (∀ j ∈ J, a j ∈ J) ∧
    ¬ ∃ y : ↥J ⧸ Subgroup.center ↥J, ∀ j j' : ↥J, a (j : L') = (j' : L') →
      (j' : ↥J ⧸ Subgroup.center ↥J) = y * (j : ↥J ⧸ Subgroup.center ↥J) * y⁻¹

@[expose] def GGSU6DiagInvertedAt {R : Type} [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ t ∈ I, t ^ 3 = 1 → t ∉ LargeEvenInnSet R →
    ∀ U : Subgroup (MulAut R), U ≠ ⊥ → IsPGroup 2 U → U ⊓ Subgroup.closure I = ⊥ →
      ¬ ∀ u ∈ U, t * u * t⁻¹ ∈ U

@[expose] def GGSU6DiagInvertedKnown : Prop :=
  ∀ f : ℕ, 3 ∣ 2 ^ f + 1 →
    LargeEvenLabelAll (⟨.twA, 5, f⟩ : LargeEvenLabel) fun R _ I _ => GGSU6DiagInvertedAt I

end CFSG.StandardType

end
