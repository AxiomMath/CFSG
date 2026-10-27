module

public import CFSG.LocalAnalysis.StandardType.GGNbrG2ASidesDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def ggNbrLSideRank (lab : LargeEvenLabel) : ℕ :=
  match lab.tag with
  | .A | .twA | .B | .C | .D | .twD => lab.rank
  | .E6 | .twE6 => 6
  | .E7 => 7
  | .E8 => 8
  | .F4 | .triD4 | .twF4 | .twF4der => 4
  | .G2 | .G2der | .B2der | .twB2 => 2

@[expose] def GGNbrLSideLargeRank (lab : LargeEvenLabel) : Prop :=
  (Even lab.n ∧ 6 ≤ ggNbrLSideRank lab) ∨ (Odd lab.n ∧ 12 ≤ ggNbrLSideRank lab)

inductive GGNbrLSideFamily : Type
  | linear | unitary | symplectic | orthogonal | excUntwisted | excTwisted | suzukiRee

@[expose] def ggNbrLSideFamilyOf (lab : LargeEvenLabel) : GGNbrLSideFamily :=
  match lab.tag with
  | .A => .linear
  | .twA => .unitary
  | .B | .C | .B2der => .symplectic
  | .D => if lab.rank = 3 then .linear else .orthogonal
  | .twD => if lab.rank = 2 then .linear else if lab.rank = 3 then .unitary else .orthogonal
  | .G2 | .G2der | .F4 | .E6 | .E7 | .E8 => .excUntwisted
  | .twE6 | .triD4 => .excTwisted
  | .twB2 | .twF4 | .twF4der => .suzukiRee

@[expose] def GGNbrLSideInduces {R : Type} [Group R] (ψ : MulAut R) (J : Subgroup R)
    (α : MulAut (↥J ⧸ Subgroup.center ↥J)) : Prop :=
  ∀ j : ↥J, ∃ j' : ↥J, (j' : R) = ψ (j : R) ∧ α (QuotientGroup.mk j) = QuotientGroup.mk j'

@[expose] def GGNbrLSideDich (lab : LargeEvenLabel) {R : Type} [Group R] (I : Set (MulAut R)) :
    Prop :=
  ∀ φ ∈ I, ∀ ψ ∈ I, φ ≠ 1 → φ ^ 3 = 1 → ψ ^ 3 = 1 → φ * ψ = ψ * φ →
    ∀ J : Subgroup R, CFSG.Open.IsComponentOf J (fixSubgroup φ) →
      ∀ Q : ℕ, 4 ≤ Q → 3 ∣ Q - 1 →
        (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = Q ∧
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃* projectiveSL 3 F)) →
        ∀ α : MulAut (↥J ⧸ Subgroup.center ↥J), GGNbrLSideInduces ψ J α →
          GGInnDiagPSL3 Q (↥J ⧸ Subgroup.center ↥J) α ∨ GGNbrLSideLargeRank lab

@[expose] def GGNbrLSideRSAt (lab : LargeEvenLabel) : Prop :=
  LargeEvenInLambda2 lab → LargeEvenSplit 3 lab →
    LargeEvenLabelAll lab fun R _ I _ => GGNbrLSideDich lab I

@[expose] def GGNbrLSideRSFamily (f : GGNbrLSideFamily) : Prop :=
  ∀ lab : LargeEvenLabel, ggNbrLSideFamilyOf lab = f → GGNbrLSideRSAt lab

@[expose] def GGNbrLSideRS : Prop :=
  ∀ lab : LargeEvenLabel, GGNbrLSideRSAt lab

@[expose] def GGNbrLSide35At (lab : LargeEvenLabel) : Prop :=
  GGNbrLSideLargeRank lab →
    ∀ (L : Type) [Group L] [Finite L],
      LargeEvenMarkingLegacy L (fun lab' _ _ _ _ _ => lab' = lab ∧ LargeEvenSplit 3 lab') →
        ∃ E U : Subgroup L, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 ∧ IsPGroup 2 U ∧
          U ≠ ⊥ ∧ E ≤ Subgroup.normalizer (U : Set L)

@[expose] def GGNbrLSide35 : Prop :=
  ∀ lab : LargeEvenLabel, GGNbrLSide35At lab

theorem ggNbrLSideRS_of_families (h : ∀ f, GGNbrLSideRSFamily f) : GGNbrLSideRS :=
  fun lab => h _ lab rfl

theorem ggNbrLSideDich_of_largeRank {lab : LargeEvenLabel} {R : Type} [Group R]
    (I : Set (MulAut R)) (h : GGNbrLSideLargeRank lab) : GGNbrLSideDich lab I :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => Or.inr h

theorem ggNbrLSide_marking_of_config {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) :
    LargeEvenMarkingLegacy L (fun lab _ _ I _ θ => LargeEvenSplit 3 lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
  obtain ⟨⟨-, -, -, -, -, -, -, hstd⟩, -, -⟩ := hcfg
  exact hstd.1

end CFSG.StandardType

end
