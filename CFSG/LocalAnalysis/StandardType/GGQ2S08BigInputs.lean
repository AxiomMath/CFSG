module

public import CFSG.LocalAnalysis.StandardType.GGTBWNorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2S08BigLabel (lab : LargeEvenLabel) : Prop :=
  GGLabQTwo 3 lab ∧
    (lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD) ∧
    9 ≤ lab.rank

@[expose] def GGQ2TBWNormClassicalInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGQ2S08BigLabel lab →
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC 3 R I

@[expose] def GGQ2S08BigCenterInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGQ2S08BigLabel lab →
    LargeEvenLabelAll lab fun R _ _ _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Nat.card (Subgroup.center L') ∣ 3

@[expose] def GGQ2S08BigInnerPartInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting 3 B Bs x L D J →
    GGInnerDiagOnLab (fun p lab' => p = 3 ∧ GGQ2S08BigLabel lab') 3 Bs L →
    ∀ {lab : LargeEvenLabel}, LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = lab) →
      GGQ2S08BigLabel lab →
      ∀ M : GGQ2LDatum 3 Bs L x, M.ShapeA → GGQ2LabelWeyl lab M.coxeter →
        ∀ b ∈ Bs, (∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set G), b = l * c) → b ∈ L

theorem ggQ2s08_tbwNormInputOn_of_classical (h : GGQ2TBWNormClassicalInput) :
    GGTBWNormInputOn (fun p lab => p = 3 ∧ GGQ2S08BigLabel lab) := by
  refine ggTBWNormInputOn_of_labels ?_
  intro p lab _ hlab hS
  obtain ⟨rfl, hB⟩ := hS
  exact largeEvenLabelAll_wnorm_toLift (h lab hlab hB)

end CFSG.StandardType

end
