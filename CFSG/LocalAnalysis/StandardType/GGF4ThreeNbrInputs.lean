module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplit
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.Open (IsElemAbelian)

@[expose] def GGF4ThreeMarking {G : Type} [Group G] (Bs K : Subgroup G) : Prop :=
  LargeEvenMarking ↥K (fun lab _ _ I _ θ => GGF4ThreeLabel 3 lab ∧
    Bs ≤ Subgroup.normalizer (K : Set G) ∧
    ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)

@[expose] def GGF4ThreeNbrRankInputStrong : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → GGNoTransvection 3 Bs → ∀ (y : G) (K : Subgroup G),
      GGNbr 3 B x D J y K → GGF4ThreeMarking Bs K →
        ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G), 3 ^ 4 ≤ Nat.card (ggGamma K hN).range

theorem ggF4ThreeNbrRankInput_of_strong (h : GGF4ThreeNbrRankInputStrong) :
    GGF4ThreeNbrRankInput := by
  intro G _ _ p B Bs x L D J hcfg hT hp y K hnb hM hN _
  subst hp
  exact h G B Bs x L D J hcfg hT y K hnb hM hN

@[expose] def GGF4ThreeSCTransvInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K + 1 →
    ∀ E : Subgroup ↥(adjointGroup .F4 K), IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3 →
      (∀ g ∈ Subgroup.centralizer (E : Set ↥(adjointGroup .F4 K)), g ^ 3 = 1 → g ∈ E) →
        ∃ φ ∈ ggInduced ⊤ E, GGIsTransvection 3 φ

@[expose] def GGF4ThreeSCCubeInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K + 1 →
    ∀ E : Subgroup ↥(adjointGroup .F4 K), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      (∀ g ∈ Subgroup.centralizer (E : Set ↥(adjointGroup .F4 K)), g ^ 3 = 1 → g ∈ E) →
        ∃ φ ∈ ggInduced ⊤ E, GGIsTransvection 3 φ

end CFSG.StandardType
