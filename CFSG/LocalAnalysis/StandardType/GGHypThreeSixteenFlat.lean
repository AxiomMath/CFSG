module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerRest
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

section HypFlat

variable {W : Type} [Group W]

@[expose] def GGHypRestIIIFlat [Finite W] (p : ℕ) (H E : Subgroup W) : Prop :=
  (∀ C : Subgroup (GGHypQuot H), IsComponentOf C ⊤ →
    ggHypImage H E ≤ Subgroup.normalizer (C : Set (GGHypQuot H)) ∧
      LargeEvenMarking ↥C (fun lab _ _ I _ θ => GGChevStTag lab ∧
        ∀ e ∈ ggHypImage H E, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : GGHypQuot H) = e⁻¹ * l * e) φ)) ∧
  (commutator ↥(ggHypLayer H) = ⊤ ∨ LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) = ⊥) ∧
  (∃ k : ℕ, derivedSeries ↥H k ≤ (ggHypLayer H).subgroupOf H) ∧
  (LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) = ⊥ →
    pRank p (⊤ : Subgroup ↥(CFSG.generalizedFitting W)) = 1 ∨
      ∃ (Kh : Type) (_ : Group Kh) (_ : Finite Kh) (π : Kh →* ↥(CFSG.generalizedFitting W)),
        Function.Surjective π ∧ π.ker ≤ Subgroup.center Kh ∧ IsCyclic ↥π.ker ∧
          IsPGroup p ↥π.ker ∧ commutator Kh = ⊤ ∧ pRank p (⊤ : Subgroup Kh) = 2)

@[expose] def GGHypRestIVFlat [Finite W] (p : ℕ) (E : Subgroup W) : Prop :=
  ∀ x ∈ E, x ≠ 1 → ∀ C : Subgroup W, LargeEvenPComponent p (Subgroup.centralizer {x}) C →
    LargeEvenMarking
      ↥((C.subgroupOf (Subgroup.centralizer {x})).map
        (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥(Subgroup.centralizer ({x} : Set W)))))
      (fun _ _ _ _ _ _ => True)

@[expose] def GGHypThreeSixteenRestFlat [Finite W] (p : ℕ) (H E : Subgroup W) : Prop :=
  GGHypRestII W ∧
  (∀ C : Subgroup (GGHypQuot H), IsComponentOf C ⊤ →
    ggHypImage H E ≤ Subgroup.normalizer (C : Set (GGHypQuot H)) ∧
      LargeEvenMarking ↥C (fun lab _ _ I _ θ => GGChevStTag lab ∧
        ∀ e ∈ ggHypImage H E, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : GGHypQuot H) = e⁻¹ * l * e) φ)) ∧
  (commutator ↥(ggHypLayer H) = ⊤ ∨ LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) = ⊥) ∧
  (∃ k : ℕ, derivedSeries ↥H k ≤ (ggHypLayer H).subgroupOf H) ∧
  (LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) = ⊥ →
    pRank p (⊤ : Subgroup ↥(CFSG.generalizedFitting W)) = 1 ∨
      ∃ (Kh : Type) (_ : Group Kh) (_ : Finite Kh) (π : Kh →* ↥(CFSG.generalizedFitting W)),
        Function.Surjective π ∧ π.ker ≤ Subgroup.center Kh ∧ IsCyclic ↥π.ker ∧
          IsPGroup p ↥π.ker ∧ commutator Kh = ⊤ ∧ pRank p (⊤ : Subgroup Kh) = 2) ∧
  GGHypRestIVFlat p E

@[expose] def GGHypThreeSixteenFlat [Finite W] (p : ℕ) (H E : Subgroup W) : Prop :=
  (p.Prime ∧ p ≠ 2 ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧ GGControlsStrongFusion H E) ∧
    GGHypThreeSixteenRestFlat p H E

variable [Finite W] {p : ℕ} {H E : Subgroup W}

theorem GGHypRestIII.flat (h : GGHypRestIII p H E) : GGHypRestIIIFlat p H E :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩

theorem ggHypThreeSixteenRestFlat_of_parts (h2 : GGHypRestII W) (h3 : GGHypRestIIIFlat p H E)
    (h4 : GGHypRestIVFlat p E) : GGHypThreeSixteenRestFlat p H E :=
  ⟨h2, h3.1, h3.2.1, h3.2.2.1, h3.2.2.2, h4⟩

end HypFlat

@[expose] def GGKGroupFusionLayerInputFlat : Prop :=
  ∀ (W : Type) [Group W] [Finite W], CFSG.Open.IsKGroup W → ∀ (p : ℕ) (H E : Subgroup W),
    GGHypThreeSixteenFlat p H E → LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥ →
      H = ⊤ ∨ GGFusionException p H E

@[expose] def GGKGroupFusionAtFlat (S : TauCeti.CFSGIndex → ℕ → Prop) : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (p : ℕ) (H E : Subgroup W) (i : TauCeti.CFSGIndex),
    S i p → GGHypThreeSixteenFlat p H E → LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥ →
      ¬ CFSG.generalizedFitting W ≤ H →
        Nonempty (↥(CFSG.generalizedFitting W) ≃* i.Group) → GGFusionException p H E

@[expose] def GGKGroupFusionAtFlatK (S : TauCeti.CFSGIndex → ℕ → Prop) : Prop :=
  ∀ (W : Type) [Group W] [Finite W], CFSG.Open.IsKGroup W → ∀ (p : ℕ) (H E : Subgroup W)
    (i : TauCeti.CFSGIndex), S i p → GGHypThreeSixteenFlat p H E →
      LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥ → ¬ CFSG.generalizedFitting W ≤ H →
        Nonempty (↥(CFSG.generalizedFitting W) ≃* i.Group) → GGFusionException p H E

theorem GGKGroupFusionAtFlat.toK {S : TauCeti.CFSGIndex → ℕ → Prop} (h : GGKGroupFusionAtFlat S) :
    GGKGroupFusionAtFlatK S :=
  fun W _ _ _ p H E i hS hyp hL hK he => h W p H E i hS hyp hL hK he

end CFSG.StandardType
