module

public import CFSG.LocalAnalysis.StandardType.GGPZNbrResRestDefs
public import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeRestDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTBXDatumResOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    (GGInnerDiagOnLabel S p Bs L → GGResXDatum p Bs L) ∧
      (GGInnerDiagOnLabel S p Bs K → GGResXDatum p Bs K)

@[expose] def GGPZNbrResDatumOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (labJ labX : LargeEvenLabel)
    (X : Subgroup G) (m : ℕ) (z : ↥Bs), GGPZPrem p B Bs x L D J y K labJ labX X m z →
    ∀ Y : Subgroup G, LargeEvenPComponent p (Subgroup.centralizer ({(z : G)} : Set G)) Y →
      J ≤ Y → Bs ≤ Subgroup.normalizer (Y : Set G) → GGNbr p B x D J (z : G) Y →
      GGInnerDiagOnLabel S p Bs Y → GGResXDatumSurj p Bs Y

theorem ggInnerDiagOnLabel_split {G : Type} [Group G] {S T : ℕ → LargeEvenLabel → Prop} {p : ℕ}
    {Bs L : Subgroup G} (h : GGInnerDiagOnLabel S p Bs L) :
    GGInnerDiagOnLabel (fun p lab => S p lab ∧ ¬ T p lab) p Bs L ∨ GGInnerDiagOnLabel T p Bs L := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  by_cases hc : T p lab
  · refine Or.inr ⟨hperf, lab, hlab, largeEvenRawDatum_mono (fun R _ I F hQ => ?_) hraw⟩
    obtain ⟨hs, hna, θ, hθ⟩ := hQ
    exact ⟨hs, hna, θ, ⟨hc, hθ.2⟩⟩
  · refine Or.inl ⟨hperf, lab, hlab, largeEvenRawDatum_mono (fun R _ I F hQ => ?_) hraw⟩
    obtain ⟨hs, hna, θ, hθ⟩ := hQ
    exact ⟨hs, hna, θ, ⟨⟨hθ.1, hc⟩, hθ.2⟩⟩

end CFSG.StandardType

end
