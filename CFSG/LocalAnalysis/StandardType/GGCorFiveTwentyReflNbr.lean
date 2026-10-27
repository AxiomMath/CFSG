module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflOrbit

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGNbrSStarInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      LargeEvenSStar p B y K ∧ ∃ S : Subgroup G, S ≤ K ∧ IsPGroup p S ∧ ¬ IsCyclic S

@[expose] def GGPseudoReflNbrStabModInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGInnerDiagOnLabel S p Bs K →
        ∀ φ ∈ ggAutomizer (Subgroup.centralizer ({y} : Set G)) Bs, GGIsPseudoReflection p φ →
          ∃ ψ ∈ ggAutomizer (ggG0 p B x L D J) Bs, (∀ b : ↥Bs, (b : G) = y → ψ b = b) ∧
            ∀ b : ↥Bs, (((ψ b)⁻¹ * φ b : ↥Bs) : G) ∈ Subgroup.zpowers y

theorem ggPseudoReflNbrStabModInputOn_of (h : GGPseudoReflNbrStabModInput)
    (S : ℕ → LargeEvenLabel → Prop) : GGPseudoReflNbrStabModInputOn S :=
  fun G _ _ p B Bs x L D J hH y K hyK _ => h G p B Bs x L D J hH y K hyK

theorem GGPseudoReflNbrStabModInputOn.or {S T : ℕ → LargeEvenLabel → Prop}
    (hS : GGPseudoReflNbrStabModInputOn S) (hT : GGPseudoReflNbrStabModInputOn T) :
    GGPseudoReflNbrStabModInputOn fun p lab => S p lab ∨ T p lab := by
  intro G _ _ p B Bs x L D J hH y K hyK hK
  rcases hK.elim_or with h | h
  · exact hS G p B Bs x L D J hH y K hyK h
  · exact hT G p B Bs x L D J hH y K hyK h

theorem ggPseudoReflNbrStabModInput_of_on {S : ℕ → LargeEvenLabel → Prop}
    (hS : GGPseudoReflNbrStabModInputOn S)
    (hT : GGPseudoReflNbrStabModInputOn fun p lab => ¬ S p lab) :
    GGPseudoReflNbrStabModInput := by
  intro G _ _ p B Bs x L D J hH y K hyK
  exact (hS.or hT) G p B Bs x L D J hH y K hyK ((hH.2.2.1.2 y K hyK).label S p)

theorem ggPseudoReflNbrStabModInputOn_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (hBL4 : GGNbrSStarInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusReflBridge p r R I) :
    GGPseudoReflNbrStabModInputOn S := by
  intro G _ _ p B Bs x L D J hH y K hyK hM φ hφ hφp
  have hcfg := hH.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hSy, hnc⟩ := hBL4 G p B Bs x L D J hH y K hyK
  obtain ⟨hK, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3⟩, r, hlift, hbr⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨ψ, hψ, hmod⟩ := exists_ggAutomizer_of_reflBridge hp hcfg.2.1 hSy
    hcfg.1.2.2.2.2.2.1.2.2.2 hnc hK θ hBsN h3 hlift hbr hφ hφp
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hSy.2.2.2.1.1
  refine ⟨ψ, ggAutomizer_mono Bs (le_ggG0_of_ggNbr hyK) hψ, fun b hb => ?_, hmod⟩
  have hc : (⟨y, hb ▸ b.2⟩ : ↥Bs) = b := Subtype.ext hb.symm
  rw [← hc]
  exact ggAutomizer_apply_eq_of_le_centralizer hKy hψ

theorem ggPseudoReflNbrStabInput_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (hBL4 : GGNbrSStarInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusReflBridge p r R I)
    (hrest : GGPseudoReflNbrStabModInputOn fun p lab => ¬ S p lab) :
    GGPseudoReflNbrStabInput :=
  ggPseudoReflNbrStabInput_of_mod
    (ggPseudoReflNbrStabModInput_of_on (ggPseudoReflNbrStabModInputOn_of_labels hBL4 h) hrest)

end CFSG.StandardType

end
