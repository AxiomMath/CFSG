module

public import CFSG.LocalAnalysis.StandardType.GGA11NbrDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyA11C3D4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard

public section

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.A8Coord Matrix

namespace CFSG.StandardType.A11

private theorem a11nl2_hasLabel_J (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown)
    (hTP : GGNbrTablePNbrInputOn GGRegimeA11) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hA : GGSecFiveA11ConfigWide p B Bs x L D J) :
    LargeEvenInLambda2 ⟨.A, 2, 3⟩ ∧ GGHasLabel ⟨.A, 2, 3⟩ (J ⧸ Subgroup.center J) := by
  obtain ⟨rfl, -, y, K, hnb, hKmod⟩ := hA
  obtain ⟨lab, labJ, hlab, hsplit, -, hlabJ, hdvd, hhasJ⟩ := ggNbr_label_J_of_tcj hTCJ hcfg hnb
  have h3 : 3 ∣ lab.n := largeEvenSplit_seven_dvd hsplit
  have hn1 : 1 ≤ lab.n := hlab.1
  have hKmod' : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL (8 + 1) 2 1 := hKmod
  have hhasK : GGHasLabel ⟨.A, 8, 1⟩ (K ⧸ Subgroup.center K) := ggHasLabel_typeA hKmod'
  obtain ⟨jlab, klab, hjΛ, hkΛ, hrow, hhasJ1, hhasK1⟩ :=
    hTP G 7 B Bs x L D J y K hcfg hInn.1 (hInn.2 y K hnb) hnb labJ ⟨.A, 8, 1⟩ hlabJ
      largeEvenInLambda2_a8 (Or.inl ⟨rfl, rfl⟩) hhasJ hhasK
  rcases ggLabelIso_typeA_cases hRig (r := 8) (f := 1) (by norm_num) hkΛ largeEvenInLambda2_a8
      hhasK1 hhasK with rfl | ⟨h83, -⟩
  · obtain ⟨t, r, n⟩ := jlab
    rcases ggTablePRow_a8_left hrow with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨hjΛ, hhasJ1⟩
    · exfalso
      rcases ggLabelIso_typeA_cases hRig (r := 5) (f := 1) (by norm_num) hlabJ hjΛ hhasJ hhasJ1
        with rfl | ⟨h53, -⟩
      · have := Nat.le_of_dvd one_pos hdvd
        omega
      · omega
  · omega

theorem a11NbrLabelInput_holds : A11NbrLabelInput := by
  intro hTP hRig hTCJ G _ _ B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb
  obtain ⟨hRest, hWide, -, -, -, -⟩ := hctx
  have hcfg : GGConfig 7 B Bs x L D J := hRest.1
  have hInn : GGInnerDiagAll 7 B Bs x L D J := hRest.2.2.1
  have hwide : GGSecFiveA11ConfigWide 7 B Bs x L D J := GGSecFiveA11Config.toWide hWide
  obtain ⟨hJΛ, hhasJ⟩ := a11nl2_hasLabel_J hRig hTCJ hTP hcfg hInn hwide
  obtain ⟨labK, hlabK, hhasK, -⟩ := largeEvenMarking_exists_hasLabel (hInn.2 y' K' hnb)
  obtain ⟨jlab, klab, hjΛ, hkΛ, hrow, hhasJ1, hhasK1⟩ :=
    hTP G 7 B Bs x L D J y' K' hcfg hInn.1 (hInn.2 y' K' hnb) hnb ⟨.A, 2, 3⟩ labK hJΛ hlabK
      (Or.inr ⟨rfl, rfl⟩) hhasJ hhasK
  rcases ggLabelIso_typeA_cases hRig (r := 2) (f := 3) (by norm_num) hjΛ hJΛ hhasJ1 hhasJ with
      rfl | ⟨h23, -⟩
  · obtain ⟨t, r, n⟩ := klab
    rcases ggTablePRow_a23_right hrow with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Or.inr (Or.inl hhasK1)
    · exact Or.inr (Or.inr (Or.inl hhasK1))
    · exact Or.inr (Or.inl (ggHasLabel_D3_iff_A3.1 hhasK1))
    · exact Or.inr (Or.inr (Or.inr hhasK1))
    · exact Or.inl (statedClassicalModel_of_hasLabel_typeA largeEvenInLambda2_a8 hhasK1)
  · omega

end CFSG.StandardType.A11

end
