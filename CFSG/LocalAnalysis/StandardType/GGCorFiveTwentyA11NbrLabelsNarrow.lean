module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyA11C3D4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

private theorem hasLabel_J_of_a11Config_narrow (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown)
    (hTP : GGNbrTablePNbrInputOn GGRegimeA11) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G}
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

theorem ggCorFiveTwentyA11CfgRootGenNbrInputOn_of_c3d4_narrow (hRig : GGLabelRigidInput)
    (hTCJ : GGTCJKnown) (hTP : GGNbrTablePNbrInputOn GGRegimeA11)
    (h : GGCorFiveTwentyA11RootGenC3D4Input) :
    GGCorFiveTwentyA11CfgRootGenNbrInputOn fun p lab =>
      ¬ GGTypeALabel p lab ∧ ¬ GGLabA8Seven p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hA y K hnb hK
  have hcfg := hHyp.1
  have hInn := hHyp.2.2.1
  obtain ⟨hJΛ, hhasJ⟩ := hasLabel_J_of_a11Config_narrow hRig hTCJ hTP hcfg hInn hA
  have hp : p = 7 := hA.1
  subst hp
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, ⟨hnA, hnA8⟩, -⟩ := largeEvenMarking_exists_hasLabel hK
  obtain ⟨jlab, klab, hjΛ, hkΛ, hrow, hhasJ1, hhasK1⟩ :=
    hTP G 7 B Bs x L D J y K hcfg hInn.1 (hInn.2 y K hnb) hnb ⟨.A, 2, 3⟩ lab hJΛ hlab
      (Or.inr ⟨rfl, rfl⟩) hhasJ hhas
  rcases ggLabelIso_typeA_cases hRig (r := 2) (f := 3) (by norm_num) hjΛ hJΛ hhasJ1 hhasJ
    with rfl | ⟨h23, -⟩
  swap
  · omega
  have hrel : GGLabC3D4Seven 7 klab → GGRootCompGenAvoiding 7 Bs K := fun hS => by
    refine h G 7 B Bs x L D J hHyp hq hA y K hnb (largeEvenMarking_mono ?_
      (ggInnerDiagOn_relabel hRig (hInn.2 y K hnb) hkΛ hhasK1))
    rintro lab' R' _ I' F' θ' ⟨rfl, hP⟩
    exact ⟨hS, hP⟩
  have hA33 : LargeEvenInLambda2 ⟨.A, 3, 3⟩ := by simp [LargeEvenInLambda2]
  obtain ⟨t, r, n⟩ := klab
  rcases ggTablePRow_a23_right hrow with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exfalso
    rcases ggLabelIso_typeA_cases hRig (r := 3) (f := 3) (by norm_num) hlab hA33 hhas hhasK1
      with rfl | ⟨-, rfl⟩
    · exact hnA (Or.inl ⟨rfl, by decide, by decide⟩)
    · exact hnA (Or.inr (Or.inl ⟨rfl, rfl, by decide⟩))
  · exact hrel ⟨Or.inl rfl, rfl⟩
  · exfalso
    rcases ggLabelIso_typeA_cases hRig (r := 3) (f := 3) (by norm_num) hlab hA33 hhas
        (ggHasLabel_D3_iff_A3.1 hhasK1) with rfl | ⟨-, rfl⟩
    · exact hnA (Or.inl ⟨rfl, by decide, by decide⟩)
    · exact hnA (Or.inr (Or.inl ⟨rfl, rfl, by decide⟩))
  · exact hrel ⟨Or.inr rfl, rfl⟩
  · exfalso
    rcases ggLabelIso_typeA_cases hRig (r := 8) (f := 1) (by norm_num) hlab hkΛ hhas hhasK1
      with rfl | ⟨h83, -⟩
    · exact hnA8 ⟨rfl, rfl, rfl, rfl⟩
    · omega

end CFSG.StandardType

end
