module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyNbrFieldRows
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpResidual

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

theorem ggSecFiveA11ConfigWide_of_a8Nbr
    (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown) (hTP : GGForkA8TablePInput)
    (hCoord : GGForkA8CoordInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J)
    (hID : GGInnerDiagAll p B Bs x L D J) (hNT : GGNoTransvection p Bs) {y : G}
    {K : Subgroup G} (hK : GGNbr p B x D J y K)
    (hA8 : p = 7 ∧ GGHasLabel ⟨.A, 8, 1⟩ (K ⧸ Subgroup.center K)) :
    GGSecFiveA11ConfigWide p B Bs x L D J := by
  obtain ⟨rfl, hKA8⟩ := hA8
  obtain ⟨lab, labJ, hlab, hsplit, hhasL, hlabJ, hdvd, hhasJ⟩ := ggNbr_label_J_of_tcj hTCJ hC hK
  have h3 : 3 ∣ lab.n := largeEvenSplit_seven_dvd hsplit
  have hn1 : 1 ≤ lab.n := hlab.1
  obtain ⟨hTPJ, hTPL⟩ := hTP G 7 B Bs x L D J hC hID rfl y K hK (Or.inl hKA8)
  obtain ⟨jlab, klab, hjΛ, hkΛ, hrow, hhasJ1, hhasK1⟩ := hTPJ labJ hlabJ hhasJ
  have hkA : klab = ⟨.A, 8, 1⟩ := eq_of_ggLabelIso_of_exc (Or.inl rfl)
    (hRig klab ⟨.A, 8, 1⟩ _ hkΛ largeEvenInLambda2_a8 hhasK1 hKA8)
  subst hkA
  obtain ⟨t, r, n⟩ := jlab
  have hLlab : GGHasLabel ⟨.A, 3, 3⟩ (L ⧸ Subgroup.center L) ∨
      GGHasLabel ⟨.C, 3, 3⟩ (L ⧸ Subgroup.center L) ∨
      GGHasLabel ⟨.twD, 4, 3⟩ (L ⧸ Subgroup.center L) := by
    rcases ggTablePRow_a8_left hrow with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rcases ggLabelIso_typeA_cases hRig (r := 2) (f := 3) (by norm_num) hlabJ hjΛ hhasJ hhasJ1
        with rfl | ⟨h23, -⟩
      · have hdvd3 : lab.n ∣ 3 := hdvd
        have h33 := Nat.le_of_dvd (by norm_num) hdvd3
        have hL3 : lab.n = 3 := by omega
        obtain ⟨jlab2, llab2, hj2Λ, hl2Λ, hrow2, hhasJ2, hhasL2⟩ :=
          hTPL ⟨.A, 2, 3⟩ lab hlabJ hlab hhasJ hhasL
        rcases ggLabelIso_typeA_cases hRig (r := 2) (f := 3) (by norm_num) hj2Λ hjΛ hhasJ2 hhasJ
          with rfl | ⟨h23, -⟩
        · obtain ⟨t2, r2, n2⟩ := llab2
          rcases ggTablePRow_a23_right hrow2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
              ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · exact Or.inl hhasL2
          · exact Or.inr (Or.inl hhasL2)
          · exact Or.inl (ggHasLabel_D3_iff_A3.1 hhasL2)
          · exact Or.inr (Or.inr hhasL2)
          · exfalso
            rcases ggLabelIso_typeA_cases hRig (r := 8) (f := 1) (by norm_num) hlab
                largeEvenInLambda2_a8 hhasL hhasL2 with rfl | ⟨h83, -⟩
            · have hL1 : (1 : ℕ) = 3 := hL3
              omega
            · omega
        · omega
      · omega
    · exfalso
      rcases ggLabelIso_typeA_cases hRig (r := 5) (f := 1) (by norm_num) hlabJ hjΛ hhasJ hhasJ1
        with rfl | ⟨h53, -⟩
      · have := Nat.le_of_dvd one_pos hdvd
        omega
      · omega
  have hKmodel : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1 :=
    statedClassicalModel_of_hasLabel_typeA (n := 8) (f := 1) largeEvenInLambda2_a8 hKA8
  obtain ⟨c, ι, hcall, hgen, hcL⟩ := hCoord G 7 B Bs x L D J hC hID hNT rfl y K hK hKmodel hLlab
  refine ⟨rfl, ?_, y, K, hK, hKmodel⟩
  by_cases hc : c ∈ Certificates.A8Nbr476.excCases
  · exact hcL (ggA8Nbr_excCases_fst c hc)
  · exact (ggA8Nbr_false_of_coord L K hNT ι hcall hc hgen).elim

@[expose] def GGCorFiveTwentyInputNbrRowR3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      ¬ GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyR3Rank p B Bs x D J →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ¬ GGInnerDiagOnLabel GGLabNbrOk p Bs K →
          p = 3 ∧ GGHasLabel ⟨.twE6, 0, 1⟩ (K ⧸ Subgroup.center K)) →
          Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

theorem GGCorFiveTwentyInputNbrFieldRows.of_rowR3
    (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown) (hTP : GGForkA8TablePInput)
    (hCoord : GGForkA8CoordInput) (hA : GGCorFiveTwentyA11CfgInput)
    (h : GGCorFiveTwentyInputNbrRowR3) : GGCorFiveTwentyInputNbrFieldRows := by
  intro G _ _ p B Bs x L D J hH hq hN _ hR hF
  by_cases hW : GGSecFiveA11ConfigWide p B Bs x L D J
  · exact hA G p B Bs x L D J hH hq hW
  · exact h G p B Bs x L D J hH hq hN hR fun y K hnb hK => (hF y K hnb hK).resolve_right
      fun h7 => hW (ggSecFiveA11ConfigWide_of_a8Nbr hRig hTCJ hTP hCoord hH.1 hH.2.2.1
        hH.2.2.2.1 hnb h7)

end CFSG.StandardType

end
