module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoPairing
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoLabel
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaNbrGrpAux3
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaNbrLabAux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem E6QTwo.three_dvd_card_of_hasLabel_twA3 {J : Subgroup G}
    (h : GGHasLabel ⟨.twA, 3, 1⟩ (J ⧸ Subgroup.center J)) : 3 ∣ Nat.card J := by
  have hq : 3 ∣ Nat.card (J ⧸ Subgroup.center J) := by
    rw [E6QTwo.card_eq_evenLieOrder_of_hasLabel_twA3 h]
    decide
  exact dvd_trans hq (Subgroup.card_quotient_dvd_card (Subgroup.center J))

theorem E6QTwo.innerDiagOnLabel_twA5_of_nbr (hRig : GGLabelRigidInput)
    (hTP : GGNbrTablePNbrInputOnL fun p n labL labJ _ =>
      p = 3 ∧ n = 3 ^ 5 ∧ labL = ⟨.D, 4, 1⟩ ∧ labJ = ⟨.twA, 3, 1⟩)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K' : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hIDL : GGInnerDiagOn Bs L) (hIDK : GGInnerDiagOn Bs K')
    (hNbr : GGNbr 3 B x D J y K') (hcard : Nat.card Bs = 3 ^ 5)
    (hlab : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = 1))
    (hlabJ : GGHasLabel ⟨.twA, 3, 1⟩ (J ⧸ Subgroup.center J))
    (h36 : 3 ^ 6 ∣ Nat.card (K' ⧸ Subgroup.center K')) :
    GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs K' := by
  obtain ⟨-, labL, hΛL, hrawL⟩ := hlab
  obtain ⟨R_L, hR_L, I_L, F_L, hs_L, hna_L, θ_L, hPL⟩ := largeEvenRawDatum_exists hrawL
  letI : Group R_L := hR_L
  obtain ⟨hPLtag, hPLrank, hPLn⟩ := hPL
  have hglL : GGHasLabel labL (L ⧸ Subgroup.center L) :=
    largeEvenRawDatum_mono (fun _ _ _ _ ⟨_, _, θ, _⟩ => ⟨θ⟩) hrawL
  have hIDK' : GGInnerDiagOn Bs K' := hIDK
  obtain ⟨hperfK, labK, hΛK, hrawK⟩ := hIDK
  have hglK : GGHasLabel labK (K' ⧸ Subgroup.center K') :=
    largeEvenRawDatum_mono (fun _ _ _ _ ⟨_, _, θ, _⟩ => ⟨θ⟩) hrawK
  have hlabL_eq : labL = ⟨.D, 4, 1⟩ := by
    obtain ⟨t, r, n⟩ := labL
    simp only at hPLtag hPLrank hPLn
    subst hPLtag hPLrank hPLn
    rfl
  have hΛ3 : LargeEvenInLambda2 (⟨.twA, 3, 1⟩ : LargeEvenLabel) := by
    simp [LargeEvenInLambda2]
  obtain ⟨labJ', labK', hΛJ', hΛK', hrow, hglJ', hglK'⟩ :=
    hTP G 3 B Bs x L D J y K' hcfg hIDL hIDK' hNbr labL ⟨.twA, 3, 1⟩ labK hΛL
      hΛ3 hΛK ⟨rfl, hcard, hlabL_eq, rfl⟩ hglL hlabJ hglK
  have hJ : labJ' = ⟨.twA, 3, 1⟩ ∨ labJ' = ⟨.twD, 3, 1⟩ :=
    E6QTwo.eq_twA_or_twD_of_ggLabelIso_twA3
      (hRig labJ' ⟨.twA, 3, 1⟩ _ hΛJ' hΛ3 hglJ' hlabJ)
  have hlabK'_eq : labK' = ⟨.twA, 5, 1⟩ :=
    E6QTwo.eq_twA5_of_ggTablePRow hJ hrow hglK' h36
  have hlabK_eq : labK = ⟨.twA, 5, 1⟩ := by
    have hiso : GGLabelIso labK ⟨.twA, 5, 1⟩ := by
      rw [← hlabK'_eq]
      exact hRig labK labK' _ hΛK hΛK' hglK hglK'
    exact E6QTwo.eq_of_ggLabelIso_end hiso ⟨Or.inl ⟨rfl, rfl⟩, rfl⟩
  subst hlabK_eq
  change CFSG.StandardType.LargeEvenRawDatum ⟨.twA, 5, 1⟩ _ at hrawK
  unfold GGInnerDiagOnLabel
  exact ⟨hperfK, ⟨.twA, 5, 1⟩, hΛK,
    largeEvenRawDatum_mono (fun R _ I F ⟨hs, hna, θ, hBsN, hI⟩ =>
      ⟨hs, hna, θ, ⟨rfl, rfl, rfl⟩, hBsN, hI⟩) hrawK⟩

end CFSG.StandardType

end
