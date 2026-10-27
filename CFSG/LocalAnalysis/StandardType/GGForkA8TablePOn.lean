module

public import CFSG.LocalAnalysis.StandardType.GGForkA8TablePClauses
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

theorem ggForkA8_not_e6Nbr (h5 : GGNbrTablePNbrInputOn GGRegimeFieldTwo) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig 7 B Bs x L D J) (hID : GGInnerDiagAll 7 B Bs x L D J)
    {y : G} {K : Subgroup G} (hK : GGNbr 7 B x D J y K)
    (hE6 : GGHasLabel ⟨.E6, 0, 1⟩ (K ⧸ Subgroup.center K)) : False := by
  obtain ⟨lab, labJ', hlab, hsplit, hhasL, hlabJ', hdvd, hhasJ'⟩ :=
    ggNbr_label_J_of_tcj hTCJ hC hK
  have h3 : 3 ∣ lab.n := largeEvenSplit_seven_dvd hsplit
  have hn1 : 1 ≤ lab.n := hlab.1
  have hn : 3 ≤ labJ'.n :=
    Nat.le_of_dvd (lt_of_lt_of_le zero_lt_one hlabJ'.1) (dvd_trans h3 hdvd)
  obtain ⟨jlab, klab, hjΛ, hkΛ, hrow, hhasJ1, hhasK1⟩ :=
    h5 G 7 B Bs x L D J y K hC hID.1 (hID.2 y K hK) hK labJ' ⟨.E6, 0, 1⟩ hlabJ'
      largeEvenInLambda2_e6 ⟨by omega, rfl, by simp⟩ hhasJ' hE6
  have hkE : klab = ⟨.E6, 0, 1⟩ := eq_of_ggLabelIso_of_exc (Or.inr rfl)
    (hRig klab ⟨.E6, 0, 1⟩ _ hkΛ largeEvenInLambda2_e6 hhasK1 hE6)
  subst hkE
  obtain ⟨t, r, n⟩ := jlab
  obtain ⟨rfl, rfl⟩ := ggTablePRow_e6_left hrow
  have hJ := eq_of_ggLabelIso_triD4 (hRig labJ' ⟨.triD4, r, 1⟩ _ hlabJ' hjΛ hhasJ' hhasJ1)
  subst hJ
  have := Nat.le_of_dvd one_pos hdvd
  omega

theorem ggForkA8TableP_clauseK_of_tpOn (h6 : GGNbrTablePNbrInputOn GGRegimeA8Seven)
    (h5 : GGNbrTablePNbrInputOn GGRegimeFieldTwo) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 7 B Bs x L D J) (hID : GGInnerDiagAll 7 B Bs x L D J) {y : G}
    {K : Subgroup G} (hK : GGNbr 7 B x D J y K)
    (hlab : GGHasLabel ⟨.A, 8, 1⟩ (K ⧸ Subgroup.center K) ∨
      GGHasLabel ⟨.E6, 0, 1⟩ (K ⧸ Subgroup.center K)) (labJ : LargeEvenLabel)
    (hlabJ : LargeEvenInLambda2 labJ) (hhasJ : GGHasLabel labJ (J ⧸ Subgroup.center J)) :
    GGTablePAt 7 (J ⧸ Subgroup.center J) (K ⧸ Subgroup.center K) := by
  rcases hlab with hA | hE
  · exact h6 G 7 B Bs x L D J y K hC hID.1 (hID.2 y K hK) hK labJ ⟨.A, 8, 1⟩ hlabJ
      largeEvenInLambda2_a8 ⟨rfl, rfl⟩ hhasJ hA
  · exact (ggForkA8_not_e6Nbr h5 hTCJ hRig hC hID hK hE).elim

theorem ggForkA8TablePInput_of_tpOn (h6 : GGNbrTablePNbrInputOn GGRegimeA8Seven)
    (h5 : GGNbrTablePNbrInputOn GGRegimeFieldTwo) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hL : GGForkA8TablePLInput) : GGForkA8TablePInput := by
  intro G _ _ p B Bs x L D J hC hID hp y K hK hlab
  refine ⟨fun labJ hlabJ hhasJ => ?_, hL G p B Bs x L D J hC hID hp y K hK hlab⟩
  subst hp
  exact ggForkA8TableP_clauseK_of_tpOn h6 h5 hTCJ hRig hC hID hK hlab labJ hlabJ hhasJ

end CFSG.StandardType

end
