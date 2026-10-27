module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermReflSigma
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrOfEnnola
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplit
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowCasesLab
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrPRank
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNFrame
import CFSG.LocalAnalysis.StandardType.GGTBJWeyl
import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitFamilies
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusHolds
import CFSG.LocalAnalysis.StandardType.GGUSixThreeWeylHolds
import CFSG.LocalAnalysis.StandardType.GGNbrTableBE6Three
import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
import CFSG.LocalAnalysis.StandardType.GGNbrTableBExcWeyl
import CFSG.LocalAnalysis.StandardType.GGF4AutWeylTableB
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitHolds
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCube
import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup
import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRank
import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMemberAux
import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneHolds
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNBCells
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNCells
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNTwAMCells
import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneOmegaLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggX_row_absurd_of_frame_of_noPair (hRig : GGLabelRigidInput)
    {S : ℕ → LargeEvenLabel → Prop} (hF : GGRowFrame S) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X) (hNP : GGNoReflFramePair p Bs X)
    (hrow : GGInnerDiagOnLabel S p Bs X) : False := by
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  have hInn : GGInnerDiagOn Bs X := by
    rcases hX with rfl | hK
    · exact hcfg.1.2.2.1.1
    · obtain ⟨y, hnb⟩ := hK.1
      exact hcfg.1.2.2.1.2 y X hnb
  obtain ⟨lab, hΛ, hhas, R, _, I, _, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel hrow
  exact hNP (ggX_exists_frame_pair hRig hcfg hX hInn hΛ hhas (hF p hp hodd lab hΛ hS))

theorem ggX_row_absurd_of_cells_of_noPair (hRig : GGLabelRigidInput)
    {S Sf Sp : ℕ → LargeEvenLabel → Prop}
    (hcov : ∀ p lab, S p lab → Sf p lab ∨ Sp p lab) (hF : GGRowFrame Sf)
    (hP : GGRowPRankLeTwo Sp) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X) (hNP : GGNoReflFramePair p Bs X)
    (hrow : GGInnerDiagOnLabel S p Bs X) : False := by
  have hor : GGInnerDiagOnLabel (fun p lab => Sf p lab ∨ Sp p lab) p Bs X :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hQ => ⟨hcov _ _ hQ.1, hQ.2⟩) hrow
  rcases hor.elim_or with h | h
  · exact ggX_row_absurd_of_frame_of_noPair hRig hF hcfg hX hNP h
  · exact ggX_row_absurd_of_pRank hP hcfg hX h

theorem ggL_ennola_of_nonSplit_of_noPair
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hNP : GGNoReflFramePair p Bs L) (hns : ¬ GGSplitLie p L) :
    GGInnerDiagOnLabel ggRowP_Ennola p Bs L := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have hST : LargeEvenStandardType p B x L := hcfg.1.1.1.2.2.2.2.2.2.2
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hST.1
  have hmark := ggInnerDiagOn_relabel ggLabelRigidInput_holds hcfg.1.2.2.1.1 hlab hhas
  have hBIG : GGInnerDiagOnLabel (fun p lab =>
      (ggRowP_SA p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_SD p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_SE6 p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_SE7 p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_SE8 p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_ESU p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_EOmP p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_EOmM p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_ETwE6 p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_EE7 p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_EE8 p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_NB p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_NF4 p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_NAP p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_NTwAM p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_NDOdd p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_NTwD p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_NE6 p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_Small p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_ZA8 p lab ∧ LargeEvenSplit p lab) ∨
      (ggRowP_ZE6 p lab ∧ LargeEvenSplit p lab)) p Bs L :=
    largeEvenMarking_mono (fun lab' _ _ _ _ _ hQ => by
      rw [hQ.1]
      exact ⟨ggRowSplit_distrib
        (ggNSRowLab_of_halfSplit hlab
          (show LargeEvenHalfSplit p lab (Subgroup.center L = ⊥) from Or.inl hP.1))
        hP.1, hQ.2⟩) hmark
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_SA p lab ∧ LargeEvenSplit p lab)
    hBIG with h | h
  · exact absurd (ggSplitLie_of_rowSA hp (h.mono' (fun _ hh => hh.1)).toMarking) hns
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_SD p lab ∧ LargeEvenSplit p lab)
    h with h | h
  · exact absurd (ggSplitLie_of_rowSD hp (h.mono' (fun _ hh => hh.1)).toMarking) hns
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_SE6 p lab ∧ LargeEvenSplit p lab)
    h with h | h
  · exact absurd (ggSplitLie_of_rowSE6 hp (h.mono' (fun _ hh => hh.1)).toMarking) hns
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_SE7 p lab ∧ LargeEvenSplit p lab)
    h with h | h
  · exact absurd (ggSplitLie_of_rowSE7 hp (h.mono' (fun _ hh => hh.1)).toMarking) hns
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_SE8 p lab ∧ LargeEvenSplit p lab)
    h with h | h
  · exact absurd (ggSplitLie_of_rowSE8 hp (h.mono' (fun _ hh => hh.1)).toMarking) hns
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_ESU p lab ∧ LargeEvenSplit p lab)
    h with h | h
  · exact h.mono' (fun _ hh => Or.inl (Or.inl hh.1))
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_EOmP p lab ∧ LargeEvenSplit p lab)
    h with h | h
  · exact h.mono' (fun _ hh => Or.inl (Or.inr (Or.inl hh.1)))
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_EOmM p lab ∧ LargeEvenSplit p lab)
    h with h | h
  · exact h.mono' (fun _ hh => Or.inl (Or.inr (Or.inr (Or.inl hh.1))))
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_ETwE6 p lab ∧ LargeEvenSplit p lab)
    h with h | h
  · exact h.mono' (fun _ hh => Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hh.1)))))
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_EE7 p lab ∧ LargeEvenSplit p lab)
    h with h | h
  · exact h.mono' (fun _ hh => Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh.1))))))
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_EE8 p lab ∧ LargeEvenSplit p lab)
    h with h | h
  · exact h.mono' (fun _ hh => Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh.1))))))
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_NB p lab ∧ LargeEvenSplit p lab)
    h with h | h
  · refine (ggX_row_absurd_of_frame_of_noPair ggLabelRigidInput_holds ?_ hcfg (Or.inl rfl) hNP
      (h.mono' (fun _ hh => hh.1))).elim
    exact fun _ hp' _ _ hlab h => h.2.2.elim
      (fun hd => largeEvenLabelAll_frame_symplectic hp' hlab ⟨h.1, hd⟩)
      (fun hd => largeEvenLabelAll_frame_symplecticNs hp' hlab ⟨h.1, hd⟩)
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_NF4 p lab ∧ LargeEvenSplit p lab)
    h with h | h
  · have h' : GGInnerDiagOnLabel (fun p lab =>
        (ggRowP_NF4 p lab ∧ LargeEvenSplit p lab ∧ (p = 3 ∧ p ∣ 2 ^ lab.n + 1)) ∨
        (ggRowP_NF4 p lab ∧ LargeEvenSplit p lab ∧ ¬ (p = 3 ∧ p ∣ 2 ^ lab.n + 1))) p Bs L :=
      h.mono' (fun lab hl => (em (p = 3 ∧ p ∣ 2 ^ lab.n + 1)).imp
        (fun h3 => ⟨hl.1, hl.2, h3⟩) (fun h3 => ⟨hl.1, hl.2, h3⟩))
    rcases GGInnerDiagOnLabel.elim_or h' with h | h
    · exact h.mono' (fun _ hh => Or.inr ⟨hh.1, hh.2.2⟩)
    · refine (ggX_row_absurd_of_frame_of_noPair ggLabelRigidInput_holds ?_ hcfg (Or.inl rfl) hNP
        (S := fun p lab => ggRowP_NF4 p lab ∧ ¬ (p = 3 ∧ p ∣ 2 ^ lab.n + 1))
        (h.mono' (fun _ hh => ⟨hh.1, hh.2.2⟩))).elim
      exact fun q hq hq2 _ _ hh => hh.1.2.elim
        (fun hd => largeEvenLabelAll_frame_F4Split hq hq2 ⟨hh.1.1, hd⟩)
        (fun hd => largeEvenLabelAll_frame_F4Plus hq (by
          have h4 : q ≠ 4 := by rintro rfl; exact absurd hq (by decide)
          have h3 : q ≠ 3 := fun h3 => hh.2 ⟨h3, hd⟩
          have := hq.two_le
          omega) ⟨hh.1.1, hd⟩)
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_NAP p lab ∧ LargeEvenSplit p lab)
    h with h | h
  · refine (ggX_row_absurd_of_cells_of_noPair ggLabelRigidInput_holds
      (Sf := fun p lab => lab.tag = .A ∧ 5 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1) ?_
      (fun p hp' hp2' lab hlab h =>
        ggNbrFrameInputOne_holds p hp' hp2' lab hlab (Or.inr (Or.inl h)))
      ggRowPRankLeTwo_smallPlus hcfg (Or.inl rfl) hNP
      (h.mono' (fun _ hh => hh.1))).elim
    rintro p lab ⟨⟨ht, hr⟩ | ⟨ht, hr⟩, hd⟩
    · by_cases h5 : 5 ≤ lab.rank
      · exact Or.inl ⟨ht, h5, hd⟩
      · exact Or.inr ⟨Or.inl ⟨ht, by omega⟩, hd⟩
    · exact Or.inr ⟨Or.inr ⟨ht, hr⟩, hd⟩
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_NTwAM p lab ∧ LargeEvenSplit p lab)
    h with h | h
  · have h' : GGInnerDiagOnLabel (fun p lab =>
        ((lab.tag = .twA ∧ 3 ≤ lab.rank) ∧ p ∣ 2 ^ lab.n - 1 ∧ LargeEvenSplit p lab) ∨
        ((lab.tag = .twD ∧ lab.rank = 3) ∧ p ∣ 2 ^ lab.n - 1 ∧ LargeEvenSplit p lab))
        p Bs L :=
      h.mono' (fun _ hl => ntwam_split hl)
    rcases GGInnerDiagOnLabel.elim_or h' with h | h
    · obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hQ⟩ := largeEvenMarking_exists_hasLabel h
      exact (not_split_twA_dvd_sub hp hp2 hQ.1.1.1 hQ.1.2.2 hQ.1.2.1).elim
    · refine (ggX_row_absurd_of_pRank ggRowPRankLeTwo_smallMinus hcfg (Or.inl rfl) ?_).elim
      exact h.mono' (fun _ hh => ⟨Or.inr ⟨hh.1.1, hh.1.2⟩, hh.2.1⟩)
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_NDOdd p lab ∧ LargeEvenSplit p lab)
    h with h | h
  · refine (ggX_row_absurd_of_frame_of_noPair ggLabelRigidInput_holds ?_ hcfg (Or.inl rfl) hNP
      (h.mono' (fun _ hh => hh.1))).elim
    exact fun _ hp' _ _ hlab h => largeEvenLabelAll_frame_omegaPlusNs hp' hlab h
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_NTwD p lab ∧ LargeEvenSplit p lab)
    h with h | h
  · refine (ggX_row_absurd_of_frame_of_noPair ggLabelRigidInput_holds ?_ hcfg (Or.inl rfl) hNP
      (h.mono' (fun _ hh => hh.1))).elim
    exact fun q hq hq2 lab hlab ⟨ht, hr, hor⟩ => hor.elim
      (fun he => largeEvenLabelAll_frame_omegaMinusNs hq hlab ⟨ht, hr, he.1, he.2⟩)
      (fun hd => largeEvenLabelAll_frame_omegaMinus hq hq2 hlab ⟨ht, hr, hd⟩)
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_NE6 p lab ∧ LargeEvenSplit p lab)
    h with h | h
  · have hcov : ∀ lab, ggRowP_NE6 p lab →
        ((lab.tag = .E6 ∧ lab.n = 1 ∧ p = 3) ∨ (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n - 1)) ∨
          GGNbrNsE6Label p lab := by
      rintro lab (⟨ht, hd⟩ | h)
      · by_cases h13 : lab.n = 1 ∧ p = 3
        · exact Or.inl (Or.inl ⟨ht, h13⟩)
        · refine Or.inr ⟨ht, fun h1 => not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 h1 hd, h13,
            fun h17 => ?_⟩
          rw [h17.1, h17.2] at hd
          norm_num at hd
      · exact Or.inl (Or.inr h)
    have h'' : GGInnerDiagOnLabel (fun p lab =>
        (((lab.tag = .E6 ∧ lab.n = 1 ∧ p = 3) ∨ (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n - 1)) ∧
          LargeEvenSplit p lab) ∨
        (GGNbrNsE6Label p lab ∧ LargeEvenSplit p lab)) p Bs L :=
      h.mono' (fun _ hh => (hcov _ hh.1).imp (fun hc => ⟨hc, hh.2⟩) (fun hn => ⟨hn, hh.2⟩))
    rcases GGInnerDiagOnLabel.elim_or h'' with h | h
    · exact (ggX_row_absurd_of_frame_of_noPair ggLabelRigidInput_holds (S := fun p lab =>
          ((lab.tag = .E6 ∧ lab.n = 1 ∧ p = 3) ∨ (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n - 1)) ∧
            LargeEvenSplit p lab)
        (fun q hq hq2 lab hlab hh => by
          rcases hh.1 with ⟨ht, hn, rfl⟩ | ht
          · exact largeEvenLabelAll_frame_E6Two ⟨ht, hn⟩
          · exact largeEvenLabelAll_frame_twE6Dvd hq hq2 hlab ht)
        hcfg (Or.inl rfl) hNP h).elim
    · obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hQ⟩ := largeEvenMarking_exists_hasLabel h
      exact (not_split_NsE6 hQ.1.1.1 hQ.1.2 hQ.1.1.2.1 hQ.1.1.2.2.1).elim
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_Small p lab ∧ LargeEvenSplit p lab)
    h with h | h
  · obtain ⟨hXc, lab, hlab, hraw⟩ := ggX_inndiag_pRank_ge_three hcfg (Or.inl rfl) h
    obtain ⟨-, -, -, -, -, -, -, hS, -⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨hSrow, hSsplit⟩ := hS
    have key : ∀ T : LargeEvenLabel → Prop, T lab → LargeEvenMarking ↥L
        (fun lab R _ I _ _ => T lab ∧ ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧
          IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E) := fun T hT =>
      ⟨hXc, lab, hlab, largeEvenRawDatum_mono (fun _ _ _ _ ⟨hs, hna, θ, _, hE⟩ =>
        ⟨hs, hna, θ, hT, hE⟩) hraw⟩
    obtain ⟨t, r, n⟩ := lab
    dsimp only [ggRowP_Small] at hSrow
    rcases hSrow with
      ⟨rfl, hr⟩ | hBC | rfl | rfl | rfl | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | rfl | rfl | rfl | rfl
    · have h1 : 1 ≤ r := hlab.2.1
      rcases (by omega : r = 1 ∨ r = 2) with hr | hr
      · exact (ggInndiag_pRank_le_two_A1 hp hp2 (key _ ⟨rfl, hr⟩)).elim
      · exact (ggInndiag_pRank_le_two_A2 hp hp2 (key _ ⟨rfl, hr⟩)).elim
    · exact (ggInndiag_pRank_le_two_B2 hp hp2 (key _ hBC)).elim
    · exact (ggInndiag_pRank_le_two_B2der hp hp2 (key _ rfl)).elim
    · exact (ggInndiag_pRank_le_two_G2 hp hp2 (key _ rfl)).elim
    · exact (ggInndiag_pRank_le_two_G2der hp hp2 (key _ rfl)).elim
    · have h2 : 2 ≤ r := hlab.2.1
      exact (ggInndiag_pRank_le_two_twA2 hp hp2 (key _ ⟨rfl, (by omega : r = 2)⟩)).elim
    · exact (ggInndiag_pRank_le_two_twD2 hp hp2 (key _ ⟨rfl, hr⟩)).elim
    · exact (ggInndiag_pRank_le_two_triD4 hp
        (key _ ⟨rfl, dvd_sub_or_add_of_split_triD4 hSsplit rfl⟩)).elim
    · exact (ggInndiag_pRank_le_two_twB2 hp hp2 (key _ rfl)).elim
    · exact (ggInndiag_pRank_le_two_twF4 hp hp2
        (key _ ⟨rfl, dvd_sub_or_add_of_split_twF4 hSsplit rfl⟩)).elim
    · exact (ggInndiag_pRank_le_two_twF4der hp hp2 (key _ rfl)).elim
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_ZA8 p lab ∧ LargeEvenSplit p lab)
    h with h | h
  · exact h.mono' (fun _ hh => (not_split_ZA8 hh.1 hh.2).elim)
  · exact h.mono' (fun _ hh => (not_split_ZE6 hh.1 hh.2).elim)

end CFSG.StandardType

end
