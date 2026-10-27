module

public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGResConjWire
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom
public import CFSG.LocalAnalysis.StandardType.GGNbrHalfSplitArith
public import CFSG.LocalAnalysis.StandardType.GGNbrLabelJOfTcjK
public import CFSG.LocalAnalysis.StandardType.GGRootGenSmallRankQFour
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRankExc
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nKM_relabel_L
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hRig : GGLabelRigidInput) (hcfg : GGConfig p B Bs x L D J)
    (hInn : GGInnerDiagOn Bs L) :
    ∃ lab : LargeEvenLabel, LargeEvenSplit p lab ∧ LargeEvenInLambda2 lab ∧
      GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) ∧
      LargeEvenMarking ↥L (fun lab' _ _ I _ θ => lab' = lab ∧
        Bs ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
  have hst : LargeEvenStandardType p B x L := hcfg.1.2.2.2.2.2.2.2
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hst.1
  exact ⟨lab, hP.1, hlab, hhas, ggInnerDiagOn_relabel hRig hInn hlab hhas⟩

private theorem l05nKM_L_conj
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hRig : GGLabelRigidInput)
    (hH : GGResHyp p B Bs x L D J y K) :
    ¬ GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∨ GGTBWeylRowRes p lab) p Bs L →
      GGResRowAt ggRowSeven p J L := by
  intro hL
  exfalso
  obtain ⟨lab, hsplit, hlab, hhas, hmark⟩ := l05nKM_relabel_L hRig hH.1 hH.2.2.1.1
  have hnotS1 : ¬ (GGTBTorCov p lab ∨ GGTBWeylRowRes p lab) := by
    intro hS1
    refine hL (largeEvenMarking_mono (fun lab' R _ I _ θ hP' => ?_) hmark)
    exact ⟨hP'.1 ▸ hS1, hP'.2⟩
  have hnotTor : ¬ GGTBTorCov p lab := fun h => hnotS1 (Or.inl h)
  have hnotWeyl : ¬ GGTBWeylRowRes p lab := fun h => hnotS1 (Or.inr h)
  have hHalf : LargeEvenHalfSplit p lab True := Or.inl hsplit
  have hRow : ¬ ggRowSeven p lab lab := by
    intro h
    obtain ⟨hp7, hlab7⟩ := h
    subst hp7
    have h3 : 3 ∣ lab.n := largeEvenSplit_seven_dvd hsplit
    rcases hlab7 with rfl | rfl | rfl | rfl | rfl <;> norm_num at h3
  have htag : lab.tag = .twF4 ∨ lab.tag = .twF4der := by
    by_contra h
    push Not at h
    exact hnotWeyl ⟨hnotTor, hHalf, hRow, h.1, h.2⟩
  have hp : p.Prime := hH.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  rcases htag with htag | htag
  · have hdvd : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1 :=
      Or.inr (TableBExcSmallRest.dvd_of_largeEvenSplit_twF4 htag hlab hsplit)
    have hrank := ggInnerDiagOnLabel_L_pRank_ge_three (S := fun _ lab' => lab' = lab) hH.1 hmark
    have hbad : LargeEvenMarking ↥L (fun lab' R _ I _ _ =>
        (lab'.tag = .twF4 ∧ (p ∣ 2 ^ lab'.n - 1 ∨ p ∣ 2 ^ lab'.n + 1)) ∧
          ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
            p ^ 3 ≤ Nat.card E) := by
      refine largeEvenMarking_mono (fun lab' R _ I _ θ hP' => ?_) hrank
      rw [hP'.1]
      exact ⟨⟨htag, hdvd⟩, hP'.2⟩
    exact absurd hbad (ggInndiag_pRank_le_two_twF4 (X := ↥L) hp hp2)
  · have hrank := ggInnerDiagOnLabel_L_pRank_ge_three (S := fun _ lab' => lab' = lab) hH.1 hmark
    have hbad : LargeEvenMarking ↥L (fun lab' R _ I _ _ =>
        lab'.tag = .twF4der ∧
          ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
            p ^ 3 ≤ Nat.card E) := by
      refine largeEvenMarking_mono (fun lab' R _ I _ θ hP' => ?_) hrank
      rw [hP'.1]
      exact ⟨htag, hP'.2⟩
    exact absurd hbad (ggInndiag_pRank_le_two_twF4der (X := ↥L) hp hp2)

private theorem l05nKM_K_conj
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    ¬ GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∨ GGTBWeylRowRes p lab) p Bs K →
      GGResRowAt ggRowSeven p J K := by
  intro hK
  have hNB : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hInnK : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hNB
  have hHS := ggNbr_halfSplit_of_hyp hraw hiso hH.1 hNB hInnK
  obtain ⟨labK, hlabK, hhasK, R, _, I, F, θ, hHSlab⟩ := largeEvenMarking_exists_hasLabel hHS
  have hmarkK := ggInnerDiagOn_relabel hRig hInnK hlabK hhasK
  have hnotS1K : ¬ (GGTBTorCov p labK ∨ GGTBWeylRowRes p labK) := by
    intro hS1
    refine hK (largeEvenMarking_mono (fun lab' R _ I _ θ hP' => ?_) hmarkK)
    exact ⟨hP'.1 ▸ hS1, hP'.2⟩
  have hnotTorK : ¬ GGTBTorCov p labK := fun h => hnotS1K (Or.inl h)
  have hnotWeylK : ¬ GGTBWeylRowRes p labK := fun h => hnotS1K (Or.inr h)
  have hHalfK : LargeEvenHalfSplit p labK True := largeEvenHalfSplit_true hHSlab
  have hcases : ggRowSeven p labK labK ∨ labK.tag = .twF4 ∨ labK.tag = .twF4der := by
    by_contra h
    push Not at h
    exact hnotWeylK ⟨hnotTorK, hHalfK, h.1, h.2.1, h.2.2⟩
  have hp : p.Prime := hH.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  rcases hcases with hrow | htag | htag
  · obtain ⟨labK', labJ, hlabK', hhasK', hlabJ, hdvd, hhasJ⟩ :=
      ggNbrK_label_J_of_tcj hTCJ hI3 hH.1 hH.2.2.1 hNB
    exact ⟨labJ, labK, hlabJ, hlabK, hhasJ, hhasK, hrow⟩
  · have hdvd : p ∣ 2 ^ labK.n - 1 ∨ p ∣ 2 ^ labK.n + 1 := by
      rcases hHSlab with h | h | h | h | h | h
      · exact Or.inr (TableBExcSmallRest.dvd_of_largeEvenSplit_twF4 htag hlabK h)
      · exfalso; rcases h.1 with h1 | h1 | h1 | h1 | h1 <;> simp [htag] at h1
      · exfalso; rcases h.1 with ⟨h1, -⟩ | h1 <;> simp [htag] at h1
      · exfalso; exact (by simp [htag] at h)
      · exfalso; exact (by simp [htag] at h)
      · exfalso; exact (by simp [htag] at h)
    have hrank := ggInnerDiagOnLabel_nbr_pRank_ge_three (S := fun _ lab' => lab' = labK)
      hH.1 hNB hmarkK
    have hbad : LargeEvenMarking ↥K (fun lab' R _ I _ _ =>
        (lab'.tag = .twF4 ∧ (p ∣ 2 ^ lab'.n - 1 ∨ p ∣ 2 ^ lab'.n + 1)) ∧
          ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
            p ^ 3 ≤ Nat.card E) := by
      refine largeEvenMarking_mono (fun lab' R _ I _ θ hP' => ?_) hrank
      rw [hP'.1]
      exact ⟨⟨htag, hdvd⟩, hP'.2⟩
    exact absurd hbad (ggInndiag_pRank_le_two_twF4 (X := ↥K) hp hp2)
  · have hrank := ggInnerDiagOnLabel_nbr_pRank_ge_three (S := fun _ lab' => lab' = labK)
      hH.1 hNB hmarkK
    have hbad : LargeEvenMarking ↥K (fun lab' R _ I _ _ =>
        lab'.tag = .twF4der ∧
          ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
            p ^ 3 ≤ Nat.card E) := by
      refine largeEvenMarking_mono (fun lab' R _ I _ θ hP' => ?_) hrank
      rw [hP'.1]
      exact ⟨htag, hP'.2⟩
    exact absurd hbad (ggInndiag_pRank_le_two_twF4der (X := ↥K) hp hp2)

theorem ggResXRest_of_known
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
      (¬ GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∨ GGTBWeylRowRes p lab) p Bs L →
          GGResRowAt ggRowSeven p J L) ∧
        (¬ GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∨ GGTBWeylRowRes p lab) p Bs K →
          GGResRowAt ggRowSeven p J K) := by
  intro G _ _ p B Bs x L D J y K hH _
  exact ⟨l05nKM_L_conj hRig hH, l05nKM_K_conj hRig hraw hiso hTCJ hI3 hH⟩

theorem ggResXDichotomy_of_res
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hR : GGTBXDatumResInput) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
      (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K) := by
  intro G _ _ p B Bs x L D J y K hH _
  have hrest := ggResXRest_of_known hRig hraw hiso hTCJ hI3 G p B Bs x L D J y K hH
  have hcov := ggResXDatum_of_cov_or_res hT hLift hR G p B Bs x L D J y K hH
  refine ⟨?_, ?_⟩
  · by_cases h : GGInnerDiagOnLabel
        (fun p lab => GGTBTorCov p lab ∨ GGTBWeylRowRes p lab) p Bs L
    · exact Or.inl (hcov.1 h)
    · exact Or.inr (hrest.1 h)
  · by_cases h : GGInnerDiagOnLabel
        (fun p lab => GGTBTorCov p lab ∨ GGTBWeylRowRes p lab) p Bs K
    · exact Or.inl (hcov.2 h)
    · exact Or.inr (hrest.2 h)

end CFSG.StandardType
