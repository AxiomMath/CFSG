module

public import CFSG.LocalAnalysis.StandardType.GGTBXDatumResRest2Defs
public import CFSG.LocalAnalysis.StandardType.GGRootGenSmallRankQFour
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRank
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRankExc
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeVac
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitMarking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggInndiag_pRank_le_two_twoThreeSmall {X : Type} [Group X] {p : ℕ} :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ =>
      StdSubRestThree.GGTwoThreeSmallLabel p lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) :=
  not_largeEvenMarking_of_labelAll_card_lt fun _ _ h =>
    (StdSubRestThree.largeEvenLabelAll_card_lt_twoThreeSmall h).mono fun _ _ _ _ h' _ _ => h'

private abbrev ResBig (p : ℕ) {R : Type} [Group R] (I : Set (MulAut R)) : Prop :=
  ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E

private theorem resSmall_or {X : Type} [Group X] {p : ℕ} {P Q : LargeEvenLabel → Prop}
    (hP : ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => P lab ∧ ResBig p I))
    (hQ : ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => Q lab ∧ ResBig p I)) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => (P lab ∨ Q lab) ∧ ResBig p I) := by
  intro h
  have h' := largeEvenMarking_mono
    (P' := fun lab R _ I _ _ => (P lab ∧ ResBig p I) ∨ (Q lab ∧ ResBig p I))
    (fun _ _ _ _ _ _ hPQE => by
      rcases hPQE with ⟨hPQ, hE⟩
      exact hPQ.elim (fun hP' => Or.inl ⟨hP', hE⟩) (fun hQ' => Or.inr ⟨hQ', hE⟩)) h
  rcases largeEvenMarking_or h' with hP' | hQ'
  · exact hP hP'
  · exact hQ hQ'

private theorem resSmall_imp {X : Type} [Group X] {p : ℕ} {P Q : LargeEvenLabel → Prop}
    (hQ : ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => Q lab ∧ ResBig p I))
    (hPQ : ∀ lab, P lab → Q lab) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => P lab ∧ ResBig p I) :=
  fun h => hQ (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hPQ _ hP.1, hP.2⟩) h)

theorem not_largeEvenMarking_resSmall
    {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ =>
      (GGTBWeylRowResRest p lab ∧ GGTBResSmallLabel p lab) ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) := by
  have hall := resSmall_or (ggInndiag_pRank_le_two_A2 (X := X) hp hp2)
    (resSmall_or (ggInndiag_pRank_le_two_twoThreeSmall (X := X) (p := p))
      (resSmall_or (ggInndiag_pRank_le_two_twA2 (X := X) hp hp2)
        (resSmall_or (ggInndiag_pRank_le_two_B2der (X := X) hp hp2)
          (resSmall_or (ggInndiag_pRank_le_two_G2der (X := X) hp hp2)
            (resSmall_or (ggInndiag_pRank_le_two_triD4 (X := X) hp)
              (ggInndiag_pRank_le_two_twB2 (X := X) hp hp2))))))
  refine resSmall_imp hall ?_
  rintro lab ⟨hrest, hsmall⟩
  rcases hsmall with ⟨htag, hr | ⟨hr, hn, hp3⟩⟩ | ⟨htag, hr⟩ | htag | htag | htag | htag
  · exact Or.inl ⟨htag, hr⟩
  · exact Or.inr (Or.inl ⟨hp3, hn, Or.inl ⟨htag, by omega⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨htag, hr⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl htag)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htag))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨htag, ?_⟩)))))
    have hHS : LargeEvenHalfSplit p lab True := hrest.1.2.1
    have key : p ∣ 2 ^ lab.n - 1 ∨ (lab.n = 1 ∧ p = 3) := by
      unfold LargeEvenHalfSplit LargeEvenSplit at hHS
      rw [htag] at hHS
      simpa [LargeEvenUntwisted] using hHS
    rcases key with h | ⟨hn, hp3⟩
    · exact Or.inl h
    · exact Or.inr (by rw [hn, hp3]; norm_num)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr htag)))))

theorem ggTBWeylRowResRest_small_false_L
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => GGTBWeylRowResRest p lab ∧ GGTBResSmallLabel p lab)
      p Bs L) : False :=
  not_largeEvenMarking_resSmall (X := ↥L) hcfg.1.2.2.2.2.2.1.1 hcfg.1.2.2.2.2.2.1.2.1
    (ggInnerDiagOnLabel_L_pRank_ge_three hcfg hL)

theorem ggTBWeylRowResRest_small_false_nbr
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hnb : GGNbr p B x D J y K)
    (hK : GGInnerDiagOnLabel (fun p lab => GGTBWeylRowResRest p lab ∧ GGTBResSmallLabel p lab)
      p Bs K) : False :=
  not_largeEvenMarking_resSmall (X := ↥K) hcfg.1.2.2.2.2.2.1.1 hcfg.1.2.2.2.2.2.1.2.1
    (ggInnerDiagOnLabel_nbr_pRank_ge_three hcfg hnb hK)

theorem ggTBXDatumResInputRest_of_rest2
    (h : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
        (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
        (GGInnerDiagOnLabel GGTBWeylRowResRest2 p Bs L → GGResXDatum p Bs L) ∧ (GGInnerDiagOnLabel
        GGTBWeylRowResRest2 p Bs K → GGResXDatum p Bs K)) :
    GGTBXDatumResInputRest := by
  intro G _ _ p B Bs x L D J y K hH hp
  have h2 := h G p B Bs x L D J y K hH
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  constructor
  · intro hM
    obtain ⟨hperf, lab, hlab, hraw⟩ := hM
    by_cases hc : GGTBResSmallLabel p lab
    · exact (ggTBWeylRowResRest_small_false_L hH.1 ⟨hperf, lab, hlab,
        largeEvenRawDatum_mono (fun R _ I F hQ => by
          obtain ⟨hs, hna, θ, hθ⟩ := hQ
          exact ⟨hs, hna, θ, ⟨⟨hθ.1, hc⟩, hθ.2⟩⟩) hraw⟩).elim
    · refine h2.1 ⟨hperf, lab, hlab, ?_⟩
      exact largeEvenRawDatum_mono (fun R _ I F hQ => by
        obtain ⟨hs, hna, θ, hθ⟩ := hQ
        exact ⟨hs, hna, θ, ⟨⟨hθ.1, hc⟩, hθ.2⟩⟩) hraw
  · intro hM
    obtain ⟨hperf, lab, hlab, hraw⟩ := hM
    by_cases hc : GGTBResSmallLabel p lab
    · exact (ggTBWeylRowResRest_small_false_nbr hH.1 hnb ⟨hperf, lab, hlab,
        largeEvenRawDatum_mono (fun R _ I F hQ => by
          obtain ⟨hs, hna, θ, hθ⟩ := hQ
          exact ⟨hs, hna, θ, ⟨⟨hθ.1, hc⟩, hθ.2⟩⟩) hraw⟩).elim
    · refine h2.2 ⟨hperf, lab, hlab, ?_⟩
      exact largeEvenRawDatum_mono (fun R _ I F hQ => by
        obtain ⟨hs, hna, θ, hθ⟩ := hQ
        exact ⟨hs, hna, θ, ⟨⟨hθ.1, hc⟩, hθ.2⟩⟩) hraw

theorem ggPZNbrResDatumRest_of_rest2
    (h : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G) (L D J
        : Subgroup G) (y : G) (K : Subgroup G) (labJ labX : LargeEvenLabel) (X : Subgroup G) (m : ℕ)
        (z : ↥Bs), GGPZPrem p B Bs x L D J y K labJ labX X m z → ∀ Y : Subgroup G,
        LargeEvenPComponent p (Subgroup.centralizer ({(z : G)} : Set G)) Y → J ≤ Y → Bs ≤
        Subgroup.normalizer (Y : Set G) → GGNbr p B x D J (z : G) Y → GGInnerDiagOnLabel
        GGTBWeylRowResRest2 p Bs Y → GGResXDatumSurj p Bs Y) : GGPZNbrResDatumRest := by
  intro G _ _ p _ B Bs x L D J y K labJ labX X m z hprem Y hY hJY hBsY hnb hMark
  obtain ⟨hperf, lab, hlab, hraw⟩ := hMark
  by_cases hc : GGTBResSmallLabel p lab
  · exact (ggTBWeylRowResRest_small_false_nbr (hprem.1.1 : GGConfig p B Bs x L D J) hnb
      ⟨hperf, lab, hlab, largeEvenRawDatum_mono (fun R _ I F hQ => by
        obtain ⟨hs, hna, θ, hθ⟩ := hQ
        exact ⟨hs, hna, θ, ⟨⟨hθ.1, hc⟩, hθ.2⟩⟩) hraw⟩).elim
  · refine h G p B Bs x L D J y K labJ labX X m z hprem Y hY hJY hBsY hnb ⟨hperf, lab, hlab, ?_⟩
    exact largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨hs, hna, θ, hθ⟩ := hQ
      exact ⟨hs, hna, θ, ⟨⟨hθ.1, hc⟩, hθ.2⟩⟩) hraw

end CFSG.StandardType

end
