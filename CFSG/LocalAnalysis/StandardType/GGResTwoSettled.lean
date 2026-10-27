module

public import CFSG.LocalAnalysis.StandardType.GGResTwoSettledDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoCensusLabelL
public import CFSG.LocalAnalysis.StandardType.GGResExact2SpSplit
public import CFSG.LocalAnalysis.StandardType.GGResSingularAExactTwo
public import CFSG.LocalAnalysis.StandardType.GGResE6DepCardSix
public import CFSG.LocalAnalysis.StandardType.GGResUnitaryExactTwo
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUFinal
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CFinal
public import CFSG.LocalAnalysis.StandardType.GGResSmallSpExactTwo
public import CFSG.LocalAnalysis.StandardType.GGResF4ExactTwo
public import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthHolds
public import CFSG.LocalAnalysis.StandardType.GGRootGenSmallRankQFour
public import CFSG.LocalAnalysis.StandardType.GGTBXDatumResRest2
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRankExc
public import CFSG.LocalAnalysis.StandardType.GGResSeven
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGResLinTwoExactTwoL
import CFSG.LocalAnalysis.StandardType.GGResExcSplitExactTwoL
import CFSG.LocalAnalysis.StandardType.GGResF4SplitExactTwoL

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Small

theorem not_innerDiagOnLabel_threeSmall_of_pRank {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Bs X : Subgroup G} (hM : GGInnerDiagOnLabel ggThreeSmallLabel p Bs X)
    (hrk : ∀ {S : ℕ → LargeEvenLabel → Prop}, GGInnerDiagOnLabel S p Bs X →
      StandardType.LargeEvenMarking ↥X (fun lab R _ I _ _ => S p lab ∧
        ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
          p ^ 3 ≤ Nat.card E)) : False := by
  rcases GGInnerDiagOnLabel.elim_or (S := GGRootGenSmallRankLabel)
      (T := fun p lab => (GGRootGenSmallExcLabel p lab ∧ GGRootGenOpenLabel p lab) ∨
        StdSubRestThree.GGTwoThreeSmallLabel p lab ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)
      hM with h1 | hM
  · exact not_largeEvenMarking_smallRank hp hp2 (hrk h1)
  rcases GGInnerDiagOnLabel.elim_or
      (S := fun p lab => GGRootGenSmallExcLabel p lab ∧ GGRootGenOpenLabel p lab)
      (T := fun p lab => StdSubRestThree.GGTwoThreeSmallLabel p lab ∨ lab.tag = .G2der ∨
        lab.tag = .twF4der) hM with h1 | hM
  · exact not_largeEvenMarking_smallExc hp hp2 (hrk h1)
  rcases GGInnerDiagOnLabel.elim_or (S := StdSubRestThree.GGTwoThreeSmallLabel)
      (T := fun _ lab => lab.tag = .G2der ∨ lab.tag = .twF4der) hM with h1 | hM
  · exact ggInndiag_pRank_le_two_twoThreeSmall (hrk h1)
  rcases GGInnerDiagOnLabel.elim_or (S := fun _ lab => lab.tag = .G2der)
      (T := fun _ lab => lab.tag = .twF4der) hM with h1 | h1
  · exact ggInndiag_pRank_le_two_G2der hp hp2 (hrk h1)
  · exact ggInndiag_pRank_le_two_twF4der hp hp2 (hrk h1)

theorem GGResHyp.not_innerDiagOnLabel_threeSmall_L {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : ¬ GGInnerDiagOnLabel ggThreeSmallLabel p Bs L :=
  fun hM => not_innerDiagOnLabel_threeSmall_of_pRank Fact.out hH.1.1.2.2.2.2.2.1.2.1 hM
    (fun h => ggInnerDiagOnLabel_L_pRank_ge_three hH.1 h)

theorem GGResHyp.not_innerDiagOnLabel_threeSettled_K {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {sel : Prop → Prop → Prop}
    {typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop}
    (hH : GGResHyp p B Bs x L D J y K)
    (hD : GGResLeviDatumLE3 p Bs L J K sel typ ∨ GGResLeviDatumLE3 p Bs K J L sel typ) :
    ¬ GGInnerDiagOnLabel ggThreeSettledLabelK p Bs K := fun hM => by
  rcases GGInnerDiagOnLabel.elim_or (S := ggThreeSmallLabel)
      (T := fun p lab => p = 7 ∧
        ((lab.tag = .A ∧ lab.rank = 8 ∧ lab.n = 1) ∨ (lab.tag = .E6 ∧ lab.n = 1))) hM with
    hM | hM
  · exact not_innerDiagOnLabel_threeSmall_of_pRank Fact.out hH.1.1.2.2.2.2.2.1.2.1 hM
      (fun h => ggInnerDiagOnLabel_nbr_pRank_ge_three hH.1 hH.2.2.2.2.1 h)
  · obtain ⟨-, ⟨t, r, n⟩, hΛ, hraw⟩ := hM
    obtain ⟨R, _, I, F, -, -, θ, ⟨hp7, hlab⟩, -⟩ := largeEvenRawDatum_exists hraw
    have has : GGHasLabel ⟨t, r, n⟩ (↥K ⧸ Subgroup.center ↥K) := by
      unfold GGHasLabel
      refine largeEvenRawDatum_mono ?_ hraw
      rintro R _ I F ⟨-, -, θ, -⟩
      exact ⟨θ⟩
    dsimp only at hlab
    subst hp7
    refine ggSeven_K_absurd_of_leviLE3 hH ?_ hD
    rcases hlab with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl has
    · obtain rfl : r = 0 := hΛ.2
      exact Or.inr has

end Small

section Settled

theorem ggResMultiNodeRestTwoLeafL_of_settled (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hKG : GGReflClassLargeInput') (hB36 : GGNbrTablePNbrInputOnL GGRegimeB36L)
    (h : GGResMultiNodeRestTwoSettledInput) :
    GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
      GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny ∧
      ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
        GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) ∧
      ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K) := by
  intro G _ _ p B Bs x L D J y K hH hfact hF hS hE ⟨hL2, hD3, hres, htwo, hC2, hSU2⟩
  have : Fact p.Prime := hfact
  by_cases hE6 : p = 3 ∧ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypLE6
  · exact ggResLeaf_e6ExactTwo hB36 G p B Bs x L D J y K hH hF hS hE
      ⟨hE6.1, hE6.2, hD3, hres, htwo, hC2, hSU2⟩
  have hsmL := hH.not_innerDiagOnLabel_threeSmall_L
  have hK7 := hH.not_innerDiagOnLabel_threeSettled_K
    (Or.inl ((ggResLeviDatumLE3_iff_exact2_or_exact3 p Bs L J K _ _).mpr (Or.inl hL2)))
  by_cases hEi : GGInnerDiagOnLabel ggTwoSettledEitherLabelL p Bs L
  · rcases GGInnerDiagOnLabel.elim_or
        (S := fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ 5 ≤ lab.rank)
        (T := fun p lab => (p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧
            ¬ 3 ∣ lab.rank + 1) ∨ (p = 3 ∧ lab.tag = .F4 ∧ lab.n = 1)) hEi with hSp | hEi
    · exact HdRo7C.ggResLeviExact2_join_of_sp_innerDiag hH hSp (Or.inl hL2)
    rcases GGInnerDiagOnLabel.elim_or
        (S := fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧
          ¬ 3 ∣ lab.rank + 1)
        (T := fun p lab => p = 3 ∧ lab.tag = .F4 ∧ lab.n = 1) hEi with hSU | hF4
    · exact HdRo7SU.ggResSUCorank2_exact2_originalL hH hSU (Or.inl hL2) hKG hRig
    · obtain ⟨_, _, _, _, _, _, _, _, ⟨rfl, _⟩, _⟩ := largeEvenMarking_exists_hasLabel hF4
      exact (ggResF4ExactTwo_either_false hH hF4 (Or.inl hL2)).elim
  by_cases hLs : GGInnerDiagOnLabel ggTwoSettledLabelL p Bs L
  · rcases GGInnerDiagOnLabel.elim_or
        (S := fun p lab => (lab.tag = .B ∨ lab.tag = .C) ∧ 6 ≤ lab.rank ∧
          p ∣ 2 ^ lab.n - 1)
        (T := fun p lab =>
          (lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) ∨
            ((lab.tag = .twA ∧ 3 ≤ lab.rank ∨ lab.tag = .twD ∧ lab.rank = 3) ∧
              p ∣ 2 ^ lab.n + 1) ∨
            (p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 3) ∨
            (p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) ∨
            (p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧ lab.n = 1 ∧ 4 ≤ lab.rank) ∨
            (p = 3 ∧ lab.tag = .A ∧ lab.n = 1 ∧ 5 ≤ lab.rank) ∨
            ((lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ∣ 2 ^ lab.n - 1) ∨
            (lab.tag = .F4 ∧ p ∣ 2 ^ lab.n - 1)) hLs with
        hSpSplit | hLs
    · exact (hH.false_of_exact2_L_spSplit_geSix hSpSplit hL2).elim
    rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1)
        (T := fun p lab =>
          ((lab.tag = .twA ∧ 3 ≤ lab.rank ∨ lab.tag = .twD ∧ lab.rank = 3) ∧
              p ∣ 2 ^ lab.n + 1) ∨
            (p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 3) ∨
            (p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) ∨
            (p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧ lab.n = 1 ∧ 4 ≤ lab.rank) ∨
            (p = 3 ∧ lab.tag = .A ∧ lab.n = 1 ∧ 5 ≤ lab.rank) ∨
            ((lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ∣ 2 ^ lab.n - 1) ∨
            (lab.tag = .F4 ∧ p ∣ 2 ^ lab.n - 1)) hLs with
      hA | hM
    · exact (htwo (Or.inl (hH.rowTwoNode_of_large_linear_exact2 hRig hA hL2))).elim
    rcases GGInnerDiagOnLabel.elim_or
        (S := fun p lab => (lab.tag = .twA ∧ 3 ≤ lab.rank ∨ lab.tag = .twD ∧ lab.rank = 3) ∧
          p ∣ 2 ^ lab.n + 1)
        (T := fun p lab =>
          (p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 3) ∨
            (p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) ∨
            (p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧ lab.n = 1 ∧ 4 ≤ lab.rank) ∨
            (p = 3 ∧ lab.tag = .A ∧ lab.n = 1 ∧ 5 ≤ lab.rank) ∨
            ((lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ∣ 2 ^ lab.n - 1) ∨
            (lab.tag = .F4 ∧ p ∣ 2 ^ lab.n - 1)) hM with
      hU | hM
    · exact (hH.not_exactTwo_left_of_esu_allFields_not_rows hRig hU (fun h => htwo (Or.inl h))
        (fun h => hSU2 (Or.inl h)) hL2).elim
    rcases GGInnerDiagOnLabel.elim_or
        (S := fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 3)
        (T := fun p lab =>
          (p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) ∨
            (p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧ lab.n = 1 ∧ 4 ≤ lab.rank) ∨
            (p = 3 ∧ lab.tag = .A ∧ lab.n = 1 ∧ 5 ≤ lab.rank) ∨
            ((lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ∣ 2 ^ lab.n - 1) ∨
            (lab.tag = .F4 ∧ p ∣ 2 ^ lab.n - 1)) hM with
      hSp3 | hM
    · exact (ggResSmallSpThreeExactTwo_false hH hSp3 hL2).elim
    rcases GGInnerDiagOnLabel.elim_or
        (S := fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4)
        (T := fun p lab => (p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧ lab.n = 1 ∧ 4 ≤ lab.rank) ∨
          (p = 3 ∧ lab.tag = .A ∧ lab.n = 1 ∧ 5 ≤ lab.rank) ∨
          ((lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ∣ 2 ^ lab.n - 1) ∨
          (lab.tag = .F4 ∧ p ∣ 2 ^ lab.n - 1))
        hM with hSp4 | hM
    · exact (ggResSmallSpFourExactTwo_false hH hSp4 hL2).elim
    rcases GGInnerDiagOnLabel.elim_or
        (S := fun p lab => p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧ lab.n = 1 ∧ 4 ≤ lab.rank)
        (T := fun p lab => (p = 3 ∧ lab.tag = .A ∧ lab.n = 1 ∧ 5 ≤ lab.rank) ∨
          ((lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ∣ 2 ^ lab.n - 1) ∨
          (lab.tag = .F4 ∧ p ∣ 2 ^ lab.n - 1)) hM with hO | hM
    · exact ggResExactTwoOrthQTwoOn_holds hRig hKG G p B Bs x L D J y K hH hF hS hE
        ⟨hO, hL2, hD3, hres, htwo, hC2, hSU2⟩
    rcases GGInnerDiagOnLabel.elim_or
        (S := fun p lab => p = 3 ∧ lab.tag = .A ∧ lab.n = 1 ∧ 5 ≤ lab.rank)
        (T := fun p lab => ((lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ∣ 2 ^ lab.n - 1) ∨
          (lab.tag = .F4 ∧ p ∣ 2 ^ lab.n - 1)) hM with hLin | hM
    · obtain ⟨_, _, _, _, _, _, _, _, ⟨hp3, -⟩, _⟩ := largeEvenMarking_exists_hasLabel hLin
      subst hp3
      exact (hH.false_of_exact2_L_linTwo_of_marking
        (hLin.mono_label fun lab ⟨_, ht, hn, hr⟩ => ⟨ht, hr, hn, rfl⟩) hL2).elim
    rcases GGInnerDiagOnLabel.elim_or
        (S := fun p lab => (lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ∣ 2 ^ lab.n - 1)
        (T := fun p lab => lab.tag = .F4 ∧ p ∣ 2 ^ lab.n - 1) hM with hE78 | hF4
    · exact (hH.false_of_exact2_L_excSplit78 hE78 hL2).elim
    · exact (hH.false_of_exact2_L_f4Split hF4 hL2).elim
  have hKset : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny →
      ¬ GGInnerDiagOnLabel ggTwoSettledLabelK p Bs K := fun hK2 hM => by
    rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1)
        (T := fun p lab =>
          (p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧ ¬ 3 ∣ lab.rank + 1) ∨
            (p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1)) hM with hA | hM
    · exact htwo (Or.inr (hH.rowTwoNode_of_large_linear_K_exact2 hRig hLB hA hK2))
    rcases GGInnerDiagOnLabel.elim_or
        (S := fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧
          ¬ 3 ∣ lab.rank + 1)
        (T := fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1) hM with
      hU | hU
    · obtain ⟨_, _, _, _, _, _, _, _, ⟨hp3, _⟩, _⟩ := largeEvenMarking_exists_hasLabel hU
      exact hSU2 (Or.inr (HdRo7SU.su_exact2_right_row_of_exact2 hH hRig hU hp3 hLB hK2))
    · exact HdRo7SU.su_not_exact2_right_singular_original hH hU (fun h => htwo (Or.inr h)) hK2
  exact h G p B Bs x L D J y K hH hF hS hE
    ⟨hL2, hLs, hKset, hEi, hsmL, hK7, hD3, hres, htwo, hC2, hSU2⟩

end Settled

section Census

theorem GGResHyp.twoResidualLabel_L (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hE : ¬ GGInnerDiagOnLabel ggTwoSettledEitherLabelL p Bs L)
    (hS : ¬ GGInnerDiagOnLabel ggTwoSettledLabelL p Bs L)
    (hsm : ¬ GGInnerDiagOnLabel ggThreeSmallLabel p Bs L) :
    GGInnerDiagOnLabel ggTwoResidualLabelL p Bs L := by
  have hst : LargeEvenStandardType p B x L := hH.1.1.2.2.2.2.2.2.2
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hst.1
  have hall : ∀ S : ℕ → LargeEvenLabel → Prop, S p lab → GGInnerDiagOnLabel S p Bs L := by
    intro S hS'
    refine largeEvenMarking_mono ?_ (ggInnerDiagOn_relabel hRig hH.2.2.1.1 hlab hhas)
    rintro lab' R' _ I' F' θ' ⟨h1, h2, h3⟩
    subst h1
    exact ⟨hS', h2, h3⟩
  rcases ggTwoCensus_label_L hlab hP.1 with h | h | h | h
  · exact absurd (hall _ h) hE
  · exact absurd (hall _ h) hS
  · exact absurd (hall _ h) hsm
  · exact hall _ h

theorem ggResMultiNodeRestTwoSettledInput_of_census (hRig : GGLabelRigidInput)
    (h : GGResMultiNodeRestTwoCensusInput) : GGResMultiNodeRestTwoSettledInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE ⟨hL2, hnL, hK, hEi, hsm, hrest⟩
  exact h G p B Bs x L D J y K hH hF hS hE
    ⟨hL2, hnL, hK, hH.twoResidualLabel_L hRig hEi hnL hsm, hEi, hsm, hrest⟩

end Census

end CFSG.StandardType

end
