module

public import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase
public import CFSG.LocalAnalysis.StandardType.GGResUnitaryQPlusKProducers
public import CFSG.LocalAnalysis.StandardType.GGResJOpenLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1DSmall
public import CFSG.LocalAnalysis.StandardType.GGResTwoCells
public import CFSG.LocalAnalysis.StandardType.GGResF4SplitExactTwoL
public import CFSG.LocalAnalysis.StandardType.GGResJOneReflCell
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdLabel
import CFSG.LocalAnalysis.StandardType.GGTCJHolds
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
import CFSG.LocalAnalysis.StandardType.GGTBE6

public section
namespace CFSG.StandardType
open CFSG CFSG.Assembly CFSG.StandardType.S2MathAs51642Interfaces
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGResHyp.innerDiag_J_of_orthogonal_split_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel GGCorFourTwoOrthSplitLabel p Bs L) :
    GGInnerDiagOn Bs J := by
  have hQ : GGInnerDiagOnLabel
      (fun p lab => CenterPrimeTo p lab ∧ (lab.tag = .D ∨ lab.tag = .twD)) p Bs L := by
    refine hL.mono_label fun lab h => ⟨?_, h.1⟩
    rcases h.1 with ht | ht <;> simp [CenterPrimeTo, SmallDerived, ht]
  exact q1DTwDInnerDiag_holds G p B Bs x L D J hH.1 hQ

theorem GGResHyp.nonsingular_row_L_of_orthogonal_split
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel GGCorFourTwoOrthSplitLabel p Bs L) :
    GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)
      p Bs L := by
  refine hL.mono_label fun lab h => ⟨?_, ?_⟩
  · rcases h.1 with ht | ht
    · exact ⟨_, _, _, _, _, GGTBTorRowAt.d (Or.inl ⟨ht, Or.inl h.2.2⟩)⟩
    · exact ⟨_, _, _, _, _, GGTBTorRowAt.relD (Or.inr ⟨ht, Or.inl h.2.2⟩)⟩
  · rcases h.1 with ht | ht <;> simp [ggSingularBaseLabel, ht]

theorem GGResHyp.five_le_twoLocalRank_of_orthogonal_split_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => GGCorFourTwoOrthSplitLabel p lab ∧
      (lab.tag = .D ∨ 5 ≤ lab.rank)) p Bs L) :
    5 ≤ LargeEvenTwoLocalRank p G := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  apply hH.five_le_twoLocalRank_of_row_L (ggTBTorAll_of_remaining trivial) ggTBTorLiftRows_holds
  refine hL.mono_label fun lab h => ?_
  rcases h.1.1 with ht | ht
  · refine ⟨_, _, _, _, _, GGTBTorRowAt.d (Or.inl ⟨ht, Or.inl h.1.2.2⟩), ?_⟩
    rw [ggTorEnn_eq_zero_of_dvd_sub_one hp hp2 h.1.2.2, Nat.sub_zero]
    exact h.1.2.1
  · have hr5 : 5 ≤ lab.rank := by
      rcases h.2 with hd | hr
      · simp [ht] at hd
      · exact hr
    exact ⟨_, _, _, _, _, GGTBTorRowAt.relD (Or.inr ⟨ht, Or.inl h.1.2.2⟩), by omega⟩

theorem GGResHyp.fix_mem_centralizer_J_or_low_of_orthogonal_split_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => GGCorFourTwoOrthSplitLabel p lab ∧
      (lab.tag = .D ∨ 5 ≤ lab.rank)) p Bs L) :
    (∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G)) ∨
      (LargeEvenTwoLocalRank p G = 5 ∧
        GGInnerDiagOnLabel GGTwA5PlusThreeLabel p Bs J) ∨
      (LargeEvenTwoLocalRank p G = 6 ∧
        GGInnerDiagOnLabel GGTableBTwE6ThreeLabel p Bs J) := by
  have hJ0 := hH.innerDiag_J_of_orthogonal_split_L (hL.mono_label fun _ h => h.1)
  have hJ : GGInnerDiagOnLabel (fun _ _ => True) p Bs J :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨trivial, h⟩) hJ0
  rcases hH.fix_mem_centralizer_J_or_low_of_tcj (ggTBTorAll_of_remaining trivial)
      ggTBTorLiftRows_holds TCJ.ggTCJKnown_holds ggLabelRigidInput_holds
      (hH.five_le_twoLocalRank_of_orthogonal_split_L hL) hJ with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h.1, h.2.mono_label fun _ h => h.2⟩)
  · exact Or.inr (Or.inr ⟨h.1, h.2.mono_label fun _ h => h.2⟩)

theorem GGResHyp.false_of_oneRefl_of_innerDiag_J
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJ : GGInnerDiagOn Bs J)
    {τ : MulAut ↥Bs} (hτ : GGIsReflection p τ)
    (hA : ggAutomizer J Bs = Subgroup.zpowers τ) : False := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  rcases (hJ.label GGResJOneReflLabel p).elim_or with hJ1 | hJ2
  · have hM := largeEvenMarking_and_labelAll_simple
      (S := fun lab => GGResJOneReflLabel p lab)
      (P' := fun R _ I _ => ∀ E : Subgroup (MulAut R),
        (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E → Nat.card E = p ^ 2 →
        ∃ F : Subgroup R, IsPGroup p F ∧ ¬ IsCyclic F)
      (fun lab hlab hS => ggResJOneReflLabelInput_holds p hp2 lab hlab hS)
      (fun _ _ _ _ _ _ hP => hP.1) hJ1
    obtain ⟨hJperf, lab, -, hraw⟩ := hM
    obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBN, h3⟩, hP'⟩ := largeEvenRawDatum_exists hraw
    haveI : Finite R := Finite.of_equiv (J ⧸ Subgroup.center J) θ.toEquiv
    let E := (ggBeta J θ hBN).range
    have hE : IsElemAbelian p E := isElemAbelian_range_ggBeta θ hBs hBN
    have hEsq : p ^ 2 ≤ Nat.card E := by
      rw [NbrU63.card_range_ggBeta_eq hJperf θ hBN]
      exact hH.sq_le_card_gamma_J
    obtain ⟨k, hk⟩ := hE.isPGroup.exists_card_eq
    have h2k : 2 ≤ k := by
      rw [hk] at hEsq
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hEsq
    have hdvd : p ^ 2 ∣ Nat.card E := by
      rw [hk]
      exact Nat.pow_dvd_pow p h2k
    obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
    let E9 := Q.map E.subtype
    have hE9le : E9 ≤ E := Subgroup.map_subtype_le Q
    have hE9 : IsElemAbelian p E9 := hE.mono hE9le
    have hE9card : Nat.card E9 = p ^ 2 := by
      rw [← Nat.card_congr (Q.equivMapOfInjective E.subtype E.subtype_injective).toEquiv]
      exact hQ
    obtain ⟨F', hF', hnc⟩ := hP' E9
      (by intro a ha
          obtain ⟨b, rfl⟩ := hE9le ha
          exact ggBeta_mem J θ hBN h3 b) hE9 hE9card
    obtain ⟨S, hSJ, hSp, hSnc⟩ := exists_noncyclic_of_noncyclic_quot
      (θ.toMonoidHom.comp (QuotientGroup.mk' _))
      (θ.surjective.comp (QuotientGroup.mk'_surjective _)) hF' hnc
    exact hSnc (hH.isCyclic_of_le_J_of_oneRefl hτ hA hSp hSJ)
  · obtain ⟨hJperf, lab, -, hraw⟩ := largeEvenMarking_and_labelAll
      (S := fun lab => ¬ GGResJOneReflLabel p lab)
      (P' := fun R _ _ _ => ∃ r, 2 ≤ r ∧ GGTorusLift p r R)
      (fun lab hΛ h => by
        simp only [GGResJOneReflLabel, not_forall, not_le, exists_prop] at h
        obtain ⟨r, m, N, C, M, hrow, hr⟩ := h
        exact (ggTBTorLiftRows_holds p lab r m N C M hp hp2 hΛ hrow).mono
          fun _ _ _ _ hT => ⟨r, hr, hT⟩)
      (fun _ _ _ _ _ _ hP => hP.1) hJ2
    obtain ⟨R, _, I, F, -, -, θ, -, r, hr, hT⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨S, hSJ, hSp, hSnc⟩ := UnitTB.exists_noncyclic_of_torusLift hp hr hJperf θ hT
    exact hSnc (hH.isCyclic_of_le_J_of_oneRefl hτ hA hSp hSJ)

theorem GGResHyp.fix_iff_centralizer_J_of_orthogonal_split_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => GGCorFourTwoOrthSplitLabel p lab ∧
      (lab.tag = .D ∨ 5 ≤ lab.rank)) p Bs L) :
    ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  have hLs : GGInnerDiagOnLabel (fun p lab => p ∣ 2 ^ lab.n - 1) p Bs L :=
    hL.mono_label fun _ h => h.1.2.2
  have hfwd : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
    rcases hH.fix_mem_centralizer_J_or_low_of_orthogonal_split_L hL with h | h5 | h6
    · exact h
    · exact (hH.false_of_split_L_J_plusThree hLs
        (h5.2.mono_label fun _ h => ⟨Or.inl h.1, h.2.2.1, h.2.2.2⟩)).elim
    · exact (hH.false_of_split_L_J_plusThree hLs
        (h6.2.mono_label fun _ h => ⟨Or.inr h.1, h.2.1, h.2.2⟩)).elim
  intro b
  constructor
  · exact hfwd b
  · intro hb
    have hJC : J ≤ Subgroup.centralizer ({(b : G)} : Set G) := by
      intro j hj
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hg' : g = (b : G) := by simpa using hg
      subst g
      exact (Subgroup.mem_centralizer_iff.mp hb j hj).symm
    exact ggResI_automizer_fix b.2 hJC

theorem GGResHyp.false_of_exact2_L_orthSplit_twDFour
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => GGCorFourTwoOrthSplitLabel p lab ∧
      lab.tag = .twD ∧ lab.rank = 4) p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) : False := by
  classical
  have hL0 : GGInnerDiagOnLabel GGCorFourTwoOrthSplitLabel p Bs L :=
    hL.mono_label fun _ h => h.1
  have hrow : GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ)
      (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
      GGTBTorRowAt p lab r m N C M ∧ N = 3 ∧ GGIsWeylMatrix M) p Bs L := by
    refine hL.mono_label fun lab h => ?_
    refine ⟨_, _, _, _, _, GGTBTorRowAt.relD (Or.inr ⟨h.2.1, Or.inl h.1.2.2⟩),
      by omega, ?_⟩
    refine Or.inl ⟨lab.rank - 1, Equiv.refl _, by omega, Or.inr (Or.inl ⟨by omega, ?_⟩)⟩
    rfl
  obtain ⟨r, m, N, C, M, ⟨hN, hWM⟩, hcardL⟩ :=
    hH.exists_row_card_automizer_L (ggTBTorAll_of_remaining trivial) ggTBTorLiftRows_holds hrow
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS2, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hdel, hclosJ⟩ := hD
  have hcardML : Nat.card ML.Group = Nat.card M.Group :=
    (Nat.card_congr fL.toEquiv).trans hcardL
  have hrank : Fintype.card Λ = N := ggWeylTypeData_rank_eq
    (ggWeylTypeData_of_isWeylMatrix hML)
    (by rw [hcardML]; simpa using ggWeylTypeData_of_isWeylMatrix hWM)
  have hcompl : Fintype.card {i : Λ // i ∉ S} = 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hrank, hN, hS2]
  obtain ⟨j, hj⟩ := Fintype.card_eq_one_iff.mp hcompl
  have hgen : Set.range (fun i : {i : Λ // i ∉ S} => φ (Sum.inl i.1)) =
      {φ (Sum.inl j.1)} := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      rw [hj i]
      exact Set.mem_singleton _
    · intro ha
      have ha' : a = φ (Sum.inl j.1) := Set.mem_singleton_iff.mp ha
      exact ⟨j, ha'.symm⟩
  have hAJ : ggAutomizer J Bs = Subgroup.zpowers (φ (Sum.inl j.1)) := by
    rw [hclosJ, hgen, ← Subgroup.zpowers_eq_closure]
  exact hH.false_of_oneRefl_of_innerDiag_J
    (hH.innerDiag_J_of_orthogonal_split_L hL0) (hrefl _) hAJ

theorem GGResHyp.false_of_exact2_L_orthSplit
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel GGCorFourTwoOrthSplitLabel p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) : False := by
  have hsplit : GGInnerDiagOnLabel (fun p lab =>
      (GGCorFourTwoOrthSplitLabel p lab ∧ (lab.tag = .D ∨ 5 ≤ lab.rank)) ∨
        (GGCorFourTwoOrthSplitLabel p lab ∧ lab.tag = .twD ∧ lab.rank = 4)) p Bs L := by
    refine hL.mono_label fun lab h => ?_
    have hr4 : 4 ≤ lab.rank := h.2.1
    by_cases hr : 5 ≤ lab.rank
    · exact Or.inl ⟨h, Or.inr hr⟩
    · rcases h.1 with ht | ht
      · exact Or.inl ⟨h, Or.inl ht⟩
      · exact Or.inr ⟨h, ht, by omega⟩
  rcases hsplit.elim_or with hhi | hlo
  · have hI1 := hH.iOne_of_eq_bstar (hH.bstar_eq_of_orthogonal_split_L hL)
    have htyped := ggResExact2_typed_dichotomy_L_of_fixed hH hI1
      (hH.fix_iff_centralizer_J_of_orthogonal_split_L hhi) hD
    exact hH.false_of_singular_card_nonsingular_L (ggTBTorAll_of_remaining trivial)
      ggTBTorLiftRows_holds (hH.nonsingular_row_L_of_orthogonal_split hL)
      (GGResLeviDatumCard.singular_card htyped)
  · exact hH.false_of_exact2_L_orthSplit_twDFour hlo hD

theorem ggResMultiNodeRestTwoCellInput_orthSplit :
    GGResMultiNodeRestTwoCellInput GGCorFourTwoOrthSplitLabel := by
  apply GGResMultiNodeRestTwoCellInput.of_false
  intro G _ _ p _ B Bs x L D J y K hH hL hD
  exact hH.false_of_exact2_L_orthSplit hL hD

end CFSG.StandardType
end
