module

public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGResExcSplitExactTwoL
public import CFSG.LocalAnalysis.StandardType.GGResFixedWeylCentralizer
public import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase
public import CFSG.LocalAnalysis.StandardType.GGRCTypeADet
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1F4
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestExc
public import CFSG.LocalAnalysis.StandardType.GGIOneFieldCFHolds
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreField
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreTypeA
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGResHigherFieldI1
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyNbrFieldRows
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds
public import CFSG.LocalAnalysis.StandardType.GGTBE6
public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsCls
public import CFSG.LocalAnalysis.StandardType.GGResJOpenLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySp
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSCore
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem GGLabelIso.n_eq_of_twisted {a b : LargeEvenLabel} (h : GGLabelIso a b)
    (hb : b.tag = .twA ∨ b.tag = .twE6) : b.n = a.n := by
  obtain ⟨ta, ra, na⟩ := a
  obtain ⟨tb, rb, nb⟩ := b
  rcases h with h | ⟨-, -, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · cases h
    rfl
  · exact h.symm
  all_goals cases h
  all_goals first | rfl | (rcases hb with hb | hb <;> cases hb)

theorem GGResHyp.false_of_split_L_J_plusThree
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => p ∣ 2 ^ lab.n - 1) p Bs L)
    (hJ : GGInnerDiagOnLabel
      (fun p lab => (lab.tag = .twA ∨ lab.tag = .twE6) ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1) p Bs J) :
    False := by
  obtain ⟨lab, labJ, -, hpn, -, hΛJ, hdvd, hhasJ⟩ :=
    ggNbr_label_J_of_tcj_onLabel TCJ.ggTCJKnown_holds hH.1 hL hH.2.2.2.2.1
  obtain ⟨labJ', hΛJ', hhasJ', _, _, _, _, _, ⟨htag, hp3, hdvd'⟩, -⟩ :=
    largeEvenMarking_exists_hasLabel hJ
  subst hp3
  have hn : labJ'.n = labJ.n :=
    (ggLabelRigidInput_holds labJ labJ' _ hΛJ hΛJ' hhasJ hhasJ').n_eq_of_twisted htag
  have hev : Even labJ'.n := by
    rw [hn, even_iff_two_dvd]
    exact (even_iff_two_dvd.mp ((ggNbrLSide_three_dvd_two_pow_sub_one_iff _).mp hpn)).trans hdvd
  exact Nat.not_odd_iff_even.mpr hev ((ggNbrLSideRSExc_three_dvd_two_pow_add_one_iff _).mp hdvd')

theorem GGResHyp.false_of_exact2_L_f4Split
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel (fun p lab => lab.tag = .F4 ∧ p ∣ 2 ^ lab.n - 1) p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) : False := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hnp : ∀ n : ℕ, p ∣ 2 ^ n - 1 → ¬ p ∣ 2 ^ n + 1 := fun n h h' => by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : p ∣ 2 := by
      have := Nat.dvd_sub h' h
      rwa [show 2 ^ n + 1 - (2 ^ n - 1) = 2 by omega] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hrow : ∀ lab : LargeEvenLabel, lab.tag = .F4 ∧ p ∣ 2 ^ lab.n - 1 →
      GGTBTorRowAt p lab (4 - ggTorEnn p lab) (ggTorMpm p lab) 4 CartanMatrix.F₄
        CoxeterMatrix.F₄ := fun lab h =>
    GGTBTorRowAt.f4 h.1 (Dvd.dvd.mul_right h.2 _) fun h3 => hnp _ h.2 h3.2
  have hiOne : Bs ⊓ Subgroup.centralizer (J : Set G) = D :=
    hH.iOne_of_eq_bstar (hH.bstar_eq_of_excLSplit hp
      (hM.mono_label fun _ h => ⟨Or.inr (Or.inr h.1), h.2⟩))
  have hm5 : 5 ≤ LargeEvenTwoLocalRank p G :=
    hH.five_le_twoLocalRank_of_row_L (ggTBTorAll_of_remaining trivial) ggTBTorLiftRows_holds
      (hM.mono_label fun lab h => ⟨_, _, _, _, _, hrow lab h, by
        have := ggTorEnn_eq_zero_of_dvd_sub_one hp hp2 h.2
        omega⟩)
  have hLq : GGInnerDiagOnLabel
      (fun p lab => S2MathAs51642Interfaces.CenterPrimeTo p lab ∧ lab.tag = .F4) p Bs L :=
    hM.mono_label fun _ h => ⟨by simp [S2MathAs51642Interfaces.CenterPrimeTo,
      S2MathAs51642Interfaces.SmallDerived, h.1], h.1⟩
  have hJ : GGInnerDiagOn Bs J := q1On_centerPrimeTo_F4 G p B Bs x L D J hH.1 hLq
  have hJlab : GGInnerDiagOnLabel (fun _ _ => True) p Bs J :=
    (GGInnerDiagOn.label (fun _ _ => True) p hJ).mono_label (fun _ _ => trivial)
  have hLs : GGInnerDiagOnLabel (fun p lab => p ∣ 2 ^ lab.n - 1) p Bs L :=
    hM.mono_label fun _ h => h.2
  have hfwd : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
    rcases hH.fix_mem_centralizer_J_or_low_of_tcj (ggTBTorAll_of_remaining trivial)
      ggTBTorLiftRows_holds TCJ.ggTCJKnown_holds ggLabelRigidInput_holds hm5 hJlab with
      hfwd | ⟨-, hA5⟩ | ⟨-, hE6⟩
    · exact hfwd
    · exact (hH.false_of_split_L_J_plusThree hLs
        (hA5.mono_label fun _ h => ⟨Or.inl h.2.1, h.2.2.2.1, h.2.2.2.2⟩)).elim
    · exact (hH.false_of_split_L_J_plusThree hLs
        (hE6.mono_label fun _ h => ⟨Or.inr h.2.1, h.2.2.1, h.2.2.2⟩)).elim
  exact hH.false_of_exact2_nonsingular_L (ggTBTorAll_of_remaining trivial) ggTBTorLiftRows_holds
    hfwd (hM.mono_label fun lab h => ⟨⟨_, _, _, _, _, hrow lab h⟩, by
      simp [ggSingularBaseLabel, h.1]⟩) hiOne hD

end CFSG.StandardType

end
