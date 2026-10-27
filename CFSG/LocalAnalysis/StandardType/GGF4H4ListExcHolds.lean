module

public import CFSG.LocalAnalysis.StandardType.GGF4H4ListFamilies
public import CFSG.LocalAnalysis.StandardType.GGF4SmallBook
public import CFSG.LocalAnalysis.StandardType.GGF4H4ListExcRank
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGRootGenExcLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreSix
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreExc
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreExcB
public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsCls
public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsExc
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoThree
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6
public import CFSG.LocalAnalysis.StandardType.GGResRowF4ThreeOn
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeExcSevenAux
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTables
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
public import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem one_le_n_of_hasLabel_exc {R : Type} [Group R] {lab : LargeEvenLabel}
    (htag : GGF4TagExc lab.tag) (h : GGHasLabel lab R) : 1 ≤ lab.n := by
  obtain ⟨t, r, n⟩ := lab
  rcases htag with h | h | h | h | h <;> subst h
  all_goals
    unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum at h
    dsimp only at h
    obtain ⟨K, hField, hFinite, hK, -⟩ := h
    have hNontriv : Nontrivial K := ⟨0, 1, zero_ne_one⟩
    have h1 : 1 < Nat.card K := (@Finite.one_lt_card_iff_nontrivial K hFinite).mpr hNontriv
    have h2 : 2 ≤ Nat.card K := by omega
    have hn0 : n ≠ 0 := by
      rintro rfl
      norm_num at hK
      omega
    exact Nat.pos_of_ne_zero hn0

private theorem hasLabel_rank_zero_of_exc {R : Type} [Group R] {lab : LargeEvenLabel}
    (htag : GGF4TagExc lab.tag) (h : GGHasLabel lab R) :
    GGHasLabel ⟨lab.tag, 0, lab.n⟩ R := by
  obtain ⟨t, r, n⟩ := lab
  rcases htag with h | h | h | h | h <;> subst h <;>
    simpa [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum] using h


private theorem ggF4Exc_halfSplit_rows
    {p : ℕ} {lab : LargeEvenLabel} {c : Prop}
    (hp : p.Prime) (hp2 : p ≠ 2) (hlab : LargeEvenInLambda2 lab)
    (htag : GGF4TagExc lab.tag) (hHS : LargeEvenHalfSplit p lab c) :
    LargeEvenLabelAll lab (fun R _ _ _ => ∃ r, 4 ≤ r ∧ GGTorusLift p r R) ∨
      (lab.tag = .F4 ∧ p ∣ 2 ^ lab.n + 1) ∨
      (lab.tag = .E6 ∧ lab.n = 1 ∧ p = 7) := by
  obtain ⟨t, l, n⟩ := lab
  rcases htag with htag | htag | htag | htag | htag <;> subst htag
  · rcases NbrInnerMore.halfSplit_E6_cases hHS with hminus | ⟨hn1, hp3⟩ | ⟨hn1, hp7⟩
    · by_cases h3 : p = 3
      · subst h3
        exact Or.inl ((largeEvenLabelAll_torusLift_E6_three rfl hminus).mono
          (fun R _ _ _ hl => ⟨5, by norm_num, hl⟩))
      · have hpM : p ∣ ggTorM ⟨.E6, l, n⟩ := by simpa [ggTorM] using hminus
        have hlift := ggTBTorLift_e6Ind hp hp2 h3 hlab (Or.inl rfl) hpM
        have hEnn : ggTorEnn p ⟨.E6, l, n⟩ = 0 :=
          ggTorEnn_eq_zero_of_dvd_sub_one hp hp2 hminus
        exact Or.inl (hlift.mono fun R _ _ _ hl => ⟨6, by
          rw [hEnn] at hl
          exact ⟨by norm_num, by simpa using hl⟩⟩)
    · subst hn1
      subst hp3
      exact Or.inl ((largeEvenLabelAll_torusLift_E6_two ⟨rfl, rfl⟩).mono
        (fun R _ _ _ hl => ⟨4, by norm_num, hl⟩))
    · exact Or.inr (Or.inr ⟨rfl, hn1, hp7⟩)
  · rcases NbrInnerMore.halfSplit_E7_cases hHS with hminus | hplus | ⟨hn1, hp3⟩
    · have hprod : p ∣ (2 ^ n - 1) * (2 ^ n + 1) := dvd_mul_of_dvd_left hminus _
      have hlift := ggTBTorLift_e7 hp hp2 (lab := ⟨.E7, l, n⟩) rfl hprod
      have hEnn : ggTorEnn p ⟨.E7, l, n⟩ = 0 :=
        ggTorEnn_eq_zero_of_dvd_sub_one hp hp2 hminus
      exact Or.inl (hlift.mono fun R _ _ _ hl => ⟨7, by
        rw [hEnn] at hl
        exact ⟨by norm_num, by simpa using hl⟩⟩)
    · have hprod : p ∣ (2 ^ n - 1) * (2 ^ n + 1) := dvd_mul_of_dvd_right hplus _
      have hlift := ggTBTorLift_e7 hp hp2 (lab := ⟨.E7, l, n⟩) rfl hprod
      exact Or.inl (hlift.mono fun R _ _ _ hl =>
        ⟨7 - ggTorEnn p ⟨.E7, l, n⟩, by
          have hle : ggTorEnn p ⟨.E7, l, n⟩ ≤ 1 := by
            unfold ggTorEnn
            split <;> norm_num
          omega, hl⟩)
    · subst hn1
      subst hp3
      have hprod : 3 ∣ (2 ^ 1 - 1) * (2 ^ 1 + 1) := by norm_num
      have hlift := ggTBTorLift_e7 (p := 3) (by norm_num) (by norm_num)
        (lab := ⟨.E7, l, 1⟩) rfl hprod
      exact Or.inl (hlift.mono fun R _ _ _ hl =>
        ⟨7 - ggTorEnn 3 ⟨.E7, l, 1⟩, by
          have hle : ggTorEnn 3 ⟨.E7, l, 1⟩ ≤ 1 := by
            unfold ggTorEnn
            split <;> norm_num
          omega, hl⟩)
  · rcases NbrInnerMore.halfSplit_E8_cases hHS with hminus | hplus | ⟨hn1, hp3⟩
    · have hprod : p ∣ (2 ^ n - 1) * (2 ^ n + 1) := dvd_mul_of_dvd_left hminus _
      have hlift := ggTBTorLift_e8 hp hp2 (lab := ⟨.E8, l, n⟩) rfl hprod
      have hEnn : ggTorEnn p ⟨.E8, l, n⟩ = 0 :=
        ggTorEnn_eq_zero_of_dvd_sub_one hp hp2 hminus
      exact Or.inl (hlift.mono fun R _ _ _ hl => ⟨8, by
        rw [hEnn] at hl
        exact ⟨by norm_num, by simpa using hl⟩⟩)
    · have hprod : p ∣ (2 ^ n - 1) * (2 ^ n + 1) := dvd_mul_of_dvd_right hplus _
      have hlift := ggTBTorLift_e8 hp hp2 (lab := ⟨.E8, l, n⟩) rfl hprod
      exact Or.inl (hlift.mono fun R _ _ _ hl =>
        ⟨8 - ggTorEnn p ⟨.E8, l, n⟩, by
          have hle : ggTorEnn p ⟨.E8, l, n⟩ ≤ 1 := by
            unfold ggTorEnn
            split <;> norm_num
          omega, hl⟩)
    · subst hn1
      subst hp3
      have hprod : 3 ∣ (2 ^ 1 - 1) * (2 ^ 1 + 1) := by norm_num
      have hlift := ggTBTorLift_e8 (p := 3) (by norm_num) (by norm_num)
        (lab := ⟨.E8, l, 1⟩) rfl hprod
      exact Or.inl (hlift.mono fun R _ _ _ hl =>
        ⟨8 - ggTorEnn 3 ⟨.E8, l, 1⟩, by
          have hle : ggTorEnn 3 ⟨.E8, l, 1⟩ ≤ 1 := by
            unfold ggTorEnn
            split <;> norm_num
          omega, hl⟩)
  · rcases NbrInnerMore.halfSplit_F4_cases hHS with hminus | hplus | ⟨hn1, hp3⟩
    · have hprod : p ∣ (2 ^ n - 1) * (2 ^ n + 1) := dvd_mul_of_dvd_left hminus _
      have hlift := ggTBTorLift_f4 hp hp2 (lab := ⟨.F4, l, n⟩) rfl hprod
      have hEnn : ggTorEnn p ⟨.F4, l, n⟩ = 0 :=
        ggTorEnn_eq_zero_of_dvd_sub_one hp hp2 hminus
      exact Or.inl (hlift.mono fun R _ _ _ hl => ⟨4, by
        rw [hEnn] at hl
        exact ⟨by norm_num, by simpa using hl⟩⟩)
    · exact Or.inr (Or.inl ⟨rfl, hplus⟩)
    · subst hn1
      subst hp3
      exact Or.inr (Or.inl ⟨rfl, by norm_num⟩)
  · rcases NbrInnerMore.halfSplit_twE6_cases hHS with hminus | hplus | ⟨hn1, hp3⟩
    · exact Or.inl ((largeEvenLabelAll_torusLift_twE6Dvd hp hp2 hlab ⟨rfl, hminus⟩).mono
        (fun R _ _ _ hl => ⟨4, by norm_num, hl⟩))
    · have hlift := largeEvenLabelAll_torusLift_twE6Add_holds hp hlab ⟨rfl, hplus⟩
      by_cases h3 : p = 3
      · subst h3
        exact Or.inl (hlift.mono fun R _ _ _ hl => ⟨4, by
          rw [TwE6Delta.liftRank_three] at hl
          exact ⟨by norm_num, hl⟩⟩)
      · exact Or.inl (hlift.mono fun R _ _ _ hl => ⟨5, by
          rw [TwE6Delta.liftRank_of_ne h3] at hl
          exact ⟨by norm_num, hl⟩⟩)
    · subst hn1
      subst hp3
      have hplus : 3 ∣ 2 ^ 1 + 1 := by norm_num
      have hlift := largeEvenLabelAll_torusLift_twE6Add_holds (p := 3) (by norm_num) hlab
        ⟨rfl, hplus⟩
      exact Or.inl (hlift.mono fun R _ _ _ hl => ⟨4, by
        rw [TwE6Delta.liftRank_three] at hl
        exact ⟨by norm_num, hl⟩⟩)

theorem ggF4H4ListExc_holds
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hTP : GGSecFiveA8TablePInput) : GGF4H4ListExc := by
  intro G _ _ p B Bs x L D J ks hres _ K hK lab htag hlab
  classical
  obtain ⟨hR, -, ⟨ι, M, e, hP, hF⟩, hA3, -⟩ := hres
  have hrest : GGSecFiveRestHyp p B Bs x L D J := hR.1
  have hcfg : GGConfig p B Bs x L D J := hrest.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hT : GGNoTransvection p Bs := hrest.2.2.2.1
  have hW4 : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizerJoin L Bs ks) :=
    ggF4Small_weylOfType_F4 e hP hF
  have hne : ks.Nonempty := ggF4Small_ks_nonempty hW4 hA3
  have hcard : Nat.card Bs = p ^ 4 := ggF4Small_card_Bs hTBF hWI hR hW4 hne
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK
  have hInnK : GGInnerDiagOn Bs K := hrest.2.2.1.2 y K hnb
  have hraw : GGRawInnFieldInput := ggRawInnFieldInput_holds
  have hiso : GGRawInndiagIsoInput :=
    ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds)
  obtain ⟨lab₁, hΛ₁, hhas₁, -, -, -, -, -, hHS⟩ :=
    largeEvenMarking_exists_hasLabel (ggNbr_halfSplit_of_secFiveRest hraw hiso hrest hnb)
  let lab' : LargeEvenLabel := ⟨lab.tag, 0, lab.n⟩
  have htag' : GGRootGenExcTag lab' := htag
  have hΛ' : LargeEvenInLambda2 lab' := by
    have hn : 1 ≤ lab.n := one_le_n_of_hasLabel_exc (lab := lab) htag hlab
    rcases htag with h | h | h | h | h <;>
      simp [LargeEvenInLambda2, lab', h, hn]
  have hlab' : GGHasLabel lab' (K ⧸ Subgroup.center K) :=
    hasLabel_rank_zero_of_exc htag hlab
  have heq : lab₁ = lab' :=
    eq_of_ggLabelIso_of_excTag htag'
      (ggLabelRigidInput_holds lab' lab₁ _ hΛ' hΛ₁ hlab' hhas₁)
  subst heq
  have hInn' : GGInnerDiagOnLabel (fun _ l => l = lab') p Bs K :=
    ggInnerDiagOn_relabel ggLabelRigidInput_holds hInnK hΛ' hhas₁
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := by
    have hInnK' : GGInnerDiagOn Bs K :=
      largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.2.1, hP.2.2⟩) hInn'
    exact ggInnerDiagOn_le_normalizer hInnK'
  rcases ggF4Exc_halfSplit_rows hp hp2 hΛ' htag' hHS with
    hlift | ⟨hF4, hplus⟩ | ⟨hE6, hn1, hp7⟩
  · refine false_of_nbr_torusLift_ge_four hcfg hcard hnb hInn' ?_
    intro lab hΛlab hS
    rw [hS]
    exact hlift
  · have hM5 : GGInnerDiagOnLabel (fun q l => l.tag = .F4 ∧ q ∣ 2 ^ l.n + 1) p Bs K := by
      refine largeEvenMarking_mono ?_ hInn'
      intro lab R _ I F θ hP
      obtain ⟨hEq, hN1, hAct⟩ := hP
      subst hEq
      refine ⟨?_, hN1, hAct⟩
      change lab'.tag = .F4 ∧ p ∣ 2 ^ lab'.n + 1
      exact ⟨hF4, hplus⟩
    have hge : p ^ 4 ≤ Nat.card (ggGamma K hN).range := by
      by_cases hp3 : p = 3
      · have hM3 : GGInnerDiagOnLabel GGF4ThreeLabel p Bs K := by
          refine largeEvenMarking_mono ?_ hInn'
          intro lab R _ I F θ hP
          obtain ⟨hEq, hN1, hAct⟩ := hP
          subst hEq
          refine ⟨?_, hN1, hAct⟩
          change lab'.tag = .F4 ∧ p = 3 ∧ 3 ∣ 2 ^ lab'.n + 1
          exact ⟨hF4, hp3, by simpa [hp3] using hplus⟩
        subst hp3
        exact ggF4Three_rank_of_innerDiagOnLabel hcfg hT hM3 hN
      · have hp5 : 5 ≤ p := by
          have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
          have := hp.two_le
          omega
        exact ggF4Plus_rank_of_marking hcfg hp5 hT hM5 hN
    exact false_of_nbr_gamma_ge_four hcfg hcard hnb hN hge
  · have hE : GGHasLabel ⟨.E6, 0, 1⟩ (K ⧸ Subgroup.center K) := by
      have hE6' : lab.tag = .E6 := hE6
      have hn1' : lab.n = 1 := hn1
      simpa [lab', hE6', hn1'] using hhas₁
    exact ggWTP8_secFiveE6TwoSeven_false ggLabelRigidInput_holds TCJ.ggTCJKnown_holds hTP
      hrest hnb hp7 hE

end CFSG.StandardType

end
