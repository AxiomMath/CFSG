module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.L2Over17
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.QDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddLieFieldThree
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotPositionB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.TenFiveBridge
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20r
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcOrder
public import CFSG.Quasithin.Vol2.Ch12Sec1H9Lin
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleField
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CNExc
public import CFSG.Quasithin.Vol2.Ch10SecKRTj
public import CFSG.Quasithin.Background.F918V6BB
public import CFSG.Quasithin.Background.RonanF918FiveK
public import CFSG.Quasithin.Background.Asc81cPfTrans2
public import CFSG.Quasithin.Background.F918V6FB
public import CFSG.GroupTheory.Fitting.QuasisimpleNormalFstar
public import CFSG.CGT.PushingUpLit.LIT.Foote.L54Aux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FstarBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.NaturalO4PlusSubnormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.IrrSetQuotient
public import CFSG.Quasithin.Background.F918Z8f
public import CFSG.Quasithin.Background.HMathieuFactsBase
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank (projectiveSpecialLinearGroupEquivStatedProj)
open Matrix
open CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

theorem o2Trivial_of_isQuasisimple_of_odd_center {W : Type} [CommGroup W] [Finite W]
    {Y : Subgroup (MulAut W)} (hq : CFSG.Open.IsQuasisimple ↥Y)
    (hodd : Odd (Nat.card (Subgroup.center ↥Y))) : O2Trivial Y := by
  intro P hPY hPN hP2
  exact (Subgroup.subgroupOf_eq_bot.mp
    (CFSG.SeitzReduction.UnitaryPilot.forall_normal_isPGroup_eq_bot_of_isQuasisimple_of_odd_center
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq) hodd (P.subgroupOf Y) hPN
      (hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPY).symm))).eq_bot_of_le hPY

theorem caseTwo_Lstar_surjective {W : Type} [CommGroup W]
    {K : Subgroup (MulAut W)} {Z I : Subgroup W}
    (hKq : CFSG.IsQuasisimple K) (hKZ : K ≤ stabSub Z) (hZK : Z ≤ fixV K)
    (hI : I ∈ irrSet K) (hnotI : ¬ I ≤ Z) :
    ∃ Φ : ↥K →* ↥(autSub (autQuot K Z) (I.map (QuotientGroup.mk' Z))),
      Function.Surjective Φ ∧ ∃ k, Φ k ≠ 1 := by
  classical
  have hKstabI : K ≤ stabSub I := B1.le_stabSub_of_invariant hI.2.2.1
  have hXle : autQuot K Z ≤ stabSub (I.map (QuotientGroup.mk' Z)) :=
    autQuot_le_stabSub_map hI.2.2.1
  let Φ : ↥K →* ↥(autSub (autQuot K Z) (I.map (QuotientGroup.mk' Z))) :=
    (CFSG.Quasithin.F918V6B.resOnto hXle).comp
      (CFSG.Quasithin.D37Lift.toQuot Z K hKZ)
  have hΦsurj : Function.Surjective Φ :=
    (CFSG.Quasithin.F918V6B.resOnto_surjective hXle).comp
      (CFSG.Quasithin.D37Lift.toQuot_surjective Z K hKZ)
  refine ⟨Φ, hΦsurj, ?_⟩
  have hnt : ∃ x ∈ autQuot K Z, ∃ v ∈ I.map (QuotientGroup.mk' Z), x v ≠ v := by
    by_contra htriv
    push Not at htriv
    have hKfixZ : ∀ k ∈ K, ∀ u ∈ I, k u * u⁻¹ ∈ Z := by
      intro k hk u hu
      have hkZ : k ∈ stabSub Z := hKZ hk
      have hx : quotHom Z ⟨k, hkZ⟩ ∈ autQuot K Z :=
        mem_autQuot.mpr ⟨⟨k, hkZ⟩, hk, rfl⟩
      have h1 : quotHom Z ⟨k, hkZ⟩ (QuotientGroup.mk u) = QuotientGroup.mk u :=
        htriv _ hx _ (Subgroup.mem_map_of_mem _ hu)
      have h2 : (QuotientGroup.mk (k u) : W ⧸ Z) = QuotientGroup.mk u := by
        simpa [quotHom_mk] using h1
      exact (CFSG.Quasithin.mk_eq_mk_iff (k u) u).1 h2
    have hKfixI : ∀ k ∈ K, ∀ u ∈ I, k u = u := by
      intro k hk u hu
      exact CFSG.Quasithin.d3q_faithful hKq hZK le_rfl (Subgroup.le_normalizer)
        hKZ hKstabI hI.1 hnotI hk (fun u hu => hKfixZ k hk u hu) u hu
    exact CFSG.LocalAnalysis.WeakClosure81.not_le_fixV_of_mem_irrSet (X := K) (I := I) hI
      (fun u hu k hk => hKfixI k hk u hu)
  obtain ⟨x, hx, v, hv, hxv⟩ := hnt
  obtain ⟨k, hk⟩ := CFSG.Quasithin.D37Lift.toQuot_surjective Z K hKZ ⟨x, hx⟩
  refine ⟨k, fun hΦ => hxv ?_⟩
  have h1 : (CFSG.Quasithin.F918V6B.resOnto hXle ⟨x, hx⟩ :
      MulAut ↥(I.map (QuotientGroup.mk' Z))) = 1 := by
    simpa [Φ, hk] using congrArg (Subtype.val) hΦ
  have := congrArg (fun f : MulAut ↥(I.map (QuotientGroup.mk' Z)) => f ⟨v, hv⟩) h1
  exact Subtype.ext_iff.mp this

theorem caseTwo_Lstar_quasisimple {W : Type} [CommGroup W]
    {K : Subgroup (MulAut W)} {Z I : Subgroup W}
    (hKq : CFSG.IsQuasisimple K) (hKZ : K ≤ stabSub Z) (hZK : Z ≤ fixV K)
    (hI : I ∈ irrSet K) (hnotI : ¬ I ≤ Z) :
    CFSG.Open.IsQuasisimple (autSub (autQuot K Z) (I.map (QuotientGroup.mk' Z))) := by
  obtain ⟨Φ, hΦsurj, hΦnt⟩ := caseTwo_Lstar_surjective hKq hKZ hZK hI hnotI
  have hLq : CFSG.IsQuasisimple
      (autSub (autQuot K Z) (I.map (QuotientGroup.mk' Z))) :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_surjective (φ := Φ) hKq hΦsurj hΦnt
  exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hLq

theorem caseTwo_Lstar_centerQuot_equiv_barInf {W : Type} [CommGroup W]
    {K : Subgroup (MulAut W)} {Z I : Subgroup W}
    (hKq : CFSG.IsQuasisimple K) (hKZ : K ≤ stabSub Z) (hZK : Z ≤ fixV K)
    (hI : I ∈ irrSet K) (hnotI : ¬ I ≤ Z)
    {B : Type} [Group B] (e : B ≃* K ⧸ Subgroup.center K) :
    Nonempty (autSub (autQuot K Z) (I.map (QuotientGroup.mk' Z)) ⧸
      Subgroup.center (autSub (autQuot K Z) (I.map (QuotientGroup.mk' Z))) ≃* B) := by
  obtain ⟨Φ, hΦsurj, hΦnt⟩ := caseTwo_Lstar_surjective hKq hKZ hZK hI hnotI
  have hΦker : Φ.ker ≤ Subgroup.center K :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hKq hΦnt
  have e1 := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple
    (φ := Φ) hKq hΦsurj hΦker
  exact ⟨e1.symm.trans e.symm⟩

theorem caseTwo_Lstar_odd_center {W : Type} [CommGroup W]
    {K : Subgroup (MulAut W)} {Z I : Subgroup W}
    (hKq : CFSG.IsQuasisimple K) (hKZ : K ≤ stabSub Z) (hZK : Z ≤ fixV K)
    (hI : I ∈ irrSet K) (hnotI : ¬ I ≤ Z)
    (hoddK : Odd (Nat.card (Subgroup.center K))) :
    Odd (Nat.card (Subgroup.center ↥(autSub (autQuot K Z)
      (I.map (QuotientGroup.mk' Z))))) := by
  obtain ⟨Φ, hΦsurj, hΦnt⟩ := caseTwo_Lstar_surjective hKq hKZ hZK hI hnotI
  have hΦker : Φ.ker ≤ Subgroup.center K :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hKq hΦnt
  have hcenter : Subgroup.center ↥(autSub (autQuot K Z) (I.map (QuotientGroup.mk' Z))) =
      (Subgroup.center K).map Φ :=
    CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple (φ := Φ) hKq hΦsurj hΦker
  rw [hcenter]
  exact Odd.of_dvd_nat hoddK (Subgroup.card_map_dvd (H := Subgroup.center K) (f := Φ))

section StepM


theorem center_bar2_eq_bot_of_isL2Over17 {M L : Subgroup G}
    (hL : L ∈ calC M) {q : ℕ} (hq : IsL2Over17 (BarInf L) q) (hq9 : q ≠ 9) :
    Subgroup.center (Bar2 L) = ⊥ := by
  classical
  have hq' : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  haveI : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr hq'.1
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) := by
    simpa [Bar2] using uc22p20p_odd_center_bar2 ↥L
  have hq3 : q ≠ 3 := fun h3 => not_isL2Over17_three (BarInf L) (h3 ▸ hq)
  obtain ⟨r, f, hr, hr2, hqeq, hf, hmodel⟩ := hq
  have hq5 : 5 ≤ q := by
    have hr3 : 3 ≤ r := by
      have h2 := hr.two_le
      omega
    have h3q : 3 ≤ q := by
      rw [hqeq]
      exact le_trans hr3 (Nat.le_self_pow (by omega) r)
    have hoddq : Odd q := by
      rw [hqeq]
      exact (hr.odd_of_ne_two hr2).pow
    rcases hoddq with ⟨k, hk⟩
    omega
  have hclass : CFSG.Open.StatedClassicalModel (BarInf L) .PSL 2 r f :=
    hmodel.statedClassicalModel (by decide)
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨eK⟩⟩ := hclass
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  letI : Fintype K := Fintype.ofFinite K
  have hKcard' : Nat.card K = q := by rw [hKcard, hqeq]
  have hK5 : 5 ≤ Fintype.card K := by
    rw [Nat.card_eq_fintype_card] at hKcard'
    omega
  have hK9 : Fintype.card K ≠ 9 := by
    rw [Nat.card_eq_fintype_card] at hKcard'
    omega
  let ePSL : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* BarInf L :=
    (eK.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).symm
  obtain ⟨-, ⟨eHopf⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_two_hopfMultiplier_of_mulEquiv
      hK5 hK9 ePSL
  have hcardHopf :
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (BarInf L)) = 2 := by
    calc Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (BarInf L))
        = Nat.card (CFSG.Open.griessHopfMultiplier (BarInf L)) :=
          (Nat.card_congr
            (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess (BarInf L)).toEquiv).symm
      _ = Nat.card (Multiplicative (ZMod (Nat.gcd 2 (Fintype.card K - 1)))) :=
          Nat.card_congr eHopf.toEquiv
      _ = Nat.gcd 2 (Fintype.card K - 1) := by
          rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
      _ = 2 := by
          have hoddK : Odd (Fintype.card K) := by
            rw [← Nat.card_eq_fintype_card, hKcard', hqeq]
            exact (hr.odd_of_ne_two hr2).pow
          rcases hoddK with ⟨k, hk⟩
          rw [hk, Nat.add_sub_cancel]
          exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  obtain ⟨eC⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hdvd := uc22p20r_card_center_dvd_hopf eC.symm
  rw [hcardHopf] at hdvd
  have hcard_one : Nat.card (Subgroup.center (Bar2 L)) = 1 := by
    rcases hodd with ⟨k, hk⟩
    have hdiv : Nat.card (Subgroup.center (Bar2 L)) ∣ 2 := hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
    · exact h
    · rw [h] at hk
      omega
  exact Subgroup.card_eq_one.mp hcard_one

theorem isL2Over17_bar2_of_barInf {M L : Subgroup G}
    (hL : L ∈ calC M) {q : ℕ} (hq : IsL2Over17 (BarInf L) q) (hq9 : q ≠ 9) :
    IsL2Over17 (Bar2 L) q := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot (L := L) hL.2.2
    (center_bar2_eq_bot_of_isL2Over17 hL hq hq9)
  exact isL2Over17_of_mulEquiv e.symm hq

end StepM

section Dispatch


theorem center_eq_bot_of_lieModel_g2 {X : Type} [Group X] {p f : ℕ}
    (hm : LieModel X .G2 0 p f) : Subgroup.center X = ⊥ := by
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e'⟩⟩ :=
    hm.chevalleyExceptionalModel (by decide)
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e'
    (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.center_adjointQuotient_eq_bot .G2 K)

theorem eight_le_mParam_or_l2_of_w4Lem10_5
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y Ls : Subgroup (MulAut W)} (hLY : Ls ≤ Y) (hLN : (Ls.subgroupOf Y).Normal)
    (hF : CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar Y = Ls)
    (hQs : CFSG.Open.IsQuasisimple ↥Ls) (ho2 : O2Trivial Ls)
    {D : Data G} {V₀ V L : Subgroup G} (hL : L ∈ calC D.M)
    {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 0 < f)
    {t : CFSG.Open.StatedLieTag} {n : ℕ}
    (hadm : CFSG.Open.StatedLieAdmissible t n r f)
    (hModel : LieModel (BarInf L) t n r f)
    (hq3 : 3 < r ^ f)
    (hnot5 : ¬ IsL2Over17 (BarInf L) 5)
    (h17_5 : R17_5At D V₀ V)
    (hF3 : OddLieFieldThree)
    (h105 : W4Lem10_5Q)
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* BarInf L) :
    8 ≤ E3.mParam Y ∨
      ((IsL2Over17 (BarInf L) r ∨ IsL2Over17 (BarInf L) 25) ∧ 4 ≤ E3.mParam Y) ∨
      IsL2Over17 (BarInf L) 7 := by
  classical
  have hZbot : ∀ {t : CFSG.Open.StatedLieTag} {n p f : ℕ}, t ∈ classicalTags →
      LieModel ↥Ls t n p f → Subgroup.center ↥Ls = ⊥ := by
    intro t n p f ht hm
    exact CFSG.RankThree.PartOne.center_eq_bot_of_cover (Group.isPerfect_def.mpr hQs.1)
      (MonoidHom.id ↥Ls) Function.surjective_id (hm.statedClassicalModel ht)
  have hGq : InGq (↥Ls ⧸ Subgroup.center ↥Ls) (r ^ f) :=
    Or.inl ⟨t, n, r, f, hr, hr2, by omega, rfl, LieModel.of_mulEquiv e.symm hModel⟩
  have h105' := h105 W hW Y Ls r f (r ^ f) hLY hLN hF
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hQs) ho2 hr hr2 hf rfl hq3 hGq
  rcases h105' with h1 | ⟨h2, h4⟩ | ⟨h3, h6⟩ | h4 | ⟨h5, h4⟩ | h6
  · exact Or.inl h1
  ·
    have hZ : Subgroup.center ↥Ls = ⊥ :=
      hZbot (by decide) h2
    have hmInf : LieModel (BarInf L) .PSL 3 3 1 :=
      LieModel.of_mulEquiv e (h2.quotient_center hZ)
    exact absurd (hF3 (BarInf L) t n r f hr2 hadm hModel (Or.inl hmInf)) (by omega)
  ·
    rcases h3 with h3 | h3 | h3 | ⟨Z, hZnorm, hZle, hZcard, h3⟩ | h3
    ·
      have hZ : Subgroup.center ↥Ls = ⊥ :=
        hZbot (by decide) h3
      have hmInf : LieModel (BarInf L) .PSL 4 3 1 :=
        LieModel.of_mulEquiv e (h3.quotient_center hZ)
      exact absurd (hF3 (BarInf L) t n r f hr2 hadm hModel
        (Or.inr (Or.inr (Or.inl hmInf)))) (by omega)
    ·
      have hZ : Subgroup.center ↥Ls = ⊥ :=
        hZbot (by decide) h3
      have hmInf : LieModel (BarInf L) .PSU 4 3 1 :=
        LieModel.of_mulEquiv e (h3.quotient_center hZ)
      exact absurd (hF3 (BarInf L) t n r f hr2 hadm hModel
        (Or.inr (Or.inr (Or.inr (Or.inl hmInf))))) (by omega)
    ·
      have hZ : Subgroup.center ↥Ls = ⊥ := center_eq_bot_of_lieModel_g2 h3
      have hmInf : LieModel (BarInf L) .G2 0 3 1 :=
        LieModel.of_mulEquiv e (h3.quotient_center hZ)
      exact absurd (hF3 (BarInf L) t n r f hr2 hadm hModel
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmInf)))))) (by omega)
    ·
      have hZq : Subgroup.center (↥Ls ⧸ Z) = ⊥ := center_eq_bot_of_lieModel_g2 h3
      have hcent_le : Subgroup.center ↥Ls ≤ Z := by
        intro z hz
        rw [← QuotientGroup.eq_one_iff]
        have hzq : (QuotientGroup.mk z : ↥Ls ⧸ Z) ∈ Subgroup.center (↥Ls ⧸ Z) := by
          rw [Subgroup.mem_center_iff]
          intro g
          induction g using QuotientGroup.induction_on with
          | H g =>
            show (QuotientGroup.mk' Z) g * (QuotientGroup.mk' Z) z =
              (QuotientGroup.mk' Z) z * (QuotientGroup.mk' Z) g
            simpa only [map_mul] using
              congrArg (QuotientGroup.mk' Z) (Subgroup.mem_center_iff.mp hz g)
        rw [hZq] at hzq
        simpa using hzq
      have hcenter : Subgroup.center ↥Ls = Z := le_antisymm hcent_le hZle
      change LieModel (↥Ls ⧸ Z) .G2 0 3 1 at h3
      have h3' : LieModel (↥Ls ⧸ Subgroup.center ↥Ls) .G2 0 3 1 :=
        LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hcenter).symm h3
      have hmq : LieModel (↥Ls ⧸ Subgroup.center ↥Ls) t n r f :=
        LieModel.of_mulEquiv e.symm hModel
      exact absurd (hF3 (↥Ls ⧸ Subgroup.center ↥Ls) t n r f hr2 hadm hmq
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3')))))) (by omega)
    ·
      have hZ : Subgroup.center ↥Ls = ⊥ :=
        hZbot (by decide) h3
      have hmInf : LieModel (BarInf L) .PSp 3 3 1 :=
        LieModel.of_mulEquiv e (h3.quotient_center hZ)
      exact absurd (hF3 (BarInf L) t n r f hr2 hadm hModel
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hmInf))))))) (by omega)
  ·
    rcases h4 with h4 | h4 | h4 | ⟨h4, -⟩
    ·
      have hZ : Subgroup.center ↥Ls = ⊥ :=
        hZbot (by decide) h4
      have hmInf : LieModel (BarInf L) .PSU 3 3 1 :=
        LieModel.of_mulEquiv e (h4.quotient_center hZ)
      exact absurd (hF3 (BarInf L) t n r f hr2 hadm hModel (Or.inr (Or.inl hmInf))) (by omega)
    ·
      have hZ : Subgroup.center ↥Ls = ⊥ :=
        hZbot (by decide) h4
      have hmInf : LieModel (BarInf L) .PSp 2 3 1 :=
        LieModel.of_mulEquiv e (h4.quotient_center hZ)
      exact absurd (hF3 (BarInf L) t n r f hr2 hadm hModel
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmInf))))))) (by omega)
    ·
      have hZ : Subgroup.center ↥Ls = ⊥ :=
        hZbot (by decide) h4
      have hmInf : LieModel (BarInf L) .PSL 2 2 3 :=
        LieModel.of_mulEquiv e (h4.quotient_center hZ)
      have hodd : CFSG.Blueprint.OddLieType (BarInf L) := ⟨t, n, r, f, hr, hr2, hadm, hModel⟩
      exact absurd hodd (CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two_of_ne_Tits
        hmInf (by decide) (by norm_num) (by norm_num) (by decide))
    ·
      have hmInf : LieModel (BarInf L) .PSU 4 3 1 := LieModel.of_mulEquiv e h4
      exact absurd (hF3 (BarInf L) t n r f hr2 hadm hModel
        (Or.inr (Or.inr (Or.inr (Or.inl hmInf))))) (by omega)
  ·
    rcases h5 with h5 | h5
    · have hZ : Subgroup.center ↥Ls = ⊥ :=
        hZbot (by decide) h5
      have hmInf : LieModel (BarInf L) .PSL 2 5 2 :=
        LieModel.of_mulEquiv e (h5.quotient_center hZ)
      exact Or.inr (Or.inl ⟨Or.inr ⟨5, 2, by norm_num, by norm_num, rfl, by norm_num, hmInf⟩, h4⟩)
    · have hZ : Subgroup.center ↥Ls = ⊥ :=
        hZbot (by decide) h5
      have hmInf : LieModel (BarInf L) .PSL 2 r 1 :=
        LieModel.of_mulEquiv e (h5.quotient_center hZ)
      exact Or.inr (Or.inl ⟨Or.inl ⟨r, 1, hr, hr2, by rw [pow_one], le_rfl, hmInf⟩, h4⟩)
  ·
    rcases h6 with h6 | h6 | h6
    · have hmInf : LieModel (BarInf L) .PSL 2 5 1 := LieModel.of_mulEquiv e h6
      exact absurd ⟨5, 1, by norm_num, by norm_num, rfl, le_rfl, hmInf⟩ hnot5
    · have hmInf : LieModel (BarInf L) .PSL 2 7 1 := LieModel.of_mulEquiv e h6
      exact Or.inr (Or.inr ⟨7, 1, by norm_num, by norm_num, rfl, le_rfl, hmInf⟩)
    · have hmInf : LieModel (BarInf L) .PSL 2 3 2 := LieModel.of_mulEquiv e h6
      exact (false_of_lieModel_barInf_psl_two_three_two hL h17_5 hmInf).elim

theorem eight_le_mParam_or_l2Bar2_of_w4Lem10_5
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y Ls : Subgroup (MulAut W)} (hLY : Ls ≤ Y) (hLN : (Ls.subgroupOf Y).Normal)
    (hF : Fstar Y = Ls) (hQs : CFSG.Open.IsQuasisimple ↥Ls) (ho2 : O2Trivial Ls)
    {D : Data G} {V₀ V L : Subgroup G} (hL : L ∈ calC D.M)
    {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 0 < f)
    {t : CFSG.Open.StatedLieTag} {n : ℕ}
    (hadm : CFSG.Open.StatedLieAdmissible t n r f)
    (hModel : LieModel (BarInf L) t n r f) (hq3 : 3 < r ^ f)
    (hnot5 : ¬ IsL2Over17 (BarInf L) 5) (h17_5 : R17_5At D V₀ V)
    (hF3 : OddLieFieldThree) (h105 : W4Lem10_5Q)
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* BarInf L) :
    8 ≤ E3.mParam Y ∨
      ((IsL2Over17 (Bar2 L) r ∨ IsL2Over17 (Bar2 L) 25) ∧ 4 ≤ E3.mParam Y) ∨
      IsL2Over17 (Bar2 L) 7 := by
  have h := eight_le_mParam_or_l2_of_w4Lem10_5 hW hLY hLN hF hQs ho2 hL hr hr2 hf hadm
    hModel hq3 hnot5
    h17_5 hF3 h105 e
  rcases h with h1 | hrest
  · exact Or.inl h1
  · rcases hrest with ⟨h2, h4⟩ | h2
    · rcases h2 with h2r | h25
      · exact Or.inr (Or.inl ⟨Or.inl (isL2Over17_bar2_of_barInf hL
          h2r (by rintro h; rw [h] at hr; norm_num at hr)), h4⟩)
      · exact Or.inr (Or.inl ⟨Or.inr (isL2Over17_bar2_of_barInf hL
          h25 (by norm_num)), h4⟩)
    · exact Or.inr (Or.inr (isL2Over17_bar2_of_barInf hL h2 (by norm_num)))

end Dispatch

section CaseOne


open CFSG.Quasithin.H13.H9Coord

theorem r17_10_of_dMinDeg_le_mBar {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hL : L ∈ calC D.M) (hne : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (hKle : dMinDeg ↥(barSub V₀ V h.isElemAbelian L) ≤ mBar D.M V₀ V h.isElemAbelian)
    {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 0 < f)
    {t : CFSG.Open.StatedLieTag} {n : ℕ}
    (hadm : CFSG.Open.StatedLieAdmissible t n r f)
    (hModel : LieModel (BarInf L) t n r f) (hq3 : 3 < r ^ f)
    (hnot5 : ¬ IsL2Over17 (BarInf L) 5) (h17_5 : R17_5At D V₀ V)
    (hF3 : OddLieFieldThree) (h105 : W4Lem10_5Q) :
    MBarGT D.M V₀ V 7 ∨
      (MBarGT D.M V₀ V 3 ∧
        (IsL2Over17 (Bar2 L) r ∨ IsL2Over17 (Bar2 L) 25)) ∨
      IsL2Over17 (Bar2 L) 7 := by
  classical
  let K := barSub V₀ V h.isElemAbelian L
  have hKcomp : K ∈ compBar D.M V₀ V h.isElemAbelian := barSub_mem_compBar_of_ne_bot h hL hne
  have hKne : K ≠ ⊥ := ne_bot_of_mem_compBar hKcomp
  haveI : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
  let d := dMinDeg ↥K
  obtain ⟨f₀, hf₀⟩ := exists_nontrivial_repr_dMinDeg ↥K
  let k : ↥K →* MulAut (Vec d) := (vecEquiv (n := d)).toMonoidHom.comp f₀
  let Y : Subgroup (MulAut (Vec d)) := k.range
  have hknt : ∃ x, k x ≠ 1 := by
    by_contra hcontra
    push Not at hcontra
    refine hf₀ (MonoidHom.ext fun x => ?_)
    have h1 : (vecEquiv (n := d)) (f₀ x) = 1 := hcontra x
    exact (vecEquiv (n := d)).injective (by simpa using h1)
  have hKqOpen : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have hKq : CFSG.IsQuasisimple ↥K := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hKqOpen
  have hker : k.ker ≤ Subgroup.center ↥K :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hKq hknt
  have hQsY : CFSG.IsQuasisimple ↥Y :=
    CFSG.HardMathSupport.Timmesfeld.LangTorus.isQuasisimple_range_of_ker_le_center hKq k hker
  have hQsYopen : CFSG.Open.IsQuasisimple ↥Y :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hQsY
  have hFY : Fstar Y = Y := fstar_eq_self_of_isQuasisimple hQsYopen
  have hoddK : Odd (Nat.card (Subgroup.center ↥K)) := odd_center_barSub h hL hne
  have hoddY : Odd (Nat.card (Subgroup.center ↥Y)) := by
    have hks : Function.Surjective k.rangeRestrict := MonoidHom.rangeRestrict_surjective k
    have hker' : k.rangeRestrict.ker ≤ Subgroup.center ↥K := by
      rwa [MonoidHom.ker_rangeRestrict]
    have hcY : Subgroup.center ↥Y = (Subgroup.center ↥K).map k.rangeRestrict :=
      CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hKq hks hker'
    rw [hcY]
    exact Odd.of_dvd_nat hoddK
      (Subgroup.card_map_dvd (H := Subgroup.center ↥K) (f := k.rangeRestrict))
  have hO2 : O2Trivial Y := o2Trivial_of_isQuasisimple_of_odd_center hQsYopen hoddY
  have e2 : ↥K ⧸ Subgroup.center ↥K ≃* ↥Y ⧸ Subgroup.center ↥Y :=
    CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hKq
      (φ := k.rangeRestrict) (MonoidHom.rangeRestrict_surjective k) (by
        rwa [MonoidHom.ker_rangeRestrict])
  obtain ⟨e1⟩ : Nonempty (BarInf L ≃* ↥K ⧸ Subgroup.center ↥K) :=
    barSub_centerQuot_equiv_barInf h hL hne
  have e : ↥Y ⧸ Subgroup.center ↥Y ≃* BarInf L := e2.symm.trans e1.symm
  have hmle : E3.mParam Y ≤ d := by
    calc E3.mParam Y ≤ rk (Vec d) := E3.mParam_le_rk Y
      _ = d := by rw [rk, H9Coord.card_vec, padicValNat.prime_pow]
  have hWexp : ∀ w : Vec d, w ^ 2 = 1 := by
    intro w
    rw [pow_two]
    change Multiplicative.ofAdd (Multiplicative.toAdd w + Multiplicative.toAdd w) = 1
    have hzero : Multiplicative.toAdd w + Multiplicative.toAdd w = 0 := by
      ext i
      have h2 : ∀ x : ZMod 2, x + x = 0 := fun x => by revert x; decide
      exact h2 _
    rw [hzero, ofAdd_zero]
  have hLN : (Y.subgroupOf Y).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hdisp := eight_le_mParam_or_l2Bar2_of_w4Lem10_5 (W := Vec d) hWexp le_rfl hLN hFY
    hQsYopen hO2 hL
    hr hr2 hf hadm hModel hq3 hnot5 h17_5 hF3 h105 e
  rcases hdisp with h1 | ⟨h2, h4⟩ | h2
  · have hm8 : 8 ≤ mBar D.M V₀ V h.isElemAbelian := h1.trans (hmle.trans hKle)
    exact Or.inl ((h.mBarGT_iff_lt_mBar 7).2 (by omega))
  · have hm4 : 4 ≤ mBar D.M V₀ V h.isElemAbelian := h4.trans (hmle.trans hKle)
    refine Or.inr (Or.inl ⟨(h.mBarGT_iff_lt_mBar 3).2 (by omega), ?_⟩)
    exact h2
  · exact Or.inr (Or.inr h2)

end CaseOne

section CaseThree


theorem false_of_isNaturalO4Plus_of_oddLieType {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V)
    (hL : L ∈ calC D.M) (hne : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {Y : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))} {e : ℕ}
    (hsn : CFSG.Open.IsSubnormal (barSub V₀ V h.isElemAbelian L) Y)
    (hnat : IsNaturalO4Plus Y e)
    {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {t : CFSG.Open.StatedLieTag} {n : ℕ}
    (hadm : CFSG.Open.StatedLieAdmissible t n r f)
    (hmodel : LieModel (BarInf L) t n r f)
    (hnot5 : ¬ IsL2Over17 (BarInf L) 5) :
    False := by
  classical
  let Kc := barSub V₀ V h.isElemAbelian L
  have hKcomp : Kc ∈ compBar D.M V₀ V h.isElemAbelian :=
    barSub_mem_compBar_of_ne_bot h hL hne
  have hKq : CFSG.Open.IsQuasisimple Kc := hKcomp.2.2
  obtain ⟨K, hKfield, hKfinite, hKcard, hK4, ⟨eK⟩⟩ :=
    exists_mulEquiv_sl2_of_isSubnormal_isNaturalO4Plus hKq hsn hnat
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := by
    have h1 : Fintype.card K = 2 ^ e := by
      rw [← Nat.card_eq_fintype_card]
      exact hKcard
    exact charP_of_card_eq_prime_pow (f := e) h1
  have hZ : Subgroup.center Kc = ⊥ :=
    CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv eK
      (CFSG.Timmesfeld.RankOne.center_SL2_eq_bot (K := K))
  obtain ⟨eBar⟩ := barSub_centerQuot_equiv_barInf (V₀ := V₀) (V := V) h hL hne
  let eBar2 : BarInf L ≃* Kc :=
    eBar.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  have hBarKc : BarInf L ≃* Matrix.SpecialLinearGroup (Fin 2) K := eBar2.trans eK
  have hBarSL : BarInf L ≃* CFSG.Open.StatedSL 2 K :=
    hBarKc.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)
  have hperf : Group.IsPerfect (BarInf L) := by
    haveI : Group.IsPerfect ↥L :=
      CFSG.Quasithin.Vol2.Ch10.SecB.KRT.isPerfect_of_commutator_eq hL.2.1
    exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.solvableRadical ↥L))
      (QuotientGroup.mk'_surjective _)
  haveI : Nontrivial Kc := (Subgroup.nontrivial_iff_ne_bot Kc).mpr (ne_bot_of_mem_compBar hKcomp)
  letI : Nontrivial (BarInf L) := eBar2.toEquiv.nontrivial
  have hmSL : LieModel (BarInf L) .PSL 2 2 e :=
    CFSG.Quasithin.H13.lieModel_psl_two_of_mulEquiv (n := e) hperf hKcard hBarSL
  have he2 : 2 ≤ e := by
    have h4 : 4 ≤ 2 ^ e := by
      rw [← hKcard]
      exact hK4
    by_contra hlt
    push Not at hlt
    interval_cases e <;> norm_num at h4
  by_cases heq : e = 2
  · have hmSL2 : LieModel (BarInf L) .PSL 2 2 2 := by simpa [heq] using hmSL
    have hm5 : LieModel (BarInf L) .PSL 2 5 1 :=
      CFSG.ComponentClassification.CatLeafProof.X10CNE.lieModel_psl_two_five_of_four hmSL2
    exact hnot5 ⟨5, 1, by norm_num, by norm_num, rfl, le_rfl, hm5⟩
  · have he3 : 3 ≤ e := by omega
    have hodd : CFSG.Blueprint.OddLieType (BarInf L) := ⟨t, n, r, f, hr, hr2, hadm, hmodel⟩
    exact absurd hodd (CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two_of_ne_Tits
      hmSL (by decide) (by omega) (by simp) (by simp))

theorem r17_10_of_mParam_mul_le_mBar {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hL : L ∈ calC D.M) (hne : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (hsum : IsDirSumOver (conjSet (barSub V₀ V h.isElemAbelian L)
      (Mbar D.M V₀ V h.isElemAbelian))
      (fun X => commV (autQuot X (fixSupConjSet (barSub V₀ V h.isElemAbelian L)
        (Mbar D.M V₀ V h.isElemAbelian)))))
    {I : Subgroup (Vtil V₀ V h.isElemAbelian)}
    (hI : I ∈ irrSet (barSub V₀ V h.isElemAbelian L))
    (hmn : (E3.mParam (autSub (autQuot (Mbar D.M V₀ V h.isElemAbelian)
        (fixSupConjSet (barSub V₀ V h.isElemAbelian L) (Mbar D.M V₀ V h.isElemAbelian)))
        (I.map (QuotientGroup.mk' (fixSupConjSet (barSub V₀ V h.isElemAbelian L)
          (Mbar D.M V₀ V h.isElemAbelian))))) : ℚ) *
      ((rk ↥(commV (autQuot (barSub V₀ V h.isElemAbelian L)
        (fixSupConjSet (barSub V₀ V h.isElemAbelian L)
          (Mbar D.M V₀ V h.isElemAbelian)))) : ℚ) /
        (rk ↥(I.map (QuotientGroup.mk' (fixSupConjSet (barSub V₀ V h.isElemAbelian L)
          (Mbar D.M V₀ V h.isElemAbelian)))) : ℚ)) ≤
      mBar D.M V₀ V h.isElemAbelian)
    {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 0 < f)
    {t : CFSG.Open.StatedLieTag} {n : ℕ}
    (hadm : CFSG.Open.StatedLieAdmissible t n r f)
    (hModel : LieModel (BarInf L) t n r f) (hq3 : 3 < r ^ f)
    (hnot5 : ¬ IsL2Over17 (BarInf L) 5) (h17_5 : R17_5At D V₀ V)
    (hF3 : OddLieFieldThree) (h105 : W4Lem10_5Q) :
    MBarGT D.M V₀ V 7 ∨
      (MBarGT D.M V₀ V 3 ∧ (IsL2Over17 (Bar2 L) r ∨ IsL2Over17 (Bar2 L) 25)) ∨
      IsL2Over17 (Bar2 L) 7 := by
  classical
  let K := barSub V₀ V h.isElemAbelian L
  let Mbar := Mbar D.M V₀ V h.isElemAbelian
  let H : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian)) := ⨆ X ∈ conjSet K Mbar, X
  let Z : Subgroup (Vtil V₀ V h.isElemAbelian) := fixV H
  let Istar : Subgroup (Vtil V₀ V h.isElemAbelian ⧸ Z) := I.map (QuotientGroup.mk' Z)
  let Lstar : Subgroup (MulAut ↥Istar) := autSub (autQuot K Z) Istar
  let G1 : Subgroup (MulAut ↥Istar) := autSub (autQuot Mbar Z) Istar
  let C : Subgroup ↥Istar := fixV Lstar
  let Wq := ↥Istar ⧸ C
  let X : Subgroup (MulAut Wq) := autQuot Lstar C
  let G1q : Subgroup (MulAut Wq) := autQuot G1 C
  have hKcomp : K ∈ compBar D.M V₀ V h.isElemAbelian :=
    barSub_mem_compBar_of_ne_bot h hL hne
  have hKleM : K ≤ Mbar := hKcomp.1
  have hKmem : K ∈ conjSet K Mbar := ⟨1, Mbar.one_mem, by ext x; simp [MulAut.conj_apply]⟩
  have hKleH : K ≤ H := le_iSup₂_of_le (f := fun X (_ : X ∈ conjSet K Mbar) => X) K hKmem le_rfl
  have hKZ : K ≤ stabSub Z := hKleH.trans (CFSG.Quasithin.RonanF918.le_stabSub_fixV H)
  have hZK : Z ≤ fixV K := fixV_anti hKleH
  have hnotI : ¬ I ≤ Z := by
    intro hle
    exact CFSG.LocalAnalysis.WeakClosure81.not_le_fixV_of_mem_irrSet (X := K) (I := I) hI
      (hle.trans hZK)
  have hIstarNe : Istar ≠ ⊥ := by
    intro hbot
    have hle : I ≤ Z := by
      rw [Subgroup.map_eq_bot_iff] at hbot
      rwa [QuotientGroup.ker_mk'] at hbot
    exact hnotI hle
  have hKq : CFSG.IsQuasisimple K := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hKcomp.2.2
  have hLstarq : CFSG.Open.IsQuasisimple ↥Lstar :=
    caseTwo_Lstar_quasisimple hKq hKZ hZK hI hnotI
  have hLstarqC : CFSG.IsQuasisimple ↥Lstar :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hLstarq
  have hLstarNe : Lstar ≠ ⊥ := by
    haveI : Nontrivial ↥Lstar := CFSG.LocalCores.isQuasisimple_nontrivial hLstarqC
    exact (Subgroup.nontrivial_iff_ne_bot Lstar).mp inferInstance
  haveI hPerfL : Group.IsPerfect ↥Lstar := hLstarqC.1
  have hLC : Lstar ≤ stabSub C := CFSG.Quasithin.RonanF918.le_stabSub_fixV Lstar
  have hLG1 : Lstar ≤ G1 := autSub_mono (autQuot_mono hKleM Z) Istar
  have hLnorm : (Lstar.subgroupOf G1).Normal :=
    autSub_autQuot_subgroupOf_normal_of_isDirSumOver (W := Vtil V₀ V h.isElemAbelian)
      hKZ hZK hI hsum hKleM
  have hG1norm : G1 ≤ Subgroup.normalizer (Lstar : Set (MulAut ↥Istar)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG1).mp hLnorm
  have hG1C : G1 ≤ stabSub C :=
    CFSG.Quasithin.B1.le_stabSub_of_invariant (fun g hg w hw =>
      CFSG.Quasithin.RonanF918.apply_mem_fixV_of_mem_normalizer (hG1norm hg) hw)
  have hcommW : commSub Istar (autQuot K Z) = Istar := by
    have h1 := map_commSub_eq_commSub_autQuot (K := K) (Z := Z) (I := I) hKZ
    rw [hI.1] at h1
    exact h1.symm
  have hcommIstar : commSub (⊤ : Subgroup ↥Istar) Lstar = ⊤ :=
    commSub_top_autSub_eq_top (X := autQuot K Z) (U := Istar)
      (autQuot_le_stabSub_map hI.2.2.1) hcommW
  have hCneTop : C ≠ ⊤ := by
    intro htop
    have hLbot : Lstar = ⊥ := by
      rw [eq_bot_iff]
      intro l hl
      rw [Subgroup.mem_bot]
      apply MulEquiv.ext
      intro u
      have hu : u ∈ C := htop ▸ Subgroup.mem_top u
      simpa using (mem_fixV.mp hu) l hl
    exact hLstarNe hLbot
  have htopStab : G1 ≤ stabSub (⊤ : Subgroup ↥Istar) := by
    intro g _
    rw [mem_stabSub]
    intro u
    exact ⟨fun _ => Subgroup.mem_top _, fun _ => Subgroup.mem_top _⟩
  have hVexp : ∀ v : Vtil V₀ V h.isElemAbelian ⧸ Z, v ^ 2 = 1 := by
    intro v
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective v
    show (QuotientGroup.mk' Z u) ^ 2 = 1
    rw [← map_pow]
    have h1 : u ^ 2 = 1 := by
      induction u using QuotientGroup.induction_on with
      | H y => rw [← QuotientGroup.mk_pow, IntMod.sq_eq_one, QuotientGroup.mk_one]
    rw [h1, map_one]
  have hWexp : ∀ w : ↥Istar, w ^ 2 = 1 := by
    intro w
    exact Subtype.ext (by simpa using hVexp (w : Vtil V₀ V h.isElemAbelian ⧸ Z))
  have hWq : ∀ w : Wq, w ^ 2 = 1 := by
    intro w
    induction w using QuotientGroup.induction_on with
    | H x => rw [← QuotientGroup.mk_pow, hWexp x, QuotientGroup.mk_one]
  have hWq' : ∀ w : Wq, w * w = 1 := fun w => by rw [← pow_two]; exact hWq w
  let π : ↥Lstar →* X := CFSG.Quasithin.D37Lift.toQuot C Lstar hLC
  have hπsurj : Function.Surjective π :=
    CFSG.Quasithin.D37Lift.toQuot_surjective C Lstar hLC
  have hfaith : ∀ (s : MulAut ↥Istar) (hs : s ∈ stabSub C), s ∈ G1 →
      quotHom C ⟨s, hs⟩ = 1 → s = 1 := by
    intro s hs hsG1 hq
    have hsU : ∀ u ∈ (⊤ : Subgroup ↥Istar), s u * u⁻¹ ∈ C := by
      intro u _
      have h1 : (QuotientGroup.mk (s u) : Wq) = QuotientGroup.mk u := by
        have hthis := congrArg (fun f : MulAut Wq => f (QuotientGroup.mk u)) hq
        rw [quotHom_mk] at hthis
        simpa using hthis
      exact (CFSG.Quasithin.mk_eq_mk_iff (s u) u).1 h1
    have hfix := CFSG.Quasithin.d3q_faithful hLstarqC (le_rfl : C ≤ fixV Lstar)
      hLG1 hG1norm hG1C htopStab hcommIstar
      (fun hle => hCneTop (top_le_iff.mp hle)) hsG1 hsU
    exact MulEquiv.ext fun u => hfix u (Subgroup.mem_top u)
  have hXne : X ≠ ⊥ := by
    intro hbot
    obtain ⟨l, hl1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hLstarNe
    have hq : quotHom C ⟨(l : MulAut ↥Istar), hLC l.2⟩ = 1 := by
      have hmem : quotHom C ⟨(l : MulAut ↥Istar), hLC l.2⟩ ∈ X :=
        mem_autQuot.mpr ⟨⟨(l : MulAut ↥Istar), hLC l.2⟩, l.2, rfl⟩
      rw [hbot] at hmem
      simpa using hmem
    have hq' : quotHom C ⟨(l : MulAut ↥Istar), hG1C (hLG1 l.2)⟩ = 1 := by
      simpa using hq
    have h1 : (l : MulAut ↥Istar) = 1 := hfaith _ _ (hLG1 l.2) hq'
    exact hl1 (Subtype.ext h1)
  have hXnt : ∃ l, π l ≠ 1 := by
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXne
    obtain ⟨l, rfl⟩ := hπsurj x
    exact ⟨l, by simpa using hx⟩
  have hπker : π.ker ≤ Subgroup.center ↥Lstar :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hLstarqC hXnt
  have hXq : CFSG.IsQuasisimple ↥X := by
    have hmap : (Lstar.subgroupOf (stabSub C)).map (quotHom C) = X := rfl
    rw [← hmap]
    exact isQuasisimple_map_subgroupOf_of_ne_bot hLC hLstarqC (quotHom C) (by rwa [hmap])
  have hXqopen : CFSG.Open.IsQuasisimple ↥X :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hXq
  have hoddX : Odd (Nat.card (Subgroup.center ↥X)) := by
    have hcenter : Subgroup.center ↥X = (Subgroup.center ↥Lstar).map π :=
      CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hLstarqC hπsurj hπker
    rw [hcenter]
    exact Odd.of_dvd_nat
      (caseTwo_Lstar_odd_center hKq hKZ hZK hI hnotI (odd_center_barSub h hL hne))
      (Subgroup.card_map_dvd (H := Subgroup.center ↥Lstar) (f := π))
  have ho2X : O2Trivial X := o2Trivial_of_isQuasisimple_of_odd_center hXqopen hoddX
  have hirr : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn X :=
    isIrrOn_autQuot_fixV_autSub hKZ hZK hI
  have eX : (X ⧸ Subgroup.center X) ≃* BarInf L := by
    have e1 : (↥Lstar ⧸ Subgroup.center ↥Lstar) ≃* (X ⧸ Subgroup.center X) :=
      CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple (φ := π) hLstarqC hπsurj hπker
    let eBar : BarInf L ≃* K ⧸ Subgroup.center K :=
      Classical.choice (barSub_centerQuot_equiv_barInf (V₀ := V₀) (V := V) h hL hne)
    have e0 : (↥Lstar ⧸ Subgroup.center ↥Lstar) ≃* BarInf L :=
      Classical.choice (caseTwo_Lstar_centerQuot_equiv_barInf hKq hKZ hZK hI hnotI
        (B := BarInf L) eBar)
    exact e1.symm.trans e0
  have hXle : X ≤ G1q := autQuot_mono hLG1 C
  have hG1qnorm : G1q ≤ Subgroup.normalizer (X : Set (MulAut Wq)) :=
    CFSG.Quasithin.d3q_autQuot_le_normalizer hLG1 hG1C hG1norm
  have key : ∀ s : MulAut ↥Istar, s ∈ G1 → s * s = 1 → s ≠ 1 →
      8 ≤ rkIdx (fixV (Subgroup.zpowers s)) ∨
        ((IsL2Over17 (Bar2 L) r ∨ IsL2Over17 (Bar2 L) 25) ∧
          4 ≤ rkIdx (fixV (Subgroup.zpowers s))) ∨
        IsL2Over17 (Bar2 L) 7 := by
    intro s hsG1 hs2 hs1
    have hsC : s ∈ stabSub C := hG1C hsG1
    have hs12 : quotHom C ⟨s, hsC⟩ ≠ 1 := fun hq =>
      hs1 (hfaith s hsC hsG1 hq)
    have hs2q : quotHom C ⟨s, hsC⟩ * quotHom C ⟨s, hsC⟩ = 1 := by
      rw [← map_mul]
      have h1 : (⟨s, hsC⟩ * ⟨s, hsC⟩ : stabSub C) = 1 := by
        refine Subtype.ext ?_
        simpa [pow_two] using hs2
      rw [h1, map_one]
    have hsord : orderOf (quotHom C ⟨s, hsC⟩) = 2 :=
      orderOf_eq_prime (by simpa [pow_two] using hs2q) hs12
    let Y : Subgroup (MulAut Wq) := X ⊔ Subgroup.zpowers (quotHom C ⟨s, hsC⟩)
    have hXY : X ≤ Y := le_sup_left
    have hsY : quotHom C ⟨s, hsC⟩ ∈ Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hsG1q : quotHom C ⟨s, hsC⟩ ∈ G1q :=
      mem_autQuot.mpr ⟨⟨s, hsC⟩, hsG1, rfl⟩
    have hYle : Y ≤ G1q := sup_le hXle (Subgroup.zpowers_le.mpr hsG1q)
    have hXN : (X.subgroupOf Y).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (hYle.trans hG1qnorm)
    haveI : Nontrivial Wq := QuotientGroup.nontrivial_iff.mpr hCneTop
    have hF : CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar Y = X :=
      fstar_eq_of_generalizedFitting_eq hXY
        (CFSG.GroupTheory.fstar_sup_zpowers_eq_of_quasisimple_normal hWq' hXY hXq hirr hXN
          hsY hs2q hs12)
    have hdisp := eight_le_mParam_or_l2Bar2_of_w4Lem10_5 (W := Wq) (Y := Y) (Ls := X)
      hWq hXY hXN hF hXqopen ho2X hL hr hr2 hf hadm hModel hq3 hnot5 h17_5 hF3 h105 eX
    have hmY : E3.mParam Y ≤ rkIdx (fixV (Subgroup.zpowers (quotHom C ⟨s, hsC⟩))) :=
      CFSG.Quasithin.Asc81c.Pf.mParam_le_of_orderOf_two hsY hsord
    have hrk : rkIdx (fixV (Subgroup.zpowers (quotHom C ⟨s, hsC⟩))) ≤
        rkIdx (fixV (Subgroup.zpowers s)) :=
      CFSG.Quasithin.f918v6f_rkIdx_le hsC
    rcases hdisp with h8 | ⟨htype, h4⟩ | h7
    · exact Or.inl (le_trans h8 (le_trans hmY hrk))
    · exact Or.inr (Or.inl ⟨htype, le_trans h4 (le_trans hmY hrk)⟩)
    · exact Or.inr (Or.inr h7)
  have hIle : Istar ≤ commV (autQuot K Z) := by
    have h1 : I ≤ commV K := by
      rw [CFSG.Quasithin.commV_eq_commSub]
      calc I = commSub I K := hI.1.symm
        _ ≤ commSub (⊤ : Subgroup (Vtil V₀ V h.isElemAbelian)) K := commSub_mono le_top le_rfl
    calc Istar = I.map (QuotientGroup.mk' Z) := rfl
      _ ≤ (commV K).map (QuotientGroup.mk' Z) := Subgroup.map_mono h1
      _ = commV (autQuot K Z) := map_commV_eq_commV_autQuot K Z hKZ
  have hIstarPos : 0 < rk ↥Istar :=
    Nat.pos_of_ne_zero fun h0 =>
      hIstarNe ((rk_eq_zero_iff (V := Vtil V₀ V h.isElemAbelian ⧸ Z) hVexp (H := Istar)).1 h0)
  have hcast : (rk ↥Istar : ℚ) ≤ (rk ↥(commV (autQuot K Z)) : ℚ) := by
    exact_mod_cast rk_mono hIle
  have hn1 : (1 : ℚ) ≤ (rk ↥(commV (autQuot K Z)) : ℚ) / (rk ↥Istar : ℚ) := by
    rw [le_div_iff₀ (by exact_mod_cast hIstarPos)]
    simpa using hcast
  have hmle : (E3.mParam G1 : ℚ) ≤ (mBar D.M V₀ V h.isElemAbelian : ℚ) := by
    calc (E3.mParam G1 : ℚ) = (E3.mParam G1 : ℚ) * 1 := by ring
      _ ≤ (E3.mParam G1 : ℚ) *
          ((rk ↥(commV (autQuot K Z)) : ℚ) / (rk ↥Istar : ℚ)) :=
          mul_le_mul_of_nonneg_left hn1 (by exact_mod_cast Nat.zero_le _)
      _ ≤ (mBar D.M V₀ V h.isElemAbelian : ℚ) := hmn
  have hmleN : E3.mParam G1 ≤ mBar D.M V₀ V h.isElemAbelian := by
    exact_mod_cast hmle
  have hevenL : Even (Nat.card ↥Lstar) :=
    CFSG.ComponentClassification.Burgoyne.even_card_of_isQuasisimple hLstarqC
  obtain ⟨t₀, ht₀L, ht₀ne, ht₀2⟩ :=
    CFSG.CGT.PushingUpLit.LIT.Foote.L54.exists_involution_of_even hevenL
  have ht₀G1 : t₀ ∈ G1 := hLG1 ht₀L
  have ht₀ord : orderOf t₀ = 2 := orderOf_eq_prime (by simpa [pow_two] using ht₀2) ht₀ne
  have hrkIdx_le : ∀ s : MulAut ↥Istar, rkIdx (fixV (Subgroup.zpowers s)) ≤ rk ↥Istar := by
    intro s
    exact CFSG.Quasithin.padicValNat_two_le_of_dvd
      (Nat.card_pos.ne')
      (Subgroup.index_dvd_card (H := fixV (Subgroup.zpowers s)))
  by_cases h7 : IsL2Over17 (Bar2 L) 7
  · exact Or.inr (Or.inr h7)
  by_cases htype : IsL2Over17 (Bar2 L) r ∨ IsL2Over17 (Bar2 L) 25
  · have hb : ∀ s ∈ G1, orderOf s = 2 → 4 ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
      intro s hsG1 hso
      have hs2 : s * s = 1 := by
        have h1 : s ^ 2 = 1 := by rw [← hso]; exact pow_orderOf_eq_one s
        simpa [pow_two] using h1
      have hs1 : s ≠ 1 := by intro h; rw [h] at hso; simp at hso
      rcases key s hsG1 hs2 hs1 with h8 | ⟨-, h4⟩ | h7'
      · omega
      · exact h4
      · exact absurd h7' h7
    have h4rk : 4 ≤ rk ↥Istar := le_trans (hb t₀ ht₀G1 ht₀ord) (hrkIdx_le t₀)
    have h4m : 4 ≤ E3.mParam G1 := CFSG.Quasithin.H.Mathieu.le_mParam_of h4rk hb
    have hmbar4 : 4 ≤ mBar D.M V₀ V h.isElemAbelian := le_trans h4m hmleN
    exact Or.inr (Or.inl ⟨(h.mBarGT_iff_lt_mBar 3).2 (by omega), htype⟩)
  · have hb : ∀ s ∈ G1, orderOf s = 2 → 8 ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
      intro s hsG1 hso
      have hs2 : s * s = 1 := by
        have h1 : s ^ 2 = 1 := by rw [← hso]; exact pow_orderOf_eq_one s
        simpa [pow_two] using h1
      have hs1 : s ≠ 1 := by intro h; rw [h] at hso; simp at hso
      rcases key s hsG1 hs2 hs1 with h8 | ⟨htyp, -⟩ | h7'
      · exact h8
      · exact absurd htyp htype
      · exact absurd h7' h7
    have h8rk : 8 ≤ rk ↥Istar := le_trans (hb t₀ ht₀G1 ht₀ord) (hrkIdx_le t₀)
    have h8m : 8 ≤ E3.mParam G1 := CFSG.Quasithin.H.Mathieu.le_mParam_of h8rk hb
    have hmbar8 : 8 ≤ mBar D.M V₀ V h.isElemAbelian := le_trans h8m hmleN
    exact Or.inl ((h.mBarGT_iff_lt_mBar 7).2 (by omega))

theorem seventeen_ten (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h4128 : W4Lem12_8) (h105 : W4Lem10_5Q)
    (hC : Ctx17_6 D V₀ V L r q)
    (h17_5 : R17_5At D V₀ V) (h17_9 : R17_9At D V₀ V L r q hC) :
    R17_10At D V₀ V L r q hC := by
  have hF3 : OddLieFieldThree := oddLieFieldThree
  intro hne
  obtain ⟨hr, hr2, t, n, f, hadm, hq, hModel⟩ := hC.lie
  have hq3 : 3 < r ^ f := by
    rw [← hq]
    exact h17_9
  have hKcomp : barSub V₀ V hC.hyp125.isElemAbelian L ∈
      compBar D.M V₀ V hC.hyp125.isElemAbelian :=
    barSub_mem_compBar_of_ne_bot hC.hyp125 hC.memL hne
  rcases twelve_twentyFour D hx h61 h127 h1214 h4128 hC.hyp125 hKcomp rfl with
    h1 | ⟨hsum, I, hI, hmn⟩ | ⟨Y, e, hY, hsumY, hsn, hnat, -⟩
  · exact r17_10_of_dMinDeg_le_mBar hC.hyp125 hC.memL hne h1 hr hr2 hadm.2.1 hadm hModel hq3
      hC.not_l2_five h17_5 hF3 h105
  · exact r17_10_of_mParam_mul_le_mBar (h := hC.hyp125) (hL := hC.memL) (hne := hne)
      (hsum := hsum) (I := I) (hI := hI) (hmn := hmn)
      (hr := hr) (hr2 := hr2) (hf := hadm.2.1) (hadm := hadm) (hModel := hModel)
      (hq3 := hq3) (hnot5 := hC.not_l2_five) (h17_5 := h17_5) (hF3 := hF3) (h105 := h105)
  · exact (false_of_isNaturalO4Plus_of_oddLieType hC.hyp125 hC.memL hne hsn hnat hr hr2 hadm
      hModel hC.not_l2_five).elim

end CaseThree

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
