module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel
public import CFSG.LocalAnalysis.StandardType.GGNSJoinOutWeakPosDefs
public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGNSJoinByType
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNsq2Cited
public import CFSG.LocalAnalysis.StandardType.GGNSJoinRMDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1009
public import Certificates.Certificate1952
public import Certificates.Certificate10015
public import Certificates.Certificate10016
public import Certificates.Certificate10017
public import Certificates.Certificate10018
import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameOfMarking
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaE6PatCox
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaE6Pat
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaE6PatRows
import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCenter
import CFSG.LocalAnalysis.StandardType.GGStdUnitaryFourExcl
import CFSG.LocalAnalysis.StandardType.GGNsq2Main
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSQ2U62Setup
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall
import CFSG.LocalAnalysis.StandardType.GGNSJoinQFourUniOrd
import CFSG.LocalAnalysis.StandardType.GGOrthDFourTwoPosition
import CFSG.LocalAnalysis.StandardType.GGFrameFSxEndsCardJoinAux
import CFSG.LocalAnalysis.StandardType.GGFrameRouteEndNormal
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar
import CFSG.LocalAnalysis.StandardType.GGResOrthogonalExactTwo
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamOutBase
import CFSG.GroupTheory.ConjTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggGamma_L_exists_ne_one {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) : ∃ b : ↥Bs, ggGamma L hN b ≠ 1 := by
  obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hN
  have hcB := card_range_ggGamma_mul L hBN hp hS
  have hle : Nat.card (ggGamma L hBN).range ≤ Nat.card (ggGamma L hN).range := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBBs b.2⟩, rfl⟩
  have h4 := pow_four_le_card_of_bmax hp hS.1 hcfg.1.2.2.2.2.2.1.2.2.2
  rw [← hcB, pow_succ] at h4
  have h3 : p ^ 3 ≤ Nat.card (ggGamma L hN).range :=
    (Nat.le_of_mul_le_mul_right h4 hp.pos).trans hle
  by_contra hall
  push Not at hall
  have hbot : (ggGamma L hN).range = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨b, rfl⟩
    exact hall b
  rw [hbot, Subgroup.card_bot] at h3
  have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
  omega

section

private theorem exists_inner_conj_of_marking_orthTwo {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G}
    {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
    {eQ : (↥L ⧸ Subgroup.center ↥L) ≃* CFSG.RankThree.Classical2.ProjOrthDerived Q}
    {ρ : Bs →* (↥L ⧸ Subgroup.center ↥L)}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hperf : Group.IsPerfect ↥L)
    (hcompat0 : ∀ (b : Bs) (z : L),
      eQ (QuotientGroup.mk (ggGamma L hN b z)) =
        MulAut.conj (eQ (ρ b)) (eQ (QuotientGroup.mk z))) :
    ∀ b ∈ Bs, ∃ a : ↥L, ∀ y ∈ L, b⁻¹ * y * b = (a : G)⁻¹ * y * a := by
  intro b hb
  refine LocalAnalysis.GLTheoremA.T171Sh.exists_conj_eq_of_marked_conj (θ := eQ) (hN hb) hperf
    (r := eQ (ρ ⟨b, hb⟩⁻¹)) fun l l' hll' => ?_
  have hll : (l' : G) = b⁻¹ * l * b := hll'
  rw [← hcompat0]
  congr 2
  apply Subtype.ext
  rw [ggGamma_coe, hll]
  simp

private theorem coprime_center_card_three_of_marking_orthTwo {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G} {lab : LargeEvenLabel} (hmarkK : GGInnerDiagOn Bs L)
    (hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L))
    (htag : lab.tag = .D ∨ lab.tag = .twD) (hrank : 4 ≤ lab.rank) :
    Nat.Coprime (Nat.card ↥(Subgroup.center ↥L)) 3 := by
  have h3 : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥L) :=
    OrthKExactTwo.center_not_dvd_of_orthogonal_marking Nat.prime_three (by norm_num) hmarkK hhas
      htag hrank
  exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm

private theorem isPGroup_three_inf_not_isCyclic {G : Type} [Group G] {Bs L : Subgroup G}
    (hBs : IsElemAbelian 3 Bs)
    (hcardE : Nat.card Bs ≤ 3 * Nat.card ↥(Bs ⊓ L)) (h81 : 81 ≤ Nat.card Bs) :
    IsPGroup 3 ↥(Bs ⊓ L) ∧ ¬ IsCyclic ↥(Bs ⊓ L) := by
  have hEp : IsPGroup 3 ↥(Bs ⊓ L) := fun g =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (hBs.2 _ g.2.1)⟩
  refine ⟨hEp, ?_⟩
  intro hcyc
  have hexp : Monoid.exponent ↥(Bs ⊓ L) ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (hBs.2 _ g.2.1)
  rw [IsCyclic.exponent_eq_card] at hexp
  have := Nat.le_of_dvd (by norm_num) hexp
  omega

private theorem le_centralizer_of_two_of_marking_orthTwo {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hRig : GGLabelRigidInput) (hcfg : GGConfig p B Bs x L D J)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1) p Bs L)
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hsplit : Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L)) :
    ∀ U : Subgroup G, U ≤ L → IsPGroup 2 U →
      Bs ⊓ L ≤ Subgroup.normalizer (U : Set G) → U ≤ Subgroup.centralizer (L : Set G) := by
  intro U hUL hU2 hEU
  have hxU : x ∈ Subgroup.normalizer (U : Set G) :=
    CFSG.GroupTheory.mem_normalizer_of_conj_mem fun u hu => by
      have hux : u * x = x * u := Subgroup.mem_centralizer_singleton_iff.mp (hLx (hUL hu))
      rw [show x * u * x⁻¹ = u by rw [← hux, mul_assoc, mul_inv_cancel, mul_one]]
      exact hu
  have hBsU : Bs ≤ Subgroup.normalizer (U : Set G) := by
    rw [hsplit]
    exact sup_le (Subgroup.zpowers_le.mpr hxU) hEU
  exact OrthTorus.le_centralizer_of_isPGroup_two_orthTwo hRig hBs hSC hmark
    (ggGamma_L_exists_ne_one hcfg) hU2 hUL hBsU

theorem GGConfig.lt_bstar_of_orthTwo {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hRig : GGLabelRigidInput)
    (hcfg : GGConfig p B Bs x L D J)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1) p Bs L) :
    B < Bs := by
  classical
  obtain ⟨hp, hBs, hxB, hLx, h4⟩ := hcfg.tableB_facts
  haveI : Fact p.Prime := ⟨hp⟩
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hmarkK : GGInnerDiagOn Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2) hmark
  have hperf : Group.IsPerfect ↥L := Group.IsPerfect.mk hmark.1
  obtain ⟨lab, hΛ, hhas, R, hRgrp, I, F', θ, hPm⟩ := largeEvenMarking_exists_hasLabel hmark
  obtain ⟨⟨hrow, hn1⟩, -, -⟩ := hPm
  obtain ⟨hp3, htag, hrank⟩ := OrthTorus.ggRowP_EOmP_or_EOmM_data hrow hn1
  subst hp3
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := GGInnerDiagOn.le_normalizer hmarkK
  obtain ⟨F, hField, hFinite, hChar, V, hAdd, hMod, hFinDim, hNontrivial, Q, hQ, eQ, ρ,
    -, -, -, -, -, -, hcompat0⟩ :=
    OrthKExactTwo.exists_quadratic_image_of_orthogonal_marking hRig (by norm_num) hmarkK hBs hSC
      hΛ hhas htag hrank
  letI : Field F := hField; letI : Finite F := hFinite; letI : CharP F 2 := hChar
  letI : AddCommGroup V := hAdd; letI : Module F V := hMod
  letI : FiniteDimensional F V := hFinDim
  have hinner : ∀ b ∈ Bs, ∃ a : ↥L, ∀ y ∈ L, b⁻¹ * y * b = (a : G)⁻¹ * y * a :=
    exists_inner_conj_of_marking_orthTwo hN hperf hcompat0
  have hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥L)) 3 :=
    coprime_center_card_three_of_marking_orthTwo hmarkK hhas htag hrank
  have hsplit : Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L) :=
    (FrameRoute.bstar_eq_sup_of_inner hBs hxB hx1 hLx hZ hinner hSC
      fun S hSL hSp => hS.2.2.2.2 S hSL hSp).2
  have hcardE := FrameRoute.card_sup_zpowers_le_three_mul_card_inf hBs hxB hx1 hsplit
  have h81 : 81 ≤ Nat.card ↥Bs := by norm_num at h4; exact h4
  obtain ⟨hEp, hEnc⟩ := isPGroup_three_inf_not_isCyclic hBs hcardE h81
  have hLn : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal :=
    FrameRoute.subgroupOf_centralizer_normal_of_sStar hS ⟨Bs ⊓ L, inf_le_right, hEp, hEnc⟩
  have hcen := le_centralizer_of_two_of_marking_orthTwo hRig hcfg hmark hBs hSC hLx hsplit
  obtain ⟨-, -, -, -, -, -, -, hST⟩ := hcfg.1
  obtain ⟨-, hT, -, -⟩ := hST
  have hne : B ≠ Bs := FrameRoute.ne_bstar_of_stdType_twoGroup hT hLx hLn hsplit
    fun T hT2 hTN hET => FrameRoute.le_centralizer_of_twoSubgroups_central Nat.prime_three
      (by norm_num) hEp inf_le_right hT2 hTN hET hcen
  exact lt_of_le_of_ne hcfg.2.1.1 hne

theorem GGConfig.center_eq_bot_of_orthTwo {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hRig : GGLabelRigidInput)
    (hcfg : GGConfig p B Bs x L D J)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1) p Bs L) :
    Subgroup.center ↥L = ⊥ := by
  classical
  obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
  haveI : Fact p.Prime := ⟨hp⟩
  have hmarkK : GGInnerDiagOn Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2) hmark
  obtain ⟨lab, hΛ, hhas, R, hRgrp, I, F', θ, hPm⟩ := largeEvenMarking_exists_hasLabel hmark
  obtain ⟨⟨hrow, hn1⟩, -, -⟩ := hPm
  obtain ⟨hp3, htag, hrank⟩ := OrthTorus.ggRowP_EOmP_or_EOmM_data hrow hn1
  subst hp3
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := GGInnerDiagOn.le_normalizer hmarkK
  have hlt : B < Bs := GGConfig.lt_bstar_of_orthTwo hRig hcfg hmark
  have hodd := hcfg.odd_card_center_of_B_lt_Bs hlt hN
  have h1 : Nat.card ↥(Subgroup.center ↥L) = 1 := by
    by_contra h1
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd h1
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hqd)
    exact OrthKExactTwo.center_not_dvd_of_orthogonal_marking hq hq2 hmarkK hhas htag hrank hqd
  exact Subgroup.eq_bot_of_card_eq _ h1

theorem GGConfig.center_eq_bot_of_D4two {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hRig : GGLabelRigidInput)
    (hcfg : GGConfig p B Bs x L D J)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4)
      p Bs L) :
    Subgroup.center ↥L = ⊥ := by
  exact hcfg.center_eq_bot_of_orthTwo hRig
    (hmark.mono_label fun lab h => ⟨Or.inl h.1, h.2.1⟩)

end

section

theorem NSJoin.false_of_twE6_L_typeD {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hD : NSJoin.NSTypeD M)
    (h : GGInnerDiagOnLabel ggRowP_ETwE6 p Bs L) : False := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hX : L = L ∨ ∃ y, GGNbr p B x D J y L := Or.inl rfl
  have hNP : GGNoReflE6Pat p Bs L :=
    ggX_noReflE6Pat_typeD hcfg hpres hD (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl))
  have h5 : GGInnerDiagOnLabel (fun p lab => (ggRowP_ETwE6 p lab ∧ 5 ≤ p) ∨
      (ggRowP_ETwE6 p lab ∧ p = 3)) p Bs L :=
    h.mono' fun _ hl => by
      by_cases h3 : p = 3
      · exact Or.inr ⟨hl, h3⟩
      · exact Or.inl ⟨hl, hp.five_le_of_ne_two_of_ne_three hp2 h3⟩
  rcases GGInnerDiagOnLabel.elim_or h5 with h | h
  · exact (ggX_row_absurd_of_noReflE6Pat hRig ggRowE6Pat_ETwE6_ge5 hcfg hX hNP h).elim
  have hp3 : p = 3 := by
    obtain ⟨lab, -, -, R, _, I, -, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel h
    exact hS.2
  subst hp3
  have hLab : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs L := by
    refine largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ?_) h
    obtain ⟨⟨htag, hdvd⟩, hp3⟩ := hP.1
    refine ⟨⟨htag, hp3, hp3 ▸ hdvd⟩, Or.inr (Or.inl ⟨by rw [htag]; exact fun h => h,
      by rw [htag]; simp, hdvd⟩), hP.2.1, hP.2.2⟩
  have hrk : ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
      3 ^ 5 ≤ Nat.card (ggGamma L hN).range :=
    fun hN => ggTwE6ThreeBstarRankInput_holds G 3 B Bs x L D J hconf hLab hN
  exact (ggX_row_absurd_of_noReflE6PatAt hRig (by norm_num) ggRowE6PatAt_ETwE6_three hcfg hX
    hNP hrk h).elim

theorem NSJoin.exists_orthWeakFrame_L_typeD {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hD : NSJoin.NSTypeD M)
    (hns : ¬ GGSplitLie p L) (hU : ¬ GGMemberUnitary p Bs L)
    (hn1 : ¬ GGInnerDiagOnLabel (fun _ lab => lab.n = 1) p Bs L) :
    ∃ Φ : OrthTorus.OrthWeakFrame p Bs L, Φ.Recognized := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := GGIsWeylMatrixAD.le_three (Or.inr hD)
  haveI : Fact p.Prime := ⟨hp⟩
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨-, hBs, -, -, -⟩ := hconf.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hconf.2.1.2.2.2
  have h1 : GGInnerDiagOnLabel (fun p lab => lab.n = 1 ∨
      ((ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))) ∨
        ggRowP_ETwE6 p lab ∨ ((ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ 2 ≤ lab.n))) p Bs L :=
    (ggL_baseLabel_of_nonSplit hcfg hpres hle3 hns).mono' fun lab hl => by
      by_cases hn : lab.n = 1
      · exact Or.inl hn
      refine Or.inr ?_
      rcases hl with hl | hl | hl | ⟨hn', -⟩
      · exact Or.inl ⟨hl, fun h => hn h.1⟩
      · refine Or.inr (Or.inr ⟨Or.inr hl, ?_⟩)
        have hd := hl.2.2.2
        have h0 : lab.n ≠ 0 := by
          intro h0
          rw [h0, pow_zero] at hd
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
        omega
      · exact Or.inr (Or.inl hl)
      · exact absurd hn' hn
  rcases GGInnerDiagOnLabel.elim_or h1 with h | h
  · exact absurd h hn1
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · exact absurd h hU
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · exact (NSJoin.false_of_twE6_L_typeD hcfg hpres hD h).elim
  · exact OrthTorus.exists_orthWeakFrame_of_marking ggLabelRigidInput_holds hp2 hBs hSC h
      (ggGamma_L_exists_ne_one hconf)

end

section

theorem NSJoin.not_innerDiagOnLabel_two_L_typeD {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hTB : GGTBFixInput) (hU62 : GGU62OuterDiagInput)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hD : NSJoin.NSTypeD M)
    (hns : ¬ GGSplitLie p L) (hU : ¬ GGMemberUnitary p Bs L)
    (hsix : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card ↥(ggRankOneIn L Bs r) ≠ 6) :
    ¬ GGInnerDiagOnLabel (fun _ lab => lab.n = 1) p Bs L := by
  intro hn1
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := GGIsWeylMatrixAD.le_three (Or.inr hD)
  haveI : Fact p.Prime := ⟨hp⟩
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨-, hBs, -, -, -⟩ := hconf.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hconf.2.1.2.2.2
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hno6 : ∀ r ∈ ggAutomizer L Bs, GGIsReflection p r → Nat.card ↥(ggRankOneIn L Bs r) ≠ 6 :=
    fun r hr hrefl => hsix r hr (ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hr) hrefl)
  obtain ⟨lab₁, hΛ₁, hhas₁, -, -, -, -, -, hn₁, -⟩ := largeEvenMarking_exists_hasLabel hn1
  have h1 : GGInnerDiagOnLabel (fun p lab => lab.n = 1 ∧ (ggRowP_ESU p lab ∨ ggRowP_EOmM p lab ∨
      ggRowP_ETwE6 p lab ∨ (lab.n = 1 ∧ p = 3 ∧ (ggRowP_EOmP p lab ∨ ggRowP_EE7 p lab ∨
        ggRowP_EE8 p lab ∨ ggRowP_NF4 p lab)))) p Bs L := by
    refine GGInnerDiagOnLabel.mono_label_of_hasLabel (fun lab hΛ hhas hrow => ⟨?_, hrow⟩)
      (ggL_baseLabel_of_nonSplit hcfg hpres hle3 hns)
    have hAD : lab.tag ≠ .A ∧ (lab.tag = .twD → lab.rank ≠ 2) := by
      rcases hrow with ⟨⟨h, -⟩ | ⟨h, h'⟩, -⟩ | ⟨h, h', -⟩ | ⟨h, -⟩ |
          ⟨-, -, ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩⟩ <;>
        refine ⟨by rw [h]; decide, fun ht => ?_⟩ <;> rw [h] at ht <;>
        first | omega | exact absurd ht (by decide)
    exact (ggLabelIso_n_eq (hRig lab lab₁ _ hΛ hΛ₁ hhas hhas₁) hAD.1 hAD.2).trans hn₁
  have h2 : GGInnerDiagOnLabel (fun p lab =>
      ((lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n + 1) ∨
      (ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) ∨
      (ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))) ∨
      ggRowP_ETwE6 p lab ∨
      (ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) ∨
      ((ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1 ∧ ¬ (lab.tag = .D ∧ lab.rank = 4)) ∨
      ggRowP_EE7 p lab ∨ ggRowP_EE8 p lab ∨ GGF4ThreeLabel p lab) p Bs L :=
    h1.mono' fun lab ⟨hn, hrow⟩ => by
      rcases hrow with hl | hl | hl | ⟨-, hp3, hl | hl | hl | hl⟩
      · by_cases h3 : lab.rank = 3
        · exact Or.inl ⟨hl.1.imp And.left And.left, h3, hl.2⟩
        by_cases h5 : lab.rank = 5
        · exact Or.inr (Or.inl ⟨hl, hn, h5⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨hl, fun h => h.2.elim h3 h5⟩))
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr hl, hn, ?_⟩)))))
        rintro ⟨ht, -⟩
        rw [hl.1] at ht
        exact absurd ht (by decide)
      · exact Or.inr (Or.inr (Or.inr (Or.inl hl)))
      · by_cases h4 : lab.rank = 4
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hl, hn, h4⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl hl, hn,
            fun h => h4 h.2⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨hl.1, hp3, ?_⟩)))))))
        rw [hn]
        norm_num
  have hOrth : ∀ P : ℕ → LargeEvenLabel → Prop,
      (∀ lab, P p lab → ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) → (∀ lab, P p lab → lab.n = 1) →
      GGInnerDiagOnLabel P p Bs L →
      (∀ lab, P p lab → GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) → Subgroup.center ↥L = ⊥) →
      False := by
    intro P hProw hPn hmark hZK
    obtain ⟨lab, hPlab, -, Φ, -, hcard, -⟩ :=
      OrthTorus.exists_orthFrameCore_of_marking hRig hp2 hBs hSC hProw hmark hZK
        (ggGamma_L_exists_ne_one hconf)
    have hK : Nat.card Φ.F = 2 := by rw [hcard, hPn lab hPlab, pow_one]
    obtain ⟨a, ha, hrefl, h6⟩ := Φ.exists_refl_card_six hK
    exact hno6 a ha hrefl h6
  have hX : L = L ∨ ∃ y, GGNbr p B x D J y L := Or.inl rfl
  have hNP : GGNoReflE6Pat p Bs L :=
    ggX_noReflE6Pat_typeD hcfg hpres hD (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl))
  rcases GGInnerDiagOnLabel.elim_or h2 with h | h
  ·
    exact not_ggInnerDiagOnLabel_unitary_four hconf h
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    have hFix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) →
        (b : G) ∈ Subgroup.zpowers x := by
      obtain ⟨y, K', hN⟩ := exists_ggNbr hconf.1.2.2.2.2.2.2.2 hconf.2.2
      intro b hb
      exact hTB G p B Bs x L D J hconf hcfg.1.2.1 hcfg.1.2.2.1 hcfg.1.2.2.2.1 y K' hN
        (hcfg.2.1 y K' hN) (Or.inr hcfg.2.1) b hb
    obtain ⟨hcard, -⟩ := nsQ2U62_card_D hcfg hFix h hpres hD
    obtain ⟨K, _hf, _hfin, lab, m', θ, hK, -, hmrank, hSide, hdvd, hperf, -, hBsN, hbs⟩ :=
      ggNSLieN3A_esuCore h (fun p lab hl => hl.1)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := lab.n) hK
    obtain ⟨tag, rank, n⟩ := lab
    obtain ⟨-, hn, hr5⟩ := hSide
    change n = 1 at hn
    change rank = 5 at hr5
    change m' = rank + 1 at hmrank
    subst hn
    subst hr5
    have hm6 : m' = 6 := by omega
    subst hm6
    obtain ⟨r, hrA, hrefl, hr6⟩ :=
      ggNsq2_exists_rankOne hU62 hTB hcfg hK hdvd θ hperf hBsN hbs (fun _ => hcard.ge)
    exact hno6 r hrA hrefl hr6
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    exact hU h
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    exact NSJoin.false_of_twE6_L_typeD hcfg hpres hD h
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    exact hOrth _ (fun _ hl => Or.inl hl.1) (fun _ hl => hl.2.1) h
      (fun _ _ _ => GGConfig.center_eq_bot_of_D4two hRig hconf h)
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    haveI : Group.IsPerfect ↥L := Group.IsPerfect.mk h.1
    refine hOrth _ (fun _ hl => hl.1) (fun _ hl => hl.2.1) h fun lab hl hhas => ?_
    obtain ⟨hrow, hn, h4⟩ := hl
    refine OrthTorus.center_eq_bot_of_hasLabel_orth_two ?_ hn hhas
    rcases hrow with ⟨ht, hr, -, -⟩ | ⟨ht, hr, -, -⟩
    · have h4' : lab.rank ≠ 4 := fun h => h4 ⟨ht, h⟩
      exact Or.inl ⟨ht, by omega⟩
    · exact Or.inr ⟨ht, by omega⟩
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    exact ggX_row_absurd_of_noReflE6Pat hRig ggRowE6Pat_EE7 hcfg hX hNP h
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    exact ggX_row_absurd_of_noReflE6Pat hRig ggRowE6Pat_EE8 hcfg hX hNP h
  ·
    exact NSJoin.not_f4Three_of_cfg hcfg hpres hle3 h

theorem NSJoin.exists_orthWeakFrame_L_typeD_of_guard {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hTB : GGTBFixInput) (hU62 : GGU62OuterDiagInput)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hD : NSJoin.NSTypeD M)
    (hns : ¬ GGSplitLie p L) (hU : ¬ GGMemberUnitary p Bs L)
    (hsix : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card ↥(ggRankOneIn L Bs r) ≠ 6) :
    ∃ Φ : OrthTorus.OrthWeakFrame p Bs L, Φ.Recognized :=
  NSJoin.exists_orthWeakFrame_L_typeD hcfg hpres hD hns hU
    (NSJoin.not_innerDiagOnLabel_two_L_typeD hTB hU62 hcfg hpres hD hns hU hsix)

end

end CFSG.StandardType

end
