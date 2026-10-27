module

public import CFSG.Quasithin.Background.SmithD321SQ
public import CFSG.Quasithin.Background.SmithD321StepU
public import CFSG.Quasithin.Background.SmithD321CaseIIb
public import CFSG.Quasithin.Vol2.Ch5Sec1L34D38
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.C2PushThree
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.D2Tools
public import CFSG.Quasithin.Background.F918C6
public import CFSG.Quasithin.Background.F918H5
public import CFSG.Quasithin.Background.F918L3
public import CFSG.Quasithin.Background.InternalSecRealB
public import CFSG.Quasithin.Background.SmithB51SL3A
public import CFSG.Quasithin.Background.SmithD321Sym
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146A2
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.S153Cases
public import CFSG.Quasithin.EmptyFaithful.S153DInputs
public import CFSG.Quasithin.EmptyFaithful.S153Five
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.H13.ExcludedOrders
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch10SecQ1Base
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523F
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QHat
public import CFSG.Quasithin.Vol2.Ch6Defs
public import CFSG.Quasithin.Vol2.Ch6Vocab
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.CentralCover.FourGroupWitness
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.Timmesfeld.Orders.Exceptional

public section

namespace CFSG.Quasithin

namespace SmithD321

open CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def CaseIStep : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W) (A : Subgroup (MulAut W)) (r : ℚ), D321Sit M Mp T L V t A r →
    V = orbSup T V → A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥ → False

@[expose] def CaseIIaStep : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W) (A : Subgroup (MulAut W)) (r : ℚ), D321Sit M Mp T L V t A r →
    V < orbSup T V → D36cConcl Mp T L V t → commSub (orbSup T V) L = V →
    A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥ → 3 ∣ Nat.card ↥L →
    D321Two L ∨ D321Three Mp L

@[expose] def SzStep : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W) (A : Subgroup (MulAut W)) (r : ℚ), D321Sit M Mp T L V t A r →
    V < orbSup T V → D36cConcl Mp T L V t → commSub (orbSup T V) L = V → ∀ n : ℕ,
    IsSz n ↥L → False

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem three_dvd_of_autSub {X : Subgroup (MulAut W)} {U : Subgroup W} (hX : X ≤ stabSub U)
    (h : 3 ∣ Nat.card ↥(autSub X U)) : 3 ∣ Nat.card ↥X := by
  rw [← card_autSub_mul hX]
  exact h.mul_right _

theorem isSz_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ}
    (h : IsSz n Y) : IsSz n X := by
  obtain ⟨hp, a, ha, K, hK, hKf, hn, hcard, ⟨f⟩⟩ := h
  exact ⟨hp, a, ha, K, hK, hKf, hn, hcard, ⟨e.trans f⟩⟩

omit [Finite W] in
theorem isSz_conjAutSub {L : Subgroup (MulAut W)} (t : MulAut W) {n : ℕ} (h : IsSz n ↥L) :
    IsSz n ↥(conjAutSub t L) :=
  isSz_of_mulEquiv
    (Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).symm h

namespace D321Base

variable {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
  (hB : D321Base M Mp T L V t)
include hB

omit [Finite W] hB in
theorem card_Lt : Nat.card ↥(conjAutSub t L) = Nat.card ↥L :=
  (Nat.card_congr (Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective).toEquiv).symm

theorem L_le_stabSub_V : L ≤ stabSub V := fun l hl =>
  mem_stabSub_of_inv (hB.Mp_inv_V l (hB.L_le_Mp hl))
    (hB.Mp_inv_V l⁻¹ (hB.L_le_Mp (L.inv_mem hl)))

theorem L_le_stabSub_orbSup : L ≤ stabSub (orbSup T V) := fun _ hl =>
  ((n1_sup_le_stabSub_sec hB.hD.hyp).trans inf_le_left)
    ((le_sup_left : Mp ≤ Mp ⊔ T) (hB.L_le_Mp hl))

theorem three_dvd_of_d37 (h37 : D37) (hVT : V = orbSup T V) : 3 ∣ Nat.card ↥L := by
  refine three_dvd_of_autSub hB.L_le_stabSub_V ?_
  rcases h37 W M Mp T L V hB.hD hVT t hB.htT hB.htn hB.hMp with ⟨n, hn, -⟩ | ⟨hn, -⟩
  · exact H13.three_dvd_card_of_isPSL_two_two hn
  · exact H13.three_dvd_card_of_isPSL_three_two hn

theorem three_dvd_of_caseIIb (hc : D36cConcl Mp T L V t) (hne : commSub (orbSup T V) L ≠ V) :
    3 ∣ Nat.card ↥L := by
  obtain ⟨hpsl, -⟩ := hc.2.2.2.resolve_left hne
  exact three_dvd_of_autSub hB.L_le_stabSub_orbSup (H13.three_dvd_card_of_isPSL_three_two hpsl)

theorem isSz_of_not_three_dvd (hA23 : A23SQTKListFact) (hSzF : H13.SimpleThreePrimeSuzukiFact)
    (h3 : ¬ 3 ∣ Nat.card ↥L) : ∃ n, IsSz n ↥L := by
  obtain ⟨n, hn⟩ := SmithD39Two.suzukiModel_of_le_of_not_dvd hA23 hSzF hB.hD.hyp.qsqtk hB.L_le
    hB.quasi h3
  have hZ : Subgroup.center ↥L = ⊥ := by
    have := hB.hsimp
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h0 | h0
    · exact h0
    · exfalso
      refine not_isSolvable_of_mem_cComp hB.hD.hyp.comp (Group.isSolvable_of_comm fun c d => ?_)
      exact Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top d) c
  refine ⟨n, isSz_of_mulEquiv ?_ hn⟩
  exact (QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)

end D321Base

namespace D321Sit

variable {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
  {A : Subgroup (MulAut W)} {r : ℚ} (hS : D321Sit M Mp T L V t A r)
include hS

theorem inf_cent_eq_bot_of_three_dvd (h38 : D38Top) (hA23 : A23SQTKListFact)
    (hSzF : H13.SimpleThreePrimeSuzukiFact) (h3L : 3 ∣ Nat.card ↥L) :
    A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥ :=
  inf_cent_eq_bot h38 hA23 hSzF hS.hD hS.hr hS.hr2 hS.hAQ
    (fun _ hp hp5 => hS.commutator_pCoreOf_eq_bot hp hp5)
    (fun _ hx hx3 => hS.eq_one_of_pow_prime Nat.prime_three (by norm_num) h3L hx hx3)

theorem concl_of_caseII (hIIa : CaseIIaStep) (hlt : V < orbSup T V) (hc : D36cConcl Mp T L V t)
    (hAC : A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥) (h3L : 3 ∣ Nat.card ↥L) :
    IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤ ∧
      commV L ≤ fixV (conjAutSub t L) ∧ (D321Two L ∨ D321Three Mp L) := by
  refine ⟨hS.isSumMod hc.1, hS.commV_le_fixV hc.1, ?_⟩
  by_cases hU : commSub (orbSup T V) L = V
  · exact hIIa W M Mp T L V t A r hS hlt hc hU hAC h3L
  · exact (caseIIb_false hS hc hU hAC).elim

theorem false_of_caseII_sz (hSz : SzStep) (hlt : V < orbSup T V) (hc : D36cConcl Mp T L V t)
    (h3L : ¬ 3 ∣ Nat.card ↥L) {n : ℕ} (hn : IsSz n ↥L) : False := by
  by_cases hU : commSub (orbSup T V) L = V
  · exact hSz W M Mp T L V t A r hS hlt hc hU n hn
  · exact h3L (hS.three_dvd_of_caseIIb hc hU)

end D321Sit

end SmithD321

open SmithD321 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique in
theorem d321_of_steps (h36 : D36c) (h37 : D37) (hL38 : D3L38)
    (h38 : D38Top) (hA23 : A23SQTKListFact) (hSzF : H13.SimpleThreePrimeSuzukiFact)
    (hI : CaseIStep) (hIIa : CaseIIaStep) (hSz : SzStep) :
    ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
      D3Std M Mp T L V → ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
        Mp = L ⊔ conjAutSub t L → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) →
        orbSup T V = ⊤ ∨
          (IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤ ∧
            commV L ≤ fixV (conjAutSub t L) ∧ (D321Two L ∨ D321Three Mp L)) := by
  intro W _ _ M Mp T L V hD t htT htn hMp hqM
  by_cases htop : orbSup T V = ⊤
  · exact Or.inl htop
  right
  have hB := d321Base_of hL38 hD htT htn hMp
  obtain ⟨A, r, hS⟩ := hB.exists_sit hqM htop
  have hcard := D321Base.card_Lt (L := L) (t := t)
  by_cases h3L : 3 ∣ Nat.card ↥L
  · have hAC := hS.inf_cent_eq_bot_of_three_dvd h38 hA23 hSzF h3L
    rcases (le_orbSup T V).eq_or_lt with hVT | hlt
    · exact (hI W M Mp T L V t A r hS hVT hAC).elim
    · rcases h36 W M Mp T L V hD hlt t htT htn hMp with hc | hc
      · exact hS.concl_of_caseII hIIa hlt hc hAC h3L
      · exact hB.concl_of_swap (hS.swap.concl_of_caseII hIIa hlt hc hAC (hcard ▸ h3L))
  · obtain ⟨n, hn⟩ := hB.isSz_of_not_three_dvd hA23 hSzF h3L
    rcases (le_orbSup T V).eq_or_lt with hVT | hlt
    · exact (h3L (hB.three_dvd_of_d37 h37 hVT)).elim
    · rcases h36 W M Mp T L V hD hlt t htT htn hMp with hc | hc
      · exact (hS.false_of_caseII_sz hSz hlt hc h3L hn).elim
      · exact (hS.swap.false_of_caseII_sz hSz hlt hc (hcard ▸ h3L) (isSz_conjAutSub t hn)).elim

end CFSG.Quasithin
