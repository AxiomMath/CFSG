module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFourTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CharTwoTorusOn
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Section17KFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRankBound
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.GroupTheory.CoprimeCentralizerCover
public import CFSG.GroupTheory.ConjClosureCentralProduct
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.TorusBound
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrOrth
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarU3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.F918H5
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
public import CFSG.Quasithin.EmptyFaithful.S14610Q1
public import CFSG.Quasithin.EmptyFaithful.S14610Top
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.H13.QRCThreeFreeRankOneStep
public import CFSG.Quasithin.SteinbergBKHigherElementaryThompson
public import CFSG.Quasithin.Vol2.Ch11SecBK10E
public import CFSG.Quasithin.Vol2.Ch11SecBK10F
public import CFSG.Quasithin.Vol2.Ch11SecSMain
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Lie
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113C2
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeC2
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeEqCartan
public import CFSG.Quasithin.Vol2.Ch6Sec1G22
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem11
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem12
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem3
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
public import CFSG.RankThree.PartOne.Q1327T.Defs
public import CFSG.RankThree.PartOne.Q1327T.ThetaLift
public import CFSG.RankThree.PartOne.S10.SelectedPrimeFixCoprimeQuotientComponents
public import CFSG.RankThree.PartTwo.KFacts.KS116Proof
public import CFSG.RankThree.PartTwo.Sec11.Item1115
public import CFSG.RankThree.PartTwo.Sec11.Item116H3Main
public import CFSG.RankThree.PartTwo.Sec11.Item116R1CD
public import CFSG.RankThree.PartTwo.Sec11.Item116R2NoHoles
public import CFSG.RankThree.PartTwo.Sec11.Item118
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec11.LSSolvableProof
public import CFSG.RankThree.PartTwo.Sec11.Transitivity
public import CFSG.RankThree.PartTwo.Sec13.Item131Transport
public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec6.Item612
public import CFSG.RankThree.PartTwo.Sec6.Item65Tools
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import Certificates.Certificate9415

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem strongly_of_two_le_pRank_centralizer {D : Data G} {p : ℕ}
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h76 : F07.R76 D) (h614 : UC6.R6_14 D) (hp : p ∈ D.sig)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {R E : Subgroup G} (hR : IsSylowOf r R D.M) (hEel : IsElemAbelian r E)
    (hEcard : Nat.card E = r ^ 2) (hEZ : E ≤ R ⊓ Subgroup.centralizer (R : Set G))
    (hF : 2 ≤ CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G))) :
    IsStronglyPEmbedded r D.M := by
  classical
  by_cases hrsig : r ∈ D.sig
  · exact hSg.sig1_sp r (by rw [← h1219]; exact hrsig)
  · have hpP : p.Prime := (D.sig_prime p hp).1
    have hp2 : p ≠ 2 := (D.sig_prime p hp).2
    have hsp : IsStronglyPEmbedded p D.M :=
      hSg.sig1_sp p (by rw [← h1219]; exact hp)
    have hEM : E ≤ D.M := (hEZ.trans inf_le_left).trans hR.le
    have hEr : IsPGroup r E := hEel.isPGroup
    have hEr2 : 2 ≤ CFSG.Open.pRank r E :=
      CFSG.SectionRank.le_pRank hr.one_lt le_rfl hEel hEcard
    haveI : Fact p.Prime := ⟨hpP⟩
    haveI : Fact r.Prime := ⟨hr⟩
    have hGamma : rankThreeGamma 1 r E ≤ D.M :=
      rankThreeGamma_le_of_two_le_pRank_inf_centralizer
        hsp (h76 p hpP hp2 hsp) hEM hEr hEr2 hF
    exact h614 (by rw [h1219]) r hr hr2 hrsig R hR E hEZ hEel hEcard hGamma

structure S17_46Core (D : Data G) (V₀ V L X : Subgroup G) (p n l : ℕ)
    (C Dc : Subgroup G) (Gamma : Set G) : Prop where
  L_eq_X : L = X
  odd_n : Odd n
  shape : ∃ (t : CFSG.Open.StatedLieTag) (m : ℕ),
    CFSG.Blueprint.LieModel (BarInf L) t m 2 n ∧
      ((t = .PSL ∧ m = 4) ∨ (t = .PSU ∧ m = 6) ∨ (t = .PSp ∧ m = 3) ∨
        (t = .POmegaMinus ∧ m = 4))
  bang : ∃ r : ℕ, r.Prime ∧ 7 ≤ r ∧ r ∣ 2 ^ n - 1 ∧
    ∀ E : Subgroup G, E ≤ L → IsElemAbelian r E → Nat.card E = r ^ 2 →
      CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G)) ≤ 1
  hM4 : 4 ≤ CFSG.Open.pRank p D.M
  hOp : CFSG.LocalAnalysis.UniquenessCase.UC22.F10.OpRes p D.M = D.M
  centOverO2 : CFSG.Open.pRank p (F08.CentOverO2 D.M L) ≤ 1
  cartanCent : CFSG.Open.pRank p C ≤ 1

theorem pRank_cartan_le_one_of_centE_of_borel {D : Data G} {V₀ V X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V X X p n l C Dc Gamma)
    {f : ℕ} (hB : Inputs1719.BorelChevOver (BarInf X) f)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hC3 : 3 ≤ CFSG.Open.pRank r C)
    (hcentE : ∀ E : Subgroup G, E ≤ X → IsElemAbelian r E → Nat.card E = r ^ 2 →
      CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G)) ≤ 1) :
    CFSG.Open.pRank p C ≤ 1 := by
  classical
  have hp1 : 1 < p := hp.one_lt
  have hCL : C ≤ X := ctx.cartan.1
  have hCX : C ≤ D.M := hCL.trans ctx.mem_calC.1.le
  have hCN : C ≤ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G) := ctx.cartan.2.2.1
  obtain ⟨A, hAC, hAel, hAcard⟩ := CFSG.SectionRank.exists_pRank hr.one_lt C
  have hA2 : r ^ 2 ≤ Nat.card A := by
    rw [hAcard]
    exact Nat.pow_le_pow_right hr.pos (by omega)
  obtain ⟨E, hEA, hEel, hEcard⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.exists_card_p_sq hr hAel hA2
  have hEC : E ≤ C := hEA.trans hAC
  have hEX : E ≤ X := hEC.trans hCL
  have hEr : IsPGroup r E := hEel.isPGroup
  have hcent : CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G)) ≤ 1 :=
    hcentE E hEX hEel hEcard
  haveI : Fact p.Prime := ⟨hp⟩
  have hquot := isMulCommutative_normalizer_inf_quotient_of_calC_of_borel (D := D) (L := X)
    (X := X) (n := f) ctx.mem_calC ctx.X_eq hB
  have hCC : ⁅C, C⁆ ≤ C ⊓ D.T := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.commutator_le_self C)
      (Subgroup.commutator_mem_commutator hu hv), ?_⟩
    have hcomm :=
      CFSG.GroupTheory.commutatorElement_mem_of_isMulCommutative_subgroupOf hquot
        ⟨hCL hu, hCN hu⟩ ⟨hCL hv, hCN hv⟩ (hCN hu) (hCN hv)
    exact (Subgroup.mem_inf.mp hcomm).1
  let N : Subgroup G := C ⊓ D.T
  have hNC : N ≤ C := inf_le_left
  have hN2 : IsPGroup 2 N := D.sylowM.isPGroup.to_le inf_le_right
  have hNnorm : (N.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNC]
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact ⟨C.mul_mem (C.mul_mem hc hn.1) (C.inv_mem hc),
        ((Subgroup.mem_normalizer_iff.mp (hCN hc) (n : G)).1 ⟨hn.2, hCL hn.1⟩).1⟩
    · intro hn
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h1 : c⁻¹ * (c * (n : G) * c⁻¹) * c ∈ C := by
          refine C.mul_mem ?_ hc
          exact C.mul_mem (C.inv_mem hc) hn.1
        simpa [mul_assoc] using h1
      · have h2 : n ∈ D.T ⊓ X := by
          have := (Subgroup.mem_normalizer_iff.mp (hCN (C.inv_mem hc))
            (c * (n : G) * c⁻¹)).1
            ⟨hn.2, hCL hn.1⟩
          simpa [mul_assoc] using this
        exact h2.1
  haveI : (N.subgroupOf C).Normal := hNnorm
  have hCnorm : C ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hNC
  have hEN : E ≤ Subgroup.normalizer (N : Set G) := hEC.trans hCnorm
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p C
  have hPC : P ≤ C := hP.le
  let Xp : Subgroup G := P ⊔ N
  have hXpC : Xp ≤ C := sup_le hPC hNC
  have hconjP : ∀ e ∈ E, ∀ q ∈ P, e * q * e⁻¹ ∈ Xp := by
    intro e he q hq
    have heC : e ∈ C := hEC he
    have hqC : q ∈ C := hPC hq
    have hcommN : ⁅e, q⁆ ∈ N := hCC (Subgroup.commutator_mem_commutator heC hqC)
    have heq : e * q * e⁻¹ = ⁅e, q⁆ * q := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact Xp.mul_mem ((le_sup_right : N ≤ Xp) hcommN) ((le_sup_left : P ≤ Xp) hq)
  have hconjN : ∀ e ∈ E, ∀ n ∈ N, e * n * e⁻¹ ∈ N := fun e he n hn =>
    (Subgroup.mem_normalizer_iff.mp (hEN he) n).1 hn
  have hPN : P ≤ Subgroup.normalizer (N : Set G) := hPC.trans hCnorm
  have hXp_eq : (Xp : Set G) = (P : Set G) * (N : Set G) := by
    rw [show Xp = P ⊔ N from rfl]
    exact Subgroup.coe_mul_of_left_le_normalizer_right P N hPN
  have hconjXp : ∀ e ∈ E, ∀ x ∈ Xp, e * x * e⁻¹ ∈ Xp := by
    intro e he x hx
    have hx' : x ∈ (P : Set G) * (N : Set G) := by
      rw [← hXp_eq]
      exact hx
    obtain ⟨q, hq, n, hn, rfl⟩ := Set.mem_mul.mp hx'
    have h1 : e * q * e⁻¹ ∈ Xp := hconjP e he q hq
    have h2 : e * n * e⁻¹ ∈ N := hconjN e he n hn
    have heq : e * (q * n) * e⁻¹ = (e * q * e⁻¹) * (e * n * e⁻¹) := by group
    rw [heq]
    exact Xp.mul_mem h1 ((le_sup_right : N ≤ Xp) h2)
  have hEXp : E ≤ Subgroup.normalizer (Xp : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconjXp e he x
    · intro hx
      have h := hconjXp e⁻¹ (E.inv_mem he) (e * x * e⁻¹) hx
      have hEq : e⁻¹ * (e * x * e⁻¹) * (e⁻¹)⁻¹ = x := by group
      rwa [hEq] at h
  have hXpE : ⁅Xp, E⁆ ≤ N :=
    (Subgroup.commutator_mono hXpC hEC).trans hCC
  have hNr : ¬ r ∣ Nat.card N :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hN2 hr (by omega)
  have hNp : ¬ p ∣ Nat.card N :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hN2 hp hp2
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨S, hS, hSE⟩ :=
    CFSG.GroupTheory.exists_isSylowOf_le_centralizer_of_commutator_le
      (p := r) (q := p) (X := Xp) (N := N) (R := E)
      le_sup_right hEXp hEN hEr hNr hXpE hNp
  have hSC : S ≤ C := hS.le.trans hXpC
  have h1 : CFSG.Open.pRank p C ≤
      CFSG.Open.pRank p (C ⊓ Subgroup.centralizer (E : Set G)) := by
    calc CFSG.Open.pRank p C = CFSG.Open.pRank p P :=
          (CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.pRank_eq_of_isSylowOf hP).symm
      _ ≤ CFSG.Open.pRank p Xp := CFSG.SectionRank.pRank_mono hp1 le_sup_left
      _ = CFSG.Open.pRank p S :=
          (CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.pRank_eq_of_isSylowOf hS).symm
      _ ≤ CFSG.Open.pRank p (C ⊓ Subgroup.centralizer (E : Set G)) :=
          CFSG.SectionRank.pRank_mono hp1 (le_inf hSC hSE)
  have h2 : CFSG.Open.pRank p (C ⊓ Subgroup.centralizer (E : Set G)) ≤
      CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G)) :=
    CFSG.SectionRank.pRank_mono hp1 (inf_le_inf hCX le_rfl)
  exact (h1.trans h2).trans hcent

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
