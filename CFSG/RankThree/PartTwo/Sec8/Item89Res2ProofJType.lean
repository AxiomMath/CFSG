module

public import CFSG.RankThree.PartTwo.Sec8.Item89Res2ProofJComp
import CFSG.RankThree.PartTwo.Sec8.Item87Proof
import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofUnitary
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofOuterPair
import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofG2Two
import CFSG.RankThree.PartTwo.KFacts.K71Sp4
import CFSG.RankThree.PartTwo.KFacts.K71Item89
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
import CFSG.Quasithin.H13.L32NSp4S6
import CFSG.Quasithin.Background.FFC2G2
import CFSG.Quasithin.Background.B5FinOutAlt
import CFSG.Quasithin.Background.B5FinG2U33
import CFSG.Quasithin.Background.JonesParshallG2Field
import CFSG.Quasithin.Background.JonesParshallG2Two
import CFSG.Quasithin.Recognition.CertU33Perm
import CFSG.Quasithin.Background.S1549DL3N
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Eq
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.AutFactsU33
import CFSG.LieType.Steinberg.G2.Perfect
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.LieType.Chevalley.ExactG2FiniteOrder
import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import Certificates.Certificate8952
public import Certificates.Certificate8953
public import Certificates.Certificate17002
public import Certificates.Certificate17028
public import Certificates.Certificate17951
public import Certificates.Certificate19953
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.RankThree.PartTwo.Sec4.Item4Res3Proof419
public import CFSG.RankThree.PartTwo.Sec6.Item612
public import CFSG.RankThree.PartTwo.Sec6.Item65One
public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofAssembly
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
import CFSG.Quasithin.Background.B69Core
import CFSG.Quasithin.Background.FFC7G
import CFSG.Quasithin.EmptyFaithful.S1417Sylow
import CFSG.Quasithin.EmptyFaithful.T1515Der
import CFSG.Quasithin.H13.L32NSp4S120
import CFSG.Quasithin.H13.L32NSp4S36
import CFSG.RankThree.Asc83Table.PermTables
import CFSG.RankThree.PartTwo.KFacts.KS12MovesSL
import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec13.Item135
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item143N
import CFSG.RankThree.PartTwo.Sec15.Item157
import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofFus
import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item167Proof
import CFSG.RankThree.PartTwo.Sec16.Item16Tail17
import CFSG.RankThree.PartTwo.Sec16.Item16Tail19
import CFSG.RankThree.PartTwo.Sec16.Item16TailMore
import CFSG.RankThree.PartTwo.Sec17.Item1724Two
import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
import CFSG.RankThree.PartTwo.Sec17.RouteProvers
import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
import CFSG.RankThree.PartTwo.Sec21.Item226Steps
import CFSG.RankThree.PartTwo.Sec21.Item229
import CFSG.RankThree.PartTwo.Sec4.Item426A6
import CFSG.RankThree.PartTwo.Sec8.Standing
import CFSG.RankThree.S4Free.SuzukiEight
import Certificates.Certificate14953
import Certificates.Certificate8166

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSp StatedSU)
open CFSG.Blueprint

section KFact


@[expose] def KF89JCentTypeRee : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G) (a : G) (m : ℕ), 1 ≤ m →
    IsGammaTypeRee (X ⧸ aschbacherSolvableCore 3 X) m → a ^ 3 = 1 →
    (KFacts.InducesStdKind X a .field ∨ KFacts.InducesStdKind X a .graphField) →
      Sec4.IsType419Theta (perfectResidual (barCentralizer (Subgroup.zpowers a) X)) ∧
        3 ∣ Nat.card (perfectResidual (barCentralizer (Subgroup.zpowers a) X))

end KFact

namespace Item89Res2

theorem perfectResidual_eq_commutator {Q : Type} [Group Q] (h : Group.IsPerfect (commutator Q)) :
    perfectResidual Q = commutator Q := by
  refine le_antisymm ?_ (Item87Res2Proof.le_perfectResidual_of_isPerfect h)
  have h1 : perfectResidual Q ≤ derivedSeries Q 1 := iInf_le _ 1
  rwa [derivedSeries_one] at h1

theorem perfectResidual_perm_six :
    perfectResidual (Equiv.Perm (Fin 6)) = alternatingGroup (Fin 6) := by
  have h5 : 5 ≤ Nat.card (Fin 6) := by rw [Nat.card_fin]; norm_num
  have hc : commutator (Equiv.Perm (Fin 6)) = alternatingGroup (Fin 6) :=
    alternatingGroup.commutator_perm_eq h5
  have hp : Group.IsPerfect (commutator (Equiv.Perm (Fin 6))) := by
    rw [hc]
    exact ⟨commutator_alternatingGroup_eq_top h5⟩
  rw [perfectResidual_eq_commutator hp, hc]

noncomputable def perfectResidualEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    perfectResidual A ≃* perfectResidual B :=
  ((perfectResidual A).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (KFacts.perfectResidual_map_mulEquiv e))

noncomputable def perfectResidualEquivSelf {A : Type} [Group A] (h : Group.IsPerfect A) :
    perfectResidual A ≃* A :=
  (MulEquiv.subgroupCongr (KFacts.perfectResidual_eq_top_of_isPerfect h)).trans Subgroup.topEquiv

theorem type_of_projSp {C : Type} [Group C] {m : ℕ} (hm : 1 ≤ m)
    (e : C ≃* projSp 2 (GaloisField 2 m)) :
    Sec4.IsType419Theta (perfectResidual C) ∧ 3 ∣ Nat.card (perfectResidual C) := by
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · obtain rfl : m = 1 := by omega
    have hF2 : Nat.card (GaloisField 2 1) = 2 := by rw [hF, pow_one]
    set ψ : C ≃* Equiv.Perm (Fin 6) :=
      ((e.trans (Sec4.projSpEquivStatedProj 2 _)).trans
        (CFSG.RankThree.PartOne.KCSpComm.statedProjEquivSympFour hF2)).trans
        CFSG.Quasithin.H13.Sp4Cert.sympFourEquiv with hψ
    set eR : perfectResidual C ≃* alternatingGroup (Fin 6) :=
      (perfectResidualEquiv ψ).trans (MulEquiv.subgroupCongr perfectResidual_perm_six) with heR
    refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨eR⟩))))), ?_⟩
    rw [Nat.card_congr eR.toEquiv, KFacts.card_alternatingGroup_six]
    norm_num
  · have h4 : 4 ≤ Nat.card (GaloisField 2 m) := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have h4' : ∃ s : Finset (GaloisField 2 m), s.card = 4 := by
      have : Fintype (GaloisField 2 m) := Fintype.ofFinite _
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ :
        Finset (GaloisField 2 m))) (n := 4) (by
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
          exact h4)
      exact ⟨s, hs⟩
    have hp := CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect 2
      (GaloisField 2 m) (Or.inl h4')
    set ψ := e.trans (Sec4.projSpEquivStatedProj 2 _) with hψ
    have hperfC : Group.IsPerfect C :=
      hp.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective
    set eR : perfectResidual C ≃* projSp 2 (GaloisField 2 m) :=
      (perfectResidualEquivSelf hperfC).trans e with heR
    refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm2, ⟨eR⟩⟩)))), ?_⟩
    rw [Nat.card_congr eR.toEquiv, Sec19.Step1911Proof.card_projSp_two hm]
    refine Dvd.dvd.mul_left (Dvd.dvd.mul_right ?_ _) _
    have h4 : (2 ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h4]
    exact Item87Proof.three_dvd_four_pow_sub_one m

section Types


open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.QuasithinUnique.Bridge.Alt57Model CFSG.Open in
theorem nonempty_commutator_g2_two_mulEquiv {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    Nonempty (commutator (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) ≃* projSU 3 3 1) := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hF, pow_one])
  let ε : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm
  set Q := CFSG.Blueprint.Chevalley.adjointGroup .G2 K
  obtain ⟨E⟩ := Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hK
  obtain ⟨f1⟩ := CFSG.Quasithin.nonempty_commutator_equiv
    (Subgroup.topEquiv.trans E : ↥(⊤ : Subgroup Q) ≃* ↥(quasithinG2 K))
  have hc : ⁅quasithinG2 K, quasithinG2 K⁆ = ⁅cayleyGroup K, cayleyGroup K⁆ := by
    rw [quasithinG2_eq_cayleyGroup]
  let f2 : ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* ↥⁅cayleyGroup K, cayleyGroup K⁆ :=
    MulEquiv.subgroupCongr hc
  let f3 : ↥⁅cayleyGroup K, cayleyGroup K⁆ ≃* ↥subG2 :=
    ((zornConj ε).subgroupMap _).trans
      (MulEquiv.subgroupCongr ((map_cayley_commutator ε).trans g2Two_commutator_eq))
  let F : ↥(⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆) ≃* U33G :=
    (((f1.trans f2).trans f3).trans u33EquivSubG2.symm)
  have hU : CFSG.Open.StatedClassicalModel (projSU 3 3 1) .PSU 3 3 1 := by
    refine ⟨⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩, GaloisField 3 (2 * 1), inferInstance,
      inferInstance, ?_, ⟨Sec4.projSUEquivStatedProj 3 3 1⟩⟩
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  obtain ⟨eU⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.nonempty_mulEquiv_u33G_of_statedClassicalModel
      hU
  exact ⟨(MulEquiv.subgroupCongr (commutator_def Q)).trans (F.trans eU.symm)⟩

theorem type_of_isoGTwoEven {C : Type} [Group C] {m : ℕ} (hm : 1 ≤ m) (h : IsoGTwoEven C m) :
    Sec4.IsType419Theta (perfectResidual C) ∧ 3 ∣ Nat.card (perfectResidual C) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  set Q := CFSG.Blueprint.Chevalley.adjointGroup .G2 K
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · obtain rfl : m = 1 := by omega
    have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
    obtain ⟨eU⟩ := nonempty_commutator_g2_two_mulEquiv hK2
    have hUs : IsSimpleGroup (projSU 3 3 1) :=
      Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 3 1 le_rfl (by norm_num)
    have hcs : IsSimpleGroup (commutator Q) := eU.isSimpleGroup
    have hnc : ∃ x y : commutator Q, x * y ≠ y * x := by
      obtain ⟨x, y, hxy⟩ := (CFSG.Quasithin.FFC.commutator_data_g2 hK2
        (Subgroup.topEquiv.trans
          (Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hK2).some)).2.1
      refine ⟨(MulEquiv.subgroupCongr (commutator_def Q)).symm x,
        (MulEquiv.subgroupCongr (commutator_def Q)).symm y, fun h' => hxy ?_⟩
      have := congrArg (MulEquiv.subgroupCongr (commutator_def Q)) h'
      simpa using this
    have hcp : Group.IsPerfect (commutator Q) :=
      Item812Res6.isPerfect_of_isSimpleGroup_of_not_comm hnc
    have hres : perfectResidual Q = commutator Q := perfectResidual_eq_commutator hcp
    set eR : perfectResidual C ≃* projSU 3 3 1 :=
      ((perfectResidualEquiv e).trans (MulEquiv.subgroupCongr hres)).trans eU with heR
    refine ⟨Or.inr (Or.inl ⟨eR⟩), ?_⟩
    rw [Nat.card_congr eR.toEquiv, ← Nat.card_congr eU.toEquiv]
    have h6048 : Nat.card (commutator Q) = 6048 := by
      have h1 := (CFSG.Quasithin.FFC.commutator_data_g2 hK2
        (Subgroup.topEquiv.trans
          (Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hK2).some))
      obtain ⟨E⟩ := Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hK2
      obtain ⟨f1⟩ := CFSG.Quasithin.nonempty_commutator_equiv
        (Subgroup.topEquiv.trans E : ↥(⊤ : Subgroup Q) ≃* ↥(CFSG.Open.quasithinG2 K))
      rw [← Nat.card_congr (MulEquiv.subgroupCongr (commutator_def Q)).symm.toEquiv,
        Nat.card_congr f1.toEquiv]
      exact CFSG.Quasithin.S1549D.card_commutator_quasithinG2_two hK2
    rw [h6048]
    norm_num
  · have hq : 4 ≤ 2 ^ m := (Nat.pow_le_pow_right (by norm_num) hm2 : 2 ^ 2 ≤ 2 ^ m)
    have hK3 : 3 ≤ Nat.card K := by omega
    have hperf : Group.IsPerfect Q :=
      CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K hK3
    have hperfC : Group.IsPerfect C :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    set eR : perfectResidual C ≃* Q := (perfectResidualEquivSelf hperfC).trans e with heR
    have eA : Q ≃* AdjointQuotient .G2 K :=
      ((QuotientGroup.quotientMulEquivOfEq CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot).symm
    refine ⟨Or.inl ⟨m, ⟨Nat.prime_two, hm, rfl, by omega⟩, K, inferInstance, inferInstance, hK,
      ⟨eR.trans eA⟩⟩, ?_⟩
    rw [Nat.card_congr eR.toEquiv, (CFSG.LieType.Chevalley.exact_G2_finite_order K hK).2.1]
    refine Dvd.dvd.mul_left ?_ _
    have h4 : (2 ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h4]
    exact Item87Proof.three_dvd_four_pow_sub_one m

end Types

end Item89Res2


theorem kF89JCentType_of (hR : KF89JCentTypeRee) : KF89JCentType := by
  intro G _ _ X a m hm htype hU ha3 hk hg
  rcases htype with hRee | hD | ⟨q, hq2, hqe, hGq⟩ | hSU | hSU' | hSp
  · exact hR G X a m hm hRee ha3 hk
  · exact Item89Res2.type_of_isoGTwoEven hm (hg m (Or.inl hD))
  · exact Item89Res2.type_of_isoGTwoEven hm
      (hg m (Or.inr (Item8KFactsProof.isoGTwoEven_of_isoGTwo hq2 hqe hGq)))
  · exact absurd (Or.inl hSU) (hU (3 * m))
  · exact absurd (Or.inr hSU') (hU (3 * m))
  · have hout : Sec4.InducesOuterTheta a X := by
      rcases hk with h | h
      · exact KFacts.InducesStdKind.inducesOuterTheta X h (by decide)
      · exact KFacts.InducesStdKind.inducesOuterTheta X h (by decide)
    obtain ⟨-, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp (by omega) ha3 hout hSp
    exact Item89Res2.type_of_projSp hm ι

end CFSG.RankThree.PartTwo.Sec8
