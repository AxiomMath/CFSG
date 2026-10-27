module

public import CFSG.Quasithin.Recognition.St84.Sec6Abelian
public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot
public import CFSG.GroupTheory.PResidualLocalFinite
public import CFSG.Quasithin.Recognition.St84.PushUp
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPRA5
public import CFSG.Quasithin.EmptyFaithful.SzF53MUni
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushNatPerm
public import CFSG.Quasithin.Background.TwoReduced
public import CFSG.GroupTheory.AlternatingFive.SylowTwo
public import CFSG.Quasithin.Background.HA5Weyl
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Quasithin.Background.A1cBridge
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Syl
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422Quot
public import CFSG.Quasithin.SteinbergCDIndexThreeTripleCores
public import Mathlib.Tactic.Group
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear
public import CFSG.Quasithin.Recognition.St84.Sec6BaumannS3
public import CFSG.Timmesfeld.LocalTwoSubgroups.CoprimeActionBounds
public import CFSG.Quasithin.Background.RonanF713Sylow
public import CFSG.Quasithin.Vol2.Ch11SecD557B

import CFSG.Quasithin.Recognition.St84.Gen.NatQuotL2
public import CFSG.CGT.PushingUpLit.BHS.OffenderInternal
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.GroupTheory.AlternatingFiveFix
public import CFSG.GroupTheory.SylowInfNormal
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannDelOrigData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelH0
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceCommon
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate6
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.C1GNA7
public import CFSG.Quasithin.Background.C1PackBasic
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModPack28Proof
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Irr
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Steps
public import CFSG.Quasithin.EmptyFaithful.SzF53BasE
public import CFSG.Quasithin.EmptyFaithful.SzF53MSecB
public import CFSG.Quasithin.H13.A7SharedCubicSylow
public import CFSG.Quasithin.H13.GoldschmidtC137BaumMain
public import CFSG.Quasithin.H13.GoldschmidtC137Data
public import CFSG.Quasithin.H13.GoldschmidtC137U33Hyp
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Over
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Self
public import CFSG.Quasithin.H13.LinearOrders
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TArcEven
public import CFSG.Quasithin.Recognition.St84.Sec6ZTools
public import CFSG.Quasithin.Recognition.St84.Sec7S3Group
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch11SecD552
public import CFSG.Quasithin.Vol2.Ch11SecD555
public import CFSG.Quasithin.Vol2.Ch11SecD556
public import CFSG.Quasithin.Vol2.Ch11SecD556I
public import CFSG.Quasithin.Vol2.Ch11SecD557A
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec15.Item153PushProofTools
public import CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86
open CFSG.QuasithinUnique.Setup.Campbell

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

@[expose] def ZM : Subgroup G := centerOf (X.Lst X.QT 0)

@[expose] def Etau (j : ℤ) : Subgroup G := conjSub (X.τ ^ j) (X.E X.QT 0)

@[expose] def Ztau (j : ℤ) : Subgroup G := conjSub (X.τ ^ j) X.ZM

@[simp] theorem Etau_zero : X.Etau 0 = X.E X.QT 0 := by
  simp [Etau, conjSub_one]

@[simp] theorem Ztau_zero : X.Ztau 0 = X.ZM := by
  simp [Ztau, conjSub_one]

private theorem conjSub_tau_zpow_QT (j : ℤ) : conjSub (X.τ ^ j) X.QT = X.QT :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (zpow_mem X.tau_mem_normalizer_QT j)

theorem conjSub_tau_QT : conjSub X.τ X.QT = X.QT :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp X.tau_mem_normalizer_QT

@[simp] theorem Etau_eq (j : ℤ) : X.Etau j = X.E X.QT (2 * j) := by
  have hQ := X.conjSub_tau_zpow_QT j
  change conjSub (X.τ ^ j) (X.Q 0 ⊓ Subgroup.normalizer (X.QT : Set G)) =
    X.Q (2 * j) ⊓ Subgroup.normalizer (X.QT : Set G)
  rw [conjSub_inf, ← X.Q_add j 0, ← conjSub_normalizer, hQ]
  simp

@[simp] theorem Ztau_eq (j : ℤ) : X.Ztau j = centerOf (X.Lst X.QT (2 * j)) := by
  have hQ := X.conjSub_tau_zpow_QT j
  have hL : conjSub (X.τ ^ j) (X.Lst X.QT 0) = X.Lst X.QT (2 * j) := by
    change conjSub (X.τ ^ j)
      (oTwoPrime (Subgroup.normalizer (X.QT : Set G) ⊓ X.Gi 0)) =
      oTwoPrime (Subgroup.normalizer (X.QT : Set G) ⊓ X.Gi (2 * j))
    rw [conjSub_oTwoPrime]
    congr 1
    rw [conjSub_inf, ← X.Gi_add j 0, ← conjSub_normalizer, hQ]
    simp
  unfold Ztau ZM
  unfold centerOf
  rw [conjSub_inf, ← conjSub_centralizer, hL]

theorem conjSub_tau_Etau (j : ℤ) : conjSub X.τ (X.Etau j) = X.Etau (j + 1) := by
  show conjSub X.τ (conjSub (X.τ ^ j) (X.E X.QT 0)) =
    conjSub (X.τ ^ (j + 1)) (X.E X.QT 0)
  rw [← conjSub_mul]
  congr 1
  rw [← zpow_one_add, show (1 : ℤ) + j = j + 1 by ring]

theorem conjSub_inv_tau_Etau (j : ℤ) :
    conjSub X.τ⁻¹ (X.Etau j) = X.Etau (j - 1) := by
  have h := conjSub_tau_Etau (X := X) (j - 1)
  rw [show j - 1 + 1 = j by ring] at h
  rw [← h, conjSub_conjSub_inv]

private theorem conjSub_tau_Ztau (j : ℤ) : conjSub X.τ (X.Ztau j) = X.Ztau (j + 1) := by
  show conjSub X.τ (conjSub (X.τ ^ j) X.ZM) = conjSub (X.τ ^ (j + 1)) X.ZM
  rw [← conjSub_mul]
  congr 1
  rw [← zpow_one_add, show (1 : ℤ) + j = j + 1 by ring]

theorem E_two_eq : X.E X.QT 2 = conjSub X.τ (X.E X.QT 0) := by
  have h := X.Etau_eq 1
  rw [show (2 : ℤ) * 1 = 2 by norm_num] at h
  simpa [Etau, zpow_one] using h.symm

theorem QT_le_skP : X.QT ≤ X.skP X.QT := by
  refine le_inf (X.QT_le_Q 1) (le_inf Subgroup.le_normalizer ?_)
  simpa using X.QT_le_stabilizer_smul_vert 0 (g := 1) (by simp)

theorem QT_le_E : X.QT ≤ X.E X.QT 0 := by
  exact le_inf (X.QT_le_Q 0) Subgroup.le_normalizer

private theorem E_le_Gi_zero : X.E X.QT 0 ≤ X.Gi 0 := inf_le_left.trans (X.Q_le_Gi 0)

theorem E_le_normalizer_ZM : X.E X.QT 0 ≤ Subgroup.normalizer (X.ZM : Set G) :=
  (le_inf (inf_le_right : X.E X.QT 0 ≤ CFSG.Quasithin.St84.M X.QT) X.E_le_Gi_zero).trans
    ((le_normalizer_oTwoPrime (X.normGi X.QT 0)).trans
      (CFSG.Quasithin.normalizer_le_normalizer_centerOf (X.Lst X.QT 0)))

private theorem finite_QT : Finite ↥X.QT :=
  finite_of_le_stabilizer X.hyp (H := X.QT) (X.QT_le_GT.trans (X.GT_le_Gi 0))

private theorem conjSub_Lst_of {t : G} (ht : t ∈ Subgroup.normalizer (X.QT : Set G))
    {i j : ℤ} (h : t • X.vert i = X.vert j) :
    conjSub t (X.Lst X.QT i) = X.Lst X.QT j := by
  change conjSub t (oTwoPrime (X.normGi X.QT i)) = oTwoPrime (X.normGi X.QT j)
  rw [conjSub_oTwoPrime, X.conjSub_normGi_of_mem_normalizer ht h]

private theorem isPGroup_skP (U : Subgroup G) : IsPGroup 2 (X.skP U) :=
  (pCoreOf_isPGroup' (X.Gi 1)).to_le inf_le_left

private theorem Ztau_le_Etau (hZ : X.ZM ≤ X.E X.QT 0) (j : ℤ) :
    X.Ztau j ≤ X.Etau j := conjSub_mono _ hZ

private theorem K_le_normalizer_E_QT : X.K ≤ Subgroup.normalizer (X.E X.QT 0 : Set G) :=
  fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0) (X.K_le_Gi 0 hk),
        Subgroup.le_normalizer (X.K_le_normalizer_QT hk)⟩

private theorem isSylowTwoOf_QT_GT : IsSylowTwoOf X.QT X.GT := by
  have hdisj : X.K ⊓ X.QT = ⊥ :=
    inf_eq_bot_of_odd_of_isPGroup X.odd_card_K (pCoreOf_isPGroup' X.GT)
  have hcard : Nat.card ↥X.GT = Nat.card ↥X.K * Nat.card ↥X.QT := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (A := X.QT) (B := X.K) X.K_le_normalizer_QT
      (by rw [disjoint_iff, inf_comm]; exact hdisj)
    calc Nat.card ↥X.GT = Nat.card ↥(X.K ⊔ X.QT) := by rw [X.GT_eq_K_sup_QT.1]
      _ = Nat.card ↥(X.QT ⊔ X.K) := by rw [sup_comm]
      _ = Nat.card ↥X.QT * Nat.card ↥X.K := h
      _ = Nat.card ↥X.K * Nat.card ↥X.QT := mul_comm _ _
  haveI := X.finite_QT
  have hidx : X.QT.relIndex X.GT = Nat.card ↥X.K := by
    have hmul := Subgroup.relIndex_mul_card (H := X.QT) (K := X.GT)
    rw [inf_eq_left.mpr X.QT_le_GT, hcard] at hmul
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
  refine F7.isSylowTwoOf_of_relIndex X.QT_le_GT (pCoreOf_isPGroup' X.GT) ?_
  rw [hidx]
  simpa [even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr X.odd_card_K)

private theorem relIndex_arcStab_inf_Gi_neg_one {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    (X.arcStab 0 (2 * (m : ℤ)) ⊓ X.Gi (-1)).relIndex (X.arcStab 0 (2 * (m : ℤ))) =
      2 ^ X.n 0 := by
  have hAdj0 : Γ.Adj (X.vert 0) (X.vert (-1)) := by
    simpa using (X.adj (-1)).symm
  have hm0 : (0 : ℤ) ≤ 2 * (m : ℤ) := hreg.1.le
  have hm1 : (1 : ℤ) ≤ 2 * (m : ℤ) := by have := hreg.1; omega
  set H : Subgroup G := X.arcStab 0 (2 * (m : ℤ)) with hHdef
  have hH0 : H ≤ X.Gi 0 :=
    X.arcStab_le_Gi_of_between (show (0 : ℤ) ≤ 0 by norm_num) hm0
  have hH1 : H ≤ X.Gi 1 := X.arcStab_le_Gi_of_between (by norm_num) hm1
  haveI hHfin : Finite ↥H :=
    finite_of_le_stabilizer X.hyp (H := H)
      (X.arcStab_le_Gi_of_between (show (0 : ℤ) ≤ 0 by norm_num) hm0)
  have hHtr : MulAction.orbit ↥H (X.vert (-1)) =
      Γ.neighborSet (X.vert 0) \ {X.vert 1} := by
    ext z
    constructor
    · rintro ⟨h, rfl⟩
      have hh : (h : G) ∈ H := h.2
      refine ⟨?_, ?_⟩
      · rw [SimpleGraph.mem_neighborSet]
        have hfix0 : (h : G) • X.vert 0 = X.vert 0 :=
          MulAction.mem_stabilizer_iff.mp (hH0 hh)
        have hadj : Γ.Adj ((h : G) • X.vert 0) ((h : G) • X.vert (-1)) :=
          (X.hyp.adj_smul (h : G) _ _).2 hAdj0
        rwa [hfix0] at hadj
      · intro hz
        have hfix1 : (h : G) • X.vert 1 = X.vert 1 :=
          MulAction.mem_stabilizer_iff.mp (hH1 hh)
        have hEq : (h : G) • X.vert (-1) = (h : G) • X.vert 1 := hz.trans hfix1.symm
        have h' : X.vert (-1) = X.vert 1 := MulAction.injective (h : G) hEq
        have : (-1 : ℤ) = 1 := X.vert_injective h'
        norm_num at this
    · rintro ⟨hadj, hne⟩
      have hne' : X.vert (-1) ≠ X.vert 1 := by
        intro h
        have : (-1 : ℤ) = 1 := X.vert_injective h
        norm_num at this
      obtain ⟨h, hhH, hh⟩ := hreg.2.1 (X.vert (-1)) z hAdj0 hne' hadj hne
      exact ⟨⟨h, hhH⟩, hh⟩
  rw [Subgroup.inf_relIndex_left,
    FanTree.relIndex_stabilizer_eq_ncard_orbit H (X.vert (-1)), hHtr]
  simpa using ncard_neighborSet_diff X.hyp (X.adj 0)

private theorem le_Q_zero_of_isPGroup (hSK : X.IsSK X.QT)
    (hPle : X.skP X.QT ≤ X.Q 0) {S : Subgroup G}
    (hS : IsPGroup 2 S) (hSM : S ≤ X.normGi X.QT 0) : S ≤ X.Q 0 := by
  have hSKP : IsSylowTwoOf (X.skP X.QT) (X.normGi X.QT 0) :=
    X.isSylowTwoOf_skP_zero hSK
  haveI hMfin : Finite ↥(X.normGi X.QT 0) :=
    finite_of_le_stabilizer X.hyp (H := X.normGi X.QT 0) (X.normGi_le_Gi X.QT 0)
  have hSKP' : IsSylowTwoOf ((X.skP X.QT).subgroupOf (X.normGi X.QT 0)) ⊤ := by
    refine F7.isSylowTwoOf_of_relIndex le_top ?_ ?_
    · exact hSKP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSKP.1).symm
    · simpa using hSKP.2.2
  have hSM' : IsPGroup 2 (S.subgroupOf (X.normGi X.QT 0)) :=
    hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSM).symm
  obtain ⟨x, -, hconj⟩ := F7.isSylowTwoOf_exists_conj_le
    (G := ↥(X.normGi X.QT 0)) hSKP' le_top hSM'
  have hSle : S ≤ conjSub (x : G) (X.skP X.QT) := by
    intro y hy
    have hyM : y ∈ X.normGi X.QT 0 := hSM hy
    have hySub : (⟨y, hyM⟩ : ↥(X.normGi X.QT 0)) ∈
        S.subgroupOf (X.normGi X.QT 0) := Subgroup.mem_subgroupOf.mpr hy
    have hmem := hconj hySub
    rw [mem_conjSub] at hmem ⊢
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have hxG0 : (x : G) ∈ X.Gi 0 := X.normGi_le_Gi X.QT 0 x.2
  have hQ0norm : X.Gi 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)
  have hconjQ0 : conjSub (x : G) (X.Q 0) = X.Q 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQ0norm hxG0)
  have hSQ0 : S ≤ X.Q 0 :=
    hSle.trans ((conjSub_mono (x : G) hPle).trans (le_of_eq hconjQ0))
  exact hSQ0

theorem not_skP_QT_le_Q_zero (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ¬ X.skP X.QT ≤ X.Q 0 := by
  intro hPle
  obtain ⟨m, -, hreg⟩ := X.exists_isMaxReg hs hodd hX
  have hAdj0 : Γ.Adj (X.vert 0) (X.vert (-1)) := by
    simpa using (X.adj (-1)).symm
  have hm0 : (0 : ℤ) ≤ 2 * (m : ℤ) := hreg.1.le
  have hm1 : (1 : ℤ) ≤ 2 * (m : ℤ) := by have := hreg.1; omega
  set H : Subgroup G := X.arcStab 0 (2 * (m : ℤ)) with hHdef
  have hH0 : H ≤ X.Gi 0 :=
    X.arcStab_le_Gi_of_between (show (0 : ℤ) ≤ 0 by norm_num) hm0
  haveI hHfin : Finite ↥H :=
    finite_of_le_stabilizer X.hyp (H := H)
      (X.arcStab_le_Gi_of_between (show (0 : ℤ) ≤ 0 by norm_num) hm0)
  have hHle : H ≤ X.normGi X.QT 0 :=
    le_inf (X.arcStab_le_normalizer_QT_of_isMaxReg hreg) hH0
  obtain ⟨S, hSyl, -⟩ := exists_isSylowTwoOf_ge_of_finite (J := H) (X := ⊥)
    (IsPGroup.of_bot) bot_le
  have hSH : S ≤ H := hSyl.1
  have hSp : IsPGroup 2 S := hSyl.2.1
  set A : Subgroup G := H ⊓ X.Gi (-1) with hAdef
  have hArel : A.relIndex H = 2 ^ X.n 0 := by
    rw [hAdef]
    exact X.relIndex_arcStab_inf_Gi_neg_one hreg
  have hodd_o : Odd (S.relIndex H) := by
    refine Nat.not_even_iff_odd.mp ?_
    rw [even_iff_two_dvd]
    exact hSyl.2.2
  have hSA : ¬ S ≤ X.Gi (-1) := by
    intro hS
    have hdvd : 2 ^ X.n 0 ∣ S.relIndex H := by
      rw [← Subgroup.relIndex_mul_relIndex S A H (le_inf hSH hS) inf_le_left, hArel]
      exact dvd_mul_left _ _
    have hn0pos : 1 ≤ X.n 0 := (X.hyp.valency (X.vert 0)).1
    exact (Nat.not_even_iff_odd.mpr hodd_o)
      (even_iff_two_dvd.mpr ((dvd_pow_self 2 (by omega)).trans hdvd))
  obtain ⟨g, hgS, hgm⟩ := SetLike.not_le_iff_exists.mp hSA
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  have hSM : S ≤ X.normGi X.QT 0 := hSH.trans hHle
  have hSQ0 : S ≤ X.Q 0 := X.le_Q_zero_of_isPGroup hSK hPle hSp hSM
  exact hgm (MulAction.mem_stabilizer_iff.mpr
    (X.Q_fixes_neighbors_vert 0 (X.vert (-1)) hAdj0 g (hSQ0 hgS)))

theorem normGi_QT_eq_of_le {U : Subgroup G} (hU : X.IsSKMax U) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hle : X.normGi X.QT 0 ≤ X.normGi U 0) :
    X.normGi U 0 = X.normGi X.QT 0 := by
  have hSKQ : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  have hQt_ne : X.QT ≠ ⊥ := X.QT_ne_bot hGT
  have hQtM : X.QT ≤ X.normGi X.QT 0 := X.QT_le_skP.trans inf_le_right
  have hQtU : X.QT ≤ X.normGi U 0 := hQtM.trans hle
  have hQtskP : X.QT ≤ X.skP U := le_inf (X.QT_le_Q 1) hQtU
  have hPU : X.skP U ≠ ⊥ := fun h =>
    hQt_ne (le_bot_iff.mp (h ▸ hQtskP))
  have hEab : IsElemAbelian 2 (X.E U 0) :=
    X.isElemAbelian_E hU (Or.inl hPU)
  have hQtE : X.QT ≤ X.E U 0 :=
    le_inf (X.QT_le_Q 0) (hQtU.trans (X.normGi_le_normalizer U 0))
  haveI : IsMulCommutative ↥(X.E U 0) := hEab.1
  have hEM : X.E U 0 ≤ X.normGi X.QT 0 :=
    le_inf ((Subgroup.le_centralizer_iff_isMulCommutative.mpr hEab.1).trans
      ((Subgroup.centralizer_le hQtE).trans (Subgroup.centralizer_le_normalizer _)))
      (inf_le_left.trans (X.Q_le_Gi 0))
  have hE_normGi : X.E U 0 ≤ X.normGi U 0 :=
    le_inf inf_le_right (inf_le_left.trans (X.Q_le_Gi 0))
  have hinf : X.Lst U 0 ⊓ X.Q 0 = X.E U 0 := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxL, hxQ⟩ := Subgroup.mem_inf.mp hx
      rw [← X.Lst_inf_kernel (U := U)]
      exact Subgroup.mem_inf.mpr ⟨hxL,
        ((X.kernelOnNeighbors_inf_edgeSylow 0).ge.trans inf_le_left) hxQ⟩
    · intro x hx
      have hxQ : x ∈ X.Q 0 := (Subgroup.mem_inf.mp (show x ∈ X.Q 0 ⊓ M U from hx)).1
      refine Subgroup.mem_inf.mpr ⟨?_, hxQ⟩
      have hEp : IsPGroup 2 (X.E U 0) := by
        intro y
        exact ⟨1, Subtype.ext (by simpa using hEab.2 (y : G) y.2)⟩
      exact le_oTwoPrime_of_isPGroup hEp hE_normGi hx
  have hLst_le : X.Lst U 0 ≤ X.Lst X.QT 0 ⊔ X.E U 0 := by
    intro x hx
    have hxL : x ∈ X.L 0 :=
      (oTwoPrime_mono (X.normGi_le_Gi U 0)) hx
    have hLQ : X.L 0 = X.Lst X.QT 0 ⊔ X.Q 0 :=
      X.L_eq_Lst_sup_Q hSKQ (Or.inl (X.not_skP_QT_le_Q_zero hGT hs hodd h5 hX))
    have hxL' : x ∈ X.Lst X.QT 0 ⊔ X.Q 0 := hLQ ▸ hxL
    have hnorm : X.Lst X.QT 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) := by
      refine (oTwoPrime_le (X.normGi X.QT 0)).trans ?_
      exact (X.normGi_le_Gi X.QT 0).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
    have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right
      (X.Lst X.QT 0) (X.Q 0) hnorm
    have hxprod : x ∈ (X.Lst X.QT 0 : Set G) * (X.Q 0 : Set G) := by
      rw [← hcoe]
      exact hxL'
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hxprod
    have haU : a ∈ X.Lst U 0 := (oTwoPrime_mono hle) ha
    have hbU : b ∈ X.Lst U 0 := by
      have h1 : a⁻¹ * x ∈ X.Lst U 0 := (X.Lst U 0).mul_mem ((X.Lst U 0).inv_mem haU) hx
      have h2 : a⁻¹ * (a * b) ∈ X.Lst U 0 := by rwa [← hab] at h1
      simpa [mul_assoc] using h2
    have hbE : b ∈ X.E U 0 := by
      rw [← hinf]
      exact Subgroup.mem_inf.mpr ⟨hbU, hb⟩
    rw [← hab]
    exact Subgroup.mul_mem_sup ha hbE
  have hM_le : X.normGi U 0 ≤ X.normGi X.QT 0 := by
    rw [X.normGi_eq_Lst_sup_K hU.1
      (X.not_skP_le_Q_zero_or_of_isSKMax hU (Or.inl hPU))]
    refine sup_le ?_ (le_inf X.K_le_normalizer_QT (X.K_le_Gi 0))
    exact hLst_le.trans (sup_le (oTwoPrime_le _) hEM)
  exact le_antisymm hM_le hle

theorem isSKMax_QT (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s)
    (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.IsSKMax X.QT := by
  refine ⟨X.isSK_QT hGT hs hodd h5 hX, ?_⟩
  intro U' hU' hle'
  obtain ⟨U, hUmax, hleU⟩ := X.exists_isSKMax_above hU'
  have hle : X.normGi X.QT 0 ≤ X.normGi U 0 := hle'.trans hleU
  have hEq := X.normGi_QT_eq_of_le hUmax hGT hs hodd h5 hX hle
  exact hleU.trans hEq.le

private theorem pair_QT_odd (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (j : ℤ) {g : G}
    (hg : g ∈ X.normGi X.QT (2 * j + 1)) :
    g • X.vert (2 * j) ∈ ({X.vert (2 * j), X.vert (2 * j + 2)} : Set V) := by
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  set h : G := X.τ ^ (-j) * g * X.τ ^ j with hh_def
  have hτN : ∀ k : ℤ, X.τ ^ k ∈ Subgroup.normalizer (X.QT : Set G) :=
    fun k => zpow_mem X.tau_mem_normalizer_QT k
  have hh : h ∈ X.normGi X.QT 1 := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hτN (-j)) hg.1) (hτN j)
    · rw [MulAction.mem_stabilizer_iff]
      calc h • X.vert 1 = X.τ ^ (-j) • (g • (X.τ ^ j • X.vert 1)) := by
            simp only [hh_def, mul_smul]
        _ = X.τ ^ (-j) • (g • X.vert (2 * j + 1)) := by
            rw [X.zpow_smul_vert j 1]
            congr 1
            ring
        _ = X.τ ^ (-j) • X.vert (2 * j + 1) := by
            rw [MulAction.mem_stabilizer_iff.mp hg.2]
        _ = X.vert 1 := by
            rw [X.zpow_smul_vert (-j) (2 * j + 1)]
            congr 1
            ring
  have hpair := hSK.pair h hh
  have hh2 : h • X.vert 0 = X.τ ^ (-j) • (g • X.vert (2 * j)) := by
    simp only [hh_def, mul_smul]
    congr 1
    rw [X.zpow_smul_vert j 0]
    congr 1
    ring
  rw [hh2] at hpair
  have := Set.mem_image_of_mem (fun v : V => X.τ ^ j • v) hpair
  simpa [Set.image_insert_eq, Set.image_singleton, X.zpow_smul_vert j 0,
    X.zpow_smul_vert j 2, show 0 + 2 * j = 2 * j by ring,
    show 1 + 2 * j = 2 * j + 1 by ring, show 2 + 2 * j = 2 * j + 2 by ring]
    using this

theorem card_skP {m : ℕ} (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    Nat.card (X.skP X.QT) = 2 ^ (X.n 0 * m) * Nat.card X.QT := by
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  set M : Subgroup G := X.normGi X.QT 0 with hMdef
  set P : Subgroup G := X.skP X.QT with hPdef
  have hM0 : M ≤ X.Gi 0 := X.normGi_le_Gi X.QT 0
  let A : ℤ → Subgroup G := fun k => M ⊓ X.arcStab 0 k
  have hA1 : A 1 = M ⊓ X.Gi 1 := by
    change M ⊓ X.arcStab 0 1 = M ⊓ X.Gi 1
    rw [X.arcStab_eq_inf (by norm_num : (0 : ℤ) ≤ 1), ← inf_assoc,
      inf_eq_left.mpr hM0]
  have hA2 : A 2 = M ⊓ X.Gi 2 := by
    change M ⊓ X.arcStab 0 2 = M ⊓ X.Gi 2
    rw [X.arcStab_eq_inf (by norm_num : (0 : ℤ) ≤ 2), ← inf_assoc,
      inf_eq_left.mpr hM0]
  have hA12 : A 1 = A 2 := by
    refine le_antisymm ?_ ?_
    · intro g hg
      rw [hA1] at hg
      obtain ⟨hgM, hgG1⟩ := Subgroup.mem_inf.mp hg
      have hg' : g ∈ X.normGi X.QT 0 ⊓ X.Gi 1 := Subgroup.mem_inf.mpr ⟨hgM, hgG1⟩
      rw [hSK.inf₀₁] at hg'
      have hgG2 : g ∈ X.Gi 2 := (Subgroup.mem_inf.mp hg').2
      rw [hA2]
      exact Subgroup.mem_inf.mpr ⟨hgM, hgG2⟩
    · intro g hg
      rw [hA2] at hg
      obtain ⟨hgM, hgG2⟩ := Subgroup.mem_inf.mp hg
      have hgG0 : g ∈ X.Gi 0 := hM0 hgM
      have hfix1 : g • X.vert 1 = X.vert 1 := by
        have h0 : g • (X.line.arc 0 2).vert 0 = (X.line.arc 0 2).vert 0 := by
          simpa [Line.arc] using hgG0
        have h2 : g • (X.line.arc 0 2).vert 2 = (X.line.arc 0 2).vert 2 := by
          simpa [Line.arc] using hgG2
        have h := Arc.fixes_of_ends X.hyp.isTree X.hyp.adj_smul (X.line.arc 0 2) h0 h2 1
          (by norm_num)
        simpa [Line.arc] using h
      rw [hA1]
      exact Subgroup.mem_inf.mpr ⟨hgM, MulAction.mem_stabilizer_iff.mpr hfix1⟩
  have hMtr : MulAction.orbit ↥M (X.vert 1) = Γ.neighborSet (X.vert 0) := by
    ext z
    constructor
    · rintro ⟨mm, rfl⟩
      rw [SimpleGraph.mem_neighborSet]
      have hfix : (mm : G) • X.vert 0 = X.vert 0 :=
        MulAction.mem_stabilizer_iff.mp (hM0 mm.2)
      have h := (X.hyp.adj_smul (mm : G) (X.vert 0) (X.vert 1)).2 (X.adj 0)
      rwa [hfix] at h
    · intro hz
      obtain ⟨g, hgM, hg⟩ := hSK.trans0 (X.vert 1) z (X.adj 0) hz
      exact ⟨⟨g, hgM⟩, hg⟩
  have hA1rel : (A 1).relIndex M = 2 ^ X.n 0 + 1 := by
    rw [hA1, Subgroup.inf_relIndex_left,
      FanTree.relIndex_stabilizer_eq_ncard_orbit M (X.vert 1), hMtr,
      ← Nat.card_coe_set_eq, (X.hyp.valency (X.vert 0)).2]
  have hApair : ∀ j : ℤ, 1 ≤ j → A (2 * j + 1) = A (2 * j + 2) := by
    intro j hj
    refine le_antisymm ?_ ?_
    · intro g hg
      obtain ⟨hgM, hgA⟩ := Subgroup.mem_inf.mp hg
      have hg1 : g ∈ X.Gi (2 * j + 1) :=
        X.arcStab_le_Gi_of_between (by omega) le_rfl hgA
      have hg0 : g ∈ X.Gi (2 * j) :=
        X.arcStab_le_Gi_of_between (by omega) (by omega) hgA
      have hgN : g ∈ X.normGi X.QT (2 * j + 1) :=
        Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hgM).1, hg1⟩
      have hfix0 : g • X.vert (2 * j) = X.vert (2 * j) :=
        MulAction.mem_stabilizer_iff.mp hg0
      obtain ⟨g0, hg0, hg0a, hg0b⟩ := hSK.exists_swap₁
      set x : G := X.τ ^ j * g0 * X.τ ^ (-j) with hxdef
      have hxmem : x ∈ X.normGi X.QT (2 * j + 1) := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact Subgroup.mul_mem _
            (Subgroup.mul_mem _ (zpow_mem X.tau_mem_normalizer_QT j) hg0.1)
            (zpow_mem X.tau_mem_normalizer_QT (-j))
        · rw [MulAction.mem_stabilizer_iff]
          calc x • X.vert (2 * j + 1)
              = X.τ ^ j • (g0 • (X.τ ^ (-j) • X.vert (2 * j + 1))) := by
                simp only [hxdef, mul_smul]
            _ = X.τ ^ j • (g0 • X.vert 1) := by
                rw [X.zpow_smul_vert (-j) (2 * j + 1)]
                congr 1
                ring
            _ = X.τ ^ j • X.vert 1 := by rw [MulAction.mem_stabilizer_iff.mp hg0.2]
            _ = X.vert (2 * j + 1) := by
                rw [X.zpow_smul_vert j 1]
                congr 1
                ring
      have hxact : x • X.vert (2 * j) = X.vert (2 * j + 2) := by
        calc x • X.vert (2 * j)
            = X.τ ^ j • (g0 • (X.τ ^ (-j) • X.vert (2 * j))) := by
              simp only [hxdef, mul_smul]
          _ = X.τ ^ j • (g0 • X.vert 0) := by
              rw [X.zpow_smul_vert (-j) (2 * j)]
              congr 1
              ring
          _ = X.τ ^ j • X.vert 2 := by rw [hg0a]
          _ = X.vert (2 * j + 2) := by
              rw [X.zpow_smul_vert j 2]
              congr 1
              ring
      have hgx : g * x ∈ X.normGi X.QT (2 * j + 1) :=
        (X.normGi X.QT (2 * j + 1)).mul_mem hgN hxmem
      have hpair := X.pair_QT_odd hGT hs hodd h5 hX j hgx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpair
      have hval : (g * x) • X.vert (2 * j) = g • X.vert (2 * j + 2) := by
        rw [mul_smul, hxact]
      rw [hval] at hpair
      have hfix2 : g • X.vert (2 * j + 2) = X.vert (2 * j + 2) := by
        rcases hpair with h | h
        · exfalso
          have hginv : g⁻¹ • X.vert (2 * j) = X.vert (2 * j) := by
            calc g⁻¹ • X.vert (2 * j) = g⁻¹ • (g • X.vert (2 * j)) := by rw [hfix0]
              _ = X.vert (2 * j) := by simp
          have hEq : X.vert (2 * j + 2) = X.vert (2 * j) := by
            have hh : g⁻¹ • (g • X.vert (2 * j + 2)) = g⁻¹ • X.vert (2 * j) := by rw [h]
            rw [hginv] at hh
            simpa using hh
          have := X.vert_injective hEq
          omega
        · exact h
      have hgG0 : g ∈ X.Gi 0 := hM0 hgM
      refine Subgroup.mem_inf.mpr ⟨hgM, ?_⟩
      rw [X.arcStab_eq_inf (by omega : (0 : ℤ) ≤ 2 * j + 2)]
      exact Subgroup.mem_inf.mpr ⟨hgG0, hfix2⟩
    · intro g hg
      obtain ⟨hgM, hgA⟩ := Subgroup.mem_inf.mp hg
      refine Subgroup.mem_inf.mpr ⟨hgM, ?_⟩
      exact X.arcStab_anti (le_refl (0 : ℤ)) (by omega) hgA
  have hAorb : ∀ j : ℤ, 1 ≤ j → j ≤ m → (A (2 * j + 1)).relIndex (A (2 * j)) = 2 ^ X.n 0 := by
    intro j hj hjm
    have hstab : A (2 * j) ⊓ X.Gi (2 * j + 1) = A (2 * j + 1) := by
      have e1 : X.arcStab 0 (2 * j) = X.Gi 0 ⊓ X.Gi (2 * j) :=
        X.arcStab_eq_inf (by omega : (0 : ℤ) ≤ 2 * j)
      have e2 : X.arcStab 0 (2 * j + 1) = X.Gi 0 ⊓ X.Gi (2 * j + 1) :=
        X.arcStab_eq_inf (by omega : (0 : ℤ) ≤ 2 * j + 1)
      have hkey : X.Gi 0 ⊓ X.Gi (2 * j + 1) ≤ X.Gi (2 * j) := by
        rintro g ⟨hg0, hg1⟩
        exact X.mem_Gi_of_between hg0 hg1 (by omega) (by omega)
      rw [show A (2 * j) = M ⊓ X.arcStab 0 (2 * j) from rfl,
        show A (2 * j + 1) = M ⊓ X.arcStab 0 (2 * j + 1) from rfl, e1, e2]
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨⟨hxM, hx0, hxj⟩, hxj1⟩
        exact ⟨hxM, hx0, hxj1⟩
      · rintro ⟨hxM, hx0, hxj1⟩
        exact ⟨⟨hxM, hx0, hkey ⟨hx0, hxj1⟩⟩, hxj1⟩
    have hrel : (A (2 * j + 1)).relIndex (A (2 * j)) =
        (MulAction.orbit ↥(A (2 * j)) (X.vert (2 * j + 1))).ncard := by
      rw [← hstab, Subgroup.inf_relIndex_left,
        FanTree.relIndex_stabilizer_eq_ncard_orbit (A (2 * j)) (X.vert (2 * j + 1))]
    have htrans : ∀ a b : V, Γ.Adj (X.vert (2 * j)) a → a ≠ X.vert (2 * j - 1) →
        Γ.Adj (X.vert (2 * j)) b → b ≠ X.vert (2 * j - 1) →
        ∃ g ∈ A (2 * j), g • a = b := by
      intro a b ha hb ha' hb'
      have hregj : X.RightTransAt (2 * j - 2 * (m : ℤ)) (2 * j) := by
        have h := X.rightTransAt_add ((j : ℤ) - (m : ℤ)) 0 (2 * (m : ℤ)) hreg.2.2.1
        rwa [show (0 : ℤ) + 2 * ((j : ℤ) - (m : ℤ)) = 2 * j - 2 * (m : ℤ) by ring,
          show 2 * (m : ℤ) + 2 * ((j : ℤ) - (m : ℤ)) = 2 * j by ring] at h
      have hHle : X.arcStab (2 * j - 2 * (m : ℤ)) (2 * j) ≤ A (2 * j) := by
        have hconj : X.arcStab (2 * j - 2 * (m : ℤ)) (2 * j) =
            conjSub (X.τ ^ ((j : ℤ) - (m : ℤ))) (X.arcStab 0 (2 * (m : ℤ))) := by
          have h := X.arcStab_add ((j : ℤ) - (m : ℤ)) 0 (2 * (m : ℤ))
          rwa [show (0 : ℤ) + 2 * ((j : ℤ) - (m : ℤ)) = 2 * j - 2 * (m : ℤ) by ring,
            show 2 * (m : ℤ) + 2 * ((j : ℤ) - (m : ℤ)) = 2 * j by ring] at h
        intro x hx
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
        · rw [hconj] at hx
          obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
          have hz : X.τ ^ ((j : ℤ) - (m : ℤ)) ∈ Subgroup.normalizer (X.QT : Set G) :=
            zpow_mem X.tau_mem_normalizer_QT _
          have hbase : X.arcStab 0 (2 * (m : ℤ)) ≤ Subgroup.normalizer (X.QT : Set G) :=
            X.arcStab_le_normalizer_QT_of_isMaxReg hreg
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hz (hbase hy))
            ((Subgroup.normalizer (X.QT : Set G)).inv_mem hz)
        · exact X.arcStab_le_Gi_of_between (by omega) (by omega) hx
        · exact X.arcStab_anti (by omega) le_rfl hx
      obtain ⟨g, hgH, hgab⟩ := hregj a b ha hb ha' hb'
      exact ⟨g, hHle hgH, hgab⟩
    have horb : MulAction.orbit ↥(A (2 * j)) (X.vert (2 * j + 1)) =
        Γ.neighborSet (X.vert (2 * j)) \ {X.vert (2 * j - 1)} := by
      ext z
      constructor
      · rintro ⟨g, rfl⟩
        have hgA : (g : G) ∈ A (2 * j) := g.2
        have hgGi : (g : G) ∈ X.Gi (2 * j) :=
          X.arcStab_le_Gi_of_between (by omega) le_rfl (Subgroup.mem_inf.mp hgA).2
        have hgGm : (g : G) ∈ X.Gi (2 * j - 1) :=
          X.arcStab_le_Gi_of_between (by omega) (by omega) (Subgroup.mem_inf.mp hgA).2
        refine ⟨?_, ?_⟩
        · rw [SimpleGraph.mem_neighborSet]
          have hfix : (g : G) • X.vert (2 * j) = X.vert (2 * j) :=
            MulAction.mem_stabilizer_iff.mp hgGi
          have h := (X.hyp.adj_smul (g : G) (X.vert (2 * j)) (X.vert (2 * j + 1))).2
            (by simpa using X.adj (2 * j))
          rwa [hfix] at h
        · intro hz
          have hfix : (g : G) • X.vert (2 * j - 1) = X.vert (2 * j - 1) :=
            MulAction.mem_stabilizer_iff.mp hgGm
          have hEq : X.vert (2 * j + 1) = X.vert (2 * j - 1) := by
            have h : (g : G) • X.vert (2 * j + 1) = (g : G) • X.vert (2 * j - 1) :=
              hz.trans hfix.symm
            exact MulAction.injective (g : G) h
          have := X.vert_injective hEq
          omega
      · rintro ⟨hz, hzne⟩
        have hadj : Γ.Adj (X.vert (2 * j)) (X.vert (2 * j + 1)) := by
          simpa using X.adj (2 * j)
        have hne : X.vert (2 * j + 1) ≠ X.vert (2 * j - 1) := by
          intro h
          have := X.vert_injective h
          omega
        obtain ⟨g, hg, hgab⟩ := htrans (X.vert (2 * j + 1)) z hadj hne hz hzne
        exact ⟨⟨g, hg⟩, hgab⟩
    rw [hrel, horb]
    have hn : X.n (2 * j) = X.n 0 := by
      simpa using X.n_add j 0
    rw [ncard_neighborSet_diff X.hyp (show Γ.Adj (X.vert (2 * j)) (X.vert (2 * j - 1)) from by
        simpa using (X.adj (2 * j - 1)).symm)]
    rw [show nOf Γ (X.vert (2 * j)) = X.n 0 from hn]
  let B : ℕ → Subgroup G := fun k => A (2 * ((k : ℤ) + 1))
  have hBmono : ∀ k : ℕ, B (k + 1) ≤ B k := by
    intro k
    refine le_inf inf_le_left ?_
    exact (inf_le_right : B (k + 1) ≤ X.arcStab 0 (2 * ((k : ℤ) + 2))).trans
      (X.arcStab_anti (le_refl (0 : ℤ)) (by omega))
  have hBanti : ∀ k : ℕ, B k ≤ B 0 := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hBmono k).trans ih
  have hBstep : ∀ k : ℕ, k < m → (B (k + 1)).relIndex (B k) = 2 ^ X.n 0 := by
    intro k hk
    have h1 : B (k + 1) = A (2 * ((k : ℤ) + 2)) := rfl
    have h3 : A (2 * ((k : ℤ) + 2)) = A (2 * ((k : ℤ) + 1) + 1) := by
      rw [show 2 * ((k : ℤ) + 2) = 2 * ((k : ℤ) + 1) + 2 by ring]
      exact (hApair ((k : ℤ) + 1) (by omega)).symm
    rw [h1, h3]
    exact hAorb ((k : ℤ) + 1) (by omega) (by omega)
  have hB0 : B 0 = A 2 := rfl
  have hBchain : ∀ k : ℕ, k ≤ m → (B k).relIndex (B 0) = (2 ^ X.n 0) ^ k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hkm : k < m := by omega
        have hstep := hBstep k hkm
        have hmul : (B (k + 1)).relIndex (B 0) =
            (B (k + 1)).relIndex (B k) * (B k).relIndex (B 0) :=
          (Subgroup.relIndex_mul_relIndex (B (k + 1)) (B k) (B 0) (hBmono k)
            (hBanti k)).symm
        rw [hmul, hstep, ih (by omega), pow_succ']
  have hB0rel : (B 0).relIndex M = 2 ^ X.n 0 + 1 := by
    rw [hB0, ← hA12]
    exact hA1rel
  have hGTleM : X.GT ≤ M :=
    le_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X.GT) (X.GT_le_Gi 0)
  have hB0M : B 0 ≤ M := inf_le_left
  have hBmrel : (B m).relIndex M = (2 ^ X.n 0) ^ m * (2 ^ X.n 0 + 1) := by
    have h := Subgroup.relIndex_mul_relIndex (B m) (B 0) M (hBanti m) hB0M
    rw [hBchain m le_rfl, hB0rel] at h
    exact h.symm
  have hBmGT : B m = X.GT := by
    refine le_antisymm ?_ ?_
    · have hle : B m ≤ X.arcStab 0 (2 * ((m : ℤ) + 1)) := inf_le_right
      have h2 : X.arcStab 0 (2 * ((m : ℤ) + 1)) ≤ X.arcStab 0 (2 * ((m : ℤ) + 1) - 1) :=
        X.arcStab_anti (le_refl (0 : ℤ)) (by omega)
      have heq : X.arcStab 0 (2 * ((m : ℤ) + 1) - 1) = X.GT := by
        rw [show 2 * ((m : ℤ) + 1) - 1 = 2 * (m : ℤ) + 1 by ring]
        exact hreg.2.2.2.1
      exact hle.trans (h2.trans (le_of_eq heq))
    · exact le_inf hGTleM (X.GT_le_arcStab _ _)
  have hGTrel : X.GT.relIndex M = (2 ^ X.n 0) ^ m * (2 ^ X.n 0 + 1) := by
    rw [← hBmGT]
    exact hBmrel
  have hPleM : P ≤ M := by
    rw [hPdef]
    exact inf_le_right
  have hcardM_P : Nat.card M = P.relIndex M * Nat.card P := by
    have h := Subgroup.relIndex_mul_card (H := P) (K := M)
    rw [inf_eq_left.mpr hPleM] at h
    exact h.symm
  have hcardM_GT : Nat.card M = X.GT.relIndex M * Nat.card X.GT := by
    have h := Subgroup.relIndex_mul_card (H := X.GT) (K := M)
    rw [inf_eq_left.mpr hGTleM] at h
    exact h.symm
  have hcardGT_QT : Nat.card X.GT = X.QT.relIndex X.GT * Nat.card X.QT := by
    have h := Subgroup.relIndex_mul_card (H := X.QT) (K := X.GT)
    rw [inf_eq_left.mpr X.QT_le_GT] at h
    exact h.symm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPsyl : IsSylowTwoOf P M := by
    rw [hPdef, hMdef]
    exact X.isSylowTwoOf_skP_zero hSK
  haveI : Finite ↥P :=
    finite_of_le_stabilizer X.hyp (H := P) (hPsyl.1.trans hM0)
  haveI := X.finite_QT
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2) (G := ↥P)).mp hPsyl.2.1
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2) (G := ↥X.QT)).mp (pCoreOf_isPGroup' X.GT)
  have hPrelOdd : Odd (P.relIndex M) := by
    refine Nat.not_even_iff_odd.mp ?_
    rw [even_iff_two_dvd]
    exact hPsyl.2.2
  have hQTrelOdd : Odd (X.QT.relIndex X.GT) := by
    refine Nat.not_even_iff_odd.mp ?_
    rw [even_iff_two_dvd]
    exact X.isSylowTwoOf_QT_GT.2.2
  have hn0ne : X.n 0 ≠ 0 := by
    have h : 1 ≤ X.n 0 := (X.hyp.valency (X.vert 0)).1
    omega
  have hqodd : Odd (2 ^ X.n 0 + 1) := by
    rw [odd_succ_iff_even]
    exact even_iff_two_dvd.mpr (dvd_pow_self 2 hn0ne)
  have hOodd : Odd ((2 ^ X.n 0 + 1) * X.QT.relIndex X.GT) := hqodd.mul hQTrelOdd
  have hqpow : (2 ^ X.n 0) ^ m = 2 ^ (X.n 0 * m) := (pow_mul 2 (X.n 0) m).symm
  have hm : P.relIndex M * 2 ^ a =
      (2 ^ (X.n 0 * m) * 2 ^ b) * ((2 ^ X.n 0 + 1) * X.QT.relIndex X.GT) := by
    rw [← ha, ← hb, ← hqpow]
    have hmaster : P.relIndex M * Nat.card P =
        ((2 ^ X.n 0) ^ m * (2 ^ X.n 0 + 1)) * (X.QT.relIndex X.GT * Nat.card X.QT) := by
      rw [← hcardM_P, hcardM_GT, hGTrel, hcardGT_QT]
    rw [hmaster]
    ring
  have hdvd1 : 2 ^ a ∣ 2 ^ (X.n 0 * m) * 2 ^ b := by
    have hdvd : 2 ^ a ∣
        (2 ^ (X.n 0 * m) * 2 ^ b) * ((2 ^ X.n 0 + 1) * X.QT.relIndex X.GT) :=
      ⟨P.relIndex M, by rw [← hm, mul_comm]⟩
    have hcop : Nat.Coprime (2 ^ a) ((2 ^ X.n 0 + 1) * X.QT.relIndex X.GT) :=
      Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hOodd)
    exact hcop.dvd_of_dvd_mul_right hdvd
  have hdvd2 : 2 ^ (X.n 0 * m) * 2 ^ b ∣ 2 ^ a := by
    have hdvd : 2 ^ (X.n 0 * m) * 2 ^ b ∣ (2 ^ a) * (P.relIndex M) :=
      ⟨(2 ^ X.n 0 + 1) * X.QT.relIndex X.GT,
        by rw [mul_comm (2 ^ a) (P.relIndex M), hm]⟩
    have hcop : Nat.Coprime (2 ^ (X.n 0 * m) * 2 ^ b) (P.relIndex M) := by
      rw [← pow_add]
      exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hPrelOdd)
    exact hcop.dvd_of_dvd_mul_right hdvd
  have hPeq : 2 ^ a = 2 ^ (X.n 0 * m) * 2 ^ b := Nat.dvd_antisymm hdvd1 hdvd2
  rw [ha]
  exact hPeq.trans (by rw [hb])

theorem card_E {m : ℕ} (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    Nat.card (X.E X.QT 0) = 2 ^ (X.n 0 * (m - 1)) * Nat.card X.QT := by
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  have hPnot : ¬ X.skP X.QT ≤ X.Q 0 :=
    X.not_skP_QT_le_Q_zero hGT hs hodd h5 hX
  have hEeq : X.E X.QT 0 = X.Q 0 ⊓ X.skP X.QT := X.E_eq_inf_skP hSK
  have hrel : (X.E X.QT 0).relIndex (X.skP X.QT) = 2 ^ X.n 0 :=
    X.relIndex_E_skP hSK (Or.inl hPnot)
  have hmul : 2 ^ X.n 0 * Nat.card (X.E X.QT 0) = Nat.card (X.skP X.QT) := by
    have h := Subgroup.relIndex_mul_card (H := X.E X.QT 0) (K := X.skP X.QT)
    rw [inf_eq_left.mpr (hEeq.le.trans inf_le_right), hrel] at h
    exact h
  have hm1 : 1 ≤ m := by
    have := hreg.1
    omega
  have hcardP := X.card_skP hGT hs hodd h5 hX hreg
  have hpow : 2 ^ (X.n 0 * m) = 2 ^ (X.n 0 * (m - 1)) * 2 ^ X.n 0 := by
    have hidx : X.n 0 * m = X.n 0 * (m - 1) + X.n 0 := by
      have h := Nat.mul_add (X.n 0) (m - 1) 1
      rw [show m - 1 + 1 = m by omega, Nat.mul_one] at h
      exact h
    rw [hidx, pow_add]
  have hmain : 2 ^ X.n 0 * Nat.card (X.E X.QT 0) =
      2 ^ X.n 0 * (2 ^ (X.n 0 * (m - 1)) * Nat.card X.QT) := by
    calc 2 ^ X.n 0 * Nat.card (X.E X.QT 0) = Nat.card (X.skP X.QT) := hmul
      _ = 2 ^ (X.n 0 * m) * Nat.card X.QT := hcardP
      _ = 2 ^ X.n 0 * (2 ^ (X.n 0 * (m - 1)) * Nat.card X.QT) := by
          rw [hpow]
          ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (n := X.n 0) (by norm_num)) hmain

theorem three_le_m {m : ℕ} (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    3 ≤ m := by
  have hle : (s : ℤ) ≤ 2 * (m : ℤ) + 1 := by
    by_contra hlt
    have hlt' : 2 * (m : ℤ) + 1 < (s : ℤ) := by omega
    have hks : 2 * m + 1 < s := by omega
    have hR : X.RightTransAt 0 (2 * (m : ℤ) + 1) := by
      have h := (X.trans_of_lt hs 0 (k := 2 * m + 1) (by omega) hks).2
      simpa using h
    exact X.arcStab_ne_GT_of_rightTransAt (m := 0) (r := 2 * (m : ℤ) + 1) (by omega) hR
      hreg.2.2.2.1
  have hm2 : 2 ≤ m := by
    have : (5 : ℤ) ≤ 2 * (m : ℤ) + 1 := by omega
    omega
  by_contra hm3
  have hm : m = 2 := by omega
  subst hm
  have hreg04 : X.IsMaxReg 0 4 := by simpa using hreg
  have hs5 : s = 5 := by
    have h1 : (s : ℤ) ≤ 5 := by simpa using hle
    omega
  have hreg15 : X.IsMaxReg 1 5 := by
    refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
    · have h := (hs.2.1 4 (by norm_num) (by omega) (X.line.arc 1 4)).1
      have h' := (X.leftTransitive_arc_iff 1 4).mp h
      simpa using h'
    · have h := (hs.2.1 4 (by norm_num) (by omega) (X.line.arc 1 4)).2
      have h' := (X.rightTransitive_arc_iff 1 (by norm_num : 1 ≤ 4)).mp h
      simpa using h'
    ·
      have h := X.arcStab_add 1 (-1) 4
      rw [show (-1 : ℤ) + 2 * 1 = 1 by norm_num,
        show (4 : ℤ) + 2 * 1 = 5 + 1 by norm_num, zpow_one] at h
      rw [h, show X.arcStab (-1) 4 = X.GT by simpa using hreg04.2.2.2.2]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp X.tau_mem_normalizer_GT
    · exact hreg04.2.2.2.1
  have hH1 : X.arcStab 1 5 ≤ X.normGi X.QT 1 :=
    le_inf (X.arcStab_le_normalizer_QT_of_isMaxReg hreg15)
      (X.arcStab_le_Gi_of_between (by norm_num) (by norm_num))
  have h02 : X.vert 0 ≠ X.vert 2 := by
    intro h
    have h' := X.vert_injective h
    norm_num at h'
  have hH1L : ∀ a b : V, Γ.Adj (X.vert 1) a → a ≠ X.vert 2 →
      Γ.Adj (X.vert 1) b → b ≠ X.vert 2 →
      ∃ g ∈ X.normGi X.QT 1, g • a = b := by
    intro a b ha ha2 hb hb2
    obtain ⟨g, hg, hgab⟩ := hreg15.2.1 a b ha ha2 hb hb2
    exact ⟨g, hH1 hg, hgab⟩
  have hthird : ∃ c : V, c ∈ Γ.neighborSet (X.vert 1) \ {X.vert 0} ∧ c ≠ X.vert 2 := by
    have hcard : (Γ.neighborSet (X.vert 1) \ {X.vert 0}).ncard = 2 ^ X.n 1 :=
      ncard_neighborSet_diff X.hyp (by simpa using (X.adj 0).symm)
    have hn1pos : 1 ≤ X.n 1 := (X.hyp.valency (X.vert 1)).1
    have hgt : 1 < (Γ.neighborSet (X.vert 1) \ {X.vert 0}).ncard := by
      rw [hcard]
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ X.n 1 := Nat.pow_le_pow_right (by norm_num) hn1pos
    obtain ⟨c, hc, hc2⟩ := Set.exists_ne_of_one_lt_ncard hgt (X.vert 2)
    exact ⟨c, hc, hc2⟩
  obtain ⟨b, hb, hb2⟩ := hthird
  have hb0 : b ≠ X.vert 0 := hb.2
  have hbΔ : Γ.Adj (X.vert 1) b := hb.1
  obtain ⟨g, hg, hgT0b⟩ := hH1L (X.vert 0) b
    (by simpa using (X.adj 0).symm) h02 hbΔ hb2
  have hpair := (X.isSK_QT hGT hs hodd h5 hX).pair g hg
  rw [hgT0b] at hpair
  rcases hpair with h | h
  · exact hb0 h
  · exact hb2 h

theorem eq_QT_of_normal {D : Subgroup G} (hQD : X.QT ≤ D)
    (hDE : D ≤ X.E X.QT 0 ⊓ X.E X.QT 2)
    (hM : X.normGi X.QT 0 ≤ Subgroup.normalizer (D : Set G))
    {t : G} (ht : t ∈ X.normGi X.QT 1) (ht02 : t • X.vert 0 = X.vert 2)
    (htD : t ∈ Subgroup.normalizer (D : Set G)) : D = X.QT := by
  have htN : t ∈ Subgroup.normalizer (X.QT : Set G) := ht.1
  have hmem : t⁻¹ * X.τ ∈ X.normGi X.QT 0 := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ ((Subgroup.normalizer (X.QT : Set G)).inv_mem htN)
        X.tau_mem_normalizer_QT
    · rw [MulAction.mem_stabilizer_iff]
      calc (t⁻¹ * X.τ) • X.vert 0 = t⁻¹ • (X.τ • X.vert 0) := mul_smul _ _ _
        _ = t⁻¹ • X.vert 2 := by rw [show X.τ • X.vert 0 = X.vert 2 from by
              simpa using X.zpow_smul_vert 1 0]
        _ = X.vert 0 := by rw [← ht02]; simp
  have hτD : X.τ ∈ Subgroup.normalizer (D : Set G) := by
    have h := Subgroup.mul_mem (Subgroup.normalizer (D : Set G)) htD (hM hmem)
    simpa only [mul_inv_cancel_left] using h
  have hfixEven : ∀ j : ℤ, D ≤ MulAction.stabilizer G (X.vert (2 * j)) := by
    intro j
    have hconj : conjSub (X.τ ^ j) D = D :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (zpow_mem hτD j)
    have h0 : D ≤ MulAction.stabilizer G (X.vert 0) :=
      (hDE.trans inf_le_left).trans (le_trans inf_le_left (X.Q_le_Gi 0))
    have h : D ≤ MulAction.stabilizer G ((X.τ ^ j) • X.vert 0) := by
      rw [stabilizer_smul_eq_conjSub]
      exact hconj.ge.trans (conjSub_mono _ h0)
    rwa [show (X.τ ^ j) • X.vert 0 = X.vert (2 * j) from by
      simpa using X.zpow_smul_vert j 0] at h
  have hfixOdd : ∀ j : ℤ, D ≤ MulAction.stabilizer G (X.vert (2 * j + 1)) := by
    intro j d hd
    have h0 : d • (X.line.arc (2 * j) 2).vert 0 = (X.line.arc (2 * j) 2).vert 0 := by
      simpa [Line.arc] using MulAction.mem_stabilizer_iff.mp (hfixEven j hd)
    have h2 : d • (X.line.arc (2 * j) 2).vert 2 = (X.line.arc (2 * j) 2).vert 2 := by
      have h := MulAction.mem_stabilizer_iff.mp (hfixEven (j + 1) hd)
      simpa [Line.arc, show 2 * (j + 1) = 2 * j + 2 by ring] using h
    have h1 := Arc.fixes_of_ends X.hyp.isTree X.hyp.adj_smul (X.line.arc (2 * j) 2) h0 h2 1
      (by norm_num)
    simpa [Line.arc] using h1
  have hfixAll : X.fixSet D = Set.univ := by
    ext i
    simp only [Set.mem_univ, iff_true]
    obtain ⟨j, hj | hj⟩ := Int.even_or_odd' i
    · rw [hj]; exact hfixEven j
    · rw [hj]; exact hfixOdd j
  have hDGT : D ≤ X.GT := X.le_GT_of_fixSet_eq_univ hfixAll
  have hDQ0 : D ≤ X.Q 0 := (hDE.trans inf_le_left).trans inf_le_left
  have hDp : IsPGroup 2 D := (pCoreOf_isPGroup' (X.Gi 0)).to_le hDQ0
  haveI : Finite ↥X.GT := finite_of_le_stabilizer X.hyp (H := X.GT) (X.GT_le_Gi 0)
  have hnorm : (X.QT.subgroupOf X.GT).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X.GT)
  exact le_antisymm (le_of_normal_isSylowTwoOf X.isSylowTwoOf_QT_GT hnorm hDGT hDp) hQD

private theorem E_inf_E_two_eq_QT_of_commutator_eq_bot (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hV : ⁅X.E X.QT 0, X.Yst X.QT 0⁆ = ⊥) :
    X.E X.QT 0 ⊓ X.E X.QT 2 = X.QT := by
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  have hP : ¬ X.skP X.QT ≤ X.Q 0 ∨ 2 ≤ X.n 0 :=
    Or.inl (X.not_skP_QT_le_Q_zero hGT hs hodd h5 hX)
  obtain ⟨t, ht, ht02, -, ht2P⟩ := IsSK.exists_t (X := X) hSK
  set E0 : Subgroup G := X.E X.QT 0 with hE0def
  set E2 : Subgroup G := X.E X.QT 2 with hE2def
  set M0 : Subgroup G := X.normGi X.QT 0 with hM0def
  set M2 : Subgroup G := X.normGi X.QT 2 with hM2def
  set P : Subgroup G := X.skP X.QT with hPdef
  have hSKP0 : IsSylowTwoOf P M0 := by
    rw [hPdef, hM0def]
    exact X.isSylowTwoOf_skP_zero hSK
  have hSKP2 : IsSylowTwoOf P M2 := by
    rw [hPdef, hM2def]
    exact X.isSylowTwoOf_skP_two hSK
  have hE0p : E0 = pCoreOf 2 M0 := by
    rw [hE0def, hM0def]
    exact X.E_eq_pCoreOf hSK
  have hE2p : E2 = pCoreOf 2 M2 := by
    rw [hE2def, ← IsSK.conjSub_E_zero (X := X) ht.1 ht02, ← hE0def, hE0p, hM0def]
    rw [show conjSub t (pCoreOf 2 (X.normGi X.QT 0)) =
        Subgroup.map (MulAut.conj t).toMonoidHom (pCoreOf 2 (X.normGi X.QT 0)) from rfl]
    rw [← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj t) (X.normGi X.QT 0)]
    have hmap : Subgroup.map (MulAut.conj t).toMonoidHom (X.normGi X.QT 0) = M2 := by
      rw [hM2def]
      change conjSub t (X.normGi X.QT 0) = X.normGi X.QT 2
      exact IsSK.conjSub_normGi_zero (X := X) ht.1 ht02
    rw [hmap]
  have hE0leP : E0 ≤ P := by
    rw [hE0p]
    exact CFSG.Quasithin.RonanF713.isSylowTwoOf_pCoreOf_le_loc hSKP0
  have hE2leP : E2 ≤ P := by
    rw [hE2p]
    exact CFSG.Quasithin.RonanF713.isSylowTwoOf_pCoreOf_le_loc hSKP2
  have hE0norm : P ≤ Subgroup.normalizer (E0 : Set G) := by
    rw [hE0p]
    exact hSKP0.1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M0)
  have hE2norm : P ≤ Subgroup.normalizer (E2 : Set G) := by
    rw [hE2p]
    exact hSKP2.1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M2)
  set D : Subgroup G := E0 ⊓ E2 with hDdef
  have hQD : X.QT ≤ D := by
    rw [hDdef]
    exact le_inf X.QT_le_E (le_inf (X.QT_le_Q 2) Subgroup.le_normalizer)
  have hDE : D ≤ E0 ⊓ E2 := le_of_eq hDdef
  have hYle : X.Yst X.QT 0 ≤ Subgroup.normalizer (D : Set G) := by
    have hE0leC : E0 ≤ Subgroup.centralizer (X.Yst X.QT 0 : Set G) := by
      rw [hE0def]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hV
    have hC : X.Yst X.QT 0 ≤ Subgroup.centralizer (D : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact (Subgroup.mem_centralizer_iff.mp (hE0leC (Subgroup.mem_inf.mp hd).1) y hy).symm
    exact hC.trans (Subgroup.centralizer_le_normalizer (D : Set G))
  have hKle : X.K ≤ Subgroup.normalizer (D : Set G) := by
    have hK0 : X.K ≤ Subgroup.normalizer (E0 : Set G) := by
      rw [hE0p]
      exact (hSK.K_le_normGi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M0)
    have hK2 : X.K ≤ Subgroup.normalizer (E2 : Set G) := by
      rw [hE2p]
      exact (hSK.K_le_normGi 2).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M2)
    intro k hk
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hK0 hk, hK2 hk⟩
  have hPleN : P ≤ Subgroup.normalizer (D : Set G) := by
    intro p hp
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hE0norm hp, hE2norm hp⟩
  have hM0le : M0 ≤ Subgroup.normalizer (D : Set G) := by
    rw [hM0def, X.normGi_eq_Yst_sup_K_sup_skP hSK hP]
    exact sup_le (sup_le hYle hKle) hPleN
  have hconjE2 : conjSub t E2 = E0 := by
    rw [hE2def, ← IsSK.conjSub_E_zero (X := X) ht.1 ht02, ← hE0def]
    rw [← conjSub_mul]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (hE0norm (by simpa [pow_two] using ht2P))
  have htD : t ∈ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub t D = D
    rw [hDdef, hE0def, hE2def, conjSub_inf, IsSK.conjSub_E_zero (X := X) ht.1 ht02,
      ← hE2def, hconjE2, inf_comm]
  have hDeq : D = X.QT := X.eq_QT_of_normal hQD hDE hM0le ht.1 ht02 htD
  exact hDeq

private theorem m_le_two_of_card_sq_le {n m q : ℕ} (hn : 1 ≤ n) (hq : 0 < q)
    (h : 2 ^ (n * (m - 1)) * q * (2 ^ (n * (m - 1)) * q) ≤ 2 ^ (n * m) * q * q) :
    m ≤ 2 := by
  have h2 : 2 ^ (n * (m - 1)) * 2 ^ (n * (m - 1)) ≤ 2 ^ (n * m) := by
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos hq hq)
    calc 2 ^ (n * (m - 1)) * 2 ^ (n * (m - 1)) * (q * q)
        = (2 ^ (n * (m - 1)) * q) * (2 ^ (n * (m - 1)) * q) := by ring
      _ ≤ (2 ^ (n * m) * q) * q := h
      _ = 2 ^ (n * m) * (q * q) := by ring
  have h3 : 2 ^ (n * (m - 1)) * 2 ^ (n * (m - 1)) = 2 ^ (n * (2 * (m - 1))) := by
    rw [← pow_add]
    congr 1
    ring
  have h4 : 2 ^ (n * m) = 2 ^ (n * m) := rfl
  rw [h3, h4] at h2
  by_contra hm
  have hm3 : 3 ≤ m := by omega
  have hlt : n * m < n * (2 * (m - 1)) := by
    refine Nat.mul_lt_mul_of_pos_left ?_ (by omega)
    omega
  exact (Nat.pow_lt_pow_right (by omega : 1 < 2) hlt).not_ge h2

private theorem false_of_card_E_sq_le {m : ℕ} (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ)))
    (hDeq : X.E X.QT 0 ⊓ X.E X.QT 2 = X.QT) : False := by
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  obtain ⟨t, ht, ht02, -, ht2P⟩ := IsSK.exists_t (X := X) hSK
  set E0 : Subgroup G := X.E X.QT 0 with hE0def
  set E2 : Subgroup G := X.E X.QT 2 with hE2def
  set M0 : Subgroup G := X.normGi X.QT 0 with hM0def
  set M2 : Subgroup G := X.normGi X.QT 2 with hM2def
  set P : Subgroup G := X.skP X.QT with hPdef
  have hSKP0 : IsSylowTwoOf P M0 := by
    rw [hPdef, hM0def]
    exact X.isSylowTwoOf_skP_zero hSK
  have hSKP2 : IsSylowTwoOf P M2 := by
    rw [hPdef, hM2def]
    exact X.isSylowTwoOf_skP_two hSK
  have hE0p : E0 = pCoreOf 2 M0 := by
    rw [hE0def, hM0def]
    exact X.E_eq_pCoreOf hSK
  have hE2p : E2 = pCoreOf 2 M2 := by
    rw [hE2def, ← IsSK.conjSub_E_zero (X := X) ht.1 ht02, ← hE0def, hE0p, hM0def]
    rw [show conjSub t (pCoreOf 2 (X.normGi X.QT 0)) =
        Subgroup.map (MulAut.conj t).toMonoidHom (pCoreOf 2 (X.normGi X.QT 0)) from rfl]
    rw [← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj t) (X.normGi X.QT 0)]
    have hmap : Subgroup.map (MulAut.conj t).toMonoidHom (X.normGi X.QT 0) = M2 := by
      rw [hM2def]
      change conjSub t (X.normGi X.QT 0) = X.normGi X.QT 2
      exact IsSK.conjSub_normGi_zero (X := X) ht.1 ht02
    rw [hmap]
  have hE0leP : E0 ≤ P := by
    rw [hE0p]
    exact CFSG.Quasithin.RonanF713.isSylowTwoOf_pCoreOf_le_loc hSKP0
  have hE2leP : E2 ≤ P := by
    rw [hE2p]
    exact CFSG.Quasithin.RonanF713.isSylowTwoOf_pCoreOf_le_loc hSKP2
  have hE0norm : P ≤ Subgroup.normalizer (E0 : Set G) := by
    rw [hE0p]
    exact hSKP0.1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M0)
  have hE2norm : P ≤ Subgroup.normalizer (E2 : Set G) := by
    rw [hE2p]
    exact hSKP2.1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M2)
  haveI : Finite ↥P :=
    finite_of_le_stabilizer X.hyp (H := P) (hSKP0.1.trans (X.normGi_le_Gi X.QT 0))
  have hcardE0 : Nat.card ↥E0 = 2 ^ (X.n 0 * (m - 1)) * Nat.card ↥X.QT := by
    rw [hE0def]
    exact X.card_E hGT hs hodd h5 hX hreg
  have hcardE2 : Nat.card ↥E2 = Nat.card ↥E0 := by
    rw [hE2def, X.E_two_eq]
    exact Subgroup.card_map_of_injective (f := (MulAut.conj X.τ).toMonoidHom)
      (MulAut.conj X.τ).injective
  have hprod :=
    CFSG.Timmesfeld.LocalTwoSubgroups.FrobeniusFixedSpaceBounds.card_sup_mul_card_inf E0 E2
      (fun b hb n hn =>
        (Subgroup.mem_normalizer_iff.mp (hE2norm (hE0leP hb)) n).mp hn)
  have hDcard : Nat.card ↥(E0 ⊓ E2) = Nat.card ↥X.QT := by
    rw [show E0 ⊓ E2 = X.QT from hDeq]
  have hmain : Nat.card ↥E0 * Nat.card ↥E0 =
      Nat.card ↥(E0 ⊔ E2) * Nat.card ↥X.QT := by
    calc Nat.card ↥E0 * Nat.card ↥E0 = Nat.card ↥E0 * Nat.card ↥E2 := by rw [hcardE2]
      _ = Nat.card ↥(E0 ⊔ E2) * Nat.card ↥(E0 ⊓ E2) := hprod.symm
      _ = Nat.card ↥(E0 ⊔ E2) * Nat.card ↥X.QT := by rw [hDcard]
  have hle : Nat.card ↥E0 * Nat.card ↥E0 ≤ Nat.card ↥P * Nat.card ↥X.QT := by
    rw [hmain]
    exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le (sup_le hE0leP hE2leP))
  have hPcard : Nat.card ↥P = 2 ^ (X.n 0 * m) * Nat.card ↥X.QT := by
    rw [hPdef]
    exact X.card_skP hGT hs hodd h5 hX hreg
  rw [hcardE0, hPcard] at hle
  haveI := X.finite_QT
  set qT : ℕ := Nat.card ↥X.QT with hqTdef
  have hqT : 0 < qT := Nat.card_pos
  have hn0pos : 1 ≤ X.n 0 := (X.hyp.valency (X.vert 0)).1
  have hm2 := m_le_two_of_card_sq_le hn0pos hqT hle
  have hm3 : 3 ≤ m := X.three_le_m hGT hs hodd h5 hX hreg
  omega

theorem commutator_E_Yst_ne_bot {m : ℕ} (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ⁅X.E X.QT 0, X.Yst X.QT 0⁆ ≠ ⊥ := by
  intro hV
  exact X.false_of_card_E_sq_le hGT hs hodd h5 hX hreg
    (X.E_inf_E_two_eq_QT_of_commutator_eq_bot hGT hs hodd h5 hX hV)

theorem isElemAbelian_E_QT (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    IsElemAbelian 2 (X.E X.QT 0) := by
  have hU := X.isSKMax_QT hGT hs hodd h5 hX
  have hP : X.skP X.QT ≠ ⊥ ∨ 2 ≤ X.n 0 := Or.inl (fun h =>
    X.QT_ne_bot hGT (le_bot_iff.mp (h ▸ X.QT_le_skP)))
  exact X.isElemAbelian_E hU hP

theorem natQuot_M (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s)
    (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    NatQuot (X.Lst X.QT 0) (X.E X.QT 0) X.ZM (X.n 0) := by
  have hU : X.IsSKMax X.QT := X.isSKMax_QT hGT hs hodd h5 hX
  have hSK : X.IsSK X.QT := hU.1
  have hP : ¬ X.skP X.QT ≤ X.Q 0 ∨ 2 ≤ X.n 0 :=
    Or.inl (X.not_skP_QT_le_Q_zero hGT hs hodd h5 hX)
  haveI : Finite ↥(X.Lst X.QT 0) :=
    finite_of_le_stabilizer X.hyp (H := X.Lst X.QT 0)
      ((oTwoPrime_le (X.normGi X.QT 0)).trans (X.normGi_le_Gi X.QT 0))
  haveI : Finite ↥(X.normGi X.QT 0) :=
    finite_of_le_stabilizer X.hyp (H := X.normGi X.QT 0) (X.normGi_le_Gi X.QT 0)
  have hEeq : X.E X.QT 0 = pCoreOf 2 (X.Lst X.QT 0) :=
    (X.pCoreOf_Lst_eq_E hSK).symm
  have hPH : X.skP X.QT ≤ X.Lst X.QT 0 := by
    rw [X.Lst_eq_Yst_sup_skP hSK]
    exact le_sup_right
  have hnc : NoCharNormal (X.skP X.QT) (X.Lst X.QT 0) :=
    IsSKMax.noCharNormal_of_le X hU hPH (oTwoPrime_le _)
      (X.normGi_eq_Lst_sup_K hSK hP)
  obtain ⟨m, -, hreg⟩ := X.exists_isMaxReg hs hodd hX
  have hV : ⁅X.E X.QT 0, X.Yst X.QT 0⁆ ≠ ⊥ :=
    X.commutator_E_Yst_ne_bot hGT hs hodd h5 hX hreg
  have hc : CharTwo (X.Lst X.QT 0) := X.charTwo_Lst hSK hP hV
  have hP' : IsSylowTwoOf (X.skP X.QT) (X.Lst X.QT 0) :=
    X.isSylowTwoOf_skP_Lst hSK
  have hq := X.isL2Quot_Lst hSK hP
  have he : IsElemAbelian 2 (pCoreOf 2 (X.Lst X.QT 0)) := by
    have h := X.isElemAbelian_E_QT hGT hs hodd h5 hX
    rwa [hEeq] at h
  have h := natQuot_of_isL2Quot (X.hyp.valency (X.vert 0)).1 hc hq hP' hnc he
  rw [← hEeq] at h
  exact h.1

private theorem relCent_eq_of_le_centralizer
    (hNQ : NatQuot (X.Lst X.QT 0) (X.E X.QT 0) X.ZM (X.n 0)) {A D : Subgroup G}
    (hA : IsSylowTwoOf A (X.Lst X.QT 0)) (hDE : D ≤ X.E X.QT 0)
    (hDC : D ≤ Subgroup.centralizer (A : Set G))
    (hcard : Nat.card ↥D = 2 ^ X.n 0 * Nat.card ↥X.ZM) :
    relCent (X.E X.QT 0) X.ZM A = D := by
  have hle : D ≤ relCent (X.E X.QT 0) X.ZM A := fun x hx =>
    (mem_relCent X.E_le_normalizer_ZM).mpr ⟨hDE hx, fun a ha => by
      rw [Commute.commutator_eq (Subgroup.mem_centralizer_iff.mp (hDC hx) a ha).symm]
      exact X.ZM.one_mem⟩
  have hZle : X.ZM ≤ relCent (X.E X.QT 0) X.ZM A := fun z hz =>
    (mem_relCent X.E_le_normalizer_ZM).mpr ⟨hNQ.Z_le hz, fun a ha => by
      rw [Commute.commutator_eq
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 a (hA.1 ha)).symm]
      exact X.ZM.one_mem⟩
  have hrel : Nat.card ↥(relCent (X.E X.QT 0) X.ZM A) = 2 ^ X.n 0 * Nat.card ↥X.ZM := by
    have h := Subgroup.relIndex_mul_card (H := X.ZM) (K := relCent (X.E X.QT 0) X.ZM A)
    rw [inf_eq_left.mpr hZle, hNQ.line A hA] at h
    exact h.symm
  haveI : Finite ↥(relCent (X.E X.QT 0) X.ZM A) := by
    refine finite_of_le_stabilizer X.hyp (α := X.vert 0)
      (H := relCent (X.E X.QT 0) X.ZM A) ?_
    exact (show relCent (X.E X.QT 0) X.ZM A ≤ X.E X.QT 0 from fun x hx => hx.1).trans
      X.E_le_Gi_zero
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hrel, hcard]

theorem isSylowTwoOf_skP_Lst_QT (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    IsSylowTwoOf (X.skP X.QT) (X.Lst X.QT 0) := by
  exact X.isSylowTwoOf_skP_Lst (X.isSK_QT hGT hs hodd h5 hX)

private theorem exists_odd_orderOf_ne_one {L : Subgroup G} [Finite ↥L]
    (h : pResidualOf 2 L ≠ ⊥) : ∃ x ∈ L, Odd (orderOf x) ∧ x ≠ 1 := by
  by_contra hgen
  push Not at hgen
  apply h
  have hL2 : IsPGroup 2 L := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [IsPGroup.iff_orderOf]
    intro x
    have hordx : orderOf ((x : ↥L) : G) = orderOf x := by
      simpa using (orderOf_injective L.subtype L.subtype_injective x)
    have hpos : 0 < orderOf ((x : ↥L) : G) := by
      change 0 < orderOf (L.subtype x)
      rw [orderOf_injective L.subtype L.subtype_injective x]
      exact orderOf_pos x
    obtain ⟨k, q, hq, hk⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
    have hxoddG : Odd (orderOf (((x : ↥L) : G) ^ (2 ^ k))) := by
      rw [orderOf_pow_of_dvd (by positivity) ⟨q, hk⟩, hk]
      simpa using hq
    have hx1 : ((x : ↥L) : G) ^ (2 ^ k) = 1 :=
      hgen _ (L.pow_mem x.2 (2 ^ k)) hxoddG
    have hq1 : q = 1 := by
      have h1 : orderOf (((x : ↥L) : G) ^ (2 ^ k)) = 1 :=
        orderOf_eq_one_iff.mpr hx1
      rw [orderOf_pow_of_dvd (by positivity) ⟨q, hk⟩, hk] at h1
      simpa using h1
    exact ⟨k, by rw [← hordx, hk, hq1, mul_one]⟩
  rw [pResidualOf]
  haveI : (⊥ : Subgroup ↥L).Normal := inferInstance
  have hbot : pResidual 2 ↥L ≤ ⊥ := by
    refine pResidual_le (p := 2) (X := ↥L) (N := ⊥) ?_
    intro x
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hL2) x
    exact ⟨k, by rw [← hk]; exact Subgroup.mem_bot.mpr (pow_orderOf_eq_one x)⟩
  simpa using Subgroup.map_mono (f := L.subtype) hbot

private theorem commutator_QT_zpowers_eq_bot {y : G} (hyY : y ∈ X.Yst X.QT 0)
    (hyL : y ∈ X.Lst X.QT 0) (hodd : Odd (orderOf y))
    (hW : ⁅X.QT, X.Yst X.QT 0⁆ ≤ X.ZM) :
    ⁅X.QT, Subgroup.zpowers y⁆ = ⊥ := by
  have hGi0le : X.QT ≤ X.Gi 0 := X.QT_le_GT.trans (X.GT_le_Gi 0)
  haveI : Finite ↥(X.Gi 0) := finite_of_le_stabilizer X.hyp (H := X.Gi 0) le_rfl
  have hLEG0 : X.Lst X.QT 0 ≤ X.Gi 0 :=
    (oTwoPrime_le (X.normGi X.QT 0)).trans (X.normGi_le_Gi X.QT 0)
  have hYLE : X.Yst X.QT 0 ≤ X.Lst X.QT 0 := Subgroup.map_subtype_le _
  have hYLE_Qt : X.Yst X.QT 0 ≤ Subgroup.normalizer (X.QT : Set G) :=
    hYLE.trans ((oTwoPrime_le (X.normGi X.QT 0)).trans inf_le_left)
  have hzpowH : Subgroup.zpowers y ≤ X.Gi 0 := (Subgroup.zpowers_le.mpr hyL).trans hLEG0
  have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (X.QT : Set G) :=
    (Subgroup.zpowers_le.mpr hyY).trans hYLE_Qt
  have hAHN : (Subgroup.zpowers y).subgroupOf (X.Gi 0) ≤
      Subgroup.normalizer ((X.QT.subgroupOf (X.Gi 0)) : Set ↥(X.Gi 0)) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have ha' : ((a : ↥(X.Gi 0)) : G) ∈ Subgroup.zpowers y :=
        Subgroup.mem_subgroupOf.mp ha
      have hx' : ((x : ↥(X.Gi 0)) : G) ∈ X.QT :=
        Subgroup.mem_subgroupOf.mp hx
      have haN : ((a : ↥(X.Gi 0)) : G) ∈
          Subgroup.normalizer (X.QT : Set G) := hyN ha'
      have hmem : ((a : ↥(X.Gi 0)) : G) * ((x : ↥(X.Gi 0)) : G) *
          ((a : ↥(X.Gi 0)) : G)⁻¹ ∈ X.QT :=
        (Subgroup.mem_normalizer_iff.mp haN) _ |>.mp hx'
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hmem)
    · intro hx
      have ha' : ((a : ↥(X.Gi 0)) : G) ∈ Subgroup.zpowers y :=
        Subgroup.mem_subgroupOf.mp ha
      have hx' : ((a : ↥(X.Gi 0)) : G) * ((x : ↥(X.Gi 0)) : G) *
          ((a : ↥(X.Gi 0)) : G)⁻¹ ∈ X.QT :=
        Subgroup.mem_subgroupOf.mp hx
      have haN : ((a : ↥(X.Gi 0)) : G) ∈
          Subgroup.normalizer (X.QT : Set G) := hyN ha'
      have hmem : ((x : ↥(X.Gi 0)) : G) ∈ X.QT :=
        (Subgroup.mem_normalizer_iff.mp haN) _ |>.mpr hx'
      exact Subgroup.mem_subgroupOf.mpr hmem
  have hcardA : Nat.card ↥((Subgroup.zpowers y).subgroupOf (X.Gi 0)) =
      Nat.card ↥(Subgroup.zpowers y) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzpowH).toEquiv
  have hcardQ : Nat.card ↥(X.QT.subgroupOf (X.Gi 0)) = Nat.card ↥X.QT :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hGi0le).toEquiv
  have hQtcard : ∃ k : ℕ, Nat.card ↥X.QT = 2 ^ k := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := X.finite_QT
    exact (IsPGroup.iff_card (p := 2) (G := ↥X.QT)).mp (pCoreOf_isPGroup' X.GT)
  have hcopH : Nat.Coprime (Nat.card ↥((Subgroup.zpowers y).subgroupOf (X.Gi 0)))
      (Nat.card ↥(X.QT.subgroupOf (X.Gi 0))) := by
    rw [hcardA, hcardQ, Nat.card_zpowers]
    obtain ⟨k, hk⟩ := hQtcard
    rw [hk]
    exact (Nat.coprime_two_left.mpr hodd).symm.pow_right k
  have hcommH := CFSG.Quasithin.Vol2.Ch11.SecD.commutator_commutator_eq
    (G := ↥(X.Gi 0)) (P := X.QT.subgroupOf (X.Gi 0))
    (X := (Subgroup.zpowers y).subgroupOf (X.Gi 0)) hAHN hcopH
  have hQmap : Subgroup.map (X.Gi 0).subtype (X.QT.subgroupOf (X.Gi 0)) = X.QT :=
    Subgroup.map_subgroupOf_eq_of_le hGi0le
  have hAmap : Subgroup.map (X.Gi 0).subtype
      ((Subgroup.zpowers y).subgroupOf (X.Gi 0)) = Subgroup.zpowers y :=
    Subgroup.map_subgroupOf_eq_of_le hzpowH
  have hcomm_id : ⁅⁅X.QT, Subgroup.zpowers y⁆, Subgroup.zpowers y⁆ =
      ⁅X.QT, Subgroup.zpowers y⁆ := by
    have hmap := congrArg (Subgroup.map (X.Gi 0).subtype) hcommH
    simp only [Subgroup.map_commutator] at hmap
    rw [hQmap, hAmap] at hmap
    exact hmap
  have hW0_le_Z : ⁅X.QT, Subgroup.zpowers y⁆ ≤ X.ZM :=
    (Subgroup.commutator_mono (le_refl X.QT) (Subgroup.zpowers_le.mpr hyY)).trans hW
  have hZA : ⁅X.ZM, Subgroup.zpowers y⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2) a
      (hYLE ((Subgroup.zpowers_le.mpr hyY) ha))
  have hW0_bot : ⁅X.QT, Subgroup.zpowers y⁆ = ⊥ := by
    have h1 : ⁅⁅X.QT, Subgroup.zpowers y⁆, Subgroup.zpowers y⁆ ≤ ⊥ := by
      rw [← hZA]
      exact Subgroup.commutator_mono hW0_le_Z le_rfl
    rw [← hcomm_id]
    exact le_bot_iff.mp h1
  exact hW0_bot

theorem QT_le_centerOf_Lst (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.QT ≤ X.ZM := by
  have hSKMax : X.IsSKMax X.QT := X.isSKMax_QT hGT hs hodd h5 hX
  have hPne : X.skP X.QT ≠ ⊥ := fun h =>
    X.QT_ne_bot hGT (le_bot_iff.mp (h ▸ X.QT_le_skP))
  obtain ⟨m, -, hreg⟩ := X.exists_isMaxReg hs hodd hX
  have hV : ⁅X.E X.QT 0, X.Yst X.QT 0⁆ ≠ ⊥ :=
    X.commutator_E_Yst_ne_bot hGT hs hodd h5 hX hreg
  have hNQ := X.natQuot_M hGT hs hodd h5 hX
  set L : Subgroup G := X.Lst X.QT 0 with hLdef
  set E : Subgroup G := X.E X.QT 0 with hEdef
  set Y : Subgroup G := X.Yst X.QT 0 with hYdef
  set Z : Subgroup G := X.ZM with hZdef
  have hYLE : Y ≤ L := by
    rw [hYdef, hLdef, Setup.Yst, pResidualOf]
    exact Subgroup.map_subtype_le _
  have hELE : E ≤ L := by simpa [hEdef, hLdef] using hNQ.E_le
  have hZLE : Z ≤ E := by simpa [hZdef, hEdef, hLdef] using hNQ.Z_le
  have hLEG0 : L ≤ X.Gi 0 :=
    (oTwoPrime_le (X.normGi X.QT 0)).trans (X.normGi_le_Gi X.QT 0)
  haveI : Finite ↥L := finite_of_le_stabilizer X.hyp (H := L) hLEG0
  have hYLE_Qt : Y ≤ Subgroup.normalizer (X.QT : Set G) :=
    hYLE.trans ((oTwoPrime_le (X.normGi X.QT 0)).trans inf_le_left)
  have hLE_Qt : L ≤ Subgroup.normalizer (X.QT : Set G) :=
    (oTwoPrime_le (X.normGi X.QT 0)).trans inf_le_left
  have hLE_Y : L ≤ Subgroup.normalizer (Y : Set G) := by
    have h := normalizer_le_normalizer_pResidualOf 2 (X.Lst X.QT 0)
    rw [hYdef, hLdef]
    exact Subgroup.le_normalizer.trans h
  have hLE_E : L ≤ Subgroup.normalizer (E : Set G) := by
    simpa [hEdef, hLdef] using (hNQ.normal.trans inf_le_left)
  have hLE_Z : L ≤ Subgroup.normalizer (Z : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.Quasithin.normalizer_le_normalizer_centerOf L)
  set W : Subgroup G := ⁅X.QT, Y⁆ with hWdef
  have hW_le_Qt : W ≤ X.QT := by
    rw [hWdef]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hYLE_Qt
  have hW_le_L : W ≤ L := hW_le_Qt.trans (X.QT_le_E.trans hELE)
  have hW_le_E : W ≤ E := by
    rw [hWdef]
    exact (Subgroup.commutator_mono (le_refl X.QT) hYLE).trans
      ((Subgroup.commutator_mono X.QT_le_E (le_refl L)).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp hLE_E))
  have hW_norm : L ≤ Subgroup.normalizer (W : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change Subgroup.map (MulAut.conj g).toMonoidHom W = W
    rw [hWdef, Subgroup.map_commutator]
    have hQ : Subgroup.map (MulAut.conj g).toMonoidHom X.QT = X.QT :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLE_Qt hg)
    have hY : Subgroup.map (MulAut.conj g).toMonoidHom Y = Y :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLE_Y hg)
    rw [hQ, hY]
  have hW_le_Z : W ≤ Z := by
    by_contra hWnZ
    have hWZ_le_E : W ⊔ Z ≤ E := sup_le hW_le_E hZLE
    have hWZ_norm : L ≤ Subgroup.normalizer ((W ⊔ Z : Subgroup G) : Set G) :=
      A1a.le_normalizer_sup (hW_norm) (hLE_Z)
    rcases hNQ.irred (W ⊔ Z) (by simpa [hZdef] using le_sup_right)
      (by simpa [hEdef] using hWZ_le_E) (by simpa [hLdef] using hWZ_norm) with h | h
    · exact hWnZ (le_sup_left.trans (le_of_eq h))
    · have hVW : ⁅E, Y⁆ ≤ W := by
        rw [← h]
        refine Subgroup.commutator_le.mpr ?_
        intro e he y hy
        have hWnormZ : W ≤ Subgroup.normalizer (Z : Set G) := hW_le_L.trans hLE_Z
        have hcoe : ((W ⊔ Z : Subgroup G) : Set G) = (W : Set G) * (Z : Set G) :=
          Subgroup.coe_mul_of_left_le_normalizer_right W Z hWnormZ
        have he' : e ∈ (W : Set G) * (Z : Set G) := by
          rw [← hcoe]; exact he
        obtain ⟨w, hw, z, hz, rfl⟩ := Set.mem_mul.mp he'
        have hzC : z ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_inf.mp hz).2
        have hzy : z * y = y * z :=
          ((Subgroup.mem_centralizer_iff.mp hzC) y (hYLE hy)).symm
        have hid : ⁅w * z, y⁆ = ⁅w, y⁆ := by
          have h1 : z * y * z⁻¹ = y := by rw [hzy]; group
          simp only [commutatorElement_def]
          rw [mul_inv_rev]
          calc w * z * y * (z⁻¹ * w⁻¹) * y⁻¹
              = w * (z * y * z⁻¹) * w⁻¹ * y⁻¹ := by group
            _ = w * y * w⁻¹ * y⁻¹ := by rw [h1]
        rw [hid]
        have hYW : Y ≤ Subgroup.normalizer (W : Set G) := hYLE.trans hW_norm
        exact (Subgroup.le_normalizer_iff_commutator_le_left.mp hYW)
          ((Subgroup.commutator_le.mp le_rfl) w hw y hy)
      have hQt_E2 : X.QT ≤ X.E X.QT 2 :=
        le_inf (X.QT_le_Q 2) Subgroup.le_normalizer
      exact (X.not_commutator_le_E_two hSKMax (Or.inl hPne) hV)
        (by simpa [hEdef, hYdef] using (hVW.trans hW_le_Qt).trans hQt_E2)
  have hYne : Y ≠ ⊥ := by
    intro h
    exact hV (by rw [h]; simp)
  have hYgen : ∃ x ∈ L, Odd (orderOf x) ∧ x ≠ 1 :=
    exists_odd_orderOf_ne_one (L := L) hYne
  obtain ⟨y0, hy0L, hy0odd, hy0ne⟩ := hYgen
  have hy0Y : y0 ∈ Y := by
    rw [hYdef, Setup.Yst, ← hLdef, pResidualOf]
    exact Subgroup.mem_map.mpr ⟨⟨y0, hy0L⟩,
      CFSG.Quasithin.mem_pResidual_of_coprime (p := 2)
        (by rw [Subgroup.orderOf_mk]; exact hy0odd.coprime_two_right), rfl⟩
  have hy0E : y0 ∉ E := fun hy0E' =>
    hy0ne (by
      have h2 : IsPGroup 2 E := (pCoreOf_isPGroup' (X.Gi 0)).to_le (by
        rw [hEdef]; exact inf_le_left)
      have hc := h2.orderOf_coprime (Nat.coprime_two_left.mpr hy0odd) ⟨y0, hy0E'⟩
      rw [Subgroup.orderOf_mk, Nat.coprime_self] at hc
      exact orderOf_eq_one_iff.mp hc)
  intro q hq
  have hqE : q ∈ E := by
    rw [hEdef]
    exact X.QT_le_E hq
  have hcommZ : ⁅q, y0⁆ ∈ X.ZM := by
    have hmem : ⁅q, y0⁆ ∈ ⁅X.QT, Subgroup.zpowers y0⁆ :=
      (Subgroup.commutator_le.mp le_rfl) q hq y0 (Subgroup.mem_zpowers y0)
    rw [X.commutator_QT_zpowers_eq_bot hy0Y hy0L hy0odd hW_le_Z] at hmem
    rw [Subgroup.mem_bot.mp hmem]
    exact X.ZM.one_mem
  exact hNQ.fpf y0 (by simpa [hLdef] using hy0L) hy0odd
    (by simpa [hEdef] using hy0E) q (by simpa [hEdef] using hqE) hcommZ

theorem commutator_QT_Lst_eq_bot (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ⁅X.QT, X.Lst X.QT 0⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hqZ : q ∈ X.ZM := X.QT_le_centerOf_Lst hGT hs hodd h5 hX hq
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hqZ).2) l hl

theorem card_ZM {m : ℕ} (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    Nat.card X.ZM = 2 ^ (X.n 0 * (m - 3)) * Nat.card X.QT := by
  have hNQ := X.natQuot_M hGT hs hodd h5 hX
  have hcardE := X.card_E hGT hs hodd h5 hX hreg
  have hm3 := X.three_le_m hGT hs hodd h5 hX hreg
  have hmul := Subgroup.relIndex_mul_card (H := X.ZM) (K := X.E X.QT 0)
  rw [inf_eq_left.mpr hNQ.Z_le, hNQ.index] at hmul
  have hpow : 2 ^ (X.n 0 * (m - 1)) =
      2 ^ (X.n 0 * (m - 3)) * 2 ^ (2 * X.n 0) := by
    rw [show m - 1 = (m - 3) + 2 by omega, Nat.mul_add, pow_add]
    congr 1
    rw [mul_comm]
  have hmain : 2 ^ (2 * X.n 0) * Nat.card X.ZM =
      2 ^ (2 * X.n 0) * (2 ^ (X.n 0 * (m - 3)) * Nat.card X.QT) := by
    calc 2 ^ (2 * X.n 0) * Nat.card X.ZM = Nat.card ↥(X.E X.QT 0) := hmul
      _ = 2 ^ (X.n 0 * (m - 1)) * Nat.card X.QT := hcardE
      _ = (2 ^ (X.n 0 * (m - 3)) * 2 ^ (2 * X.n 0)) * Nat.card X.QT := by
          rw [hpow]
      _ = 2 ^ (2 * X.n 0) * (2 ^ (X.n 0 * (m - 3)) * Nat.card X.QT) := by ring
  have hpos : 0 < 2 ^ (2 * X.n 0) :=
    Nat.pow_pos (a := 2) (n := 2 * X.n 0) (by norm_num)
  exact Nat.eq_of_mul_eq_mul_left hpos hmain

private theorem conjSub_tau_normGi_zero :
    conjSub X.τ (X.normGi X.QT 0) = X.normGi X.QT 2 :=
  X.conjSub_normGi_of_mem_normalizer X.tau_mem_normalizer_QT
    (by simpa using X.zpow_smul_vert 1 0)

private theorem E_two_eq_pCoreOf_two (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.E X.QT 2 = pCoreOf 2 (X.normGi X.QT 2) := by
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  have hE0 : X.E X.QT 0 = pCoreOf 2 (X.normGi X.QT 0) := X.E_eq_pCoreOf hSK
  rw [X.E_two_eq, show conjSub X.τ (X.E X.QT 0) =
      Subgroup.map (MulAut.conj X.τ).toMonoidHom (X.E X.QT 0) from rfl, hE0,
    ← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj X.τ)
      (X.normGi X.QT 0)]
  congr 1
  exact X.conjSub_tau_normGi_zero

private theorem K_le_normalizer_Ztau_one (hSK : X.IsSK X.QT) :
    X.K ≤ Subgroup.normalizer (X.Ztau 1 : Set G) := by
  intro k hk
  have hkM2 : k ∈ X.normGi X.QT 2 := hSK.K_le_normGi 2 hk
  have hkN : k ∈ Subgroup.normalizer (oTwoPrime (X.normGi X.QT 2) : Set G) :=
    le_normalizer_oTwoPrime (X.normGi X.QT 2) hkM2
  rw [X.Ztau_eq 1, Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub k (centerOf (X.Lst X.QT 2)) = centerOf (X.Lst X.QT 2)
  exact CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer
    (CFSG.Quasithin.normalizer_le_normalizer_centerOf _ hkN)

private theorem K_le_normalizer_Etau_one (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.K ≤ Subgroup.normalizer (X.Etau 1 : Set G) := by
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  rw [X.Etau_eq, show (2 : ℤ) * 1 = 2 by norm_num,
    X.E_two_eq_pCoreOf_two hGT hs hodd h5 hX]
  exact (hSK.K_le_normGi 2).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.normGi X.QT 2))

private theorem skP_le_normGi_two (hSK : X.IsSK X.QT) :
    X.skP X.QT ≤ X.normGi X.QT 2 := by
  rw [skP_eq_inf_two (X := X) hSK]
  exact inf_le_right

private theorem isSylowTwoOf_skP_Lst_two (hSK : X.IsSK X.QT) :
    IsSylowTwoOf (X.skP X.QT) (X.Lst X.QT 2) := by
  have hP2 := X.isPGroup_skP X.QT
  have hPleM : X.skP X.QT ≤ X.normGi X.QT 2 := X.skP_le_normGi_two hSK
  have hPleL : X.skP X.QT ≤ X.Lst X.QT 2 :=
    le_oTwoPrime_of_isPGroup hP2 hPleM
  have hSylM : IsSylowTwoOf (X.skP X.QT) (X.normGi X.QT 2) :=
    X.isSylowTwoOf_skP_two hSK
  have hLleM : X.Lst X.QT 2 ≤ X.normGi X.QT 2 := oTwoPrime_le _
  have hrelodd : ¬ 2 ∣ (X.skP X.QT).relIndex (X.Lst X.QT 2) := by
    intro h2
    apply hSylM.2.2
    change 2 ∣ (X.skP X.QT).relIndex (X.normGi X.QT 2)
    rw [← Subgroup.relIndex_mul_relIndex (X.skP X.QT) (X.Lst X.QT 2)
      (X.normGi X.QT 2) hPleL hLleM]
    exact dvd_mul_of_dvd_left h2 _
  exact F7.isSylowTwoOf_of_relIndex hPleL hP2 hrelodd

private theorem Etau_one_le_skP (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Etau 1 ≤ X.skP X.QT := by
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  have hSKP2 : IsSylowTwoOf (X.skP X.QT) (X.normGi X.QT 2) :=
    X.isSylowTwoOf_skP_two hSK
  have hEt : X.E X.QT 2 = pCoreOf 2 (X.normGi X.QT 2) :=
    X.E_two_eq_pCoreOf_two hGT hs hodd h5 hX
  rw [X.Etau_eq, show (2 : ℤ) * 1 = 2 by norm_num, hEt]
  exact CFSG.Quasithin.RonanF713.isSylowTwoOf_pCoreOf_le_loc hSKP2
private theorem commutator_Etau_one_skP_eq_bot_of_not_le (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hZ : ¬ X.Ztau 1 ≤ X.E X.QT 0) :
    ⁅X.Etau 1, X.skP X.QT⁆ = ⊥ := by
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  have hNQ := X.natQuot_M hGT hs hodd h5 hX
  have hE_eq : X.E X.QT 0 = pCoreOf 2 (X.normGi X.QT 0) := X.E_eq_pCoreOf hSK
  have hE_le_P := X.E_le_skP hSK
  have hEtau_le_P : X.Etau 1 ≤ X.skP X.QT :=
    X.Etau_one_le_skP hGT hs hodd h5 hX
  have hP_le_Lst2 := (X.isSylowTwoOf_skP_Lst_two hSK).1
  have hE_le_Lst2 : X.E X.QT 0 ≤ X.Lst X.QT 2 := hE_le_P.trans hP_le_Lst2
  have hZtau_eq : X.Ztau 1 = centerOf (X.Lst X.QT 2) := by
    simpa using X.Ztau_eq 1
  have hZtau_le_Etau : X.Ztau 1 ≤ X.Etau 1 := X.Ztau_le_Etau hNQ.Z_le 1
  have hE_NZtau : X.E X.QT 0 ≤
      Subgroup.normalizer (X.Ztau 1 : Set G) := by
    rw [hZtau_eq]
    intro e he
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub e (centerOf (X.Lst X.QT 2)) = centerOf (X.Lst X.QT 2)
    exact CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer
      (CFSG.Quasithin.normalizer_le_normalizer_centerOf _
        (Subgroup.le_normalizer (hE_le_Lst2 he)))
  have hsupP : X.Ztau 1 ⊔ X.E X.QT 0 = X.skP X.QT := by
    refine eq_skP_of_K_invariant_zero (X := X) le_sup_right ?_ ?_ ?_
    · exact sup_le (hZtau_le_Etau.trans hEtau_le_P) hE_le_P
    · have hKE := X.K_le_normalizer_E_QT
      exact A1a.le_normalizer_sup (X.K_le_normalizer_Ztau_one hSK) hKE
    · intro h
      exact hZ (le_sup_left.trans h)
  have hDed := Subgroup.inf_sup_assoc_of_le (H := X.E X.QT 0) (K := X.Etau 1)
    (N := X.Ztau 1) hE_NZtau hZtau_le_Etau
  rw [sup_comm (X.E X.QT 0) (X.Ztau 1), hsupP,
    inf_eq_left.mpr hEtau_le_P] at hDed
  have hEel := X.isElemAbelian_E_QT hGT hs hodd h5 hX
  have hE_C_E : X.E X.QT 0 ≤
      Subgroup.centralizer (X.E X.QT 0 : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.2 hEel.1
  have hE_C_Ztau : X.E X.QT 0 ≤
      Subgroup.centralizer (X.Ztau 1 : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzC : z ∈ Subgroup.centralizer (X.Lst X.QT 2 : Set G) := by
      rw [hZtau_eq] at hz
      exact (Subgroup.mem_inf.mp hz).2
    exact ((Subgroup.mem_centralizer_iff.mp hzC) e (hE_le_Lst2 he)).symm
  have hE_C_P : X.E X.QT 0 ≤
      Subgroup.centralizer (X.skP X.QT : Set G) := by
    have h := CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hE_C_E hE_C_Ztau
    rwa [sup_comm, hsupP] at h
  have hZ_C_P : X.Ztau 1 ≤
      Subgroup.centralizer (X.skP X.QT : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hzC : z ∈ Subgroup.centralizer (X.Lst X.QT 2 : Set G) := by
      rw [hZtau_eq] at hz
      exact (Subgroup.mem_inf.mp hz).2
    exact (Subgroup.mem_centralizer_iff.mp hzC) p (hP_le_Lst2 hp)
  have hEtauP : ⁅X.Etau 1, X.skP X.QT⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← hDed]
    exact sup_le (inf_le_right.trans hE_C_P) hZ_C_P
  exact hEtauP

private theorem commutator_E_skP_eq_bot_of_Etau (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (h : ⁅X.Etau 1, X.skP X.QT⁆ = ⊥) :
    ⁅X.E X.QT 0, X.skP X.QT⁆ = ⊥ := by
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  have hE_eq : X.E X.QT 0 = pCoreOf 2 (X.normGi X.QT 0) := X.E_eq_pCoreOf hSK
  obtain ⟨t, ht, ht02, -, ht2P⟩ := IsSK.exists_t X hSK
  have hPmap : Subgroup.map (MulAut.conj t).toMonoidHom (X.skP X.QT) =
      X.skP X.QT := by
    change conjSub t (X.skP X.QT) = X.skP X.QT
    exact IsSK.conjSub_skP X ht.1 ht02
  have hEtmap : Subgroup.map (MulAut.conj t).toMonoidHom (X.Etau 1) =
      X.E X.QT 0 := by
    change conjSub t (X.Etau 1) = X.E X.QT 0
    rw [X.Etau_eq, show (2 : ℤ) * 1 = 2 by norm_num,
      ← IsSK.conjSub_E_zero (X := X) ht.1 ht02, ← conjSub_mul]
    have ht2P' : t * t ∈ X.skP X.QT := by
      have h := ht2P
      rwa [pow_two] at h
    have hmem : t * t ∈ Subgroup.normalizer (X.E X.QT 0 : Set G) := by
      rw [hE_eq]
      exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.normGi X.QT 0))
        ((show X.skP X.QT ≤ X.normGi X.QT 0 from inf_le_right) ht2P')
    have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hmem
    change Subgroup.map (MulAut.conj (t * t)).toMonoidHom (X.E X.QT 0) =
      X.E X.QT 0
    exact hmap
  have hEP : ⁅X.E X.QT 0, X.skP X.QT⁆ = ⊥ := by
    have hmap := congrArg (Subgroup.map (MulAut.conj t).toMonoidHom) h
    rw [Subgroup.map_commutator, Subgroup.map_bot, hEtmap, hPmap] at hmap
    exact hmap
  exact hEP

private theorem commutator_E_skP_ne_bot (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ⁅X.E X.QT 0, X.skP X.QT⁆ ≠ ⊥ := by
  intro hEP
  have hNQ := X.natQuot_M hGT hs hodd h5 hX
  have hE_NZM := X.E_le_normalizer_ZM
  have hrelCent : relCent (X.E X.QT 0) X.ZM (X.skP X.QT) =
      X.E X.QT 0 := by
    apply le_antisymm
    · intro x hx
      exact hx.1
    · intro e he
      refine (mem_relCent hE_NZM).mpr ⟨he, ?_⟩
      intro p hp
      have h1 : ⁅e, p⁆ = 1 := by
        have hle : ⁅X.E X.QT 0, X.skP X.QT⁆ ≤ ⊥ := le_of_eq hEP
        have := Subgroup.commutator_le.mp hle e he p hp
        simpa using this
      rw [h1]
      exact X.ZM.one_mem
  have hPL0 : IsSylowTwoOf (X.skP X.QT) (X.Lst X.QT 0) :=
    X.isSylowTwoOf_skP_Lst_QT hGT hs hodd h5 hX
  have hline := hNQ.line (X.skP X.QT) hPL0
  rw [hrelCent] at hline
  have hpow : 2 ^ X.n 0 = 2 ^ (2 * X.n 0) := hline.symm.trans hNQ.index
  have hn := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
  have hn0pos : 0 < X.n 0 := by
    have h : 1 ≤ X.n 0 := (X.hyp.valency (X.vert 0)).1
    omega
  omega

private theorem Ztau_one_le_E (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Ztau 1 ≤ X.E X.QT 0 := by
  by_contra hZ
  exact X.commutator_E_skP_ne_bot hGT hs hodd h5 hX
    (X.commutator_E_skP_eq_bot_of_Etau hGT hs hodd h5 hX
      (X.commutator_Etau_one_skP_eq_bot_of_not_le hGT hs hodd h5 hX hZ))

private theorem centerOf_conjSub_general (g : G) (H : Subgroup G) :
    centerOf (conjSub g H) = conjSub g (centerOf H) :=
  (CFSG.Quasithin.centerOf_map_mulEquiv (MulAut.conj g) H).symm

theorem ZM_le_Etau_one (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.ZM ≤ X.Etau 1 := by
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  have hZ := X.Ztau_one_le_E hGT hs hodd h5 hX
  obtain ⟨t, ht, ht02, ht20⟩ := hSK.exists_swap₁
  have hZtau_eq : X.Ztau 1 = centerOf (X.Lst X.QT 2) := by
    simpa using X.Ztau_eq 1
  have hL2 : conjSub t (X.Lst X.QT 2) = X.Lst X.QT 0 := X.conjSub_Lst_of ht.1 ht20
  have hZt : conjSub t (X.Ztau 1) = X.ZM := by
    rw [hZtau_eq, ← centerOf_conjSub_general, hL2]
    rfl
  have hEt : conjSub t (X.E X.QT 0) = X.Etau 1 := by
    rw [X.Etau_eq, show (2 : ℤ) * 1 = 2 by norm_num]
    exact IsSK.conjSub_E_zero (X := X) ht ht02
  have h := conjSub_mono t hZ
  rwa [hZt, hEt] at h

private theorem Etau_one_not_le_E (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ¬ X.Etau 1 ≤ X.E X.QT 0 := by
  intro hle
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  have hE_eq : X.E X.QT 0 = pCoreOf 2 (X.normGi X.QT 0) := X.E_eq_pCoreOf hSK
  have hE2le : X.E X.QT 2 ≤ X.E X.QT 0 := by
    rwa [X.Etau_eq, show (2 : ℤ) * 1 = 2 by norm_num] at hle
  have hcardE2 : Nat.card ↥(X.E X.QT 2) = Nat.card ↥(X.E X.QT 0) := by
    rw [X.E_two_eq]
    exact card_conjSub X.τ (X.E X.QT 0)
  have hNQ := X.natQuot_M hGT hs hodd h5 hX
  haveI : Finite ↥(X.E X.QT 0) :=
    finite_of_le_stabilizer X.hyp (H := X.E X.QT 0)
      (hNQ.E_le.trans ((oTwoPrime_le (X.normGi X.QT 0)).trans (X.normGi_le_Gi X.QT 0)))
  have hE2eq : X.E X.QT 2 = X.E X.QT 0 :=
    Subgroup.eq_of_le_of_card_ge hE2le (by rw [hcardE2])
  obtain ⟨t, ht, ht02, -, -⟩ := IsSK.exists_t X hSK
  have hME : X.normGi X.QT 0 ≤ Subgroup.normalizer (X.E X.QT 0 : Set G) := by
    rw [hE_eq]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.normGi X.QT 0)
  have htE : t ∈ Subgroup.normalizer (X.E X.QT 0 : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub t (X.E X.QT 0) = X.E X.QT 0
    rw [IsSK.conjSub_E_zero (X := X) ht.1 ht02, hE2eq]
  have hEeq : X.E X.QT 0 = X.QT := by
    refine eq_QT_of_normal (X := X) (D := X.E X.QT 0) X.QT_le_E ?_ hME ht.1 ht02 htE
    rw [hE2eq]
    exact le_inf le_rfl le_rfl
  have hcardE := X.card_E hGT hs hodd h5 hX hreg
  rw [hEeq] at hcardE
  haveI := X.finite_QT
  have hQtpos : 0 < Nat.card ↥X.QT := Nat.card_pos
  have hq1 : 2 ^ (X.n 0 * (m - 1)) = 1 := by
    have h1 : 2 ^ (X.n 0 * (m - 1)) * Nat.card ↥X.QT =
        1 * Nat.card ↥X.QT := by
      rw [one_mul]
      exact hcardE.symm
    exact Nat.eq_of_mul_eq_mul_right hQtpos h1
  have hexp : X.n 0 * (m - 1) = 0 := by
    have h : 2 ^ (X.n 0 * (m - 1)) = 2 ^ 0 := by simpa using hq1
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
  have hn0pos : 0 < X.n 0 := by
    have h : 1 ≤ X.n 0 := (X.hyp.valency (X.vert 0)).1
    omega
  have hmpos : 0 < m := by
    have h := hreg.1
    omega
  have hm1 : m = 1 := by
    rcases Nat.eq_zero_or_pos (m - 1) with h | h
    · omega
    · have : 0 < X.n 0 * (m - 1) := Nat.mul_pos hn0pos h
      omega
  have hm3 := X.three_le_m hGT hs hodd h5 hX hreg
  omega

private theorem sup_E_Etau_one_eq_skP (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.E X.QT 0 ⊔ X.Etau 1 = X.skP X.QT := by
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  have hE_eq : X.E X.QT 0 = pCoreOf 2 (X.normGi X.QT 0) := X.E_eq_pCoreOf hSK
  have hE_le_P := X.E_le_skP hSK
  have hEtau_le_P : X.Etau 1 ≤ X.skP X.QT :=
    X.Etau_one_le_skP hGT hs hodd h5 hX
  refine eq_skP_of_K_invariant_zero (X := X) le_sup_left ?_ ?_ ?_
  · exact sup_le hE_le_P hEtau_le_P
  · have hKE := X.K_le_normalizer_E_QT
    exact A1a.le_normalizer_sup hKE
      (X.K_le_normalizer_Etau_one hGT hs hodd h5 hX)
  · intro h
    exact X.Etau_one_not_le_E hGT hs hodd h5 hX hreg
      (le_sup_right.trans h)

private theorem K_le_normalizer_ZM (hSK : X.IsSK X.QT) :
    X.K ≤ Subgroup.normalizer (X.ZM : Set G) := by
  intro k hk
  have hkM0 : k ∈ X.normGi X.QT 0 := hSK.K_le_normGi 0 hk
  have hkN : k ∈ Subgroup.normalizer (oTwoPrime (X.normGi X.QT 0) : Set G) :=
    le_normalizer_oTwoPrime (X.normGi X.QT 0) hkM0
  show k ∈ Subgroup.normalizer (centerOf (X.Lst X.QT 0) : Set G)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub k (centerOf (X.Lst X.QT 0)) = centerOf (X.Lst X.QT 0)
  exact CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer
    (CFSG.Quasithin.normalizer_le_normalizer_centerOf _ hkN)

private theorem ZM_inf_Ztau_one_eq_QT (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.ZM ⊓ X.Ztau 1 = X.QT := by
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  have hP : ¬ X.skP X.QT ≤ X.Q 0 ∨ 2 ≤ X.n 0 :=
    Or.inl (X.not_skP_QT_le_Q_zero hGT hs hodd h5 hX)
  have hNQ := X.natQuot_M hGT hs hodd h5 hX
  have hZtau_E2 : X.Ztau 1 ≤ X.E X.QT 2 := by
    have h := X.Ztau_le_Etau hNQ.Z_le 1
    rwa [X.Etau_eq, mul_one] at h
  have hQt_ZM : X.QT ≤ X.ZM := X.QT_le_centerOf_Lst hGT hs hodd h5 hX
  have hτQt := X.conjSub_tau_QT
  have hQt_Ztau : X.QT ≤ X.Ztau 1 := by
    show X.QT ≤ conjSub (X.τ ^ (1 : ℤ)) X.ZM
    rw [zpow_one, ← hτQt]
    exact conjSub_mono X.τ hQt_ZM
  have hDE : X.ZM ⊓ X.Ztau 1 ≤ X.E X.QT 0 ⊓ X.E X.QT 2 :=
    le_inf (inf_le_left.trans hNQ.Z_le) (inf_le_right.trans hZtau_E2)
  have hKZM : X.K ≤ Subgroup.normalizer (X.ZM : Set G) := X.K_le_normalizer_ZM hSK
  have hKZtau : X.K ≤ Subgroup.normalizer (X.Ztau 1 : Set G) :=
    X.K_le_normalizer_Ztau_one hSK
  have hKD : X.K ≤ Subgroup.normalizer ((X.ZM ⊓ X.Ztau 1 : Subgroup G) : Set G) :=
    (le_inf hKZM hKZtau).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hLstD : X.Lst X.QT 0 ≤
      Subgroup.normalizer ((X.ZM ⊓ X.Ztau 1 : Subgroup G) : Set G) :=
    (Subgroup.le_centralizer_iff.1 (inf_le_left.trans inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hM0D : X.normGi X.QT 0 ≤
      Subgroup.normalizer ((X.ZM ⊓ X.Ztau 1 : Subgroup G) : Set G) := by
    rw [X.normGi_eq_Lst_sup_K hSK hP]
    exact sup_le hLstD hKD
  obtain ⟨t, ht, ht02, ht20⟩ := hSK.exists_swap₁
  have hL2 : conjSub t (X.Lst X.QT 0) = X.Lst X.QT 2 := X.conjSub_Lst_of ht.1 ht02
  have hL0 : conjSub t (X.Lst X.QT 2) = X.Lst X.QT 0 := X.conjSub_Lst_of ht.1 ht20
  have hZt' : conjSub t X.ZM = X.Ztau 1 := by
    rw [X.Ztau_eq 1]
    show conjSub t (centerOf (X.Lst X.QT 0)) = centerOf (X.Lst X.QT 2)
    rw [← centerOf_conjSub_general, hL2]
  have hZt : conjSub t (X.Ztau 1) = X.ZM := by
    rw [X.Ztau_eq 1]
    show conjSub t (centerOf (X.Lst X.QT 2)) = centerOf (X.Lst X.QT 0)
    rw [← centerOf_conjSub_general, hL0]
  have htD : t ∈ Subgroup.normalizer ((X.ZM ⊓ X.Ztau 1 : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub t (X.ZM ⊓ X.Ztau 1) = X.ZM ⊓ X.Ztau 1
    rw [conjSub_inf, hZt', hZt, inf_comm]
  refine eq_QT_of_normal (X := X) (D := X.ZM ⊓ X.Ztau 1)
    (le_inf hQt_ZM hQt_Ztau) hDE hM0D ht ht02 htD

private theorem card_Ztau_one : Nat.card ↥(X.Ztau 1) = Nat.card ↥X.ZM :=
  card_conjSub (X.τ ^ (1 : ℤ)) X.ZM

private theorem E_inf_Etau_one_card (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    Nat.card ↥(X.E X.QT 0 ⊓ X.Etau 1) =
      2 ^ (X.n 0 * (m - 2)) * Nat.card ↥X.QT := by
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  haveI := X.finite_QT
  have hsup := X.sup_E_Etau_one_eq_skP hGT hs hodd h5 hX hreg
  have hcardP := X.card_skP hGT hs hodd h5 hX hreg
  have hcardE := X.card_E hGT hs hodd h5 hX hreg
  have hE_le_P := X.E_le_skP hSK
  have hP_le_M2 : X.skP X.QT ≤ X.normGi X.QT 2 := X.skP_le_normGi_two hSK
  have hEt : X.Etau 1 = pCoreOf 2 (X.normGi X.QT 2) := by
    rw [X.Etau_eq, show (2 : ℤ) * 1 = 2 by norm_num]
    exact X.E_two_eq_pCoreOf_two hGT hs hodd h5 hX
  have hnorm : ∀ b ∈ X.E X.QT 0, ∀ n ∈ X.Etau 1,
      b * n * b⁻¹ ∈ X.Etau 1 := by
    intro b hb n hn
    rw [hEt] at hn ⊢
    exact (Subgroup.le_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.normGi X.QT 2)))
      b (hP_le_M2 (hE_le_P hb)) n hn
  have hprod :=
    CFSG.Timmesfeld.LocalTwoSubgroups.FrobeniusFixedSpaceBounds.card_sup_mul_card_inf
      (X.E X.QT 0) (X.Etau 1) hnorm
  have hcardEt : Nat.card ↥(X.Etau 1) = Nat.card ↥(X.E X.QT 0) := by
    rw [X.Etau_eq, show (2 : ℤ) * 1 = 2 by norm_num, X.E_two_eq]
    exact card_conjSub X.τ (X.E X.QT 0)
  rw [hsup, hcardP, hcardE, hcardEt, hcardE] at hprod
  have hpos : 0 < 2 ^ (X.n 0 * m) * Nat.card ↥X.QT :=
    Nat.mul_pos (Nat.pow_pos (by norm_num)) Nat.card_pos
  have harith : (2 ^ (X.n 0 * (m - 1)) * Nat.card ↥X.QT) *
        (2 ^ (X.n 0 * (m - 1)) * Nat.card ↥X.QT) =
      (2 ^ (X.n 0 * m) * Nat.card ↥X.QT) *
        (2 ^ (X.n 0 * (m - 2)) * Nat.card ↥X.QT) := by
    have hm2 : 2 ≤ m := by
      have := X.three_le_m hGT hs hodd h5 hX hreg
      omega
    have h1 : (2:ℕ)^(X.n 0*(m-1)) = 2^(X.n 0*(m-2)) * 2^(X.n 0) := by
      rw [← pow_add]; congr 1
      rw [show m - 1 = (m - 2) + 1 by omega, Nat.mul_add, Nat.mul_one]
    have h2 : (2:ℕ)^(X.n 0*m) =
        2^(X.n 0*(m-2)) * 2^(X.n 0) * 2^(X.n 0) := by
      have h : X.n 0*m = X.n 0*(m-2) + X.n 0 + X.n 0 := by
        calc X.n 0*m = X.n 0*((m-2)+1+1) := by
              rw [show (m-2)+1+1 = m by omega]
          _ = X.n 0*(m-2) + X.n 0 + X.n 0 := by
              rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      rw [h, ← pow_add, ← pow_add]
    rw [h1, h2]
    ring
  have hmain : 2 ^ (X.n 0 * m) * Nat.card ↥X.QT *
        Nat.card ↥(X.E X.QT 0 ⊓ X.Etau 1) =
      2 ^ (X.n 0 * m) * Nat.card ↥X.QT *
        (2 ^ (X.n 0 * (m - 2)) * Nat.card ↥X.QT) := by
    rw [hprod]
    exact harith
  exact Nat.eq_of_mul_eq_mul_left hpos hmain

private theorem ZM_sup_Ztau_one_card (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    Nat.card ↥(X.ZM ⊔ X.Ztau 1) =
      2 ^ (X.n 0 * (2 * m - 6)) * Nat.card ↥X.QT := by
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  haveI := X.finite_QT
  have hNQ := X.natQuot_M hGT hs hodd h5 hX
  have hD := X.ZM_inf_Ztau_one_eq_QT hGT hs hodd h5 hX
  have hcardZM := X.card_ZM hGT hs hodd h5 hX hreg
  have hcardZtau := X.card_Ztau_one
  have hE_le_P := X.E_le_skP hSK
  have hP_le_Lst2 := (X.isSylowTwoOf_skP_Lst_two hSK).1
  have hZtau_eq : X.Ztau 1 = centerOf (X.Lst X.QT 2) := by
    simpa using X.Ztau_eq 1
  have hnorm : ∀ b ∈ X.ZM, ∀ n ∈ X.Ztau 1,
      b * n * b⁻¹ ∈ X.Ztau 1 := by
    intro b hb n hn
    have hbL2 : b ∈ X.Lst X.QT 2 := hP_le_Lst2 (hE_le_P (hNQ.Z_le hb))
    have hnC : n ∈ Subgroup.centralizer (X.Lst X.QT 2 : Set G) := by
      rw [hZtau_eq] at hn
      exact (Subgroup.mem_inf.mp hn).2
    have hcomm : b * n = n * b :=
      (Subgroup.mem_centralizer_iff.mp hnC) b hbL2
    have heq : b * n * b⁻¹ = n := by rw [hcomm]; group
    rwa [heq]
  have hprod :=
    CFSG.Timmesfeld.LocalTwoSubgroups.FrobeniusFixedSpaceBounds.card_sup_mul_card_inf
      X.ZM (X.Ztau 1) hnorm
  rw [hD, hcardZtau, hcardZM] at hprod
  have hQtpos : 0 < Nat.card ↥X.QT := Nat.card_pos
  have hm3 := X.three_le_m hGT hs hodd h5 hX hreg
  have harith : (2 ^ (X.n 0 * (m - 3)) * Nat.card ↥X.QT) *
        (2 ^ (X.n 0 * (m - 3)) * Nat.card ↥X.QT) =
      (2 ^ (X.n 0 * (2 * m - 6)) * Nat.card ↥X.QT) * Nat.card ↥X.QT := by
    have h1 : (2:ℕ)^(X.n 0*(m-3)) * 2^(X.n 0*(m-3)) =
        2^(X.n 0*(2*m-6)) := by
      rw [← pow_add]
      congr 1
      rw [show 2*m-6 = (m-3)+(m-3) by omega, Nat.mul_add]
    calc (2^(X.n 0*(m-3))*Nat.card ↥X.QT) *
          (2^(X.n 0*(m-3))*Nat.card ↥X.QT)
        = (2^(X.n 0*(m-3))*2^(X.n 0*(m-3))) *
            (Nat.card ↥X.QT * Nat.card ↥X.QT) := by ring
      _ = (2^(X.n 0*(2*m-6))*Nat.card ↥X.QT) * Nat.card ↥X.QT := by
          rw [h1]; ring
  have hmain : Nat.card ↥(X.ZM ⊔ X.Ztau 1) * Nat.card ↥X.QT =
      (2 ^ (X.n 0 * (2 * m - 6)) * Nat.card ↥X.QT) * Nat.card ↥X.QT := by
    rw [hprod]
    exact harith
  exact Nat.mul_right_cancel hQtpos hmain

private theorem ZM_sup_Ztau_le_E_inf (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.ZM ⊔ X.Ztau 1 ≤ X.E X.QT 0 ⊓ X.Etau 1 := by
  have hNQ := X.natQuot_M hGT hs hodd h5 hX
  have hZtau_le_E : X.Ztau 1 ≤ X.E X.QT 0 :=
    X.Ztau_one_le_E hGT hs hodd h5 hX
  have hZtau_le_E2 : X.Ztau 1 ≤ X.Etau 1 := X.Ztau_le_Etau hNQ.Z_le 1
  exact sup_le (le_inf hNQ.Z_le (X.ZM_le_Etau_one hGT hs hodd h5 hX))
    (le_inf hZtau_le_E hZtau_le_E2)

theorem m_le_four {m : ℕ} (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : m ≤ 4 := by
  have hm3 := X.three_le_m hGT hs hodd h5 hX hreg
  have hNQ := X.natQuot_M hGT hs hodd h5 hX
  have hcardI := X.E_inf_Etau_one_card hGT hs hodd h5 hX hreg
  have hcardJ := X.ZM_sup_Ztau_one_card hGT hs hodd h5 hX hreg
  haveI := X.finite_QT
  haveI : Finite ↥(X.E X.QT 0 ⊓ X.Etau 1) :=
    finite_of_le_stabilizer X.hyp (H := X.E X.QT 0 ⊓ X.Etau 1)
      (inf_le_left.trans (hNQ.E_le.trans
        ((oTwoPrime_le (X.normGi X.QT 0)).trans (X.normGi_le_Gi X.QT 0))))
  have hle : X.ZM ⊔ X.Ztau 1 ≤ X.E X.QT 0 ⊓ X.Etau 1 :=
    X.ZM_sup_Ztau_le_E_inf hGT hs hodd h5 hX
  have hcardle : Nat.card ↥(X.ZM ⊔ X.Ztau 1) ≤
      Nat.card ↥(X.E X.QT 0 ⊓ X.Etau 1) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  rw [hcardJ, hcardI] at hcardle
  have hQtpos : 0 < Nat.card ↥X.QT := Nat.card_pos
  have hpowle : 2 ^ (X.n 0 * (2 * m - 6)) ≤ 2 ^ (X.n 0 * (m - 2)) :=
    Nat.le_of_mul_le_mul_right hcardle hQtpos
  have hexple := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpowle
  have hn0pos : 0 < X.n 0 := by
    have h : 1 ≤ X.n 0 := (X.hyp.valency (X.vert 0)).1
    omega
  have hsub : 2 * m - 6 ≤ m - 2 := Nat.le_of_mul_le_mul_left hexple hn0pos
  omega

theorem centerOf_eq_QT_of_m_eq_three {m : ℕ} (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) (hm : m = 3) : X.ZM = X.QT := by
  have hZ := X.card_ZM hGT hs hodd h5 hX hreg
  have hQtZ : X.QT ≤ X.ZM := X.QT_le_centerOf_Lst hGT hs hodd h5 hX
  have hNQ := X.natQuot_M hGT hs hodd h5 hX
  haveI : Finite ↥X.ZM :=
    finite_of_le_stabilizer X.hyp (H := X.ZM)
      (hNQ.Z_le.trans (hNQ.E_le.trans
        ((oTwoPrime_le (X.normGi X.QT 0)).trans (X.normGi_le_Gi X.QT 0))))
  refine (Subgroup.eq_of_le_of_card_ge hQtZ ?_).symm
  rw [hZ, hm]
  simp

theorem E_inf_E_two {m : ℕ} (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) (hm : m = 4) :
    X.E X.QT 0 ⊓ X.Etau 1 = X.ZM ⊔ X.Ztau 1 := by
  have hcardI := X.E_inf_Etau_one_card hGT hs hodd h5 hX hreg
  have hcardJ := X.ZM_sup_Ztau_one_card hGT hs hodd h5 hX hreg
  rw [hm, show 4 - 2 = 2 by norm_num] at hcardI
  rw [hm, show 2 * 4 - 6 = 2 by norm_num] at hcardJ
  have hle : X.ZM ⊔ X.Ztau 1 ≤ X.E X.QT 0 ⊓ X.Etau 1 :=
    X.ZM_sup_Ztau_le_E_inf hGT hs hodd h5 hX
  have hNQ := X.natQuot_M hGT hs hodd h5 hX
  haveI : Finite ↥(X.E X.QT 0 ⊓ X.Etau 1) :=
    finite_of_le_stabilizer X.hyp (H := X.E X.QT 0 ⊓ X.Etau 1)
      (inf_le_left.trans (hNQ.E_le.trans
        ((oTwoPrime_le (X.normGi X.QT 0)).trans (X.normGi_le_Gi X.QT 0))))
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hcardI, hcardJ]

private theorem conjSub_tau_inv_Lst_two :
    conjSub X.τ⁻¹ (X.Lst X.QT 2) = X.Lst X.QT 0 := by
  have hL : conjSub X.τ (X.Lst X.QT 0) = X.Lst X.QT 2 :=
    X.conjSub_Lst_of X.tau_mem_normalizer_QT (by simpa using X.zpow_smul_vert 1 0)
  rw [← hL, conjSub_conjSub_inv]

private theorem isSylowTwoOf_conjSub_tau_inv_skP (hSK : X.IsSK X.QT) :
    IsSylowTwoOf (conjSub X.τ⁻¹ (X.skP X.QT)) (X.Lst X.QT 0) := by
  have h := F7.isSylowTwoOf_conj (X.isSylowTwoOf_skP_Lst_two hSK) X.τ⁻¹
  rwa [conjSub_tau_inv_Lst_two] at h

private theorem conjSub_tau_inv_skP_le_Q_neg_one :
    conjSub X.τ⁻¹ (X.skP X.QT) ≤ X.Q (-1) := by
  have hQadd : X.Q (-1) = conjSub X.τ⁻¹ (X.Q 1) := by
    have h := X.Q_add (-1) 1
    norm_num at h
    simpa using h
  rw [hQadd]
  exact conjSub_mono X.τ⁻¹ (show X.skP X.QT ≤ X.Q 1 from inf_le_left)

private theorem conjSub_tau_inv_skP_le_Gi_neg_two :
    conjSub X.τ⁻¹ (X.skP X.QT) ≤ X.Gi (-2) := by
  have h := (X.Q_le_Gi_adj (-1)).trans inf_le_left
  rw [show (-1 : ℤ) - 1 = -2 by norm_num] at h
  exact X.conjSub_tau_inv_skP_le_Q_neg_one.trans h

private theorem conjSub_tau_inv_skP_le_normalizer :
    conjSub X.τ⁻¹ (X.skP X.QT) ≤
      Subgroup.normalizer (X.QT : Set G) := by
  have hPN : X.skP X.QT ≤ Subgroup.normalizer (X.QT : Set G) :=
    (show X.skP X.QT ≤ X.normGi X.QT 0 from inf_le_right).trans inf_le_left
  have hN : conjSub X.τ⁻¹ (Subgroup.normalizer (X.QT : Set G)) =
      Subgroup.normalizer (X.QT : Set G) := by
    rw [← conjSub_normalizer,
      show conjSub X.τ⁻¹ X.QT = X.QT from
        CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer
          (inv_mem X.tau_mem_normalizer_QT)]
  exact (conjSub_mono X.τ⁻¹ hPN).trans_eq hN

private theorem conjSub_tau_inv_skP_le_Lst_neg_two (hSK : X.IsSK X.QT) :
    conjSub X.τ⁻¹ (X.skP X.QT) ≤ X.Lst X.QT (-2) := by
  have hSyl := X.isSylowTwoOf_conjSub_tau_inv_skP hSK
  have hM2 : conjSub X.τ⁻¹ (X.skP X.QT) ≤ X.normGi X.QT (-2) :=
    le_inf (X.conjSub_tau_inv_skP_le_normalizer)
      (X.conjSub_tau_inv_skP_le_Gi_neg_two)
  exact le_oTwoPrime_of_isPGroup hSyl.2.1 hM2

private theorem conjSub_tau_inv_E : conjSub X.τ⁻¹ (X.E X.QT 0) = X.Etau (-1) := by
  rw [show X.Etau (-1) = conjSub (X.τ ^ (-1 : ℤ)) (X.E X.QT 0) from rfl,
    zpow_neg_one]

private theorem conjSub_tau_inv_Etau_one :
    conjSub X.τ⁻¹ (X.Etau 1) = X.E X.QT 0 := by
  rw [X.Etau_eq, show (2 : ℤ) * 1 = 2 by norm_num, X.E_two_eq]
  exact conjSub_conjSub_inv X.τ (X.E X.QT 0)

private theorem conjSub_tau_inv_ZM : conjSub X.τ⁻¹ X.ZM = X.Ztau (-1) := by
  rw [show X.Ztau (-1) = conjSub (X.τ ^ (-1 : ℤ)) X.ZM from rfl, zpow_neg_one]

private theorem conjSub_tau_inv_Ztau_one :
    conjSub X.τ⁻¹ (X.Ztau 1) = X.ZM := by
  rw [show X.Ztau 1 = conjSub (X.τ ^ (1 : ℤ)) X.ZM from rfl, zpow_one]
  exact conjSub_conjSub_inv X.τ X.ZM

private theorem sup_Etau_neg_one_E_eq_conjSub_tau_inv_skP
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s)
    (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Etau (-1) ⊔ X.E X.QT 0 = conjSub X.τ⁻¹ (X.skP X.QT) := by
  have hsup := X.sup_E_Etau_one_eq_skP hGT hs hodd h5 hX hreg
  have h := congrArg (conjSub X.τ⁻¹) hsup
  rw [conjSub_sup] at h
  rwa [X.conjSub_tau_inv_Etau_one, X.conjSub_tau_inv_E] at h

private theorem not_skP_le_conjSub_tau_inv_skP (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ¬ X.skP X.QT ≤ conjSub X.τ⁻¹ (X.skP X.QT) := by
  intro hPP'
  have hP2 := X.isPGroup_skP X.QT
  have hP_Qm1 : X.skP X.QT ≤ X.Q (-1) :=
    hPP'.trans X.conjSub_tau_inv_skP_le_Q_neg_one
  have hP_Gm1 : X.skP X.QT ≤ X.Gi (-1) :=
    hP_Qm1.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 (X.Gi (-1)))
  have hP_G1 : X.skP X.QT ≤ X.Gi 1 :=
    (show X.skP X.QT ≤ X.Q 1 from inf_le_left).trans
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (X.Gi 1))
  have hP_G0 : X.skP X.QT ≤ X.Gi 0 :=
    (show X.skP X.QT ≤ X.normGi X.QT 0 from inf_le_right).trans
      (X.normGi_le_Gi X.QT 0)
  have hne : X.vert 1 ≠ X.vert (-1) := by
    intro h
    have := X.vert_injective h
    norm_num at this
  have hleQ0 := le_pCoreOf_of_isPGroup_fixes_two X.hyp hP2 hP_G0
    (X.adj 0) (by simpa using (X.adj (-1)).symm) hne
    (fun y hy => MulAction.mem_stabilizer_iff.mp (hP_G1 hy))
    (fun y hy => MulAction.mem_stabilizer_iff.mp (hP_Gm1 hy))
  exact X.not_skP_QT_le_Q_zero hGT hs hodd h5 hX hleQ0

theorem E_minus_inf_E_inf_E_two {m : ℕ} (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) (hm : m = 4) :
    X.Etau (-1) ⊓ X.E X.QT 0 ⊓ X.Etau 1 = X.ZM := by
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  have hNQ := X.natQuot_M hGT hs hodd h5 hX
  set P : Subgroup G := X.skP X.QT with hPdef
  set P' : Subgroup G := conjSub X.τ⁻¹ (X.skP X.QT) with hP'def
  have hPL0 : IsSylowTwoOf P (X.Lst X.QT 0) := X.isSylowTwoOf_skP_Lst hSK
  have hP'syl : IsSylowTwoOf P' (X.Lst X.QT 0) :=
    X.isSylowTwoOf_conjSub_tau_inv_skP hSK
  have hP'leLm2 : P' ≤ X.Lst X.QT (-2) :=
    X.conjSub_tau_inv_skP_le_Lst_neg_two hSK
  have hsup' : X.Etau (-1) ⊔ X.E X.QT 0 = P' :=
    X.sup_Etau_neg_one_E_eq_conjSub_tau_inv_skP hGT hs hodd h5 hX hreg
  have hE_le_P' : X.E X.QT 0 ≤ P' := by rw [← hsup']; exact le_sup_right
  have hE_inf := X.E_inf_E_two hGT hs hodd h5 hX hreg hm
  have hthree : X.Etau (-1) ⊓ X.E X.QT 0 = X.Ztau (-1) ⊔ X.ZM := by
    have h := congrArg (conjSub X.τ⁻¹) hE_inf
    rw [conjSub_inf, conjSub_sup, X.conjSub_tau_inv_E,
      X.conjSub_tau_inv_Etau_one, X.conjSub_tau_inv_ZM,
      X.conjSub_tau_inv_Ztau_one] at h
    exact h
  have hC : X.Etau (-1) ⊓ X.E X.QT 0 ≤
      Subgroup.centralizer (P' : Set G) := by
    rw [hthree, X.Ztau_eq (-1), show (2 : ℤ) * (-1) = -2 by norm_num]
    exact sup_le (inf_le_right.trans (Subgroup.centralizer_le hP'leLm2))
      (inf_le_right.trans (Subgroup.centralizer_le hP'syl.1))
  have hcardZM4 := X.card_ZM hGT hs hodd h5 hX hreg
  have hcardJ := X.ZM_sup_Ztau_one_card hGT hs hodd h5 hX hreg
  rw [hm, show 4 - 3 = 1 by norm_num, mul_one] at hcardZM4
  rw [hm, show 2 * 4 - 6 = 2 by norm_num] at hcardJ
  have hJ : Nat.card ↥(X.ZM ⊔ X.Ztau 1) = 2 ^ X.n 0 * Nat.card ↥X.ZM := by
    rw [hcardJ, hcardZM4, ← Nat.mul_assoc, ← pow_add, mul_two]
  have hZtauM : conjSub X.τ (X.Ztau (-1)) = X.ZM := by
    rw [X.conjSub_tau_Ztau, show (-1 : ℤ) + 1 = 0 by norm_num, X.Ztau_zero]
  have hZtau1 : conjSub X.τ X.ZM = X.Ztau 1 := by
    rw [← X.Ztau_zero, X.conjSub_tau_Ztau, zero_add]
  have hcardSup : Nat.card ↥(X.Ztau (-1) ⊔ X.ZM) =
      Nat.card ↥(X.ZM ⊔ X.Ztau 1) := by
    rw [← card_conjSub X.τ (X.Ztau (-1) ⊔ X.ZM)]
    congr 1
    rw [conjSub_sup, hZtauM, hZtau1]
  have hthreeCard : Nat.card ↥(X.Etau (-1) ⊓ X.E X.QT 0) =
      2 ^ X.n 0 * Nat.card ↥X.ZM := by
    rw [hthree, hcardSup, hJ]
  have hrelP' := X.relCent_eq_of_le_centralizer hNQ hP'syl inf_le_right hC hthreeCard
  have hC_P : X.E X.QT 0 ⊓ X.Etau 1 ≤
      Subgroup.centralizer (P : Set G) := by
    rw [hE_inf, X.Ztau_eq 1, show (2 : ℤ) * 1 = 2 by norm_num]
    exact sup_le (inf_le_right.trans (Subgroup.centralizer_le hPL0.1))
      (inf_le_right.trans
        (Subgroup.centralizer_le (X.isSylowTwoOf_skP_Lst_two hSK).1))
  have hthreeCardP : Nat.card ↥(X.E X.QT 0 ⊓ X.Etau 1) =
      2 ^ X.n 0 * Nat.card ↥X.ZM := by
    rw [hE_inf, hJ]
  have hrelP := X.relCent_eq_of_le_centralizer hNQ hPL0 inf_le_left hC_P hthreeCardP
  have hnot : ¬ P ≤ P' ⊔ X.E X.QT 0 := by
    have hsupPE : P' ⊔ X.E X.QT 0 = P' :=
      sup_eq_left.mpr hE_le_P'
    rw [hsupPE]
    exact X.not_skP_le_conjSub_tau_inv_skP hGT hs hodd h5 hX
  have hlines := hNQ.lines_inf P P' hPL0 hP'syl hnot
  rw [hrelP, hrelP'] at hlines
  rw [show X.Etau (-1) ⊓ X.E X.QT 0 ⊓ X.Etau 1 =
      (X.E X.QT 0 ⊓ X.Etau 1) ⊓ (X.Etau (-1) ⊓ X.E X.QT 0) by ac_rfl,
    hlines.1]

theorem E_minus_inf_E_inf_E_two_inf_E_four {m : ℕ} (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) (hm : m = 4) :
    X.Etau (-1) ⊓ X.E X.QT 0 ⊓ X.Etau 1 ⊓ X.Etau 2 = X.QT := by
  have h1 := X.E_minus_inf_E_inf_E_two hGT hs hodd h5 hX hreg hm
  have h2 : X.E X.QT 0 ⊓ X.Etau 1 ⊓ X.Etau 2 = X.Ztau 1 := by
    have h := congrArg (conjSub X.τ) h1
    rw [conjSub_inf, conjSub_inf] at h
    have hA : conjSub X.τ (X.Etau (-1)) = X.E X.QT 0 := by
      rw [X.conjSub_tau_Etau, show (-1 : ℤ) + 1 = 0 by norm_num, X.Etau_zero]
    have hB : conjSub X.τ (X.E X.QT 0) = X.Etau 1 := by
      rw [← X.Etau_zero, X.conjSub_tau_Etau, zero_add]
    have hC : conjSub X.τ (X.Etau 1) = X.Etau 2 := by
      rw [X.conjSub_tau_Etau, show (1 : ℤ) + 1 = 2 by norm_num]
    have hZ : conjSub X.τ X.ZM = X.Ztau 1 := by
      rw [← X.Ztau_zero, X.conjSub_tau_Ztau, zero_add]
    rw [hA, hB, hC, hZ] at h
    exact h
  have hD := X.ZM_inf_Ztau_one_eq_QT hGT hs hodd h5 hX
  rw [show X.Etau (-1) ⊓ X.E X.QT 0 ⊓ X.Etau 1 ⊓ X.Etau 2 =
      (X.Etau (-1) ⊓ X.E X.QT 0 ⊓ X.Etau 1) ⊓
        (X.E X.QT 0 ⊓ X.Etau 1 ⊓ X.Etau 2) by ac_rfl,
    h1, h2, hD]

theorem E_le_Gi_two {U : Subgroup G} (hU : X.IsSK U) :
    X.E U 0 ≤ X.Gi 2 := by
  intro e he
  obtain ⟨heQ, heN⟩ := Subgroup.mem_inf.mp he
  have heG0 : e ∈ X.Gi 0 := X.Q_le_Gi 0 heQ
  have heG1 : e ∈ X.Gi 1 := (X.Q_le_Gi_adj 0 heQ).2
  have he' : e ∈ X.normGi U 0 ⊓ X.Gi 1 :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨heN, heG0⟩, heG1⟩
  rw [hU.inf₀₁] at he'
  exact (Subgroup.mem_inf.mp he').2

theorem E_QT_le_Gi_two (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.E X.QT 0 ≤ X.Gi 2 ⊓ X.Gi (-2) := by
  have hU := X.isSK_QT hGT hs hodd h5 hX
  refine le_inf (X.E_le_Gi_two hU) ?_
  intro e he
  obtain ⟨heQ, heN⟩ := Subgroup.mem_inf.mp he
  have he0 : e • X.vert 0 = X.vert 0 := MulAction.mem_stabilizer_iff.mp (X.Q_le_Gi 0 heQ)
  have hem1 : e ∈ X.Gi (-1) := (X.Q_le_Gi_adj 0 heQ).1
  have heM : e ∈ X.normGi X.QT (-1) := Subgroup.mem_inf.mpr ⟨heN, hem1⟩
  have hconjQt := X.conjSub_tau_QT
  have hGi : X.Gi 1 = conjSub X.τ (X.Gi (-1)) := by
    have h := X.Gi_add 1 (-1)
    rw [show (-1 : ℤ) + 2 * 1 = 1 by norm_num, zpow_one] at h
    exact h
  have hconj : conjSub X.τ (X.normGi X.QT (-1)) = X.normGi X.QT 1 := by
    change conjSub X.τ (Subgroup.normalizer (X.QT : Set G) ⊓ X.Gi (-1)) =
      Subgroup.normalizer (X.QT : Set G) ⊓ X.Gi 1
    rw [conjSub_inf, hGi]
    congr 1
    rw [← conjSub_normalizer, hconjQt]
  set h : G := X.τ * e * X.τ⁻¹ with hh_def
  have hh : h ∈ X.normGi X.QT 1 := by
    rw [← hconj]
    refine mem_conjSub.mpr ?_
    have hEq : X.τ⁻¹ * h * X.τ = e := by rw [hh_def]; group
    rwa [hEq]
  have hpair := hU.pair h hh
  have hh2 : h • X.vert 0 = X.τ • (e • X.vert (-2)) := by
    rw [hh_def, mul_smul, mul_smul, show X.τ⁻¹ • X.vert 0 = X.vert (-2) by
      simpa using X.zpow_smul_vert (-1) 0]
  rw [hh2] at hpair
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpair
  have key : e • X.vert (-2) = X.vert (-2) := by
    rcases hpair with h0 | h2
    · have := congrArg (fun z => X.τ⁻¹ • z) h0
      simpa [mul_smul, show X.τ⁻¹ • X.vert 0 = X.vert (-2) by
        simpa using X.zpow_smul_vert (-1) 0] using this
    · exfalso
      have h1 : e • X.vert (-2) = X.vert 0 := by
        have := congrArg (fun z => X.τ⁻¹ • z) h2
        simpa [mul_smul, show X.τ⁻¹ • X.vert 2 = X.vert 0 by
          simpa using X.zpow_smul_vert (-1) 2] using this
      have h2' : X.vert (-2) = X.vert 0 := MulAction.injective e (h1.trans he0.symm)
      have h3 : (-2 : ℤ) = 0 := X.vert_injective h2'
      norm_num at h3
  exact MulAction.mem_stabilizer_iff.mpr key

end Setup

end CFSG.Quasithin.St84
