module

public import CFSG.Quasithin.H13.NQCoreFixedSpaceWitness
public import CFSG.Quasithin.H13.NQCoreWholeModuleMain
public import CFSG.Quasithin.H13.NQCoreRadicalEscape
public import CFSG.Quasithin.H13.NQCoreFixedSpaceGlue
public import CFSG.Quasithin.H13.NQCoreChiefFactorBound
public import CFSG.Quasithin.H13.NQCoreFixedSpaceSum
public import CFSG.Quasithin.SteinbergCAStrictFixedSpaceNormalClosure
public import CFSG.Quasithin.SteinbergCDExactPlaneWreathResidual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellElem
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate5
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.D14Normal
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146A2
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.H13.NQBlockOddRankOne
public import CFSG.Quasithin.H13.NQBlockWholeAction
public import CFSG.Quasithin.H13.NQCatQuasisimpleJ4
public import CFSG.Quasithin.H13.NQRigidInputs
public import CFSG.Quasithin.H13.QTESylowStmt
public import CFSG.Quasithin.SteinbergCDExactPlaneWreathAggregate
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
public import CFSG.Sporadic.Schreier.TitsOther
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Setup.Campbell (elemThompsonIn)
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem exists_noncentral_step {H U : Subgroup G} :
    ∀ {N : Subgroup G} {n : ℕ}, IsChiefSeriesFrom H U N n → 0 < n →
      ∃ L' N' : Subgroup G, IsChiefStep H U L' N' ∧ ¬ IsCentralStep H L' N'
  | _, _, .bot, h => absurd h (lt_irrefl 0)
  | _, _, .central _ _ hs, h => exists_noncentral_step hs h
  | _, _, .noncentral hstep hnc _, _ => ⟨_, _, hstep, hnc⟩

theorem isElementaryAbelian_autOn {D V : Subgroup G} (hD : IsElemAbelian 2 D) :
    IsElementaryAbelian 2 ↥(autOn D V) := by
  have key : ∀ σ ∈ autOn D V, ∃ d ∈ D, ∃ hd : d ∈ normalizer (V : Set G),
      conjAct V ⟨d, hd⟩ = σ := by
    rintro σ ⟨n, hn, rfl⟩
    exact ⟨n, hn, n.2, rfl⟩
  refine
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext ?_ }
  · obtain ⟨d, hd, hdN, hda⟩ := key a a.2
    obtain ⟨e, he, heN, heb⟩ := key b b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hda, ← heb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := hD.1
    have h3 : d * e = e * d := congrArg Subtype.val (mul_comm (⟨d, hd⟩ : ↥D) ⟨e, he⟩)
    exact h3
  · obtain ⟨d, hd, hdN, hda⟩ := key a a.2
    rw [Subgroup.coe_pow, ← hda, ← map_pow, OneMemClass.coe_one]
    have h2 : (⟨d, hdN⟩ : normalizer (V : Set G)) ^ 2 = 1 := Subtype.ext (hD.2 d hd)
    rw [h2, map_one]

variable [Finite G]

theorem stmtCoreContainedAtMostOneNoncentral_holds : StmtCoreContainedAtMostOneNoncentral := by
  intro G _ _ H T M V hHs hT hTn hMH hMmax hTM hMu hVT hTV hVe hV1 hVQ hUe hstrict hJQ n hn
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hn1
  push Not at hn1
  set U := ⨆ (h : G) (_ : h ∈ H), V.map (MulAut.conj h).toMonoidHom with hUdef
  set Q := (CFSG.pCore 2 ↥H).map H.subtype with hQ
  have hTH : T ≤ H := hT.1
  have hQeq : Q = pCoreOf 2 H := by rw [hQ, pCoreOf]
  have hQT : Q ≤ T := hQeq ▸ EscapingLocal.pCoreOf_le_of_isSylowTwoOf hT
  have hHQ : H ≤ normalizer (Q : Set G) := hQeq ▸ LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hUQ : U ≤ Q := SteinbergCD.iSup_conj_le hVQ hHQ
  have hUT : U ≤ T := hUQ.trans hQT
  have hUH : U ≤ H := hUT.trans hTH
  have hrel0 : ∀ X Y : Subgroup G, X.relIndex Y ≠ 0 := D15Proof.relIndex_ne_zero
  obtain ⟨A, hAfam, hAQ⟩ : ∃ A ∈ Setup.Campbell.elemFamilyIn 2 T, ¬ A ≤ Q := by
    by_contra hall
    push Not at hall
    apply hJQ
    rw [Setup.Campbell.elemThompsonIn_eq]
    exact sSup_le hall
  have hAT : A ≤ T := Setup.Campbell.le_of_mem_elemFamilyIn hAfam
  have hAe : IsElemAbelian 2 A := (SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A).mp
    (Setup.Campbell.isElementaryAbelian_of_mem_elemFamilyIn hAfam)
  have hAH : A ≤ H := hAT.trans hTH
  have hAmax : IsMaxElemAbelian T A := ⟨hAT, hAe, fun B hBT hB => by
    rw [(Setup.Campbell.mem_elemFamilyIn.mp hAfam).2.2]
    exact Setup.Campbell.card_le_pow_pRank_of_le hBT
      ((SectionRank.isElementaryAbelian_iff_isElemAbelian 2 B).mpr hB)⟩
  have hbd := fun {L' N' : Subgroup G} (hs : IsChiefStep H U L' N')
      (hnc : ¬ IsCentralStep H L' N') =>
    noncentral_chief_factor_bound hHs hT hTn hMH hMmax hTM hMu hUe hs hnc
  have hpow := D15Proof.pow_le_relIndex hUH hAH
    (fun L' N' hs hnc => (hbd hs hnc).2 A hAT hAe) hn
  obtain ⟨L', N', hs, hnc⟩ := exists_noncentral_step hn (by omega)
  set C := A ⊓ centralizer (U : Set G) with hC
  have hCQ : C ≤ Q := fun c hc => (hbd hs hnc).1 c (hAT hc.1) fun x hx => by
    have h1 : c * x = x * c := (mem_centralizer_iff.mp hc.2 x (hs.1.1 hx)).symm
    rw [h1, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem L'
  set B := A ⊓ Q with hB
  have hBA : B ≤ A := inf_le_left
  have hCB : C ≤ B := le_inf inf_le_left hCQ
  have hx : Q.relIndex A = B.relIndex A := by rw [hB, inf_relIndex_left]
  have hAC : (centralizer (U : Set G)).relIndex A = B.relIndex A * C.relIndex B := by
    rw [← inf_relIndex_left, ← hC, ← relIndex_mul_relIndex C B A hCB hBA, mul_comm]
  have hcard : ∀ X Y : Subgroup G, Nat.card ((centralizer (X : Set G)).subgroupOf Y) =
      Nat.card ↥(Y ⊓ centralizer (X : Set G)) := fun X Y => by
    rw [← inf_subgroupOf_right (centralizer (X : Set G)) Y, inf_comm]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmaxineq : (centralizer (A : Set G)).relIndex U ≤
      (centralizer (U : Set G)).relIndex A := by
    obtain ⟨-, h⟩ := Setup.Campbell.action_inequality hAmax hUT hUe
    have h1 := ((centralizer (A : Set G)).subgroupOf U).card_mul_index
    have h2 := ((centralizer (U : Set G)).subgroupOf A).card_mul_index
    rw [hcard] at h1 h2
    rw [← h1, ← h2, ← relIndex, ← relIndex] at h
    have hpos : 0 < Nat.card ↥(U ⊓ centralizer (A : Set G)) * Nat.card ↥(A ⊓ centralizer
        (U : Set G)) := Nat.mul_pos Nat.card_pos Nat.card_pos
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc Nat.card ↥(U ⊓ centralizer (A : Set G)) * Nat.card ↥(A ⊓ centralizer (U : Set G)) *
          (centralizer (A : Set G)).relIndex U =
        Nat.card ↥(U ⊓ centralizer (A : Set G)) * (centralizer (A : Set G)).relIndex U *
          Nat.card ↥(A ⊓ centralizer (U : Set G)) := by ring
      _ ≤ Nat.card ↥(A ⊓ centralizer (U : Set G)) * (centralizer (U : Set G)).relIndex A *
          Nat.card ↥(U ⊓ centralizer (A : Set G)) := h
      _ = Nat.card ↥(U ⊓ centralizer (A : Set G)) * Nat.card ↥(A ⊓ centralizer (U : Set G)) *
          (centralizer (U : Set G)).relIndex A := by ring
  have hxy : B.relIndex A ≤ C.relIndex B := by
    have h1 : B.relIndex A ^ 2 ≤ B.relIndex A ^ n :=
      Nat.pow_le_pow_right (Nat.pos_of_ne_zero (hrel0 _ _)) hn1
    rw [hx] at hpow
    have h3 : B.relIndex A ^ 2 ≤ B.relIndex A * C.relIndex B :=
      h1.trans (hpow.trans (hmaxineq.trans hAC.le))
    rw [sq] at h3
    exact Nat.le_of_mul_le_mul_left h3 (Nat.pos_of_ne_zero (hrel0 _ _))
  have hx1 : 1 < B.relIndex A := by
    have hne : B.relIndex A ≠ 1 := fun h => hAQ ((relIndex_eq_one.mp h).trans inf_le_right)
    have hpos := Nat.pos_of_ne_zero (hrel0 B A)
    omega
  have hB2 : IsPGroup 2 B := hT.2.1.to_le (hBA.trans hAT)
  have hQH : ∀ h ∈ H, ∀ q ∈ Q, h⁻¹ * q * h ∈ Q := fun h hh q hq => by
    have := (mem_normalizer_iff.mp (hHQ (inv_mem hh)) q).mp hq
    rwa [inv_inv] at this
  have hBV : ∀ h ∈ H, B ≤ normalizer ((V.map (MulAut.conj h).toMonoidHom : Subgroup G) :
      Set G) := by
    intro h hh
    refine SteinbergCD.le_normalizer_of_conj_mem_of_finite fun q hq y hy => ?_
    obtain ⟨v, hv, rfl⟩ := hy
    have ht : h⁻¹ * q * h ∈ T := hQT (hQH h hh q (inf_le_right (a := A) hq))
    refine ⟨(h⁻¹ * q * h) * v * (h⁻¹ * q * h)⁻¹,
      (mem_normalizer_iff.mp (hTV ht) v).mp hv, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hbound : ∀ h ∈ H, ∀ D ≤ B,
      ¬ D ≤ centralizer ((V.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) →
        (centralizer ((V.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G)).relIndex D ^ 2 <
          (centralizer (D : Set G)).relIndex (V.map (MulAut.conj h).toMonoidHom) := by
    intro h hh D hDB hDnc
    set D' := D.map (MulAut.conj h⁻¹).toMonoidHom with hD'
    have hDD' : D = D'.map (MulAut.conj h).toMonoidHom := by
      rw [hD', ← LieType.Steinberg.map_conj_mul, mul_inv_cancel, LieType.Steinberg.map_conj_one]
    have hD'T : D' ≤ T := by
      rintro _ ⟨d, hd, rfl⟩
      have h1 := hQH h hh d (inf_le_right (a := A) (hDB hd))
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact hQT h1
    have hD'N : D' ≤ normalizer (V : Set G) := hD'T.trans hTV
    have hD'nc : ¬ D' ≤ centralizer (V : Set G) := fun hle => hDnc (by
      rw [hDD', ← SteinbergCA.map_conj_centralizer]
      exact map_mono hle)
    have hD'e : IsElemAbelian 2 D' := by
      have hDe : IsElemAbelian 2 D := Setup.Campbell.isElemAbelian_mono hAe (hDB.trans hBA)
      refine ⟨(D.equivMapOfInjective _ (MulAut.conj h⁻¹).injective).surjective.isMulCommutative
        hDe.1, ?_⟩
      rintro _ ⟨d, hd, rfl⟩
      rw [← map_pow, hDe.2 d hd, map_one]
    have hE := hstrict (autOn D' V) (by
        rintro σ ⟨n, hn, rfl⟩
        exact ⟨n, hD'T hn, fun v => normalizerMonoidHom_apply_apply_coe V
          (inclusion le_rfl n) v⟩)
      (autOn_ne_bot_of_not_le_centralizer hD'N hD'nc) (isElementaryAbelian_autOn hD'e)
    rw [card_autOn_eq_relIndex hD'N, inf_relIndex_left, fixedPoints_autOn hD'N,
      ← ((centralizer (D' : Set G)).subgroupOf V).card_mul_index, ← relIndex, mul_comm] at hE
    rw [hDD', SteinbergCA.relIndex_centralizer_map_conj,
      SteinbergCA.relIndex_centralizer_map_conj]
    exact Nat.lt_of_mul_lt_mul_left hE
  have hBU : ¬ B ≤ centralizer (U : Set G) := by
    intro h
    have h1 : C.relIndex B = 1 := relIndex_eq_one.mpr (le_inf hBA h)
    omega
  have hsum := pow_lt_relIndex_of_iSup_conj 2 hUe hB2 hBV hbound hBU
  have hCB' : (centralizer (U : Set G)).relIndex B = C.relIndex B := by
    rw [← inf_relIndex_left]
    congr 1
    refine le_antisymm (fun x hx => ⟨hBA hx.1, hx.2⟩) fun x hx => ⟨hCB hx, hx.2⟩
  have hBAcent : (centralizer (B : Set G)).relIndex U ≤ (centralizer (A : Set G)).relIndex U :=
    relIndex_le_of_le_left (centralizer_le hBA) (hrel0 _ _)
  have hyx : C.relIndex B < B.relIndex A := by
    rw [hCB'] at hsum
    have h1 : C.relIndex B ^ 2 < B.relIndex A * C.relIndex B :=
      hsum.trans_le (hBAcent.trans (hmaxineq.trans hAC.le))
    rw [sq] at h1
    exact Nat.lt_of_mul_lt_mul_right h1
  omega

theorem stmtIntrinsicActionExclusion_of_atLeastTwo
    (hA7u : U3.SylowNormalizedMaximalLocalUniqueNormalizer)
    (hA7n : NQBlock.SylowNormalizedLocalNormalComponent) (hsing : StmtOriginalWitnessSingleton)
    (hge2 : StmtCoreContainedAtLeastTwoNoncentral) : StmtIntrinsicActionExclusion :=
  stmtIntrinsicActionExclusion_of hA7u hA7n (stmtWholeModuleComparison_of hA7u hA7n)
      (stmtOriginalRadicalEscape_of hsing)
      (stmtSolvableFixedSpaceWitness_of stmtCoreContainedAtMostOneNoncentral_holds hge2)

end CFSG.Quasithin.H13.NQCore
