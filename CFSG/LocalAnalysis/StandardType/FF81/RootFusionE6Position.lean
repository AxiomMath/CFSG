module

public import Certificates.Certificate3951
public import CFSG.LocalAnalysis.StandardType.FF81.Defs
public import CFSG.LocalAnalysis.SeitzReduction.EPilotFusionEntrywise
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
public import CFSG.GroupTheory.PCore.Construction
import CFSG.LocalAnalysis.StandardType.MarkingChevalley
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionCenter
import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLin
import CFSG.LocalAnalysis.StandardType.FF81.RootFusionE6Radical
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.Timmesfeld.Orders.Classical
import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.StandardType.FF81

open CFSG.Blueprint.Chevalley CFSG.SeitzReduction
open CFSG.StandardType.FrameRoute.FS81 (IsSylow2In)

theorem exists_mulEquiv_adjointGroup_of_ggHasLabel_E6
    {R : Type} [Group R] (h : GGHasLabel ⟨.E6, 0, 1⟩ R) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      Nonempty (R ≃* adjointGroup .E6 K) := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h
  obtain ⟨ψ⟩ := centerQuot_chevGroup_equiv K .E6
  have hcenK : Subgroup.center (adjointGroup .E6 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let q₀ : CFSG.Blueprint.AdjointQuotient .E6 K ≃* ↥(adjointGroup .E6 K) :=
    (QuotientGroup.quotientMulEquivOfEq hcenK).trans QuotientGroup.quotientBot
  exact ⟨K, inferInstance, inferInstance, by simpa using hK, ⟨(φ.trans ψ).trans q₀⟩⟩

theorem exists_conj_eq_pinnedElt_of_isSylow2In
    {G : Type} [Group G] {Y : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
    (φ : ↥Y ≃* adjointGroup .E6 K) {S : Subgroup G} (hS : IsSylow2In S Y) {t : G} (htY : t ∈ Y)
    (ht : orderOf t = 2) (hcS : ∀ s ∈ S, s * t = t * s) :
    ∃ c : adjointGroup .E6 K, c * φ ⟨t, htY⟩ * c⁻¹ = EPilot.pinnedElt .E6 (highRoot .E6) (1 : K) := by
  obtain ⟨S', hS'p, hS'max, hS'mem⟩ := exists_maximal_pGroup_of_isSylow2In hS φ
  let U : Sylow 2 ↥(adjointGroup .E6 K) :=
    { toSubgroup := S', isPGroup' := hS'p, is_maximal' := fun hQ hle => hS'max _ hQ hle }
  have hz : φ ⟨t, htY⟩ ∈ Subgroup.centralizer ((U : Subgroup ↥(adjointGroup .E6 K)) : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : u ∈ S' := hu
    have hy : ((φ.symm u : ↥Y) : G) ∈ S :=
      (hS'mem (φ.symm u)).1 (by rw [MulEquiv.apply_symm_apply]; exact hu')
    have h2 : φ.symm u * ⟨t, htY⟩ = ⟨t, htY⟩ * φ.symm u := Subtype.ext (hcS _ hy)
    have h3 := congrArg φ h2
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
    exact h3
  have hz1 : φ ⟨t, htY⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨t, htY⟩ : ↥Y) = 1 := φ.injective (by rw [h1, map_one])
    have h3 : t = 1 := congrArg Subtype.val h2
    rw [h3, orderOf_one] at ht
    exact absurd ht (by norm_num)
  exact E8Pilot.exists_conj_eq_pinnedElt_highRoot_of_mem_centralizer_sylow (Or.inl rfl) U hz hz1

private theorem inf_eq_bot_of_isPGroup_two_of_isSimpleGroup
    {G : Type} [Group G] {L R T : Subgroup G}
    (hL : IsSimpleGroup ↥L) (hL3 : ∃ x : ↥L, orderOf x = 3)
    (hLT : L ≤ T) (hR2 : IsPGroup 2 R)
    (hRnorm : ∀ x ∈ T, ∀ r ∈ R, x * r * x⁻¹ ∈ R) :
    R ⊓ L = ⊥ := by
  let N : Subgroup ↥L := (R ⊓ L).subgroupOf L
  have hN : N.Normal := by
    refine ⟨?_⟩
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨hRnorm (g : G) (hLT g.2) (n : G) hn.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hn.2) (Subgroup.inv_mem _ g.2)⟩
  have : N.Normal := hN
  rcases hL.eq_bot_or_eq_top_of_normal N with hbot | htop
  · rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxN : (⟨x, hx.2⟩ : ↥L) ∈ N := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    rw [hbot] at hxN
    have hx1 : (⟨x, hx.2⟩ : ↥L) = 1 := by simpa using hxN
    simpa using congrArg Subtype.val hx1
  · exfalso
    have hLR : L ≤ R := by
      intro x hx
      have hxN : (⟨x, hx⟩ : ↥L) ∈ N := by
        rw [htop]
        exact Subgroup.mem_top _
      rw [Subgroup.mem_subgroupOf] at hxN
      exact hxN.1
    obtain ⟨x, hx3⟩ := hL3
    obtain ⟨k, hk⟩ := hR2 ⟨(x : G), hLR x.2⟩
    have hx3' : orderOf (x : G) = 3 := by
      rw [Subgroup.orderOf_coe, hx3]
    have hpow : (x : G) ^ 2 ^ k = 1 := by
      simpa using hk
    have hdvd : 3 ∣ 2 ^ k := by
      rw [← hx3']
      exact orderOf_dvd_of_pow_eq_one hpow
    exact absurd (Nat.prime_three.dvd_of_dvd_pow hdvd) (by norm_num)

theorem twoCore_inf_eq_bot_and_sup_eq
    {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G} {K : ℕ → Subgroup G} {t : G}
    (hA : HypA G n b L) (hup : Upstream n b L K t)
    (hY : YData n b L (⨆ i : Fin (n + 2), K (i : ℕ)) t) (h5 : n = 5)
    (hlab : GGHasLabel ⟨.E6, 0, 1⟩ ↥(⨆ i : Fin (n + 2), K (i : ℕ))) :
    let HY := Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ)
    let Q := (CFSG.pCore 2 ↥HY).map HY.subtype
    IsPGroup 2 Q ∧ Q ⊓ L = ⊥ ∧ Q ⊔ L = HY ∧ Nat.card HY = Nat.card Q * Nat.card L := by
  obtain ⟨z, hz, hF⟩ := hup
  dsimp only
  set Y : Subgroup G := ⨆ i : Fin (n + 2), K (i : ℕ) with hYdef
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hCdef
  set H : Subgroup G := C ⊓ Y with hHdef
  set Q : Subgroup G := (CFSG.pCore 2 ↥H).map H.subtype with hQdef
  show IsPGroup 2 Q ∧ Q ⊓ L = ⊥ ∧ Q ⊔ L = H ∧ Nat.card H = Nat.card Q * Nat.card L
  obtain ⟨F, _, _, hF2, ⟨φ⟩⟩ :=
    exists_mulEquiv_adjointGroup_of_ggHasLabel_E6 hlab
  have : CharP F 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 1) (by rw [hF2]; norm_num)
  obtain ⟨S, hS, htS, ht2, hcS⟩ := hY.syl
  have htY : t ∈ Y := hS.1 htS
  obtain ⟨c, hc⟩ := exists_conj_eq_pinnedElt_of_isSylow2In φ hS htY ht2 hcS
  obtain ⟨Q1, hQ1_2, hQ1_le, hQ1_norm, hQ1_card⟩ :=
    exists_twoRadical_of_conj_eq_pinnedElt φ hF2 htY hc
  have htK0 : t ∈ K 0 := by
    rw [hF.K0]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hLC : L ≤ C := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact hF.comm_L t htK0 y hy
  have hLH : L ≤ H := by
    rw [hHdef]
    exact le_inf hLC hY.le
  obtain ⟨x, hxK2, hx3, -⟩ := hF.conj_b 2 (by omega)
  have hK2L : K 2 ≤ L := by
    rw [← hF.sysL.2.1]
    exact le_iSup (fun i : Fin n => K ((i : ℕ) + 2)) ⟨0, by omega⟩
  have hL3 : ∃ x : ↥L, orderOf x = 3 :=
    ⟨⟨x, hK2L hxK2⟩, by simpa using hx3⟩
  have hQ1normH : ∀ x ∈ H, ∀ q ∈ Q1, x * q * x⁻¹ ∈ Q1 := by
    intro x hx q hq
    refine hQ1_norm x ?_ q hq
    rw [hHdef] at hx
    rwa [inf_comm] at hx
  have hQ1H : Q1 ≤ H := by
    rw [hHdef]
    exact hQ1_le.trans (le_of_eq (inf_comm Y C))
  have hQ1L : Q1 ⊓ L = ⊥ :=
    inf_eq_bot_of_isPGroup_two_of_isSimpleGroup hz.model.simple hL3 hLH hQ1_2 hQ1normH
  have hcardL : Nat.card L = CFSG.Open.ordA 5 2 := by
    have h := (CFSG.Timmesfeld.card_statedClassicalModel_two hA.model).1 rfl
    rw [Nat.add_sub_cancel, pow_one, h5] at h
    exact h
  have hQ1_cardH : Nat.card H = Nat.card Q1 * CFSG.Open.ordA 5 2 := by
    rw [hHdef, inf_comm]
    exact hQ1_card
  have hcardQ1card : Nat.card H = Nat.card Q1 * Nat.card L := by
    rw [hQ1_cardH, ← hcardL]
  have hQ1normQ1 : L ≤ Subgroup.normalizer (Q1 : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy q hq
    exact hQ1normH y (hLH hy) q hq
  have hcardQ1sup : Nat.card ↥(Q1 ⊔ L) = Nat.card Q1 * Nat.card L := by
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := Q1) (B := L) hQ1normQ1
    rw [hQ1L, Subgroup.card_bot, mul_one] at h
    exact h
  have hQ1supL : Q1 ⊔ L = H := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hQ1H hLH) ?_
    rw [hcardQ1card, hcardQ1sup]
  have hHnormQ1 : H ≤ Subgroup.normalizer (Q1 : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    exact hQ1normH
  have hQ1sub_normal : (Q1.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ1H).mpr hHnormQ1
  have hQ1sub_2 : IsPGroup 2 (Q1.subgroupOf H) :=
    hQ1_2.of_equiv (Subgroup.subgroupOfEquivOfLe hQ1H).symm
  have hQ1sub_le_pcore : Q1.subgroupOf H ≤ CFSG.pCore 2 ↥H := by
    unfold CFSG.pCore
    exact le_sSup ⟨hQ1sub_normal, hQ1sub_2⟩
  have hQ1_le_Q : Q1 ≤ Q := by
    have h := Subgroup.map_mono (f := H.subtype) hQ1sub_le_pcore
    rwa [Subgroup.map_subgroupOf_eq_of_le hQ1H, ← hQdef] at h
  have hQ_le_H : Q ≤ H := by
    rw [hQdef]
    exact Subgroup.map_subtype_le (CFSG.pCore 2 ↥H)
  have hQ2 : IsPGroup 2 Q := by
    rw [hQdef]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype
  have hQnormH : ∀ x ∈ H, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q := by
    intro x hx q hq
    rw [hQdef] at hq ⊢
    obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.1 hq
    have hpc : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
    exact Subgroup.mem_map.2 ⟨⟨x, hx⟩ * q' * ⟨x, hx⟩⁻¹,
      hpc.conj_mem q' hq' ⟨x, hx⟩, rfl⟩
  have hQL : Q ⊓ L = ⊥ :=
    inf_eq_bot_of_isPGroup_two_of_isSimpleGroup hz.model.simple hL3 hLH hQ2 hQnormH
  have hQsupL : Q ⊔ L = H := by
    apply le_antisymm
    · exact sup_le hQ_le_H hLH
    · calc H = Q1 ⊔ L := hQ1supL.symm
        _ ≤ Q ⊔ L := sup_le_sup hQ1_le_Q le_rfl
  have hQnormQ : L ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy q hq
    exact hQnormH y (hLH hy) q hq
  have hcardH : Nat.card H = Nat.card Q * Nat.card L := by
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := Q) (B := L) hQnormQ
    rw [hQsupL, hQL, Subgroup.card_bot, mul_one] at h
    exact h
  exact ⟨hQ2, hQL, hQsupL, hcardH⟩

end CFSG.StandardType.FF81
