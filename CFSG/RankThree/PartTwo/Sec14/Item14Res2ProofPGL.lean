module

public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofCoreDefs
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofCore
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofTrans
import CFSG.RankThree.PartTwo.Sec14.Item14Res2ProofLBalComp
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.RankThree.PartTwo.Sec4.T444.Step450
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def cStar142 (c : G) (L : Subgroup G) :
    Subgroup (↥(Subgroup.centralizer ({c} : Set G)) ⧸
      CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({c} : Set G))) :=
  ((Subgroup.centralizer ({c} : Set G) ⊓ thetaQuotCentralizer L).subgroupOf
    (Subgroup.centralizer ({c} : Set G))).map (QuotientGroup.mk' _)

@[expose] noncomputable def aStar142 (c : G) (A : Subgroup G) :
    Subgroup (↥(Subgroup.centralizer ({c} : Set G)) ⧸
      CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({c} : Set G))) :=
  (A.subgroupOf (Subgroup.centralizer ({c} : Set G))).map (QuotientGroup.mk' _)

@[expose] def Step142PGLNoComp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → Sec8.IsZ3PGLThreePi (Sec13.lBarA c L A) →
      layer ↥(cStar142 c L) = ⊥

@[expose] def Step142PGLCentO3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → Sec8.IsZ3PGLThreePi (Sec13.lBarA c L A) →
      ∀ W : Subgroup (↥(Subgroup.centralizer ({c} : Set G)) ⧸
          CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({c} : Set G))),
        W ≤ cStar142 c L → ¬ 3 ∣ Nat.card W →
        aStar142 c A ≤ Subgroup.normalizer (W : Set _) →
        W ≤ Subgroup.centralizer (inSubgroup (CFSG.pCore 3) (cStar142 c L) : Set _)

theorem step142PGLKer_of (hNC : Step142PGLNoComp) (hCO : Step142PGLCentO3) : Step142PGLKer := by
  intro G _ _ A c L h hPGL V hV hV3 hAV
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M := Subgroup.centralizer ({c} : Set G) with hM
  set T := thetaQuotCentralizer L with hT
  set O := pPrimeCoreOf 3 M with hO
  set N3 := CFSG.pPrimeCore 3 ↥M with hN3
  set ψ := QuotientGroup.mk' N3 with hψ
  have hD := h.toSec13Data
  have h3L : 3 ∣ Nat.card L := by
    have h1 := Sec16.Proof1614Trans.card_inf_eq_three_of_pgl hD hPGL
    exact h1 ▸ Subgroup.card_dvd_of_le inf_le_right
  have hML : M ≤ Subgroup.normalizer (L : Set G) := centralizer_le_normalizer_of_three_dvd h h3L
  have hMT : M ≤ Subgroup.normalizer (T : Set G) :=
    hML.trans (Proof142Res.normalizer_le_normalizer_thetaQuotCentralizer L)
  have hOM : O ≤ M := pPrimeCoreOf_le 3 M
  have hVM : V ≤ M := hV.trans (sup_le inf_le_left hOM)
  have hOsub : O.subgroupOf M = N3 := by
    rw [hO, pPrimeCoreOf, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      M.subtype_injective]
  set W := (V.subgroupOf M).map ψ with hW
  have hWC : W ≤ cStar142 c L := by
    have h1 : V.subgroupOf M ≤ ((M ⊓ T) ⊔ O).subgroupOf M := Subgroup.comap_mono hV
    rw [Subgroup.subgroupOf_sup inf_le_left hOM, hOsub] at h1
    refine (Subgroup.map_mono h1).trans ?_
    rw [Subgroup.map_sup]
    have h2 : N3.map ψ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hψ, QuotientGroup.ker_mk']
    rw [h2, sup_bot_eq]
    rfl
  have hW3 : ¬ 3 ∣ Nat.card W := by
    intro h3
    apply hV3
    refine h3.trans ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVM).toEquiv]
  have hAM : A ≤ M := hD.A_le_centralizer
  have hAW : aStar142 c A ≤ Subgroup.normalizer (W : Set _) := by
    have h1 : A.subgroupOf M ≤ Subgroup.normalizer ((V.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      have := Subgroup.mem_normalizer_iff.mp (hAV (Subgroup.mem_subgroupOf.mp hx)) (y : G)
      simpa using this
    exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map ψ)
  have hWcent := hCO G A c L h hPGL W hWC hW3 hAW
  set Cs := cStar142 c L with hCs
  have hCn : Cs.Normal := by
    have h1 : ((M ⊓ T).subgroupOf M).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      intro m hm
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hm, hMT hm⟩
    exact h1.map ψ (QuotientGroup.mk'_surjective N3)
  have hCO3 : CFSG.pPrimeCore 3 ↥Cs = ⊥ := by
    have h1 := pPrimeCoreOf_le_of_subnormal 3 hCn.isSubnormal
    rw [CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three, le_bot_iff, pPrimeCoreOf,
      Subgroup.map_eq_bot_iff_of_injective _ Cs.subtype_injective] at h1
    exact h1
  have hF : generalizedFitting ↥Cs = CFSG.pCore 3 ↥Cs := by
    rw [generalizedFitting, hNC G A c L h hPGL, sup_bot_eq, CFSG.Fitting_eq_pcore _ 3 hCO3]
  set W' := W.subgroupOf Cs with hW'
  have hW'3 : ¬ 3 ∣ Nat.card W' := by
    rwa [hW', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv]
  have hW'F : W' ≤ Subgroup.centralizer (generalizedFitting ↥Cs : Set ↥Cs) := by
    rw [hF]
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    apply Subtype.ext
    have h1 := Subgroup.mem_centralizer_iff.mp (hWcent (Subgroup.mem_subgroupOf.mp hw)) (x : _)
      ⟨x, hx, rfl⟩
    simpa using h1
  have hW'le : W' ≤ CFSG.pCore 3 ↥Cs :=
    hF ▸ hW'F.trans (CFSG.centralizer_generalizedFitting_le ↥Cs)
  have hW'bot : ∀ w ∈ W', w = 1 := by
    intro w hw
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 3) (G := ↥Cs)) ⟨w, hW'le hw⟩
    have hk' : w ^ 3 ^ k = 1 := congrArg Subtype.val hk
    exact Res2LBal.eq_one_of_mem_of_pow hW'3 hw hk'
  intro v hv
  have hvW : ψ ⟨v, hVM hv⟩ ∈ W := ⟨⟨v, hVM hv⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
  have h1 : (⟨ψ ⟨v, hVM hv⟩, hWC hvW⟩ : ↥Cs) = 1 :=
    hW'bot _ (Subgroup.mem_subgroupOf.mpr hvW)
  have h2 : ψ ⟨v, hVM hv⟩ = 1 := congrArg Subtype.val h1
  rw [hψ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact ⟨⟨v, hVM hv⟩, h2, rfl⟩

theorem step142PGLNoComp_of (hSz : KFacts.KPSz) :
    Step142PGLNoComp := by
  intro G _ _ A c L h hPGL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M := Subgroup.centralizer ({c} : Set G) with hM
  set T := thetaQuotCentralizer L with hT
  set N3 := CFSG.pPrimeCore 3 ↥M with hN3
  set ψ := QuotientGroup.mk' N3 with hψ
  have hD := h.toSec13Data
  have hc3 : Nat.card (Subgroup.zpowers c) = 3 :=
    (Sec13.zpowers_mem_omegaA_iff.mp hD.zpowers_mem_omegaA).2.1
  have hc1 : c ≠ 1 := by
    intro hc
    rw [hc, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc3
    exact absurd hc3 (by norm_num)
  have hMtop : M ≠ ⊤ := by
    intro htop
    have : IsSimpleGroup G := h.isSimpleGroup
    have hcen : c ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ M := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with hb | ht
    · exact hc1 (by rw [hb] at hcen; exact hcen)
    · obtain ⟨x, y, hxy⟩ := h.nonabelian
      apply hxy
      have hx : x ∈ Subgroup.center G := ht ▸ Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.mp hx y).symm
  have hM4 : SectionFourHyp ↥M := h.toTheoremFourHyp.sectionFourHyp hMtop
  have h3L : 3 ∣ Nat.card L := by
    have h1 := Sec16.Proof1614Trans.card_inf_eq_three_of_pgl hD hPGL
    exact h1 ▸ Subgroup.card_dvd_of_le inf_le_right
  have hML : M ≤ Subgroup.normalizer (L : Set G) := centralizer_le_normalizer_of_three_dvd h h3L
  have hMT : M ≤ Subgroup.normalizer (T : Set G) :=
    hML.trans (Proof142Res.normalizer_le_normalizer_thetaQuotCentralizer L)
  set Cs := cStar142 c L with hCs
  have hCn : Cs.Normal := by
    have h1 : ((M ⊓ T).subgroupOf M).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      intro m hm
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hm, hMT hm⟩
    exact h1.map ψ (QuotientGroup.mk'_surjective N3)
  have hLM : L ≤ M := le_centralizer_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  have hθLO : inSubgroup (aschbacherSolvableCore 3) L ≤ pPrimeCoreOf 3 M := by
    rw [Sec6.theta_eq_inf_of_mem_thetaComponentsIn hD.mem_thetaComponentsAt]
    exact inf_le_right.trans (inSubgroup_theta_le_pPrimeCoreOf M)
  have hcent : ∀ t ∈ Cs, ∀ l ∈ (L.subgroupOf M).map ψ, t * l = l * t := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨l, hl, rfl⟩
    obtain ⟨-, htT⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ht)
    obtain ⟨-, htl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp htT
    have h1 := htl (l : G) (Subgroup.mem_subgroupOf.mp hl)
    have h2 : (l : G)⁻¹ * ((t : G) * l * (t : G)⁻¹) ∈ pPrimeCoreOf 3 M := hθLO h1
    obtain ⟨o, ho, hoeq⟩ := h2
    have h3 : ψ (l⁻¹ * (t * l * t⁻¹)) = 1 := by
      have : l⁻¹ * (t * l * t⁻¹) = o := Subtype.ext (by simpa using hoeq.symm)
      rw [this, hψ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ho
    rw [map_mul, map_inv, inv_mul_eq_one, map_mul, map_mul, map_inv] at h3
    calc ψ t * ψ l = ψ t * ψ l * (ψ t)⁻¹ * ψ t := by group
      _ = ψ l * ψ t := by rw [← h3]
  refine le_bot_iff.mp (sSup_le fun K hK => ?_)
  exfalso
  set J := K.map Cs.subtype with hJdef
  have hJ : IsComponent J :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (K.equivMapOfInjective _ Cs.subtype_injective)
      hK.1, hK.2.trans' hCn.isSubnormal⟩
  obtain ⟨L', hL', hL'J⟩ := Sec4.exists_mem_thetaComponents_map_eq hSz hM4.kGroup
    (Sec4.localRank_theta_quotient_le hM4) hJ
  have hJ3 : 3 ∣ Nat.card J := by
    by_contra h3
    have hle : J ≤ CFSG.pPrimeCore 3 (↥M ⧸ N3) :=
      le_pPrimeCore_of_subnormal 3 hJ.2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
    rw [CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three, le_bot_iff] at hle
    have : Nontrivial J := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
    exact (Subgroup.nontrivial_iff_ne_bot J).mp this hle
  have hL'3 : 3 ∣ Nat.card (L'.map M.subtype) := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    refine hJ3.trans ?_
    rw [← hL'J]
    exact Subgroup.card_map_dvd _ _
  have hL'c : L'.map M.subtype ∈ thetaComponentsAt 3 c := ⟨L', hL', rfl⟩
  have hL'L : L'.map M.subtype = L :=
    (h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).2 _ hL'c hL'3
  have hL'eq : L' = L.subgroupOf M := by
    rw [← hL'L, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hJL : J = (L.subgroupOf M).map ψ := by
    rw [← hL'J, hL'eq]
  have hJC : J ≤ Cs := Subgroup.map_subtype_le K
  obtain ⟨a, b, hab⟩ := hJ.1.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have hb : ((b : J) : ↥M ⧸ N3) ∈ (L.subgroupOf M).map ψ := hJL ▸ b.2
  have h1 := hcent ((a : J) : ↥M ⧸ N3) (hJC a.2) ((b : J) : ↥M ⧸ N3) hb
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext h1

theorem step142PGLKer_of_centO3 (hSz : KFacts.KPSz)
    (hCO : Step142PGLCentO3) : Step142PGLKer :=
  step142PGLKer_of (step142PGLNoComp_of hSz) hCO

end CFSG.RankThree.PartTwo.Sec14
