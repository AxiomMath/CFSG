module

public import CFSG.LocalAnalysis.StandardType.GGF4N2Frame
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.LocalAnalysis.StandardType.GGF4N2JModelExclusions
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailHolds
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenIso
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineOrthBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointSchreier
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Std
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
public import CFSG.GroupTheory.SubgroupCardMul
public import CFSG.Holt.General.Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Layer
public import CFSG.LocalAnalysis.WeakClosure81.EightNine
public import CFSG.LocalAnalysis.WeakClosure81.EightThreeE
public import CFSG.LocalAnalysis.WeakClosure81.ThirteenFour
public import CFSG.LocalAnalysis.WeakClosure81.W18Gamma
public import CFSG.LocalAnalysis.WeakClosure81.W18Tail
public import CFSG.LocalAnalysis.WeakClosure81.W19Conf
public import CFSG.LocalAnalysis.WeakClosure81.W19Hyp197
public import CFSG.LocalAnalysis.WeakClosure81.W19Min
public import CFSG.Quasithin.Background.B3Facts
public import CFSG.Quasithin.Background.B3FourConj
public import CFSG.Quasithin.Background.E2TwoLieQuotLift
public import CFSG.Quasithin.Background.H16TwoM22
public import CFSG.Quasithin.Background.HMathieuO2Data
public import CFSG.Quasithin.Background.HSecQuot
public import CFSG.Quasithin.Background.HTriU3
public import CFSG.Quasithin.Background.SmithB42SL3Key
public import CFSG.Quasithin.Background.SmithB45SL3Label
public import CFSG.Quasithin.Background.SmithB45SL3Outer
public import CFSG.Quasithin.Vol2.Ch11SecBNPCaseS
public import CFSG.Quasithin.Vol2.Ch11SecBTCIso
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS4
public import CFSG.Quasithin.Vol2.Ch7NotFFS7
public import CFSG.Quasithin.Vol2.Ch8Sec2L825O
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LM1
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN0

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.RankThree.Classical2 Module Multiplicative
open CFSG.ComponentClassification.CatalogueBOrthogonalPointSchreier

theorem ggF4N2OmegaK_inner_action
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .POmegaMinus 4 2 K) :
    let hN := ggF4N2_Bs_le_normalizer_K hR hNbr hL
    let beta : Bs →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion hN)
    ∃ rho : Bs →* K,
      (∀ b, MulAut.conj (rho b) = beta b) ∧
      rho.ker = (Subgroup.zpowers y).subgroupOf Bs ∧
      (∀ b, rho b ^ 5 = 1) ∧
      (K.subtype.comp rho).range = Bs ⊓ K := by
  classical
  dsimp only
  let hN := ggF4N2_Bs_le_normalizer_K hR hNbr hL
  let beta : Bs →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion hN)
  obtain ⟨hker, _, hpow, _⟩ := ggF4N2_Bs_action_data hR hNbr hL hN
  have hZ : Subgroup.center K = ⊥ := ggN2Center_eq_bot_of_centralImage hK
  let theta : (K ⧸ Subgroup.center K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hinn (b : Bs) : beta b ∈ (MulAut.conj : K →* MulAut K).range :=
    ggN2Inner_of_fifth hK theta (beta b) (hpow b)
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZ
  let e : K ≃* (MulAut.conj : K →* MulAut K).range := MonoidHom.ofInjective hinj
  let rho : Bs →* K := e.symm.toMonoidHom.comp
    (beta.codRestrict (MulAut.conj : K →* MulAut K).range hinn)
  have hrho (b : Bs) : MulAut.conj (rho b) = beta b := by
    have h := congrArg Subtype.val (e.apply_symm_apply
      ((beta.codRestrict (MulAut.conj : K →* MulAut K).range hinn) b))
    exact h
  have hrhopow (b : Bs) : rho b ^ 5 = 1 := by
    apply hinj
    rw [map_pow, hrho, hpow, map_one]
  have hrhoker : rho.ker = (Subgroup.zpowers y).subgroupOf Bs := by
    rw [← hker]
    apply Subgroup.ext
    intro b
    change rho b = 1 ↔ beta b = 1
    constructor
    · intro hb
      rw [← hrho, hb, map_one]
    · intro hb
      apply hinj
      rw [hrho, hb, map_one]
  have hEl : IsElemAbelian 5 Bs := hR.1.2.1.2.1
  have hcomm (b c : Bs) : rho b * rho c = rho c * rho b := by
    rw [← map_mul, ← map_mul]
    exact congrArg rho (Subtype.ext (hEl.comm b.2 c.2))
  have hrhoBs (b : Bs) : (rho b : G) ∈ Bs := by
    have hC : (rho b : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      let cb : Bs := ⟨c, hc⟩
      have hfix : beta cb (rho b) = rho b := by
        rw [← hrho, MulAut.conj_apply, hcomm, mul_assoc, mul_inv_cancel, mul_one]
      have h := congrArg Subtype.val hfix
      change c * (rho b : G) * c⁻¹ = (rho b : G) at h
      have h' := congrArg (fun z : G => z * c) h
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using h'
    have hg5 : (rho b : G) ^ 5 = 1 := congrArg Subtype.val (hrhopow b)
    exact hR.1.2.1.2.2.2 (rho b) hC hg5
  refine ⟨rho, hrho, hrhoker, hrhopow, ?_⟩
  apply le_antisymm
  · rintro _ ⟨b, rfl⟩
    exact ⟨hrhoBs b, (rho b).2⟩
  · intro z hz
    let b : Bs := ⟨z, hz.1⟩
    let k : K := ⟨z, hz.2⟩
    have hbk : beta b = MulAut.conj k := by
      apply MulEquiv.ext
      intro u
      apply Subtype.ext
      rfl
    have hrhok : rho b = k := hinj ((hrho b).trans hbk)
    exact ⟨b, congrArg Subtype.val hrhok⟩

theorem ggF4N2OmegaK_Bstar_split
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .POmegaMinus 4 2 K) :
    Bs = Subgroup.zpowers y ⊔ (Bs ⊓ K) ∧ Disjoint (Subgroup.zpowers y) (Bs ⊓ K) := by
  obtain ⟨rho, hrho, hker, _, hrange⟩ := ggF4N2OmegaK_inner_action hR hNbr hL hK
  have hZ := ggN2Center_eq_bot_of_centralImage hK
  have hinj := CFSG.mulAutConj_injective_of_center_eq_bot hZ
  have hyBs : y ∈ Bs := by rw [← ggF4N2_B_eq_Bs hR hL]; exact hNbr.1.2.1
  have hYBs : Subgroup.zpowers y ≤ Bs := Subgroup.zpowers_le.mpr hyBs
  have hYC : Subgroup.zpowers y ≤ Subgroup.centralizer (K : Set G) := by
    rw [← inf_centralizer_eq_zpowers_of_sHat hNbr.1]
    exact inf_le_right
  refine ⟨le_antisymm ?_ (sup_le hYBs inf_le_left), ?_⟩
  · intro b hb
    let bB : Bs := ⟨b, hb⟩
    have hk : (rho bB : G) ∈ Bs ⊓ K := by
      rw [← hrange]
      exact ⟨bB, rfl⟩
    let bK : Bs := ⟨rho bB, hk.1⟩
    have hbk : (K.normalizerMonoidHom.comp
        (Subgroup.inclusion (ggF4N2_Bs_le_normalizer_K hR hNbr hL))) bK =
        MulAut.conj (rho bB) := by
      apply MulEquiv.ext
      intro u
      apply Subtype.ext
      rfl
    have hrhok : rho bK = rho bB := hinj ((hrho bK).trans hbk)
    let cB : Bs := bB * bK⁻¹
    have hcKer : cB ∈ rho.ker := by
      change rho (bB * bK⁻¹) = 1
      rw [map_mul, map_inv, hrhok, mul_inv_cancel]
    rw [hker] at hcKer
    have hcY : (cB : G) ∈ Subgroup.zpowers y := Subgroup.mem_subgroupOf.mp hcKer
    have h1 : Subgroup.zpowers y ≤ Subgroup.zpowers y ⊔ (Bs ⊓ K) := le_sup_left
    have h2 : Bs ⊓ K ≤ Subgroup.zpowers y ⊔ (Bs ⊓ K) := le_sup_right
    have hv : (cB : G) * (rho bB : G) ∈ Subgroup.zpowers y ⊔ (Bs ⊓ K) :=
      Subgroup.mul_mem _ (h1 hcY) (h2 hk)
    have heq : (cB : G) * (rho bB : G) = b := by
      change (b * (rho bB : G)⁻¹) * (rho bB : G) = b
      group
    rwa [heq] at hv
  · rw [Subgroup.disjoint_def]
    intro z hzY hzK
    let k : K := ⟨z, hzK.2⟩
    have hkZ : k ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro u
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hYC hzY) u u.2)
    rw [hZ] at hkZ
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hkZ)

theorem ggF4N2OmegaK_inf_K_card
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .POmegaMinus 4 2 K) : Nat.card ↥(Bs ⊓ K) = 5 ^ 3 := by
  obtain ⟨rho, _, hrhoker, _, hrange⟩ := ggF4N2OmegaK_inner_action hR hNbr hL hK
  let hN := ggF4N2_Bs_le_normalizer_K hR hNbr hL
  let beta : Bs →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion hN)
  obtain ⟨hker, hcard, _, _⟩ := ggF4N2_Bs_action_data hR hNbr hL hN
  have hkerEq : rho.ker = beta.ker := hrhoker.trans hker.symm
  let er : rho.range ≃* beta.range :=
    (QuotientGroup.quotientKerEquivRange rho).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkerEq).trans
        (QuotientGroup.quotientKerEquivRange beta))
  rw [← hrange, MonoidHom.range_comp, Subgroup.card_map_of_injective K.subtype_injective]
  exact (Nat.card_congr er.toEquiv).trans hcard

theorem ggF4N2OmegaK_inf_K_selfCent
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .POmegaMinus 4 2 K)
    {g : G} (hgK : g ∈ K) (hg5 : g ^ 5 = 1)
    (hc : ∀ c ∈ Bs ⊓ K, g * c = c * g) : g ∈ Bs ⊓ K := by
  have hYC : Subgroup.zpowers y ≤ Subgroup.centralizer (K : Set G) := by
    rw [← inf_centralizer_eq_zpowers_of_sHat hNbr.1]
    exact inf_le_right
  exact ggBstar_inf_selfCent_of_split hR.1.2.1.2.1 hR.1.2.1.2.2.2
    (ggF4N2OmegaK_Bstar_split hR hNbr hL hK).1 hYC hgK hg5 hc

theorem ggF4N2OmegaK_internal_torus
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .POmegaMinus 4 2 K)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {Q : QuadraticForm F V} (hF : Nat.card F = 4) (hV : finrank F V = 8)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule F V, finrank F T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (e : ↥K ≃* ↥(orthDerived Q)) :
    ∃ τ : (Fin 3 → Multiplicative (ZMod 5)) →* ↥K,
      Function.Injective τ ∧ τ.range = (Bs ⊓ K).subgroupOf K ∧
      (∀ σ : Equiv.Perm (Fin 3), ∃ w : K, ∀ f,
        w * τ f * w⁻¹ = τ (SpCoord.permAut σ f)) ∧
      (∀ i : Fin 3, ∃ w : K, ∀ f,
        w * τ f * w⁻¹ = τ (SpCoord.sgnAut i f)) ∧
      (∀ n : K, n ∈ Subgroup.normalizer (((Bs ⊓ K).subgroupOf K : Subgroup K) : Set K) →
        ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 5),
          (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', n * τ f * n⁻¹ = τ f' →
            ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)) := by
  exact ggF4N2Bstar_internal_torus_of_selfCent hR.1.2.1.2.1
    (ggF4N2OmegaK_inf_K_card hR hNbr hL hK)
    (fun hgK hg5 hc => ggF4N2OmegaK_inf_K_selfCent hR hNbr hL hK hgK hg5 hc)
    hF hV hQ hT e

theorem ggF4N2OmegaK_twoLocal_torus
    {G : Type} [Group G] {K : Subgroup G}
    (hK : GGCentralImage .POmegaMinus 4 2 K) :
    ∃ T U : Subgroup G, T ≤ K ∧ U ≤ K ∧ IsElemAbelian 5 T ∧
      Nat.card T = 5 ^ 3 ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      T ≤ Subgroup.normalizer (U : Set G) := by
  classical
  let F := GaloisField 2 2
  let b : F := (minusCoeffs 2 2).1
  let c : F := (minusCoeffs 2 2).2
  have hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0 := minusCoeffs_irr 2 2
  obtain ⟨eK⟩ := ggN2OrthDerived_model_of_centralImage hK
  let eΩ : StatedOmega (StatedQuadMinus 4 F b c) ≃* orthDerived (quadMinus 4 F b c) :=
    CFSG.LocalAnalysis.WeakClosure81.statedOmegaEquivDerived (coe_quadMinus 4 F b c)
  let e : OrthRest.RMinus F 3 b c ≃* K :=
    (rMinusEquivStatedOmega F 3 b c).trans (eΩ.trans eK.symm)
  obtain ⟨U, E, hUne, hUp, hEN, hEab, hEcard⟩ :=
    OrthRestTail.torus_minus (m := 3) (n := 2) (p := 5) b c
      (GaloisField.card 2 2 (by norm_num)) (by norm_num) Nat.prime_five
      (by norm_num) (by norm_num) hbc
  let η : OrthRest.RMinus F 3 b c →* G := K.subtype.comp e.toMonoidHom
  have hη : Function.Injective η := K.subtype_injective.comp e.injective
  refine ⟨E.map η, U.map η, ?_, ?_, TableB.isElemAbelian_map hEab η, ?_, ?_, hUp.map η, ?_⟩
  · rintro _ ⟨t, _, rfl⟩
    exact (e t).2
  · rintro _ ⟨u, _, rfl⟩
    exact (e u).2
  · rw [Subgroup.card_map_of_injective hη, hEcard]
  · intro hbot
    exact hUne ((Subgroup.map_eq_bot_iff_of_injective _ hη).mp hbot)
  · exact (Subgroup.map_mono hEN).trans (Subgroup.le_normalizer_map η)

theorem ggF4N2OmegaK_outer_solvable
    {G : Type} [Group G] {K : Subgroup G}
    (hK : GGCentralImage .POmegaMinus 4 2 K) :
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) := by
  have hZ : Subgroup.center K = ⊥ := ggN2Center_eq_bot_of_centralImage hK
  let θ : (K ⧸ Subgroup.center K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact (orthogonal_geometry_classical_model_Schreier .POmegaMinus (Or.inr (Or.inr rfl))
      (ggN2Model_of_centralImage hK θ)).2.2

theorem ggF4N2OmegaK_centralizer_pRank_le_one
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .POmegaMinus 4 2 K) :
    CFSG.Open.pRank 5 (Subgroup.centralizer (K : Set G)) ≤ 1 := by
  obtain ⟨T, U, hTleK, hUleK, hTelem, hTcard, hUne, hU₂, hTnorm⟩ :=
    ggF4N2OmegaK_twoLocal_torus hK
  have hTdisj : Disjoint T ((Subgroup.center K).map K.subtype) := by
    rw [ggN2Center_eq_bot_of_centralImage hK, Subgroup.map_bot]
    exact disjoint_bot_right
  exact ggF4N2_pRank_five_centralizer_le_one_of_torus (ggF4N2Rank hR hL).2.2
    hTleK hUleK hTelem hTcard hUne hU₂ hTnorm hTdisj

theorem ggF4N2OmegaK_centralizer_le_normalizer
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .POmegaMinus 4 2 K) :
    Subgroup.centralizer ({y} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  have hst : LargeEvenStandardType 5 B x L := hR.1.1.2.2.2.2.2.2.2
  have hDJ : LargeEvenStdSub 5 B x L D J := hR.1.2.2
  have hneigh : LargeEvenIsNeighborOf 5 B x L y K := isNeighborOf_of_ggNbr hDJ hNbr
  have hcomp : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    (isComponentOf_of_isNeighborOf hst hneigh).1
  have hcyc : ∀ P : Subgroup G,
      P ≤ Subgroup.centralizer (K : Set G) → IsPGroup 5 P → IsCyclic P :=
    CFSG.all_pSubgroups_isCyclic_of_pRank_le_one Nat.prime_five (by norm_num)
      (ggF4N2OmegaK_centralizer_pRank_le_one hR hL hK)
  obtain ⟨T, _, hTleK, _, hTelem, hTcard, _, _, _⟩ := ggF4N2OmegaK_twoLocal_torus hK
  have hTcard5 : 5 < Nat.card T := by rw [hTcard]; norm_num
  exact ggF4N2_centralizer_le_normalizer_of_isComponentOf_of_cyclic
    hcomp hcyc hTleK hTelem hTcard5

theorem ggF4N2J_le_omega_neighbor
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .POmegaMinus 4 2 K) : J ≤ K := by
  have hS : CFSG.Assembly.LargeEvenSStar 5 B x L := hR.1.1.2.2.2.2.2.2.1
  have hJY := isComponentOf_inf_centralizer_of_stdSub hS hR.1.2.2.1 hNbr.2.1
  have hJCy : J ≤ Subgroup.centralizer ({y} : Set G) := hJY.1.trans inf_le_left
  have hJN : J ≤ Subgroup.normalizer (K : Set G) :=
    hJCy.trans (ggF4N2OmegaK_centralizer_le_normalizer hR hNbr hL hK)
  exact le_of_ggNbr_of_normalizes_of_outer_solvable hR.1.1 hR.1.2.2 hNbr hJN
    (ggF4N2OmegaK_outer_solvable hK)

theorem ggF4N2OmegaK_J_component
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .POmegaMinus 4 2 K) :
    CFSG.Assembly.IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) := by
  exact isComponentOf_inf_centralizer_of_ggNbr hR.1.1.2.2.2.2.2.2.1 hR.1.2.2 hNbr
    (ggF4N2J_le_omega_neighbor hR hNbr hL hK)

theorem ggF4N2OmegaK_plane_basis
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .POmegaMinus 4 2 K) :
    ∃ a : K, (a : G) ∈ D ∧ orderOf a = 5 ∧
      D = Subgroup.zpowers y ⊔ Subgroup.zpowers (a : G) ∧
      ∀ k : K, x * (k : G) * x⁻¹ = ((a * k * a⁻¹ : K) : G) := by
  classical
  obtain ⟨hxBs, hxNot, _, hDcl, hDcard, hDe⟩ := ggF4N2_x_data hR hNbr
  obtain ⟨rho, hrho, hker, hpow, hrange⟩ := ggF4N2OmegaK_inner_action hR hNbr hL hK
  let xB : Bs := ⟨x, hxBs⟩
  let a : K := rho xB
  have haInf : (a : G) ∈ Bs ⊓ K := by rw [← hrange]; exact ⟨xB, rfl⟩
  let aB : Bs := ⟨a, haInf.1⟩
  have hself : rho aB = a := by
    apply CFSG.mulAutConj_injective_of_center_eq_bot (ggN2Center_eq_bot_of_centralImage hK)
    rw [hrho]
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    rfl
  let cB : Bs := xB * aB⁻¹
  have hcKer : cB ∈ rho.ker := by
    change rho (xB * aB⁻¹) = 1
    rw [map_mul, map_inv, hself]
    exact mul_inv_cancel (rho xB)
  rw [hker] at hcKer
  have hcY : (cB : G) ∈ Subgroup.zpowers y := Subgroup.mem_subgroupOf.mp hcKer
  have hxD : x ∈ D := by rw [hDcl]; exact Subgroup.subset_closure (by simp)
  have hyD : y ∈ D := by rw [hDcl]; exact Subgroup.subset_closure (by simp)
  have hYD : Subgroup.zpowers y ≤ D := Subgroup.zpowers_le.mpr hyD
  have haD : (a : G) ∈ D := by
    have hmem := D.mul_mem (D.inv_mem (hYD hcY)) hxD
    have heq : (cB : G)⁻¹ * x = (a : G) := by
      change (x * (a : G)⁻¹)⁻¹ * x = (a : G)
      group
    rwa [heq] at hmem
  have haNe : a ≠ 1 := by
    intro ha
    have hxker : xB ∈ rho.ker := ha
    rw [hker] at hxker
    exact hxNot (Subgroup.mem_subgroupOf.mp hxker)
  have haOrder : orderOf a = 5 := orderOf_eq_prime (hpow xB) haNe
  have haNot : (a : G) ∉ Subgroup.zpowers y := by
    intro haY
    have haKer : aB ∈ rho.ker := by rw [hker]; exact haY
    have ha1 : rho aB = 1 := haKer
    rw [hself] at ha1
    exact haNe ha1
  have hspan := eq_sup_zpowers_of_card Nat.prime_five hDe hDcard hyD hNbr.1.2.2.1 haD haNot
  refine ⟨a, haD, haOrder, hspan, fun k => ?_⟩
  have h := congrArg (fun α : MulAut K => ((α k : K) : G)) (hrho xB)
  exact h.symm

theorem ggF4N2OmegaK_J_singleton_component
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .POmegaMinus 4 2 K) :
    ∃ a : K, (a : G) ∈ D ∧ orderOf a = 5 ∧
      D = Subgroup.zpowers y ⊔ Subgroup.zpowers (a : G) ∧
      CFSG.Assembly.IsComponentOf (J.subgroupOf K) (Subgroup.centralizer ({a} : Set K)) ∧
      ∀ k : K, x * (k : G) * x⁻¹ = ((a * k * a⁻¹ : K) : G) := by
  obtain ⟨a, haD, haO, hspan, hpoint⟩ := ggF4N2OmegaK_plane_basis hR hNbr hL hK
  have hcent : (K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K =
      Subgroup.centralizer ({a} : Set K) := by
    ext k
    change (k : G) ∈ K ⊓ Subgroup.centralizer ({x} : Set G) ↔
      k ∈ Subgroup.centralizer ({a} : Set K)
    constructor
    · intro hk
      have hkc : (k : G) * x = x * (k : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hk.2
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hfix : x * (k : G) * x⁻¹ = (k : G) := by rw [← hkc]; group
      have hafix := (hpoint k).symm.trans hfix
      exact ((mul_inv_eq_iff_eq_mul).mp hafix).symm
    · intro hk
      refine ⟨k.2, ?_⟩
      change (k : G) ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
      have hafix : a * k * a⁻¹ = k := by rw [← hk]; group
      have hfix := (hpoint k).trans (congrArg Subtype.val hafix)
      exact ((mul_inv_eq_iff_eq_mul).mp hfix).symm
  have hJG := ggF4N2OmegaK_J_component hR hNbr hL hK
  have hJK : CFSG.Assembly.IsComponentOf (J.subgroupOf K)
      ((K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr
      (CFSG.LocalAnalysis.GLTheoremA.S265.isComponentOf_subgroupOf inf_le_left
        (CFSG.Assembly.isComponentOf_iff_open.mp hJG))
  rw [hcent] at hJK
  exact ⟨a, haD, haO, hspan, hJK, hpoint⟩

end CFSG.StandardType
