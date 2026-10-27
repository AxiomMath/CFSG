module

public import CFSG.Quasithin.H13.ZCentLieCore
public import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers
public import CFSG.Quasithin.H13.NQCatLieCentralG2
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenLongCentralizer
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersCentral
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieFrame
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Quasithin.Vol2.Ch7Sec77A23Stmts
public import CFSG.Quasithin.Vol2.Ch7Sec77Inputs
public import CFSG.Sporadic.J4Base
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin.H13.ZCentLie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_pow_orderOf_eq_two {G : Type*} [Group G] {u : G} (hu1 : u ≠ 1) {n : ℕ}
    (hn : orderOf u = 2 ^ n) : orderOf (u ^ 2 ^ (n - 1)) = 2 := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hu1 (orderOf_eq_one_iff.1 (by rw [hn, pow_zero]))
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
    (by rw [hn]; exact pow_dvd_pow 2 (Nat.sub_le n 1)), hn,
    Nat.pow_div (Nat.sub_le n 1) two_pos, show n - (n - 1) = 1 by omega, pow_one]

theorem commute_conj_of_commute {G : Type*} [Group G] {d k x : G}
    (h : k * (d * x * d⁻¹) = d * x * d⁻¹ * k) : x * (d⁻¹ * k * d) = d⁻¹ * k * d * x := by
  have e1 : x * (d⁻¹ * k * d) = d⁻¹ * ((d * x * d⁻¹) * k) * d := by group
  have e2 : d⁻¹ * k * d * x = d⁻¹ * (k * (d * x * d⁻¹)) * d := by group
  rw [e1, e2, h]

theorem commute_of_commute_conj {G : Type*} [Group G] {d k y : G}
    (h : d⁻¹ * k * d * y = y * (d⁻¹ * k * d)) : k * (d * y * d⁻¹) = d * y * d⁻¹ * k := by
  have e1 : k * (d * y * d⁻¹) = d * ((d⁻¹ * k * d) * y) * d⁻¹ := by group
  have e2 : d * y * d⁻¹ * k = d * (y * (d⁻¹ * k * d)) * d⁻¹ := by group
  rw [e1, e2, h]

section Suzuki

theorem zCentAt_suzuki {a : ℕ} {K : Type} [Field K] [Finite K]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (P : Sylow 2 (suzukiGroup a K)) :
    ZCentAt (P : Subgroup (suzukiGroup a K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro u w k hu _ hu1 _ hcw hk
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 P.isPGroup') ⟨u, hu⟩
  rw [Subgroup.orderOf_mk] at hn
  have hyo := exists_pow_orderOf_eq_two hu1 hn
  obtain ⟨Q, -, hCQ, huniq⟩ :=
    (CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers ha hK).1 _ hyo
  have hPQ : P = Q := huniq P (pow_mem hu _)
  have hkC : k ∈ Subgroup.centralizer {u ^ 2 ^ (n - 1)} :=
    Subgroup.mem_centralizer_singleton_iff.2 (Commute.pow_right hk _).eq
  rw [hCQ, ← hPQ] at hkC
  exact (hcw k hkC).symm

theorem zCentAt_sylow_of_suzuki {X : Type} [Group X] [Finite X]
    {f : ℕ} (h : SuzukiModel X 2 f) (P : Sylow 2 X) : ZCentAt (P : Subgroup X) := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
  have : Finite K := ‹_›
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hf]
  exact zCentAt_sylow_of_mulEquiv e (fun Q => zCentAt_suzuki ha hK' Q) P

end Suzuki

section G2

open CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.Quasithin.H13.NQCat.LieCentral.G2 CFSG.QuasithinUnique.Setup.X6

variable {K : Type} [Field K] [Finite K] [CharP K 2]

noncomputable abbrev g2Sylow (K : Type) [Field K] :
    Subgroup ↥(adjointGroup Tag.G2 K) :=
  (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)

omit [Finite K] in
theorem center_mem_g2
    {x : ModGL Tag.G2 K} (hx : x ∈ posUnipotent Tag.G2 K)
    (hc : ∀ y ∈ posUnipotent Tag.G2 K, y * x = x * y) : ∃ c : K, x = gX rC c := by
  obtain ⟨a, r, u, v, b, c, rfl⟩ := exists_eq_prod_of_mem_posUnipotent hx
  have hB := hc _ (gX_mem_posUnipotent (d := rB) (by simp) (1 : K))
  have hV := hc _ (gX_mem_posUnipotent (d := rV) (by simp) (1 : K))
  have hU := hc _ (gX_mem_posUnipotent (d := rU) (by simp) (1 : K))
  have hA := hc _ (gX_mem_posUnipotent (d := rA) (by simp) (1 : K))
  have ha := a_eq_zero_of_commute (one_ne_zero : (1 : K) ≠ 0) hB
  obtain ⟨hr, hu⟩ := r_eq_zero_of_commute (one_ne_zero : (1 : K) ≠ 0) hV
  subst ha hr hu
  simp only [gX_zero, one_mul] at hU hA ⊢
  have hv := v_eq_zero_of_commute (a := 0) (u := 0) (one_ne_zero : (1 : K) ≠ 0)
    (by simpa [gX_zero] using hU)
  subst hv
  simp only [gX_zero, one_mul] at hA ⊢
  have hb := b_eq_zero_of_commute (a := 0) (one_ne_zero : (1 : K) ≠ 0)
    (by simpa [gX_zero] using hA)
  subst hb
  simp only [gX_zero, one_mul]
  exact ⟨c, rfl⟩

omit [Finite K] [CharP K 2] in
theorem torus_a_conj_c (t : Kˣ)
    (y : K) : torusElt .G2 K g2ia t * pinnedX .G2 K g2c y * (torusElt .G2 K g2ia t)⁻¹ =
      pinnedX .G2 K g2c ((t : K) * y) := by
  rw [root_torus_conjugation g2ia isRoot_g2c, show (∑ j, Tag.G2.cartan g2ia j * g2c j) = 1 by
    decide, zpow_one]

theorem zCentAt_g2 :
    ZCentAt (g2Sylow K) := by
  intro u w k hu hcu hu1 hw hcw hk
  have hcen : ∀ z : ↥(adjointGroup Tag.G2 K), z ∈ g2Sylow K → (∀ t ∈ g2Sylow K, z * t = t * z) →
      ∃ c : K, (z : ModGL Tag.G2 K) = pinnedX .G2 K g2c c := by
    intro z hz hzc
    refine center_mem_g2 hz fun y hy => ?_
    have := hzc ⟨y, posUnipotent_le_adjointGroup hy⟩ hy
    exact (congrArg Subtype.val this).symm
  obtain ⟨c₀, hc₀⟩ := hcen u hu hcu
  obtain ⟨c, hc⟩ := hcen w hw hcw
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    apply hu1
    apply Subtype.ext
    rw [hc₀, pinnedX_zero]
    rfl
  obtain ⟨d, hd⟩ : ∃ d : ModGL Tag.G2 K, d = torusElt .G2 K g2ia (Units.mk0 c₀ hc₀0) := ⟨_, rfl⟩
  have hdC : d ∈ adjointGroup Tag.G2 K := hd ▸ torusElt_mem_adjointGroup _ _
  have hdX : ∀ y : K, d * pinnedX .G2 K g2c y * d⁻¹ = pinnedX .G2 K g2c (c₀ * y) := by
    intro y
    rw [hd, torus_a_conj_c, Units.val_mk0]
  have hk' : d⁻¹ * (k : ModGL Tag.G2 K) * d ∈
      adjointGroup Tag.G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2c 1} := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hdC) k.2) hdC,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hku : (k : ModGL Tag.G2 K) * pinnedX .G2 K g2c c₀ =
        pinnedX .G2 K g2c c₀ * (k : ModGL Tag.G2 K) := by
      rw [← hc₀]
      exact congrArg Subtype.val hk
    have hX1 : pinnedX .G2 K g2c c₀ = d * pinnedX .G2 K g2c 1 * d⁻¹ := by
      rw [hdX, mul_one]
    exact (commute_conj_of_commute (hX1 ▸ hku)).symm
  obtain ⟨-, -, -, hCQL, -, -, -, -, hQ, -, -, hL⟩ := even_G2_highest_long_root_centralizer K
  have hQL : ∀ y : K, Commute (d⁻¹ * (k : ModGL Tag.G2 K) * d) (pinnedX .G2 K g2c y) := by
    intro y
    have hle : g2LongRadical K ⊔ g2RankOne K g2ir ≤
        Subgroup.centralizer {pinnedX .G2 K g2c y} := by
      refine sup_le (fun q hq => Subgroup.mem_centralizer_singleton_iff.2 ((hQ y).2 q hq).eq.symm)
        (fun l hl => Subgroup.mem_centralizer_singleton_iff.2 (hL l hl y).eq)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle (hCQL.le hk'))
  have hw' : (w : ModGL Tag.G2 K) = d * pinnedX .G2 K g2c (c₀⁻¹ * c) * d⁻¹ := by
    rw [hc, hdX, ← mul_assoc, mul_inv_cancel₀ hc₀0, one_mul]
  have key := commute_of_commute_conj (hQL (c₀⁻¹ * c)).eq
  rw [← hw'] at key
  exact Subtype.ext key

theorem zCentAt_sylow_of_g2
    {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 1 ≤ f)
    (h : ChevalleyExceptionalModel X .G2 2 f) (P : Sylow 2 X) : ZCentAt (P : Subgroup X) := by
  obtain ⟨L, _, _, hL, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 h.2
  have : CharP L 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 L) := finite_modGL
  refine zCentAt_sylow_of_mulEquiv e (fun Q => ?_) P
  have hU : IsPGroup 2 ((posUnipotent Tag.G2 L).subgroupOf (adjointGroup Tag.G2 L)) := by
    have h1 := (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := L) 2).1
    obtain ⟨-, h2, -⟩ := isSylowTwoOf_iff_isSylowOf.2 h1
    exact h2.of_equiv (Subgroup.subgroupOfEquivOfLe posUnipotent_le_adjointGroup).symm
  have hidx : ¬ 2 ∣ ((posUnipotent Tag.G2 L).subgroupOf (adjointGroup Tag.G2 L)).index :=
    (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := L) 2).1).2.2
  exact zCentAt_sylow (P₀ := hU.toSylow hidx) zCentAt_g2 Q

end G2

section Ree

open CFSG.LieType.Ree CFSG.LieType.Ree.LargeReeInvolution ReeTag

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem zCentAt_ree
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ZCentAt ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) := by
  intro u w k hu hcu hu1 hw hcw hk
  have hUΓ : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a :=
    reeFixedPosUnipotent_le_reeFixedBorel.trans reeFixedBorel_le_reeGamma
  have hcen : ∀ z : ↥(F4.reeGamma K a), z ∈ (F4.reeFixedPosUnipotent K a).subgroupOf
      (F4.reeGamma K a) → (∀ t ∈ (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a),
        z * t = t * z) → ∃ c : K, (z : ModGL F4.tag K) = centralZ K a c := by
    intro z hz hzc
    have hmem : (z : ModGL F4.tag K) ∈ ((Subgroup.center (F4.reeFixedPosUnipotent K a)).map
        (F4.reeFixedPosUnipotent K a).subtype : Set (ModGL F4.tag K)) := by
      refine ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun y => ?_, rfl⟩
      have := hzc ⟨y, hUΓ y.2⟩ y.2
      exact Subtype.ext (congrArg Subtype.val this).symm
    rw [coe_center_eq_range_centralZ ha hK] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩
  obtain ⟨c₀, hc₀⟩ := hcen u hu hcu
  obtain ⟨c, hc⟩ := hcen w hw hcw
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    apply hu1
    apply Subtype.ext
    rw [hc₀, centralZ_zero]
    rfl
  have hfrob : Function.Bijective fun x : K => x ^ 2 ^ a := by
    have : CharP K 2 := ‹CharP K F4.prime›
    refine Finite.injective_iff_bijective.1 fun x y hxy => ?_
    have h1 : (x - y) ^ 2 ^ a = 0 := by
      rw [sub_pow_char_pow, hxy, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.1 h1)
  obtain ⟨s, hs⟩ := hfrob.2 c₀
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hc₀0 (by rw [← hs]; simp)
  obtain ⟨τ, hτ⟩ : ∃ τ : ModGL F4.tag K, τ = LargeReeCover.torusPair a (Units.mk0 s hs0, 1) :=
    ⟨_, rfl⟩
  have hτΓ : τ ∈ F4.reeGamma K a := hτ ▸ LargeReeCover.torusPair_mem_reeGamma a hK _
  have hτz : ∀ y : K, τ * centralZ K a y * τ⁻¹ = centralZ K a (c₀ * y) := by
    intro y
    rw [hτ, torusPair_conj_centralZ hK, Units.val_mk0]
    simp only at hs
    rw [hs]
  have hk' : τ⁻¹ * (k : ModGL F4.tag K) * τ ∈ F4.reeGamma K a ⊓
      Subgroup.centralizer {centralZ K a 1} := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hτΓ) k.2) hτΓ,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hku : (k : ModGL F4.tag K) * centralZ K a c₀ = centralZ K a c₀ * (k : ModGL F4.tag K) := by
      rw [← hc₀]
      exact congrArg Subtype.val hk
    have hz1 : centralZ K a c₀ = τ * centralZ K a 1 * τ⁻¹ := by rw [hτz, mul_one]
    rw [hz1] at hku
    exact (commute_conj_of_commute hku).symm
  have hk'' := (reeGamma_inf_centralizer_eq ha hK).le hk'
  have hw' : (w : ModGL F4.tag K) = τ * centralZ K a (c₀⁻¹ * c) * τ⁻¹ := by
    rw [hc, hτz, ← mul_assoc, mul_inv_cancel₀ hc₀0, one_mul]
  have h1 := Subgroup.mem_centralizer_singleton_iff.1
    (centralizerZ_le_centralizer ha hK (c₀⁻¹ * c) hk'')
  have key := commute_of_commute_conj h1
  rw [← hw'] at key
  exact Subtype.ext key

omit [Finite K] [CharP K F4.prime] in
theorem zCentAt_sylow_of_ree
    {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : ReeTitsModel X .twistedF4 2 f) (P : Sylow 2 X) : ZCentAt (P : Subgroup X) := by
  obtain ⟨-, -, -, -, -, hiso⟩ := large_Ree_model_Schreier X 2 f h
  obtain ⟨hadm, a, hfa, L, _, _, hL, hw⟩ := h
  have hf3 : 3 ≤ f := hadm.2.2.2.2.2
  have ha : 1 ≤ a := by omega
  have : CharP L F4.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hL
  have hL' : Nat.card L = 2 ^ (2 * a + 1) := by rw [hL, hfa]
  obtain ⟨e⟩ := hiso a L hfa hL hw
  refine zCentAt_sylow_of_mulEquiv e (fun Q => ?_) P
  have : Finite ↥(F4.reeGamma L a) := Finite.of_equiv X e.toEquiv
  obtain ⟨⟨S, hS⟩, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_Sylow_center a ha L hL'
  refine zCentAt_sylow (P₀ := S) ?_ Q
  rw [hS]
  exact zCentAt_ree ha hL'

end Ree

end CFSG.Quasithin.H13.ZCentLie
