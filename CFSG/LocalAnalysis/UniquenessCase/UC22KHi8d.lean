module

public import CFSG.LocalAnalysis.UniquenessCase.UC22KHi8c
public import CFSG.LocalAnalysis.UniquenessCase.UC22KHi2r
import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
import CFSG.Quasithin.Vol2.Ch11L2Q5cMult
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open P22x P22s
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace P22k8

omit [Finite G] in
theorem mem_normalizer_subgroupOf {M A : Subgroup G} {g : G} (hgM : g ∈ M) (hg : g ∈ normalizer (A : Set G)) :
    (⟨g, hgM⟩ : ↥M) ∈ normalizer ((A.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.1 hg h

omit [Finite G] in
theorem mem_normalizer_map_subtype {M : Subgroup G} {P : Subgroup ↥M} {g : ↥M}
    (hg : g ∈ normalizer (P : Set ↥M)) : (g : G) ∈ normalizer ((P.map M.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg y).1 hy, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hy' : g⁻¹ * y * g ∈ P := by
      refine (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * y * g)).2 ?_
      have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rw [e]
      exact hy
    refine ⟨g⁻¹ * y * g, hy', ?_⟩
    have hyx' : (y : G) = (g : G) * x * (g : G)⁻¹ := hyx
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hyx']
    group

noncomputable abbrev radX (D : Data G) (Y : Subgroup (MBar D.M D.U)) : Subgroup ↥D.M :=
  (rad118 D ⊓ preMbar D Y).subgroupOf D.M

noncomputable abbrev kLiftM (D : Data G) (Y : Subgroup (MBar D.M D.U)) : Subgroup ↥D.M :=
  (CFSG.perfectResidual ↥(radX D Y)).map (radX D Y).subtype

noncomputable def kLift (D : Data G) (Y : Subgroup (MBar D.M D.U)) : Subgroup G :=
  (kLiftM D Y).map D.M.subtype

theorem kLift_le_M (D : Data G) (Y : Subgroup (MBar D.M D.U)) : kLift D Y ≤ D.M :=
  Subgroup.map_subtype_le _

theorem kLift_subgroupOf (D : Data G) (Y : Subgroup (MBar D.M D.U)) :
    (kLift D Y).subgroupOf D.M = kLiftM D Y :=
  Subgroup.comap_map_eq_self_of_injective D.M.subtype_injective _

theorem kLift_le (D : Data G) (Y : Subgroup (MBar D.M D.U)) : kLift D Y ≤ rad118 D ⊓ preMbar D Y := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' : y ∈ radX D Y := Subgroup.map_subtype_le (CFSG.perfectResidual ↥(radX D Y)) hy
  exact hy'

theorem kLift_perfect (D : Data G) (Y : Subgroup (MBar D.M D.U)) : ⁅kLift D Y, kLift D Y⁆ = kLift D Y := by
  have hP : ⁅kLiftM D Y, kLiftM D Y⁆ = kLiftM D Y :=
    Subgroup.isPerfect_iff.1 (CFSG.SignalizerFunctorTheorem.Nonsolvable.isPerfect_perfectResidual_map (radX D Y))
  rw [kLift, ← Subgroup.map_commutator, hP]

theorem commutator_eq_self_of_isL2Ev {X : Type} [Group X] {Y : Subgroup X} {n : ℕ} (hY : IsL2Ev ↥Y n)
    (hn : 2 ≤ n) : ⁅Y, Y⁆ = Y := by
  classical
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hY
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨a, -, ha⟩ : ∃ a ∈ (Finset.univ : Finset F), a ∉ ({0, 1, -1} : Finset F) :=
    Finset.exists_mem_notMem_of_card_lt_card (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact lt_of_le_of_lt Finset.card_le_three (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  obtain ⟨ha0, ha1, ha2⟩ := ha
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) := by
    refine ⟨Matrix.SL2.commutator_eq_top ha0 fun h => ?_⟩
    rcases sq_eq_one_iff.mp h with h | h
    · exact ha1 h
    · exact ha2 h
  set e' : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥Y :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).trans e.symm with he'
  haveI : Group.IsPerfect ↥Y := Group.IsPerfect.ofSurjective (f := e'.toMonoidHom) e'.surjective
  exact Subgroup.isPerfect_iff.1 inferInstance

theorem six_lt_card_of_isL2Ev {X : Type} [Group X] {n : ℕ} (hX : IsL2Ev X n) (hn : 2 ≤ n) : 6 < Nat.card X := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hX
  rw [Nat.card_congr e.toEquiv, card_statedSL_two, hF]
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h15 : 15 ≤ (2 ^ n) ^ 2 - 1 := by
    have : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
    omega
  nlinarith

theorem radX_map (D : Data G) (h118U : C118 D ⊥ D.U) {Y : Subgroup (MBar D.M D.U)} (hYp : ⁅Y, Y⁆ = Y) :
    (radX D Y).map (QuotientGroup.mk' (kerAct D.M D.U).normalCore) = Y := by
  have hV := uc22p22xf_hV D
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ rad118 D ⊓ preMbar D Y := hx
    obtain ⟨hxM, hxY⟩ := (mem_preMbar D).1 hx'.2
    exact hxY
  · intro y hy
    have hy' : y ∈ (⁅(⊤ : Subgroup ↥D.M), (⊤ : Subgroup ↥D.M)⁆).map
        (QuotientGroup.mk' (kerAct D.M D.U).normalCore) := by
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
      rw [← hYp] at hy
      exact Subgroup.commutator_mono le_top le_top hy
    obtain ⟨z, hz, rfl⟩ := hy'
    have hzG : (z : G) ∈ ⁅D.M, D.M⁆ := by
      have hcomm : ⁅D.M, D.M⁆ = (⁅(⊤ : Subgroup ↥D.M), (⊤ : Subgroup ↥D.M)⁆).map D.M.subtype := by
        rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
      rw [hcomm]
      exact ⟨z, hz, rfl⟩
    obtain ⟨r, hr, c, hc, hrc⟩ := rad118_lift D h118U _ hzG
    have hrM : r ∈ D.M := rad118_le_M D hr
    have hzeq : z = ⟨r, hrM⟩ * ⟨c, hc.1⟩ := Subtype.ext hrc
    have hc1 : (QuotientGroup.mk ⟨c, hc.1⟩ : MBar D.M D.U) = 1 := (uc22br_gt_mk_eq_one_iff hV _).2 hc.2
    have hrz : (QuotientGroup.mk ⟨r, hrM⟩ : MBar D.M D.U) = QuotientGroup.mk' (kerAct D.M D.U).normalCore z := by
      rw [hzeq, QuotientGroup.mk'_apply, QuotientGroup.mk_mul, hc1, mul_one]
    refine ⟨⟨r, hrM⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hr, (mem_preMbar D).2 ⟨hrM, ?_⟩⟩), hrz⟩
    rw [hrz]
    exact hy

theorem kLift_image (D : Data G) (h118U : C118 D ⊥ D.U) {Y : Subgroup (MBar D.M D.U)} (hYp : ⁅Y, Y⁆ = Y) :
    mbarImage D.M D.U (kLift D Y) = Y := by
  rw [mbarImage, kLift_subgroupOf, kLiftM, CFSG.SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map,
    radX_map D h118U hYp]
  exact CFSG.SignalizerFunctorTheorem.Nonsolvable.perfectResidual_map_eq_of_isPerfect (Subgroup.isPerfect_iff.2 hYp)

theorem mem_normalizer_kLift (D : Data G) {Y : Subgroup (MBar D.M D.U)} {g : G} (hg : g ∈ D.M)
    (hgY : (QuotientGroup.mk ⟨g, hg⟩ : MBar D.M D.U) ∈ normalizer (Y : Set (MBar D.M D.U))) :
    g ∈ normalizer (kLift D Y : Set G) := by
  have h1 : g ∈ normalizer ((rad118 D ⊓ preMbar D Y : Subgroup G) : Set G) :=
    mem_normalizer_inf (M_le_normalizer_rad118 D hg) (mem_normalizer_preMbar D hg hgY)
  have h2 := mem_normalizer_subgroupOf hg h1
  have h3 : (⟨g, hg⟩ : ↥D.M) ∈ normalizer ((kLiftM D Y : Subgroup ↥D.M) : Set ↥D.M) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.normalizer_le_normalizer_perfectResidual_map (radX D Y) h2
  exact mem_normalizer_map_subtype h3

theorem isSubnormal_nb (D : Data G) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb)
    (i : Fin m) : (Nb i).IsSubnormal := by
  have hNbn : (mbarImage D.M D.U (proofN D)).Normal :=
    uc22br4_mbarImage_normal D.M D.U _ (uc22p22e_jOf_le_self D.M) (uc22p22t_M_le_normalizer_jOf D)
  have hle : Nb i ≤ mbarImage D.M D.U (proofN D) := (le_iSup Nb i).trans hNb.1.1.le
  have hnorm : mbarImage D.M D.U (proofN D) ≤ normalizer (Nb i : Set (MBar D.M D.U)) := fun g hg =>
    Subgroup.mem_normalizer_iff.2 fun x =>
      ⟨fun hx => uc22p22v_internalDirect_conj hNb.1 i g hg x hx, fun hx => by
        have := uc22p22v_internalDirect_conj hNb.1 i g⁻¹ (inv_mem hg) _ hx
        simpa [mul_assoc] using this⟩
  exact Subgroup.IsSubnormal.step _ _ hle hNbn.isSubnormal (Subgroup.normal_subgroupOf_of_le_normalizer hnorm)

theorem kLiftM_isSubnormal (D : Data G) {Y : Subgroup (MBar D.M D.U)} (hY : Y.IsSubnormal) :
    (kLiftM D Y).IsSubnormal := by
  have h1 : radX D Y = (rad118 D).subgroupOf D.M ⊓ (preMbar D Y).subgroupOf D.M := by
    ext x
    exact Iff.rfl
  have h2 : (preMbar D Y).subgroupOf D.M = Y.comap (QuotientGroup.mk' (kerAct D.M D.U).normalCore) := by
    rw [preMbar]
    exact Subgroup.comap_map_eq_self_of_injective D.M.subtype_injective _
  have hR : ((rad118 D).subgroupOf D.M).IsSubnormal :=
    (Subgroup.normal_subgroupOf_of_le_normalizer (M_le_normalizer_rad118 D)).isSubnormal
  have hX : (radX D Y).IsSubnormal := by
    rw [h1, h2]
    exact hR.inf (hY.comap _)
  exact CFSG.SignalizerFunctorTheorem.Nonsolvable.isSubnormal_perfectResidual_map hX

theorem ker_le_of_rad118 (D : Data G) {Y : Subgroup (MBar D.M D.U)} {n : ℕ} (hY : IsL2Ev ↥Y n) (hn : 3 ≤ n)
    {K : Subgroup G} (hKR : K ≤ rad118 D) (hKp : ⁅K, K⁆ = K) (himg : mbarImage D.M D.U K = Y) :
    K ⊓ centralizer (D.U : Set G) ≤ pCoreOf 2 K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := uc22p22xf_hV D
  have hKM : K ≤ D.M := hKR.trans (rad118_le_M D)
  have hMQ : D.M ≤ normalizer ((pCoreOf 2 D.M : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M
  have hQ2 : IsPGroup 2 (pCoreOf 2 D.M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M
  have hmem : ∀ k : ↥K,
      ((QuotientGroup.mk' (kerAct D.M D.U).normalCore).comp (Subgroup.inclusion hKM)) k ∈ Y := fun k => by
    rw [← himg]
    exact ⟨⟨k, hKM k.2⟩, k.2, rfl⟩
  set πK : ↥K →* ↥Y :=
    ((QuotientGroup.mk' (kerAct D.M D.U).normalCore).comp (Subgroup.inclusion hKM)).codRestrict Y hmem
    with hπKdef
  have hπK : ∀ k : ↥K, ((πK k : ↥Y) : MBar D.M D.U) = QuotientGroup.mk ⟨k, hKM k.2⟩ := fun k => rfl
  have hπsurj : Function.Surjective πK := by
    intro y
    have hy : (y : MBar D.M D.U) ∈ mbarImage D.M D.U K := by
      rw [himg]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hker : πK.ker = (K ⊓ centralizer (D.U : Set G)).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : (QuotientGroup.mk ⟨k, hKM k.2⟩ : MBar D.M D.U) = 1 := by
        rw [← hπK, h]
        rfl
      exact ⟨k.2, (uc22br_gt_mk_eq_one_iff hV ⟨k, hKM k.2⟩).1 h1⟩
    · rintro ⟨-, hkc⟩
      apply Subtype.ext
      rw [hπK]
      exact (uc22br_gt_mk_eq_one_iff hV ⟨k, hKM k.2⟩).2 hkc
  have hKQ : K ≤ normalizer ((pCoreOf 2 D.M ⊓ K : Subgroup G) : Set G) := fun k hk =>
    mem_normalizer_inf (hMQ (hKM hk)) (Subgroup.le_normalizer hk)
  have hQC : pCoreOf 2 D.M ⊓ K ≤ centralizer (D.U : Set G) := by
    set Qb : Subgroup ↥Y := (mbarImage D.M D.U (pCoreOf 2 D.M ⊓ K)).subgroupOf Y with hQbdef
    have hQle : mbarImage D.M D.U (pCoreOf 2 D.M ⊓ K) ≤ Y := by
      rw [← himg]
      exact mbarImage_mono D.M D.U inf_le_right
    have hQb2 : IsPGroup 2 Qb := by
      have h1 : IsPGroup 2 (mbarImage D.M D.U (pCoreOf 2 D.M ⊓ K)) :=
        ((hQ2.to_le inf_le_left).comap_subtype (K := D.M)).map _
      exact h1.comap_subtype
    have hQbn : Qb.Normal := by
      constructor
      intro q hq y
      obtain ⟨w, hw, hwq⟩ := hq
      obtain ⟨k, rfl⟩ := hπsurj y
      have hwQK : (w : G) ∈ pCoreOf 2 D.M ⊓ K := hw
      have hc : (k : G) * w * (k : G)⁻¹ ∈ pCoreOf 2 D.M ⊓ K := (mem_normalizer_iff.1 (hKQ k.2) w).1 hwQK
      refine ⟨⟨k, hKM k.2⟩ * w * ⟨k, hKM k.2⟩⁻¹, hc, ?_⟩
      change (QuotientGroup.mk' _ (⟨k, hKM k.2⟩ * w * ⟨k, hKM k.2⟩⁻¹) : MBar D.M D.U) =
        ((πK k * q * (πK k)⁻¹ : ↥Y) : MBar D.M D.U)
      rw [map_mul, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hπK]
      congr 2
    have hbot := P22so.eq_bot_of_normal_of_isL2Ev hY hQbn hQb2
    intro x hx
    have hxM : x ∈ D.M := hKM hx.2
    have hxQ : (⟨QuotientGroup.mk ⟨x, hxM⟩, hQle ⟨⟨x, hxM⟩, hx, rfl⟩⟩ : ↥Y) ∈ Qb := ⟨⟨x, hxM⟩, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hxQ
    exact (uc22br_gt_mk_eq_one_iff hV ⟨x, hxM⟩).1 (congrArg Subtype.val hxQ)
  haveI hP'n : ((pCoreOf 2 D.M ⊓ K).subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKQ
  haveI hA'n : ((K ⊓ centralizer (D.U : Set G)).subgroupOf K).Normal := by
    rw [← hker]
    exact πK.normal_ker
  have hPA : (pCoreOf 2 D.M ⊓ K).subgroupOf K ≤ (K ⊓ centralizer (D.U : Set G)).subgroupOf K := fun x hx =>
    ⟨x.2, hQC hx⟩
  haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hKp
  have hZc : ((K ⊓ centralizer (D.U : Set G)).subgroupOf K).map
      (QuotientGroup.mk' ((pCoreOf 2 D.M ⊓ K).subgroupOf K)) ≤
        Subgroup.center (↥K ⧸ (pCoreOf 2 D.M ⊓ K).subgroupOf K) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    induction y using QuotientGroup.induction_on with
    | H k =>
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have ha' : (a : G) ∈ K ⊓ centralizer (D.U : Set G) := ha
      have h1 := rad118_centr D (hKR (K.inv_mem ha'.1)) ((centralizer (D.U : Set G)).inv_mem ha'.2)
        (hKR (K.inv_mem k.2))
      show (((k * a)⁻¹ * (a * k) : ↥K) : G) ∈ pCoreOf 2 D.M ⊓ K
      refine ⟨?_, ((k * a)⁻¹ * (a * k)).2⟩
      have e : (((k * a)⁻¹ * (a * k) : ↥K) : G) =
          (a : G)⁻¹ * (k : G)⁻¹ * (a : G)⁻¹⁻¹ * (k : G)⁻¹⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact h1
  obtain ⟨F, _, _, hF, ⟨eY⟩⟩ := hY
  have e : (↥K ⧸ (pCoreOf 2 D.M ⊓ K).subgroupOf K) ⧸ ((K ⊓ centralizer (D.U : Set G)).subgroupOf K).map
      (QuotientGroup.mk' ((pCoreOf 2 D.M ⊓ K).subgroupOf K)) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientQuotientEquivQuotient _ _ hPA).trans
      ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        ((QuotientGroup.quotientKerEquivOfSurjective πK hπsurj).trans
          (eY.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm)))
  rcases CFSG.Quasithin.Vol2.Ch11.SecH.as_I_1_3_L2_holds n (by omega) F hF _ inferInstance _ hZc ⟨e⟩ with
    hZ | ⟨hn2, -, -⟩
  · intro x hx
    have hxZ : QuotientGroup.mk' ((pCoreOf 2 D.M ⊓ K).subgroupOf K) (⟨x, hx.1⟩ : ↥K) ∈
        ((K ⊓ centralizer (D.U : Set G)).subgroupOf K).map
          (QuotientGroup.mk' ((pCoreOf 2 D.M ⊓ K).subgroupOf K)) := ⟨⟨x, hx.1⟩, hx, rfl⟩
    rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxZ
    have hxQ : x ∈ pCoreOf 2 D.M ⊓ K := hxZ
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hKQ (hQ2.to_le inf_le_left) hxQ
  · omega

theorem kLift_isKLift (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (h118U : C118 D ⊥ D.U) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ}
    {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb) (i : Fin m) {n : ℕ}
    (hn : IsL2Ev ↥(Nb i) n) (hn3 : 3 ≤ n) : KLift D (Nb i) (kLift D (Nb i)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := uc22p22xf_hV D
  have hYp := commutator_eq_self_of_isL2Ev hn (by omega)
  have himg := kLift_image D h118U hYp
  have hKR : kLift D (Nb i) ≤ rad118 D := (kLift_le D (Nb i)).trans inf_le_left
  have hsub : ((kLift D (Nb i)).subgroupOf D.M).IsSubnormal := by
    rw [kLift_subgroupOf]
    exact kLiftM_isSubnormal D (isSubnormal_nb D hNb i)
  refine ⟨kLift_le_M D (Nb i), kLift_perfect D (Nb i), himg,
    ker_le_of_rad118 D hn hn3 hKR (kLift_perfect D (Nb i)) himg, fun s hs => ?_, fun x hx => ?_,
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_of_subnormalIn D.sylowM (kLift_le_M D (Nb i)) hsub,
    hsub⟩
  · exact mem_normalizer_kLift D (proofS_le_M D hs) (uc22p22x_S_normalizes D Ch h2 h3 h51 hH c m Nb hNb i hs).1
  · have hx1 : (QuotientGroup.mk ⟨x, hx.1⟩ : MBar D.M D.U) = 1 :=
      (uc22br_gt_mk_eq_one_iff hV ⟨x, hx.1⟩).2 hx.2
    refine mem_normalizer_kLift D hx.1 ?_
    rw [hx1]
    exact one_mem _

end P22k8

open P22k8

theorem uc22k_Hi_exists_eight (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (h640 : UC6.R6_40_1 D) (h118U : C118 D ⊥ D.U)
    (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb)
    (i : Fin m) {n : ℕ} (hn : IsL2Ev ↥(Nb i) n) (hn3 : 3 ≤ n) : ∃ H : Subgroup G, HiPkgK D (Nb i) H :=
  ⟨_, uc22k_hiPkgK_of_klift D Ch h2 h3 h51 h640 hH c hNb (kLift_isKLift D Ch h2 h3 h51 h118U hH c hNb i hn hn3)
    (six_lt_card_of_isL2Ev hn (by omega))⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
