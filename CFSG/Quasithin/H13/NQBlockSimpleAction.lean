module

public import CFSG.Quasithin.H13.NQBlockSimpleCore
public import CFSG.Quasithin.H13.NQBlockSourceRank
public import CFSG.Quasithin.H13.NQBlockSourceGlue
public import CFSG.Quasithin.H13.NQBlockFiveModelRigidity

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open Module
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace CFSG.QuasithinUnique.Setup.Family
open scoped commutatorElement IsMulCommutative

section Glue

variable {G : Type} [Group G] (W : Subgroup G) [IsElementaryAbelian 2 W]

theorem conjImage_mono {E F : Subgroup G} (hEF : E ≤ F) (hF : F ≤ normalizer (W : Set G)) :
    conjImage W (hEF.trans hF) ≤ conjImage W hF := by
  rintro _ ⟨⟨e, he⟩, rfl⟩
  exact ⟨⟨e, hEF he⟩, rfl⟩

theorem relIndex_conjImage_dvd {E F : Subgroup G} (hEF : E ≤ F)
    (hF : F ≤ normalizer (W : Set G)) :
    (conjImage W (hEF.trans hF)).relIndex (conjImage W hF) ∣ E.relIndex F := by
  set f := (conjGL W).comp (Subgroup.inclusion hF) with hfdef
  have e : (conjImage W (hEF.trans hF)).subgroupOf f.range =
      (E.subgroupOf F).map f.rangeRestrict := by
    ext ⟨x, hx⟩
    constructor
    · intro h
      obtain ⟨⟨e, he⟩, hex⟩ := Subgroup.mem_subgroupOf.mp h
      exact Subgroup.mem_map.mpr ⟨⟨e, hEF he⟩, Subgroup.mem_subgroupOf.mpr he,
        Subtype.ext hex⟩
    · intro h
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h
      exact Subgroup.mem_subgroupOf.mpr
        ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, congrArg Subtype.val hyx⟩
  change ((conjImage W (hEF.trans hF)).subgroupOf f.range).index ∣ (E.subgroupOf F).index
  rw [e]
  exact Subgroup.index_map_dvd _ f.rangeRestrict_surjective

theorem conjImage_equiv_of_simple {B : Subgroup G} (hB : B ≤ normalizer (W : Set G))
    (hs : IsSimpleGroup (↥B ⧸ CFSG.pCore 2 ↥B)) (hO : pCoreOf 2 B ≤ centralizer (W : Set G))
    (hnt : ¬ B ≤ centralizer (W : Set G)) :
    B ⊓ centralizer (W : Set G) ≤ pCoreOf 2 B ∧
      Nonempty (↥(conjImage W hB) ≃* ↥B ⧸ CFSG.pCore 2 ↥B) := by
  classical
  set f := (conjGL W).comp (Subgroup.inclusion hB) with hfdef
  set P := CFSG.pCore 2 ↥B with hPdef
  have hmemk : ∀ b : ↥B, b ∈ f.ker ↔ (b : G) ∈ centralizer (W : Set G) := fun b => by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, conjGL_eq_one_iff]
    rfl
  have hPk : P ≤ f.ker := fun b hb =>
    (hmemk b).mpr (hO ((mem_pCore_iff_mem_pCoreOf b).mp hb))
  have hkP : f.ker ≤ P := by
    have : (f.ker.map (QuotientGroup.mk' P)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective P)
    have : IsSimpleGroup (↥B ⧸ P) := hs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.ker.map (QuotientGroup.mk' P)) with h0 | h0
    · intro b hb
      have h1 : QuotientGroup.mk' P b ∈ f.ker.map (QuotientGroup.mk' P) := ⟨b, hb, rfl⟩
      rw [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    · exfalso
      apply hnt
      intro b hb
      have h1 : QuotientGroup.mk' P ⟨b, hb⟩ ∈ f.ker.map (QuotientGroup.mk' P) := by
        rw [h0]
        exact Subgroup.mem_top _
      obtain ⟨k, hk, hkb⟩ := h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkb
      have h3 : (⟨b, hb⟩ : ↥B) ∈ f.ker := by
        have h2 : (⟨b, hb⟩ : ↥B) = k * (k⁻¹ * ⟨b, hb⟩) := by group
        rw [h2]
        exact mul_mem hk (hPk hkb)
      exact (hmemk _).mp h3
  have hkeq : f.ker = P := le_antisymm hkP hPk
  refine ⟨fun g hg => ?_, ⟨(QuotientGroup.quotientKerEquivRange f).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hkeq)⟩⟩
  have h1 : (⟨g, hg.1⟩ : ↥B) ∈ f.ker := (hmemk _).mpr hg.2
  rw [hkeq] at h1
  exact (mem_pCore_iff_mem_pCoreOf _).mp h1

theorem mem_commutator_iff_commSpace {Y : Subgroup G} (hY : Y ≤ normalizer (W : Set G)) {v : G} :
    v ∈ ⁅W, Y⁆ ↔ ∃ hvW : v ∈ W,
      Additive.ofMul (⟨v, hvW⟩ : ↥W) ∈ CFSG.LocalAnalysis.commSpace ⊤ (conjImage W hY) := by
  constructor
  · exact commutator_mem_commSpace W hY
  · rintro ⟨hvW, hv⟩
    suffices h : ∀ u ∈ CFSG.LocalAnalysis.commSpace ⊤ (conjImage W hY),
        ((Additive.toMul u : ↥W) : G) ∈ ⁅W, Y⁆ from h _ hv
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, w, -, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := (mem_conjImage W hY).mp hg
      have e : ((Additive.toMul (((conjGL W ⟨y, hY hy⟩ : (Module.End (ZMod 2) (Additive ↥W))ˣ) :
          Module.End (ZMod 2) (Additive ↥W)) w - w) : ↥W) : G) =
          ⁅y, ((Additive.toMul w : ↥W) : G)⁆ := by
        rw [toMul_sub, Subgroup.coe_div, conjGL_apply, commutatorElement_def, div_eq_mul_inv]
      rw [e, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hy (Additive.toMul w).2
    | zero => exact one_mem _
    | add x y _ _ hx hy => exact mul_mem hx hy
    | smul c x _ hx =>
      rcases zmod_two_eq_zero_or_one c with rfl | rfl
      · rw [zero_smul]
        exact one_mem _
      · rw [one_smul]
        exact hx

@[expose] noncomputable def commEquiv {Y : Subgroup G} (hY : Y ≤ normalizer (W : Set G)) :
    ↥⁅W, Y⁆ ≃* Multiplicative ↥(CFSG.LocalAnalysis.commSpace ⊤ (conjImage W hY)) where
  toFun u := Multiplicative.ofAdd
    ⟨Additive.ofMul ⟨u, ((mem_commutator_iff_commSpace W hY).mp u.2).1⟩,
      ((mem_commutator_iff_commSpace W hY).mp u.2).2⟩
  invFun c := ⟨((Additive.toMul (Multiplicative.toAdd c).1 : ↥W) : G),
    (mem_commutator_iff_commSpace W hY).mpr ⟨(Additive.toMul (Multiplicative.toAdd c).1).2,
      (Multiplicative.toAdd c).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end Glue

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCoreOf_of_commutator_mem {B : Subgroup G} (hs : IsSimpleGroup (↥B ⧸ CFSG.pCore 2 ↥B))
    (hnc : ∃ a b : ↥B ⧸ CFSG.pCore 2 ↥B, a * b ≠ b * a) {z : G} (hz : z ∈ B)
    (hc : ∀ b ∈ B, ⁅z, b⁆ ∈ pCoreOf 2 B) : z ∈ pCoreOf 2 B := by
  classical
  have : IsSimpleGroup (↥B ⧸ CFSG.pCore 2 ↥B) := hs
  obtain ⟨a, b, hab⟩ := hnc
  have hZ : center (↥B ⧸ CFSG.pCore 2 ↥B) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (↥B ⧸ CFSG.pCore 2 ↥B)) with
      h0 | h0
    · exact h0
    · exact absurd ((mem_center_iff.mp (h0 ▸ mem_top b)) a) hab
  have hmem : (QuotientGroup.mk (⟨z, hz⟩ : ↥B) : ↥B ⧸ CFSG.pCore 2 ↥B) ∈
      center (↥B ⧸ CFSG.pCore 2 ↥B) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      mem_pCore_iff_mem_pCoreOf]
    have h1 : ⁅z, ((b' : ↥B) : G)⁻¹⁆ ∈ pCoreOf 2 B := hc _ (B.inv_mem b'.2)
    change (b' * z : G)⁻¹ * (z * b') ∈ pCoreOf 2 B
    have e : ((b' : G) * z)⁻¹ * (z * b') = z⁻¹ * ⁅z, ((b' : ↥B) : G)⁻¹⁆⁻¹ * z⁻¹⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    have hzinv : z⁻¹ ∈ normalizer (pCoreOf 2 B : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 B (B.inv_mem hz)
    exact (mem_normalizer_iff.mp hzinv _).mp (inv_mem h1)
  rw [hZ, mem_bot, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at hmem
  exact hmem

theorem mem_pCoreOf_of_commutator_mem_centralizer {W Y R : Subgroup G}
    (hRY : R ≤ normalizer (Y : Set G)) (hR2 : IsPGroup 2 R)
    (hYRW : Y ⊔ R ≤ normalizer (W : Set G))
    (hYO : ∀ z ∈ Y, (∀ y ∈ Y, ⁅z, y⁆ ∈ centralizer (W : Set G)) → z ∈ pCoreOf 2 Y)
    {s : G} (hs : s ∈ Y ⊔ R) (hsc : ∀ y ∈ Y, ⁅s, y⁆ ∈ centralizer (W : Set G)) :
    s ∈ pCoreOf 2 (Y ⊔ R) := by
  classical
  have hYRY : Y ⊔ R ≤ normalizer (Y : Set G) := sup_le le_normalizer hRY
  let Cs : Subgroup G :=
    { carrier := {s | s ∈ Y ⊔ R ∧ ∀ y ∈ Y, ⁅s, y⁆ ∈ centralizer (W : Set G)}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun y hy => by
        have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem (conj_mem_centralizer_of_normalizer (hYRW ha.1) (hb.2 y hy)) (ha.2 y hy)⟩
      one_mem' := ⟨one_mem _, fun y _ => by
        rw [commutatorElement_def, one_mul, inv_one, mul_one, mul_inv_cancel]
        exact one_mem _⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun y hy => by
        have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact conj_mem_centralizer_of_normalizer (hYRW (inv_mem ha.1)) (inv_mem (ha.2 y hy))⟩ }
  have hCsN : Y ⊔ R ≤ normalizer (Cs : Set G) := by
    intro g hg
    have hfwd : ∀ g ∈ Y ⊔ R, ∀ c ∈ Cs, g * c * g⁻¹ ∈ Cs := by
      intro g hg c hc
      refine ⟨mul_mem (mul_mem hg hc.1) (inv_mem hg), fun y hy => ?_⟩
      have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ Y :=
        (mem_normalizer_iff.mp (hYRY (inv_mem hg)) y).mp hy
      have e : ⁅g * c * g⁻¹, y⁆ = g * ⁅c, g⁻¹ * y * g⁻¹⁻¹⁆ * g⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact conj_mem_centralizer_of_normalizer (hYRW hg) (hc.2 _ hy')
    refine mem_normalizer_of_conj_mem (hfwd g hg) fun c hc => ?_
    have := hfwd g⁻¹ (inv_mem hg) c hc
    rwa [inv_inv] at this
  have hYCs : ∀ y ∈ Y, y ∈ Cs → y ∈ pCoreOf 2 Y := fun y hy hyC => hYO y hy hyC.2
  have hCs2 : IsPGroup 2 Cs := by
    rintro ⟨c, hcC⟩
    obtain ⟨hcYR, hcc⟩ : c ∈ Y ⊔ R ∧ ∀ y ∈ Y, ⁅c, y⁆ ∈ centralizer (W : Set G) := hcC
    have hc' : c ∈ ((Y ⊔ R : Subgroup G) : Set G) := hcYR
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Y R hRY] at hc'
    obtain ⟨y₀, hy₀, r, hr, rfl⟩ := hc'
    obtain ⟨a, ha⟩ := hR2 ⟨r, hr⟩
    have hr1 : r ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have hpow : ∀ n : ℕ, ∃ y' ∈ Y, (y₀ * r) ^ n = y' * r ^ n := by
      intro n
      induction n with
      | zero => exact ⟨1, one_mem _, by rw [pow_zero, pow_zero, mul_one]⟩
      | succ n ih =>
        obtain ⟨y', hy', he⟩ := ih
        have hrn : r ^ n * y₀ * (r ^ n)⁻¹ ∈ Y :=
          (mem_normalizer_iff.mp (hRY (pow_mem hr n)) y₀).mp hy₀
        refine ⟨y' * (r ^ n * y₀ * (r ^ n)⁻¹), mul_mem hy' hrn, ?_⟩
        rw [pow_succ, he, pow_succ]
        group
    obtain ⟨y', hy', he⟩ := hpow (2 ^ a)
    rw [hr1, mul_one] at he
    have hy'C : y' ∈ Cs := he ▸ Cs.pow_mem ⟨hcYR, hcc⟩ _
    obtain ⟨b, hb⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) ⟨y', hYCs y' hy' hy'C⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : y' ^ 2 ^ b = 1 := by
      have := congrArg Subtype.val hb
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    change (y₀ * r) ^ 2 ^ (a + b) = 1
    rw [pow_add, pow_mul, he, hb']
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (fun c (hc : c ∈ Cs) =>
      (hc : c ∈ Y ⊔ R ∧ ∀ y ∈ Y, ⁅c, y⁆ ∈ centralizer (W : Set G)).1) hCsN hCs2 ⟨hs, hsc⟩

theorem simple_source_setup {T L M : Subgroup G} (h : QTNQ T L M)
    {R : Subgroup G} (hR : (R : Set G) = nqOriginalCentralizer T L)
    {H : Subgroup G} (hH : quasithinIsMaxTwoLocal H) (hKTH : nqOriginalK T L ⊔ T ≤ H)
    {Y : Subgroup G} (hYH : Y ≤ H) (hYn : (Y.subgroupOf H).Normal)
    (hKY : ⁅nqOriginalK T L, Y⁆ ≤ pCoreOf 2 Y) :
    IsElementaryAbelian 2 (nqSourceModule Y R) ∧ nqSourceModule Y R ≤ R ∧ IsPGroup 2 R ∧
      R ≤ H ∧ H ≤ normalizer (Y : Set G) ∧
      nqOriginalK T L ≤ normalizer (nqSourceModule Y R : Set G) ∧
      Y ⊔ R ≤ normalizer (nqSourceModule Y R : Set G) ∧
      pCoreOf 2 Y ≤ centralizer (nqSourceModule Y R : Set G) ∧
      pCoreOf 2 (nqOriginalK T L) ≤ centralizer (nqSourceModule Y R : Set G) ∧
      ⁅nqOriginalK T L, R⁆ ≤ centralizer (nqSourceModule Y R : Set G) ∧
      pCoreOf 2 (Y ⊔ R) ≤ centralizer (nqSourceModule Y R : Set G) ∧
      pCoreOf 2 (Y ⊔ R) ≤ R ∧ ¬ 2 ∣ R.relIndex (Y ⊔ R) := by
  classical
  set K := nqOriginalK T L with hKdef
  set W := nqSourceModule Y R with hWdef
  obtain ⟨hTK, -, hRchar, htrans⟩ :=
    normal_original_K_overgroup_factors_have_core_containment_and_commutator_transport h hR
  obtain ⟨hOYH, hOHR, htr⟩ := htrans H Y hKTH hYH hYn
  obtain ⟨-, hYK, -, -, -, hSyl⟩ := htr hKY
  obtain ⟨-, hRKT, -⟩ := original_radical_supplements_share_simple_residual_and_internal_module h hR
  have hTH : T ≤ H := le_sup_right.trans hKTH
  have hKH : K ≤ H := le_sup_left.trans hKTH
  have hRT : R ≤ T := fun r hr => by
    rw [← SetLike.mem_coe, hR] at hr
    exact hr.1
  have hRH : R ≤ H := hRT.trans hTH
  have hSH : Y ⊔ R ≤ H := sup_le hYH hRH
  have hHY : H ≤ normalizer (Y : Set G) := (normal_subgroupOf_iff_le_normalizer hYH).mp hYn
  have hRY : R ≤ normalizer (Y : Set G) := hRH.trans hHY
  have hKY' : K ≤ normalizer (Y : Set G) := hKH.trans hHY
  have hKR : K ≤ normalizer (R : Set G) := by
    rw [hRKT]
    exact le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hSyl' : QuasithinUnique.IsSylowTwoOf R (Y ⊔ R) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mp hSyl
  have hT' : QuasithinUnique.IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, h.sylow.1, ?_⟩
    change ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact h.sylow.2
  have hHc : QuasithinUnique.CharTwo H :=
    QuasithinUnique.charTwo_of_isTwoLocal_of_isSylowTwoOf_le h.qtke.2.1 hT' hH.1 hTH
  have hOHS : pCoreOf 2 H ≤ pCoreOf 2 (Y ⊔ R) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hOHR.trans le_sup_right)
      (hSH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  have hchar : QuasithinUnique.CharTwo (Y ⊔ R) := fun x hx =>
    hOHS (hHc ⟨hSH hx.1, centralizer_le hOHS hx.2⟩)
  have hWZ := nqSourceModule_le_omegaOneCenterOf_pCoreOf hSyl' hchar
  have hOR : pCoreOf 2 (Y ⊔ R) ≤ R := QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSyl'
  have hOW : pCoreOf 2 (Y ⊔ R) ≤ centralizer (W : Set G) := fun o ho =>
    mem_centralizer_iff.mpr fun w hw => (mem_omegaOneCenterOf_iff.mp (hWZ hw)).2.1 o ho
  have hKTQ : K ⊔ T ≤ normalizer (pCoreOf 2 K : Set G) :=
    sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
      (hTK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
  have hQKR : pCoreOf 2 K ≤ R := by
    rw [hRKT]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left) hKTQ
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hQKO : pCoreOf 2 K ≤ pCoreOf 2 (Y ⊔ R) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQKR.trans le_sup_right)
      (sup_le (hYK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
        (hRT.trans (le_sup_right.trans hKTQ)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hKRQ : ⁅K, R⁆ ≤ pCoreOf 2 K := by
    rw [Subgroup.commutator_le]
    intro k hk t ht
    have h1 := ((hRchar t).mp ht).2 k⁻¹ (K.inv_mem hk)
    have e : ⁅k, t⁆ = k * (t * k⁻¹ * t⁻¹ * k⁻¹⁻¹) * k⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk) _).mp h1
  exact ⟨isElementaryAbelian_of_le_omegaOneCenterOf hWZ,
    hWZ.trans (((omegaOneCenterOf_le 2 _).trans inf_le_left).trans hOR), hSyl'.2.1, hRH, hHY,
    fun k hk => mem_normalizer_nqSourceModule (hKY' hk) (hKR hk), le_normalizer_nqSourceModule Y R,
    (hOYH.trans hOHS).trans hOW, hQKO.trans hOW, (hKRQ.trans hQKO).trans hOW, hOW, hOR,
    hSyl'.2.2⟩

theorem codim_le_of_mem_higherElemThompsonFamily {R W : Subgroup G} [IsElementaryAbelian 2 W]
    (hWR : W ≤ R) (hRW : R ≤ normalizer (W : Set G)) {j : ℕ} {A : Subgroup ↥R}
    (hA : A ∈ CFSG.higherElemThompsonFamily R j)
    (hA'W : A.map R.subtype ≤ normalizer (W : Set G)) :
    2 ^ (finrank (ZMod 2) (Additive ↥W) -
        finrank (ZMod 2) (CFSG.LocalAnalysis.CommutingFactor.fixedSub (conjImage W hA'W))) ≤
      2 ^ j * Nat.card (conjImage W hA'W) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A' := A.map R.subtype with hA'def
  have hA'R : A' ≤ R := Subgroup.map_subtype_le A
  have : Finite (Additive ↥W) := inferInstanceAs (Finite ↥W)
  set W' : Subgroup ↥R := W.subgroupOf R with hW'def
  have : W'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWR).mpr hRW
  have : IsElementaryAbelian 2 ↥W' := CFSG.IsElementaryAbelian.subgroupOf hWR
  obtain ⟨d, e, hd, he, hde, -, -⟩ :=
    Quasithin.SteinbergBK.near_maximal_elementary_whole_module_rank_inequality W' hA
  have hcW' : centralizer (W' : Set ↥R) = (centralizer (W : Set G)).subgroupOf R := by
    ext r
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h w hw
      exact congrArg Subtype.val (h ⟨w, hWR hw⟩ (Subgroup.mem_subgroupOf.mpr hw))
    · intro h w hw
      exact Subtype.ext (h w (Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hw)))
  have hcA : centralizer (A : Set ↥R) = (centralizer (A' : Set G)).subgroupOf R := by
    ext r
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · rintro h _ ⟨a, ha, rfl⟩
      exact congrArg Subtype.val (h a ha)
    · intro h a ha
      exact Subtype.ext (h a ⟨a, ha, rfl⟩)
  have hAA' : A'.subgroupOf R = A := by
    ext a
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨b, hb, hba⟩
      rwa [show a = b from Subtype.ext hba.symm]
    · intro ha
      exact ⟨a, ha, rfl⟩
  have hcardA : Nat.card ↥(conjImage W hA'W) = 2 ^ e := by
    rw [card_conjImage, ← he, Subgroup.inf_relIndex_left, hcW', ← hAA',
      Subgroup.relIndex_subgroupOf hA'R]
  have hrelW : (centralizer (A' : Set G)).relIndex W = 2 ^ d := by
    rw [← hd, Subgroup.inf_relIndex_left, hcA, hW'def, Subgroup.relIndex_subgroupOf hWR]
  have hcD : Nat.card ↥W = 2 ^ finrank (ZMod 2) (Additive ↥W) :=
    (FiniteField.pow_finrank_eq_natCard 2 (Additive ↥W)).symm
  have hcF : Nat.card ↥(CFSG.LocalAnalysis.CommutingFactor.fixedSub (conjImage W hA'W)) =
      2 ^ finrank (ZMod 2) ↥(CFSG.LocalAnalysis.CommutingFactor.fixedSub (conjImage W hA'W)) :=
    (FiniteField.pow_finrank_eq_natCard 2 _).symm
  have h1 := Subgroup.relIndex_mul_card (H := centralizer (A' : Set G)) (K := W)
  rw [hrelW, inf_comm, ← card_fixedSub_conjImage W hA'W, hcF, hcD, ← pow_add] at h1
  have h2 := Nat.pow_right_injective le_rfl h1
  have hFD := Submodule.finrank_le (CFSG.LocalAnalysis.CommutingFactor.fixedSub (conjImage W hA'W))
  rw [hcardA, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem simpleSourceTensorAction_of (hA5 : MixedA5RankBudget) :
    SimpleSourceTensorAction := by
  intro G _ _ T L M h R hR H hH hKTH hHM Y hYH hYn hYM hKY hsimp j hj hm hJM A hA hne
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := nqOriginalK T L with hKdef
  set W := nqSourceModule Y R with hWdef
  set A' := A.map R.subtype with hA'def
  obtain ⟨hWel, hWR, hR2, hRH, hHY, hKW, hSW, hOYW, hOKW, hKRW, hOSW, hOSR, hRodd⟩ :=
    simple_source_setup h hR hH hKTH hYH hYn hKY
  have : IsElementaryAbelian 2 ↥W := hWel
  have hYW : Y ≤ normalizer (W : Set G) := le_sup_left.trans hSW
  have hRW : R ≤ normalizer (W : Set G) := le_sup_right.trans hSW
  have hA'R : A' ≤ R := Subgroup.map_subtype_le A
  have hA'W : A' ≤ normalizer (W : Set G) := hA'R.trans hRW
  have hRY : R ≤ normalizer (Y : Set G) := hRH.trans hHY
  obtain ⟨hAel, -⟩ := (CFSG.mem_higherElemThompsonFamily_iff j A).mp hA
  have hA'el : IsElementaryAbelian 2 ↥A' := CFSG.IsElementaryAbelian.map R.subtype
  have : Finite (Additive ↥W) := inferInstanceAs (Finite ↥W)
  have hKWsub : ⁅W, K⁆ ≤ W := fun v hv => (commutator_mem_commSpace W hKW hv).1
  have hKnt : ¬ K ≤ centralizer (W : Set G) := by
    intro hK
    apply hne
    have h1 : ⁅W, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact ((Subgroup.mem_centralizer_iff.mp (hK hk)) w hw).symm
    rw [h1, Subgroup.commutator_bot_left]
  have hYnt : ¬ Y ≤ centralizer (W : Set G) := by
    intro hY
    apply hne
    have h1 : ⁅Y, A'⁆ ≤ centralizer (W : Set G) := by
      rw [Subgroup.commutator_le]
      intro y hy a ha
      have e : ⁅y, a⁆ = y * (a * y⁻¹ * a⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact mul_mem (hY hy) (conj_mem_centralizer_of_normalizer (hA'W ha) (inv_mem (hY hy)))
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((Subgroup.mem_centralizer_iff.mp (h1 hz)) v (hKWsub hv)).symm
  obtain ⟨-, -, hKp, hKs, -, -⟩ := original_K_quotient_facts h
  obtain ⟨-, -, -, -, ⟨e, -⟩, ⟨s, hsf, hs5, ⟨e'⟩⟩, -⟩ :=
    original_radical_supplements_share_simple_residual_and_internal_module h hR
  obtain ⟨-, ⟨eK⟩⟩ := conjImage_equiv_of_simple W hKW hKs hOKW hKnt
  obtain ⟨hYs, hYnc⟩ : IsSimpleGroup (↥Y ⧸ CFSG.pCore 2 ↥Y) ∧
      ∃ a b : ↥Y ⧸ CFSG.pCore 2 ↥Y, a * b ≠ b * a := by
    rcases hsimp with hY5 | hY3
    · obtain ⟨e5⟩ := hY5
      obtain ⟨a, b, hab⟩ := alternatingGroup_five_noncomm
      refine ⟨e5.isSimpleGroup, e5.symm a, e5.symm b, fun hc => hab ?_⟩
      have h1 := congrArg e5 hc
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
    · obtain ⟨e3⟩ := hY3
      have := CFSG.Quasithin.H13.L619.isSimpleGroup_GL32
      obtain ⟨a, b, hab⟩ := GL32_noncomm
      refine ⟨e3.isSimpleGroup, e3.symm a, e3.symm b, fun hc => hab ?_⟩
      have h1 := congrArg e3 hc
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
  obtain ⟨hYCW, ⟨eY⟩⟩ := conjImage_equiv_of_simple W hYW hYs hOYW hYnt
  have hYcases : Nonempty (↥(conjImage W hYW) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (↥(conjImage W hYW) ≃* GL (Fin 3) (ZMod 2)) :=
    hsimp.imp (fun ⟨e5⟩ => ⟨eY.trans e5⟩) (fun ⟨e3⟩ => ⟨eY.trans e3⟩)
  have hYO : ∀ z ∈ Y, (∀ y ∈ Y, ⁅z, y⁆ ∈ centralizer (W : Set G)) → z ∈ pCoreOf 2 Y := by
    intro z hz hc
    refine mem_pCoreOf_of_commutator_mem hYs hYnc hz fun y hy => hYCW ⟨?_, hc y hy⟩
    rw [commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem hz hy) (Y.inv_mem hz)) (Y.inv_mem hy)
  have hCset : ∀ s ∈ Y ⊔ R, (∀ y ∈ Y, ⁅s, y⁆ ∈ centralizer (W : Set G)) →
      s ∈ centralizer (W : Set G) := fun s hs hc =>
    hOSW (mem_pCoreOf_of_commutator_mem_centralizer hRY hR2 hSW hYO hs hc)
  have hX : ⁅conjImage W hKW, conjImage W hKW⁆ = conjImage W hKW := by
    have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKp
    exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.range ((conjGL W).comp
      (Subgroup.inclusion hKW)))
  have hXY := conjImage_comm W hKW hYW fun k hk y hy =>
    hOYW (hKY (Subgroup.commutator_mem_commutator hk hy))
  have hXR := conjImage_comm W hKW hRW fun k hk r hr =>
    hKRW (Subgroup.commutator_mem_commutator hk hr)
  have hRYl : conjImage W hRW ≤
      normalizer (conjImage W hYW : Set (Module.End (ZMod 2) (Additive ↥W))ˣ) := by
    rintro _ ⟨⟨r, hr⟩, rfl⟩
    exact conjGL_mem_normalizer W hYW (a := ⟨r, hRW hr⟩)
      (fun y hy => (mem_normalizer_iff.mp (hRY hr) y).mp hy)
      (fun y hy => by simpa using (mem_normalizer_iff.mp (hRY (R.inv_mem hr)) y).mp hy)
  have hΓ : conjImage W hYW ⊔ conjImage W hRW = conjImage W hSW := by
    refine le_antisymm (sup_le (conjImage_mono W le_sup_left hSW)
      (conjImage_mono W le_sup_right hSW)) ?_
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    have hg' : g ∈ ((Y ⊔ R : Subgroup G) : Set G) := hg
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Y R hRY] at hg'
    obtain ⟨y, hy, r, hr, rfl⟩ := hg'
    have e : (conjGL W).comp (Subgroup.inclusion hSW) ⟨y * r, hg⟩ =
        conjGL W ⟨y, hYW hy⟩ * conjGL W ⟨r, hRW hr⟩ := by
      rw [← map_mul]
      rfl
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (conjGL_mem_conjImage W hYW hy))
      (Subgroup.mem_sup_right (conjGL_mem_conjImage W hRW hr))
  have hCYl : ∀ g ∈ conjImage W hYW ⊔ conjImage W hRW,
      (∀ y ∈ conjImage W hYW, g * y = y * g) → g = 1 := by
    intro g hg hc
    rw [hΓ] at hg
    obtain ⟨⟨s, hs⟩, rfl⟩ := hg
    apply (conjGL_eq_one_iff W _).mpr
    refine hCset s hs fun y hy => ?_
    exact (conjGL_mul_comm_iff W ⟨s, hSW hs⟩ ⟨y, hYW hy⟩).mp
      (hc _ (conjGL_mem_conjImage W hYW hy))
  have hAl : conjImage W hA'W ≤ conjImage W hRW := conjImage_mono W hA'R hRW
  have hA2 : ∀ g ∈ conjImage W hA'W, g ^ 2 = 1 := by
    rintro _ ⟨⟨a, ha⟩, rfl⟩
    rw [← map_pow, MonoidHom.comp_apply]
    apply (conjGL_eq_one_iff W _).mpr
    change a ^ 2 ∈ centralizer (W : Set G)
    rw [CFSG.elemPow_eq_one_of_isElementaryAbelian (A := A') a ha]
    exact Subgroup.one_mem _
  have hAc := conjImage_comm W hA'W hA'W fun a ha b hb => by
    have hab : a * b = b * a := congrArg Subtype.val (hA'el.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hab]
    exact Subgroup.one_mem _
  have hRl2 : IsPGroup 2 ↥(conjImage W hRW) :=
    hR2.of_surjective _ ((conjGL W).comp (Subgroup.inclusion hRW)).rangeRestrict_surjective
  have hRlodd : ¬ 2 ∣ (conjImage W hRW).relIndex (conjImage W hYW ⊔ conjImage W hRW) := by
    rw [hΓ]
    intro h2
    exact hRodd (dvd_trans h2 (relIndex_conjImage_dvd W le_sup_right hSW))
  have hcodim := codim_le_of_mem_higherElemThompsonFamily hWR hRW hA hA'W
  have hV : ∃ g ∈ ⁅conjImage W hYW, conjImage W hA'W⁆,
      ∃ v ∈ CFSG.LocalAnalysis.commSpace ⊤ (conjImage W hKW),
        ((g : (Module.End (ZMod 2) (Additive ↥W))ˣ) : Module.End (ZMod 2) (Additive ↥W)) v ≠
          v := by
    by_contra hV
    apply hne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    by_contra hzv
    obtain ⟨hvW, hvX⟩ := commutator_mem_commSpace W hKW hv
    obtain ⟨hzN, hzPA⟩ := conjGL_mem_commutator W hYW hA'W hz
    exact hV ⟨conjGL W ⟨z, hzN⟩, hzPA, Additive.ofMul ⟨v, hvW⟩, hvX,
      conjGL_apply_ne W hvW hzv⟩
  have : Fact s.Prime := hsf
  obtain ⟨hj1, hRYle, ψ, θ, hψb, hθ, hψR, hψA⟩ :=
    simple_source_linear_core hA5 hs5 (eK.trans (e.trans e')) hX hYcases hXY hXR hRYl hCYl hAl
      hA2 hAc hRl2 hRlodd hj hcodim hV
  have hsY : ∀ (s : G) (hs : s ∈ Y ⊔ R), conjGL W ⟨s, hSW hs⟩ ∈ conjImage W hYW := by
    intro s hs
    have h1 := conjGL_mem_conjImage W hSW hs
    rwa [← hΓ, sup_eq_left.mpr hRYle] at h1
  set f' : ↥(Y ⊔ R) →* ↥(conjImage W hYW) :=
    ((conjGL W).comp (Subgroup.inclusion hSW)).codRestrict (conjImage W hYW)
      (fun s => hsY s s.2) with hf'def
  have hf' : ∀ s : ↥(Y ⊔ R), ((f' s : ↥(conjImage W hYW)) :
      (Module.End (ZMod 2) (Additive ↥W))ˣ) = conjGL W ⟨s, hSW s.2⟩ := fun _ => rfl
  refine ⟨hj1, fun s hs => hOSR (mem_pCoreOf_of_commutator_mem_centralizer hRY hR2 hSW hYO hs.1
    fun y hy => ?_), ψ.comp f', fun s => ?_, ?_, ?_, ?_, ?_⟩
  ·
    have e : ⁅s, y⁆ = s * (y * s⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hs.2 (conj_mem_centralizer_of_normalizer (hYW hy) (inv_mem hs.2))
  ·
    rw [MonoidHom.comp_apply, map_eq_one_iff ψ hψb.1, ← conjGL_eq_one_iff W ⟨s, hSW s.2⟩,
      ← hf']
    exact ⟨fun h1 => by rw [h1]; rfl, fun h1 => Subtype.ext h1⟩
  ·
    rw [eq_top_iff]
    intro M _
    obtain ⟨y', rfl⟩ := hψb.2 M
    obtain ⟨⟨y, hy⟩, hyy'⟩ := y'.2
    refine ⟨⟨y, le_sup_left (b := R) hy⟩, Subgroup.mem_subgroupOf.mpr hy, ?_⟩
    rw [MonoidHom.comp_apply]
    congr 1
    exact Subtype.ext hyy'
  ·
    rw [← hψR]
    ext M
    constructor
    · rintro ⟨⟨r, hr⟩, hrR, rfl⟩
      exact ⟨f' ⟨r, hr⟩, Subgroup.mem_subgroupOf.mpr ⟨⟨r, Subgroup.mem_subgroupOf.mp hrR⟩, rfl⟩,
        rfl⟩
    · rintro ⟨y', hy', rfl⟩
      obtain ⟨⟨r, hr⟩, hry⟩ := Subgroup.mem_subgroupOf.mp hy'
      exact ⟨⟨r, le_sup_right (a := Y) hr⟩, Subgroup.mem_subgroupOf.mpr hr,
        congrArg ψ (Subtype.ext hry)⟩
  ·
    rw [← hψA]
    ext M
    constructor
    · rintro ⟨⟨a, ha⟩, haA, rfl⟩
      exact ⟨f' ⟨a, ha⟩, Subgroup.mem_subgroupOf.mpr ⟨⟨a, Subgroup.mem_subgroupOf.mp haA⟩, rfl⟩,
        rfl⟩
    · rintro ⟨y', hy', rfl⟩
      obtain ⟨⟨a, ha⟩, hay⟩ := Subgroup.mem_subgroupOf.mp hy'
      exact ⟨⟨a, le_sup_right (a := Y) (hA'R ha)⟩, Subgroup.mem_subgroupOf.mpr ha,
        congrArg ψ (Subtype.ext hay)⟩
  ·
    refine ⟨(commEquiv W hYW).trans θ.toAddEquiv.toMultiplicative, fun s u hsu => ?_⟩
    change θ (Multiplicative.toAdd (commEquiv W hYW ⟨_, hsu⟩)) =
      ((ψ (f' s) : GL32) : Mat3) * θ (Multiplicative.toAdd (commEquiv W hYW u))
    have hmem := CFSG.LocalAnalysis.isInvariantBy_commSpace (H := conjImage W hYW)
      (W := ⊤) _ (f' s).2 _ (Multiplicative.toAdd (commEquiv W hYW u)).2
    rw [← hθ (f' s) _ hmem]
    congr 1

theorem simpleSourceTensorEquality_of_mixedA5
    (hA5 : MixedA5RankBudget) : SimpleSourceTensorEquality :=
  simpleSourceTensorEquality_of (simpleSourceTensorAction_of hA5)

end CFSG.Quasithin.H13.NQBlock
