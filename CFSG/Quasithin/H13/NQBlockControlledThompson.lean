module

public import CFSG.Quasithin.SteinbergBKHigherElementaryThompson
public import CFSG.Quasithin.H13.NQBlockOriginalOvergroup
public import CFSG.Quasithin.H13.NQBlockSourceModule

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open scoped commutatorElement

section Frattini

variable {G : Type*} [Group G] [Finite G]

theorem exists_map_conj_eq_of_isSylowOf' {p : ℕ} [Fact p.Prime] {B B' N : Subgroup G}
    (hB : CFSG.ABGLocalTools.IsSylowOf p B N) (hB' : CFSG.ABGLocalTools.IsSylowOf p B' N) :
    ∃ n ∈ N, B' = B.map (MulAut.conj n).toMonoidHom := by
  obtain ⟨Q, rfl⟩ := hB
  obtain ⟨Q', rfl⟩ := hB'
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N Q Q'
  refine ⟨n, n.2, ?_⟩
  rw [← hn]
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    rw [Sylow.coe_subgroup_smul] at hy
    obtain ⟨z, hz, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hy
    refine ⟨(z : G), ⟨_, hz, rfl⟩, ?_⟩
    change (n : G) * (z : G) * (n : G)⁻¹ = ((MulAut.conj n • z : N) : G)
    rw [MulAut.smul_def, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨MulAut.conj n • y, ?_, ?_⟩
    · rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hy
    · change ((MulAut.conj n • y : N) : G) = (n : G) * (y : G) * (n : G)⁻¹
      rw [MulAut.smul_def, MulAut.conj_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem le_sup_normalizer_of_isSylowOf' {p : ℕ} [Fact p.Prime] {B N K : Subgroup G}
    (hB : CFSG.ABGLocalTools.IsSylowOf p B N) (hK : K ≤ normalizer (N : Set G)) :
    K ≤ N ⊔ normalizer (B : Set G) := by
  intro k hk
  have hkN : k ∈ normalizer (N : Set G) := hK hk
  have hle : B.map (MulAut.conj k).toMonoidHom ≤ N := by
    rintro _ ⟨b, hb, rfl⟩
    exact (mem_normalizer_iff.mp hkN b).mp (hB.le hb)
  have hB' : CFSG.ABGLocalTools.IsSylowOf p (B.map (MulAut.conj k).toMonoidHom) N := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective]
    exact hB.card_eq
  obtain ⟨n, hn, hnk⟩ := exists_map_conj_eq_of_isSylowOf' hB hB'
  have hm : n⁻¹ * k ∈ normalizer (B : Set G) := by
    rw [mem_normalizer_iff]
    have key : ∀ b, b ∈ B ↔ k * b * k⁻¹ ∈ B.map (MulAut.conj n).toMonoidHom := by
      intro b
      rw [← hnk]
      constructor
      · intro hb
        exact ⟨b, hb, rfl⟩
      · rintro ⟨b', hb', hbb'⟩
        have h2 : k * b' * k⁻¹ = k * b * k⁻¹ := hbb'
        rwa [mul_left_cancel (mul_right_cancel h2)] at hb'
    intro b
    rw [key b]
    constructor
    · rintro ⟨b', hb', hbb'⟩
      have h1 : n * b' * n⁻¹ = k * b * k⁻¹ := hbb'
      have : n⁻¹ * k * b * (n⁻¹ * k)⁻¹ = b' := by
        calc n⁻¹ * k * b * (n⁻¹ * k)⁻¹ = n⁻¹ * (k * b * k⁻¹) * n := by group
          _ = n⁻¹ * (n * b' * n⁻¹) * n := by rw [h1]
          _ = b' := by group
      rw [this]
      exact hb'
    · intro hb
      refine ⟨_, hb, ?_⟩
      change n * (n⁻¹ * k * b * (n⁻¹ * k)⁻¹) * n⁻¹ = k * b * k⁻¹
      group
  have e : k = n * (n⁻¹ * k) := by group
  rw [e]
  exact Subgroup.mul_mem _ (mem_sup_left hn) (mem_sup_right hm)

end Frattini

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_commutator_of_normalizer {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) {x : G}
    (hx : x ∈ ⁅A, B⁆) : g * x * g⁻¹ ∈ ⁅A, B⁆ := by
  have hle : ⁅A, B⁆ ≤ ⁅A, B⁆.comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    change g * ⁅a, b⁆ * g⁻¹ ∈ ⁅A, B⁆
    have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator ((mem_normalizer_iff.mp hA a).mp ha)
      ((mem_normalizer_iff.mp hB b).mp hb)
  exact hle hx

omit [Finite G] in
theorem mem_normalizer_commutator {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) :=
  mem_normalizer_of_conj_mem (fun _ hx => conj_mem_commutator_of_normalizer hA hB hx)
    fun x hx => by
      have := conj_mem_commutator_of_normalizer (inv_mem hA) (inv_mem hB) hx
      rwa [inv_inv] at this

theorem le_normalizer_nqHigherThompson (R : Subgroup G) (j : ℕ) :
    R ≤ normalizer (nqHigherThompson R j : Set G) := by
  have hc : (CFSG.higherElemThompson ↥R j).Characteristic :=
    CFSG.Quasithin.SteinbergBK.higherElemThompson_characteristic j
  exact Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)

omit [Finite G] in
theorem map_le_nqHigherThompson {R : Subgroup G} {j : ℕ} {A : Subgroup ↥R}
    (hA : A ∈ CFSG.higherElemThompsonFamily ↥R j) : A.map R.subtype ≤ nqHigherThompson R j :=
  Subgroup.map_mono (le_sSup hA)

theorem normalizer_le_normalizer_nqHigherThompson {R P : Subgroup G} {j : ℕ}
    (hJP : nqHigherThompson R j ≤ P) (hPR : P ≤ R) :
    normalizer (P : Set G) ≤ normalizer (nqHigherThompson R j : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfwd : ∀ g ∈ normalizer (P : Set G), ∀ x ∈ nqHigherThompson R j,
      g * x * g⁻¹ ∈ nqHigherThompson R j := by
    intro g hg x hx
    have hle : nqHigherThompson R j ≤
        (nqHigherThompson R j).comap (MulAut.conj g).toMonoidHom := by
      rw [nqHigherThompson, Subgroup.map_le_iff_le_comap]
      apply sSup_le
      intro A hA
      rw [← Subgroup.map_le_iff_le_comap, ← Subgroup.map_le_iff_le_comap]
      set A' := A.map R.subtype with hA'def
      have hA'P : A' ≤ P := (map_le_nqHigherThompson hA).trans hJP
      set B' := A'.map (MulAut.conj g).toMonoidHom with hB'def
      have hB'P : B' ≤ P := by
        rintro _ ⟨a, ha, rfl⟩
        exact (mem_normalizer_iff.mp hg a).mp (hA'P ha)
      have hB'R : B' ≤ R := hB'P.trans hPR
      obtain ⟨hAel, hAcard⟩ := (CFSG.mem_higherElemThompsonFamily_iff j A).mp hA
      have hBmem : B'.subgroupOf R ∈ CFSG.higherElemThompsonFamily ↥R j := by
        rw [CFSG.mem_higherElemThompsonFamily_iff]
        refine ⟨?_, ?_⟩
        · have : CFSG.IsElementaryAbelian 2 ↥A' := CFSG.IsElementaryAbelian.map R.subtype
          have : CFSG.IsElementaryAbelian 2 ↥B' :=
            CFSG.IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
          exact CFSG.IsElementaryAbelian.subgroupOf hB'R
        · rw [← hAcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB'R).toEquiv,
            hB'def, Subgroup.card_map_of_injective (MulAut.conj g).injective, hA'def,
            Subgroup.card_map_of_injective R.subtype_injective]
      have hB'eq : (B'.subgroupOf R).map R.subtype = B' := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hB'R]
      rw [← hB'eq]
      exact map_le_nqHigherThompson hBmem
    exact hle hx
  intro g hg
  exact mem_normalizer_of_conj_mem (hfwd g hg) fun x hx => by
    have := hfwd g⁻¹ (inv_mem hg) x hx
    rwa [inv_inv] at this

theorem controlledThompsonSourceCommutator_holds :
    ControlledThompsonSourceCommutator := by
  intro G _ _ T L M h R hR H hH hKTH hHM Y hYH hYn hYM hKY _ j hj hm hJM
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := nqOriginalK T L with hKdef
  set W := nqSourceModule Y R with hWdef
  obtain ⟨hTK, -, -, htrans⟩ :=
    normal_original_K_overgroup_factors_have_core_containment_and_commutator_transport h hR
  obtain ⟨-, hOHR, htr⟩ := htrans H Y hKTH hYH hYn
  obtain ⟨-, hYK, -, -, -, hSyl⟩ := htr hKY
  obtain ⟨-, hRKT, -⟩ := original_radical_supplements_share_simple_residual_and_internal_module h hR
  obtain ⟨-, -, -, -, hVK, -⟩ :=
    original_common_residual_is_faithful_and_has_exact_reduced_action_kernel h hR
  have hTH : T ≤ H := le_sup_right.trans hKTH
  have hKH : K ≤ H := le_sup_left.trans hKTH
  have hRT : R ≤ T := fun r hr => by
    rw [← SetLike.mem_coe, hR] at hr
    exact hr.1
  have hRH : R ≤ H := hRT.trans hTH
  have hSH : Y ⊔ R ≤ H := sup_le hYH hRH
  have hHY : H ≤ normalizer (Y : Set G) := (normal_subgroupOf_iff_le_normalizer hYH).mp hYn
  have hKTR : K ⊔ T ≤ normalizer (R : Set G) := by
    rw [hRKT]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
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
  have hOR : pCoreOf 2 (Y ⊔ R) ≤ R :=
    QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSyl'
  have hWR : W ≤ R := hWZ.trans (((omegaOneCenterOf_le 2 _).trans inf_le_left).trans hOR)
  have hW2 : ∀ w ∈ W, w ^ 2 = 1 := fun w hw =>
    pow_eq_one_of_mem_omegaOneCenterOf (hWZ hw)
  have hNW : ∀ g, g ∈ normalizer (Y : Set G) → g ∈ normalizer (R : Set G) →
      g ∈ normalizer (W : Set G) := fun g hgY hgR => mem_normalizer_nqSourceModule hgY hgR
  have hKW : K ≤ normalizer (W : Set G) := fun k hk =>
    hNW k (hHY (hKH hk)) (hKTR (le_sup_left (a := K) hk))
  have hTW : T ≤ normalizer (W : Set G) := fun t ht =>
    hNW t (hHY (hTH ht)) (hKTR (le_sup_right (a := K) ht))
  have hSW : Y ⊔ R ≤ normalizer (W : Set G) := le_normalizer_nqSourceModule Y R
  have hRK : R ≤ normalizer (K : Set G) := hRT.trans hTK
  set V := ⁅W, K⁆ with hVdef
  have hVW : V ≤ W := by
    rw [hVdef, Subgroup.commutator_le]
    intro w hw k hk
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine W.mul_mem hw ?_
    rw [← mul_assoc]
    exact (mem_normalizer_iff.mp (hKW hk) _).mp (W.inv_mem hw)
  have hVT : V ≤ T := (hVW.trans hWR).trans hRT
  have hNV : ∀ g, g ∈ normalizer (W : Set G) → g ∈ normalizer (K : Set G) →
      g ∈ normalizer (V : Set G) := fun g hgW hgK => mem_normalizer_commutator hgW hgK
  have hYV : Y ≤ normalizer (V : Set G) := fun y hy => hNV y (hSW (le_sup_left (a := Y) hy))
    (hYK hy)
  have hRV : R ≤ normalizer (V : Set G) := fun r hr => hNV r (hSW (le_sup_right (a := Y) hr))
    (hRK hr)
  have hTV : T ≤ normalizer (V : Set G) := fun t ht => hNV t (hTW ht) (hTK ht)
  have hSV : Y ⊔ R ≤ normalizer (V : Set G) := sup_le hYV hRV
  have hVne : V ≠ ⊥ := by
    obtain ⟨hVK0, -⟩ := hVK _ rfl
    intro hV0
    apply hVK0
    rw [eq_bot_iff, ← hV0]
    refine Subgroup.commutator_mono (fun z hz => ?_) le_rfl
    obtain ⟨hzQ, hzC⟩ := mem_inf.mp hz
    obtain ⟨hzQ', -, hz2⟩ := mem_omegaOneCenterOf_iff.mp hzQ
    have hQKR : pCoreOf 2 K ≤ R := by
      rw [hRKT]
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
        (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
          (hTK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    exact omegaOneCenterOf_le_nqSourceModule Y R
      (subset_omegaOneCenterOf (hQKR hzQ') hzC hz2)
  set Z₀ := V ⊓ centralizer (T : Set G) with hZ₀def
  have hZ₀ne : Z₀ ≠ ⊥ := by
    have hT2 : IsPGroup 2 ↥T := h.sylow.1
    have : Group.IsNilpotent ↥T := hT2.isNilpotent
    have hVn : (V.subgroupOf T).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVT).mpr hTV
    have hVne' : V.subgroupOf T ≠ ⊥ := by
      intro h0
      apply hVne
      rw [eq_bot_iff]
      intro v hv
      have : (⟨v, hVT hv⟩ : ↥T) ∈ V.subgroupOf T := hv
      rw [h0, mem_bot] at this
      exact (mem_bot).mpr (congrArg Subtype.val this)
    have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hVne'
    intro h0
    apply hc
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨htV, htc⟩ := mem_inf.mp ht
    have h1 : (t : G) ∈ Z₀ := mem_inf.mpr ⟨htV, mem_centralizer_iff.mpr fun s hs =>
      congrArg Subtype.val ((mem_center_iff.mp htc) ⟨s, hs⟩)⟩
    rw [h0, mem_bot] at h1
    exact (mem_bot).mpr (Subtype.ext h1)
  have hZ₀Z : Z₀ ≤ quasithinOmegaOneCenter T := fun z hz =>
    subset_closure ⟨mem_inf.mpr ⟨hVT hz.1, hz.2⟩, hW2 z (hVW hz.1)⟩
  have hCZ₀ : centralizer (Z₀ : Set G) ≤ M := by
    have hZ₀2 : IsPGroup 2 Z₀ := h.sylow.1.to_le (inf_le_left.trans hVT)
    have hloc : IsTwoLocal (normalizer (Z₀ : Set G)) := ⟨Z₀, hZ₀ne, hZ₀2, rfl⟩
    obtain ⟨M', hM'⟩ := Set.Finite.exists_maximal
      (s := {X : Subgroup G | IsTwoLocal X ∧ normalizer (Z₀ : Set G) ≤ X}) (Set.toFinite _)
      ⟨_, hloc, le_rfl⟩
    have hM'max : quasithinIsMaxTwoLocal M' :=
      ⟨hM'.1.1, fun X hX hMX => le_antisymm (hM'.2 ⟨hX, hM'.1.2.trans hMX⟩ hMX) hMX⟩
    have hCN : centralizer (Z₀ : Set G) ≤ normalizer (Z₀ : Set G) :=
      Subgroup.centralizer_le_normalizer _
    have hCM' : centralizer (quasithinOmegaOneCenter T : Set G) ≤ M' :=
      ((centralizer_le hZ₀Z).trans hCN).trans hM'.1.2
    rw [← h.centralizer_unique M' hM'max hCM']
    exact hCN.trans hM'.1.2
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  set J := nqHigherThompson R j with hJdef
  set CV := centralizer (V : Set G) with hCVdef
  have hRCV : R ≤ normalizer (CV : Set G) := fun r hr g =>
    ⟨fun hg => conj_mem_centralizer_of_normalizer (hRV hr) hg, fun hg => by
      have := conj_mem_centralizer_of_normalizer (inv_mem (hRV hr)) hg
      rwa [show r⁻¹ * (r * g * r⁻¹) * r⁻¹⁻¹ = g by group] at this⟩
  let X : Subgroup G :=
    { carrier := {a | a ∈ normalizer (CV : Set G) ∧ ∀ y ∈ Y, ⁅y, a⁆ ∈ CV}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨mul_mem ha.1 hb.1, fun y hy => ?_⟩
        have e : ⁅y, a * b⁆ = ⁅y, a⁆ * (a * ⁅y, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact CV.mul_mem (ha.2 y hy) ((mem_normalizer_iff.mp ha.1 _).mp (hb.2 y hy))
      one_mem' := ⟨one_mem _, fun y _ => by
        rw [commutatorElement_def, mul_one, mul_inv_cancel, one_mul, inv_one]
        exact CV.one_mem⟩
      inv_mem' := fun {a} ha => by
        refine ⟨inv_mem ha.1, fun y hy => ?_⟩
        have e : ⁅y, a⁻¹⁆ = a⁻¹ * ⁅y, a⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (mem_normalizer_iff.mp (inv_mem ha.1) _).mp (CV.inv_mem (ha.2 y hy)) }
  have hJX : J ≤ X := by
    rw [hJdef, nqHigherThompson, Subgroup.map_le_iff_le_comap]
    apply sSup_le
    intro A hA
    rw [← Subgroup.map_le_iff_le_comap]
    intro a ha
    refine ⟨hRCV (Subgroup.map_subtype_le A ha), fun y hy => ?_⟩
    have h1 := hall A hA
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
    have h2 : ⁅Y, A.map R.subtype⁆ ≤ CV := Subgroup.le_centralizer_iff.mp h1
    exact h2 (Subgroup.commutator_mem_commutator hy ha)
  set S := Y ⊔ R with hSdef
  set C := S ⊓ CV with hCdef
  set D := J ⊔ C with hDdef
  have hJR : J ≤ R := Subgroup.map_subtype_le _
  have hDS : D ≤ S := sup_le (hJR.trans le_sup_right) inf_le_left
  have hCnorm : ∀ g ∈ S, ∀ c ∈ C, g * c * g⁻¹ ∈ C := fun g hg c hc =>
    mem_inf.mpr ⟨S.mul_mem (S.mul_mem hg (mem_inf.mp hc).1) (S.inv_mem hg),
      conj_mem_centralizer_of_normalizer (hSV hg) (mem_inf.mp hc).2⟩
  have hDfwd : ∀ g ∈ S, ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
    intro g hg d hd
    have hle : S ≤ normalizer (D : Set G) := by
      refine sup_le (fun y hy => ?_) (fun r hr => ?_)
      · have hfy : ∀ y' ∈ Y, ∀ d' ∈ D, y' * d' * y'⁻¹ ∈ D := by
          intro y' hy' d' hd'
          have hle' : D ≤ D.comap (MulAut.conj y').toMonoidHom := by
            refine sup_le (fun a ha => ?_) (fun c hc => ?_)
            · change y' * a * y'⁻¹ ∈ D
              have e : y' * a * y'⁻¹ = ⁅y', a⁆ * a := by
                rw [commutatorElement_def]
                group
              rw [e]
              refine D.mul_mem (mem_sup_right (mem_inf.mpr ⟨?_, (hJX ha).2 y' hy'⟩))
                (mem_sup_left ha)
              rw [commutatorElement_def]
              have haS : a ∈ S := le_sup_right (a := Y) (hJR ha)
              have hy'S : y' ∈ S := le_sup_left (a := Y) hy'
              exact S.mul_mem (S.mul_mem (S.mul_mem hy'S haS) (S.inv_mem hy'S)) (S.inv_mem haS)
            · exact mem_sup_right (hCnorm y' (le_sup_left (a := Y) hy') c hc)
          exact hle' hd'
        exact mem_normalizer_of_conj_mem (hfy y hy) fun d' hd' => by
          have := hfy y⁻¹ (inv_mem hy) d' hd'
          rwa [inv_inv] at this
      · have hfr : ∀ r' ∈ R, ∀ d' ∈ D, r' * d' * r'⁻¹ ∈ D := by
          intro r' hr' d' hd'
          have hle' : D ≤ D.comap (MulAut.conj r').toMonoidHom :=
            sup_le (fun a ha => mem_sup_left
                ((mem_normalizer_iff.mp (le_normalizer_nqHigherThompson R j hr') a).mp ha))
              (fun c hc => mem_sup_right (hCnorm r' (le_sup_right (a := Y) hr') c hc))
          exact hle' hd'
        exact mem_normalizer_of_conj_mem (hfr r hr) fun d' hd' => by
          have := hfr r⁻¹ (inv_mem hr) d' hd'
          rwa [inv_inv] at this
    exact (mem_normalizer_iff.mp (hle hg) d).mp hd
  have hSD : S ≤ normalizer (D : Set G) := fun g hg =>
    mem_normalizer_of_conj_mem (hDfwd g hg) fun d hd => by
      have := hDfwd g⁻¹ (inv_mem hg) d hd
      rwa [inv_inv] at this
  have hP : CFSG.ABGLocalTools.IsSylowOf 2 (R ⊓ D) D :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hSyl hDS hSD
  have hFr := le_sup_normalizer_of_isSylowOf' hP hSD
  have hNP : normalizer ((R ⊓ D : Subgroup G) : Set G) ≤ normalizer (J : Set G) :=
    normalizer_le_normalizer_nqHigherThompson (le_inf hJR le_sup_left) inf_le_left
  have hCM : C ≤ M := (inf_le_right.trans (centralizer_le (inf_le_left : Z₀ ≤ V))).trans hCZ₀
  have hDM : D ≤ M := sup_le (Subgroup.le_normalizer.trans hJM) hCM
  exact hYM ((le_sup_left.trans hFr).trans (sup_le hDM (hNP.trans hJM)))

end CFSG.Quasithin.H13.NQBlock
