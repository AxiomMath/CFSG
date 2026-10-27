module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommRootStandardClosure
public import CFSG.LocalAnalysis.SteinbergBKOddNormalQuotientStandard
public import CFSG.LocalAnalysis.EvenBN.GMSK.LayerRankOne
public import CFSG.LocalAnalysis.EvenBN.GMSK.ConsumerSections
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCOddNormalCore
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace TorusLayer

open Subgroup CFSG.LocalAnalysis.EvenBN.GMSK CFSG.RankThree.PartOne.KCRootAxis
  CFSG.LocalAnalysis.ComponentInitial.OddNormalCore

structure LayerHyp {F : Type} [Group F] {K : Type} [Field K] (n : ℕ) {S : Subgroup F}
    (_e : SL₂ K ≃* ↥S) (J V : Subgroup F) (t u w : F) : Prop where
  two_le : 2 ≤ n
  card_K : Nat.card K = 2 ^ n
  order_t : orderOf t = 2
  S_le : S ≤ centralizer ({t} : Set F)
  S_normal : (S.subgroupOf (centralizer ({t} : Set F))).Normal
  J_le : J ≤ center F
  J_odd : Odd (Nat.card J)
  cent_eq : centralizer (S : Set F) ⊓ centralizer ({t} : Set F) = J ⊔ zpowers t
  u_mem : u ∈ S
  u_ne : u ≠ 1
  u_sq : u * u = 1
  w_conj : w⁻¹ * t * w = t * u
  four : ∃ E : Subgroup F, E ≤ S ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4
  sylow : ∃ P : Sylow 2 ↥S, Nat.card P = 2 ^ n
  V_pgroup : IsPGroup 2 V
  V_le : V ≤ normalClosure (S : Set F)
  V_card : (2 ^ n) ^ 2 ≤ Nat.card V
  kgroup : CFSG.SectionRank.IsKGroupCat F

section General

variable {X : Type*} [Group X]

theorem normal_of_le_center {J : Subgroup X} (hJ : J ≤ center X) : J.Normal :=
  ⟨fun x hx g => by
    rw [show g * x * g⁻¹ = x by rw [mem_center_iff.mp (hJ hx) g, mul_inv_cancel_right]]
    exact hx⟩

theorem card_map_of_injOn {Y : Type*} [Group Y] (f : X →* Y) {Q : Subgroup X}
    (h : Set.InjOn f (Q : Set X)) : Nat.card (Q.map f) = Nat.card Q := by
  change Nat.card ((Q.map f : Subgroup Y) : Set Y) = Nat.card (Q : Set X)
  rw [coe_map]
  exact Nat.card_image_of_injOn h

theorem card_le_of_sylow [Finite X] {S Q : Subgroup X} {m : ℕ}
    (hSyl : ∃ P : Sylow 2 ↥S, Nat.card P = m) (hQ : IsPGroup 2 Q) (hQS : Q ≤ S) :
    Nat.card Q ≤ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hSyl
  have hQ' : IsPGroup 2 (Q.subgroupOf S) := hQ.comap_of_injective S.subtype S.subtype_injective
  obtain ⟨P', hP'⟩ := hQ'.exists_le_sylow
  rw [← Nat.card_congr (subgroupOfEquivOfLe hQS).toEquiv, ← hP, P.card_eq_multiplicity,
    ← P'.card_eq_multiplicity]
  exact card_le_of_le hP'

end General

section Kernel

variable {F : Type} [Group F] [Finite F]

set_option quotPrecheck false in
local notation "𝐎" => CFSG.Open.standardComponentOddCore F

omit [Finite F] in
theorem le_oddCore {J : Subgroup F} (hJ : J ≤ center F) (hJodd : Odd (Nat.card J)) : J ≤ 𝐎 :=
  le_sSup ⟨normal_of_le_center hJ, hJodd⟩

theorem eq_one_of_mem_oddCore {S : Subgroup F} [IsSimpleGroup S] (h2 : 2 ∣ Nat.card S) {x : F}
    (hxS : x ∈ S) (hxO : x ∈ 𝐎) : x = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((𝐎).subgroupOf S) with h | h
  · have hx : (⟨x, hxS⟩ : S) ∈ (𝐎).subgroupOf S := hxO
    rw [h] at hx
    exact congrArg Subtype.val ((mem_bot).mp hx)
  · exfalso
    have hSO : S ≤ 𝐎 := fun y hy => by
      have hy' : (⟨y, hy⟩ : S) ∈ (𝐎).subgroupOf S := h ▸ mem_top _
      exact hy'
    exact (Nat.not_even_iff_odd.mpr (odd_card_standardComponentOddCore F))
      (even_iff_two_dvd.mpr (h2.trans (card_dvd_of_le hSO)))

theorem not_mem_oddCore {t : F} (ht : orderOf t = 2) : t ∉ 𝐎 := by
  intro htO
  have h1 := orderOf_dvd_natCard (⟨t, htO⟩ : 𝐎)
  rw [Subgroup.orderOf_mk, ht] at h1
  exact (Nat.not_even_iff_odd.mpr (odd_card_standardComponentOddCore F))
    (even_iff_two_dvd.mpr h1)

variable {K : Type} [Field K] {n : ℕ} {S : Subgroup F} {e : SL₂ K ≃* ↥S} {J V : Subgroup F}
  {t u w : F}

omit [Finite F] in
theorem isSimpleGroup_S [Finite K] [CharP K 2] (h : LayerHyp n e J V t u w) : IsSimpleGroup S := by
  have : IsSimpleGroup (SL₂ K) := CFSG.RankThree.PartOne.KCRootAxis.sl2_isSimpleGroup (by
    rw [h.card_K]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le)
  exact e.symm.isSimpleGroup

omit [Finite F] in
theorem two_dvd_card_S (h : LayerHyp n e J V t u w) : 2 ∣ Nat.card S := by
  obtain ⟨E, hES, -, hE4⟩ := h.four
  have := card_dvd_of_le hES
  rw [hE4] at this
  exact (by norm_num : 2 ∣ 4).trans this

omit [Finite F] in
theorem t_mul_t (h : LayerHyp n e J V t u w) : t * t = 1 := by
  rw [← pow_two, ← h.order_t, pow_orderOf_eq_one]

omit [Finite F] in
theorem t_not_mem_S [Finite K] [CharP K 2] (h : LayerHyp n e J V t u w) : t ∉ S := by
  intro htS
  have : IsSimpleGroup S := isSimpleGroup_S h
  have hc : (⟨t, htS⟩ : S) ∈ center S := mem_center_iff.mpr fun g => Subtype.ext
    (mem_centralizer_singleton_iff.mp (h.S_le g.2))
  have hcS : center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨x, y, hxy⟩ := sl2_exists_mul_ne (K := K)
      apply hxy
      apply e.injective
      rw [map_mul, map_mul]
      exact (mem_center_iff.mp (h1 ▸ mem_top (e y)) (e x))
  rw [hcS, mem_bot] at hc
  have := h.order_t
  rw [show t = 1 from congrArg Subtype.val hc, orderOf_one] at this
  exact absurd this (by norm_num)

theorem oddCore_inf_centralizer [Finite K] [CharP K 2] (h : LayerHyp n e J V t u w) :
    𝐎 ⊓ centralizer ({t} : Set F) = J := by
  have : IsSimpleGroup S := isSimpleGroup_S h
  have hJO := le_oddCore h.J_le h.J_odd
  apply le_antisymm
  · intro r hr
    obtain ⟨hrO, hrt⟩ := mem_inf.mp hr
    have hrS : r ∈ centralizer (S : Set F) := by
      refine mem_centralizer_iff.mpr fun s hs => ?_
      have h1 : r * s * r⁻¹ ∈ S := by
        have := h.S_normal.conj_mem ⟨s, h.S_le hs⟩ (mem_subgroupOf.mpr hs) ⟨r, hrt⟩
        rw [mem_subgroupOf] at this
        exact this
      have h2 : r * s * r⁻¹ * s⁻¹ ∈ S := mul_mem h1 (inv_mem hs)
      have h3 : r * s * r⁻¹ * s⁻¹ ∈ 𝐎 := by
        have := (inferInstance : (𝐎).Normal).conj_mem r⁻¹ (inv_mem hrO) s
        rw [show r * s * r⁻¹ * s⁻¹ = r * (s * r⁻¹ * s⁻¹) by group]
        exact mul_mem hrO this
      have h4 := eq_one_of_mem_oddCore (two_dvd_card_S h) h2 h3
      calc s * r = (r * s * r⁻¹ * s⁻¹)⁻¹ * (r * s) := by group
        _ = r * s := by rw [h4, inv_one, one_mul]
    have hrJt : r ∈ J ⊔ zpowers t := by
      rw [← h.cent_eq]
      exact mem_inf.mpr ⟨hrS, hrt⟩
    obtain ⟨j, hj, τ, hτ, rfl⟩ := (GomiFusion.mem_sup_of_commute fun x hx y _ =>
      (mem_center_iff.mp (h.J_le hx) y).symm).mp hrJt
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hτ
    rcases RootAxisTwoCore.zpow_eq_one_or_eq (t_mul_t h) m with h1 | h1
    · rw [h1, mul_one]
      exact hj
    · exfalso
      rw [h1] at hrO
      apply not_mem_oddCore h.order_t
      have := mul_mem (inv_mem (hJO hj)) hrO
      rwa [inv_mul_cancel_left] at this
  · exact le_inf hJO fun x hx => mem_centralizer_singleton_iff.mpr
      (mem_center_iff.mp (h.J_le hx) t).symm

theorem oddCore_le_centralizer [Finite K] [CharP K 2] (h : LayerHyp n e J V t u w) :
    𝐎 ≤ centralizer (normalClosure (S : Set F) : Set F) := by
  have : IsSimpleGroup S := isSimpleGroup_S h
  have hC := oddCore_inf_centralizer h
  have hJc : ∀ x ∈ J, ∀ y : F, y * x = x * y := fun x hx => mem_center_iff.mp (h.J_le hx)
  have hON : ∀ x : F, x ∈ normalizer (𝐎 : Set F) := fun x => by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact mem_top x
  have htu : t * u = u * t := (mem_centralizer_singleton_iff.mp (h.S_le h.u_mem)).symm
  have ht1 : t ≠ 1 := fun h1 => by
    have := h.order_t
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have htne : t ≠ u := fun h1 => t_not_mem_S h (h1 ▸ h.u_mem)
  have hu : ∀ x ∈ 𝐎, u * x = x * u := by
    refine commute_of_four_group_centralizers (odd_card_standardComponentOddCore F) (t_mul_t h)
      h.u_sq htu ht1 h.u_ne htne (hON t) (hON u) ?_ ?_ ?_
    · intro x hx hxt
      have hxJ : x ∈ J := by
        rw [← hC]
        exact mem_inf.mpr ⟨hx, mem_centralizer_singleton_iff.mpr hxt⟩
      exact hJc x hxJ u
    · intro x _ hxu
      exact hxu.symm
    · intro x hx hxtu
      rw [← h.w_conj] at hxtu
      have hy : w * x * w⁻¹ ∈ 𝐎 := (inferInstance : (𝐎).Normal).conj_mem x hx w
      have hyt : w * x * w⁻¹ * t = t * (w * x * w⁻¹) := by
        calc w * x * w⁻¹ * t = w * (x * (w⁻¹ * t * w)) * w⁻¹ := by group
          _ = w * ((w⁻¹ * t * w) * x) * w⁻¹ := by rw [hxtu]
          _ = t * (w * x * w⁻¹) := by group
      have hyJ : w * x * w⁻¹ ∈ J := by
        rw [← hC]
        exact mem_inf.mpr ⟨hy, mem_centralizer_singleton_iff.mpr hyt⟩
      have hxe : x = w * x * w⁻¹ := by
        have := hJc _ hyJ w⁻¹
        calc x = w⁻¹ * (w * x * w⁻¹) * w := by group
          _ = w * x * w⁻¹ * w⁻¹ * w := by rw [this]
          _ = w * x * w⁻¹ := by group
      rw [hxe]
      exact hJc _ hyJ u
  have hCn : (centralizer (𝐎 : Set F)).Normal := ⟨fun c hc g => mem_centralizer_iff.mpr
    fun x hx => by
      have hx' : g⁻¹ * x * g ∈ 𝐎 := by
        simpa using (inferInstance : (𝐎).Normal).conj_mem x hx g⁻¹
      have h1 := mem_centralizer_iff.mp hc (g⁻¹ * x * g) hx'
      calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
        _ = g * c * g⁻¹ * x := by group⟩
  have hSC : S ≤ centralizer (𝐎 : Set F) := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((centralizer (𝐎 : Set F)).subgroupOf S) with
      h1 | h1
    · exfalso
      have huC : (⟨u, h.u_mem⟩ : S) ∈ (centralizer (𝐎 : Set F)).subgroupOf S :=
        mem_subgroupOf.mpr (mem_centralizer_iff.mpr fun x hx => (hu x hx).symm)
      rw [h1, mem_bot] at huC
      exact h.u_ne (congrArg Subtype.val huC)
    · exact fun x hx => by
        have : (⟨x, hx⟩ : S) ∈ (centralizer (𝐎 : Set F)).subgroupOf S := h1 ▸ mem_top _
        exact this
  rw [le_centralizer_iff]
  exact normalClosure_le_normal hSC

end Kernel


section Quotient

variable {F : Type} [Group F] [Finite F] {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
  {S : Subgroup F} {e : SL₂ K ≃* ↥S} {J V : Subgroup F} {t u w : F}

set_option quotPrecheck false in
local notation "𝐎" => CFSG.Open.standardComponentOddCore F
set_option quotPrecheck false in
local notation "θ" => QuotientGroup.mk' (CFSG.Open.standardComponentOddCore F)

omit [Finite K] [CharP K 2] in
theorem exists_sylow_cent (h : LayerHyp n e J V t u w) :
    ∃ P : Sylow 2 ↥(centralizer (S : Set F) ⊓ centralizer ({t} : Set F)),
      (P : Subgroup _).map (centralizer (S : Set F) ⊓ centralizer ({t} : Set F)).subtype =
        zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [h.cent_eq, RootStandard.exists_sylow_map_iff]
  have hc : ∀ x ∈ J, ∀ y ∈ zpowers t, x * y = y * x := fun x hx y _ =>
    (mem_center_iff.mp (h.J_le hx) y).symm
  have hJt : J ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxJ, hxt⟩ := mem_inf.mp hx
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hxt
    rcases RootAxisTwoCore.zpow_eq_one_or_eq (t_mul_t h) m with h1 | h1
    · rw [h1]
      exact one_mem _
    · exfalso
      rw [h1] at hxJ
      exact not_mem_oddCore h.order_t (le_oddCore h.J_le h.J_odd hxJ)
  have hcard := GomiFusion.card_sup_of_commute hc hJt
  have ht2 : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, h.order_t]
  refine ⟨le_sup_right, IsPGroup.of_card (n := 1) (by rw [ht2, pow_one]), ?_⟩
  have h1 := card_mul_index ((zpowers t).subgroupOf (J ⊔ zpowers t))
  rw [Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv, hcard, ht2, mul_comm] at h1
  have h2 : (zpowers t).relIndex (J ⊔ zpowers t) = Nat.card J :=
    Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  rw [h2]
  exact fun h3 => (Nat.not_even_iff_odd.mpr h.J_odd) (even_iff_two_dvd.mpr h3)

theorem quotient_facts (h : LayerHyp n e J V t u w) :
    Set.InjOn θ (S : Set F) ∧ (∀ Q : Subgroup F, IsPGroup 2 Q → Set.InjOn θ (Q : Set F)) ∧
      orderOf (θ t) = 2 ∧ IsSimpleGroup (S.map θ) ∧ (∃ x y : S.map θ, x * y ≠ y * x) ∧
      S.map θ ≤ centralizer ({θ t} : Set (F ⧸ 𝐎)) ∧
      ((S.map θ).subgroupOf (centralizer ({θ t} : Set (F ⧸ 𝐎)))).Normal ∧
      centralizer ({θ t} : Set (F ⧸ 𝐎)) = (centralizer ({t} : Set F)).map θ ∧
      centralizer ((S.map θ : Subgroup (F ⧸ 𝐎)) : Set (F ⧸ 𝐎)) ⊓
          centralizer ({θ t} : Set (F ⧸ 𝐎)) = zpowers (θ t) ∧
      CFSG.Open.standardComponentIsStandard (S.map θ) ∧
      ∃ P : Sylow 2 ↥(centralizer ((S.map θ : Subgroup (F ⧸ 𝐎)) : Set (F ⧸ 𝐎))),
        (P : Subgroup _).map
          (centralizer ((S.map θ : Subgroup (F ⧸ 𝐎)) : Set (F ⧸ 𝐎))).subtype = zpowers (θ t) := by
  have : IsSimpleGroup S := isSimpleGroup_S h
  have hnab : ∃ x y : S, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := sl2_exists_mul_ne (K := K)
    exact ⟨e x, e y, fun h1 => hxy (e.injective (by rw [map_mul, map_mul, h1]))⟩
  obtain ⟨hinj, hinj2, hθt, hsimp, hnab', hle, hn, hCt, hCC, hstd, hsyl, -⟩ :=
    CFSG.LocalAnalysis.SteinbergBK.simple_involution_centralizer_odd_normal_quotient_standardness
      hnab h.four h.order_t h.S_le h.S_normal (exists_sylow_cent h) 𝐎
      (odd_card_standardComponentOddCore F)
  refine ⟨hinj, hinj2, hθt, hsimp, hnab', hle, hn, hCt, ?_, hstd, hsyl⟩
  rw [hCC, h.cent_eq, Subgroup.map_sup, MonoidHom.map_zpowers]
  have hJ : J.map θ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff x).mpr (le_oddCore h.J_le h.J_odd hx)
  rw [hJ, bot_sup_eq]

theorem exists_equiv_map (h : LayerHyp n e J V t u w) :
    ∃ e' : SL₂ K ≃* ↥(S.map θ), ∀ X, (e' X : F ⧸ 𝐎) = θ (e X) := by
  have hinj := (quotient_facts h).1
  let f : SL₂ K →* F ⧸ 𝐎 :=
    (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore F)).comp (S.subtype.comp e.toMonoidHom)
  have hf : Function.Injective f := fun X Y hXY =>
    e.injective (Subtype.ext (hinj (e X).2 (e Y).2 hXY))
  have hr : f.range = S.map θ := by
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨e X, (e X).2, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨e.symm ⟨s, hs⟩, by simp [f]⟩
  exact ⟨(MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr), fun _ => rfl⟩

omit [Finite F] in
theorem map_normalClosure_S :
    (normalClosure (S : Set F)).map θ =
      normalClosure ((S.map θ : Subgroup (F ⧸ 𝐎)) : Set (F ⧸ 𝐎)) := by
  rw [map_normalClosure _ _ (QuotientGroup.mk'_surjective _), ← coe_map]

theorem exists_sylow_map (h : LayerHyp n e J V t u w) :
    ∃ P : Sylow 2 ↥(S.map θ), Nat.card P = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := h.sylow
  have hcS : Nat.card (S.map θ) = Nat.card S := card_map_of_injOn θ (quotient_facts h).1
  refine ⟨Classical.arbitrary _, ?_⟩
  rw [Sylow.card_eq_multiplicity, hcS, ← P.card_eq_multiplicity, hP]

omit [Finite F] [Finite K] [CharP K 2] in
theorem pow_lt_sq (h : LayerHyp n e J V t u w) : 2 ^ n < (2 ^ n) ^ 2 := by
  have h1 : 1 < 2 ^ n := Nat.one_lt_two_pow (by have := h.two_le; omega)
  nlinarith

theorem not_normal_map (h : LayerHyp n e J V t u w) : ¬ (S.map θ).Normal := by
  intro hN
  obtain ⟨-, hinj2, -⟩ := quotient_facts h
  have hD : normalClosure ((S.map θ : Subgroup (F ⧸ 𝐎)) : Set (F ⧸ 𝐎)) = S.map θ :=
    normalClosure_eq_self _
  have hVS : V.map θ ≤ S.map θ :=
    (map_mono h.V_le).trans (map_normalClosure_S.trans hD).le
  have h1 := card_le_of_sylow (exists_sylow_map h) (h.V_pgroup.map θ) hVS
  rw [card_map_of_injOn θ (hinj2 V h.V_pgroup)] at h1
  exact absurd (h.V_card.trans h1) (not_le.mpr (pow_lt_sq h))

theorem layer_conclusion (h : LayerHyp n e J V t u w) :
    CFSG.LocalAnalysis.SteinbergBV.OneOrTwoLayerConclusion (S.map θ) (θ t) := by
  obtain ⟨hinj, -, hθt, hsimp, hnab, hle, hn, -, -, -, ⟨P, hP⟩⟩ := quotient_facts h
  have hKbar : CFSG.SectionRank.IsKGroupCat (F ⧸ 𝐎) := h.kgroup.quotient 𝐎
  have hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog (F ⧸ 𝐎) :=
    fun K L _ _ _ hs _ => hKbar K (L.subgroupOf K) hs
  have hcore : CFSG.pPrimeCore 2 (F ⧸ 𝐎) = ⊥ :=
    pPrimeCore_eq_bot_of_oddCore_eq_bot (standardComponentOddCore_quotient_eq_bot F)
  have hE : ∃ E : Subgroup (F ⧸ 𝐎), E ≤ S.map θ ∧ CFSG.IsElementaryAbelian 2 E ∧
      Nat.card E = 4 := by
    obtain ⟨E, hES, hEab, hE4⟩ := h.four
    have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hEab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    refine ⟨E.map θ, map_mono hES, FullCenter.isElementaryAbelian_of ?_ ?_,
      by rw [card_map_of_injOn θ (hinj.mono hES), hE4]⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, ← pow_two, hEab.2 x hx, map_one]
  have hCN : centralizer ({θ t} : Set (F ⧸ 𝐎)) ≤ normalizer ((S.map θ : Subgroup _) : Set _) :=
    (normal_subgroupOf_iff_le_normalizer hle).mp hn
  have hodd := (RootStandard.exists_sylow_map_iff.mp ⟨P, hP⟩).2.2
  exact nonnormalInvolutionComponentLayerStmt (F ⧸ 𝐎) hKP hcore (S.map θ) hsimp hnab hE (θ t)
    hθt hle hCN hodd (not_normal_map h)

theorem centralizer_normalClosure (h : LayerHyp n e J V t u w) :
    centralizer (normalClosure (S : Set F) : Set F) = 𝐎 := by
  obtain ⟨-, -, -, -, hCD, -⟩ := layer_conclusion h
  apply le_antisymm _ (oddCore_le_centralizer h)
  intro c hc
  have hθc : θ c ∈ centralizer (normalClosure ((S.map θ : Subgroup (F ⧸ 𝐎)) :
      Set (F ⧸ 𝐎)) : Set (F ⧸ 𝐎)) := by
    rw [← map_normalClosure_S, mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hc l hl]
  rw [hCD, mem_bot] at hθc
  exact (QuotientGroup.eq_one_iff c).mp hθc

theorem center_normalClosure (h : LayerHyp n e J V t u w) :
    (center (normalClosure (S : Set F))).map (normalClosure (S : Set F)).subtype =
      normalClosure (S : Set F) ⊓ 𝐎 := by
  have hCL := centralizer_normalClosure h
  ext x
  rw [GomiFusion.mem_center_map_iff, mem_inf, ← hCL, mem_centralizer_iff]
  exact Iff.rfl

theorem oddCore_normalClosure :
    (CFSG.Open.standardComponentOddCore (normalClosure (S : Set F))).map
        (normalClosure (S : Set F)).subtype =
      normalClosure (S : Set F) ⊓ 𝐎 := by
  apply le_antisymm
  · refine le_inf (map_subtype_le _) ?_
    have : (CFSG.Open.standardComponentOddCore (normalClosure (S : Set F))).Characteristic :=
      oddCore_characteristic _
    refine le_sSup ⟨ConjAct.normal_of_characteristic_of_normal, ?_⟩
    rw [card_subtype]
    exact odd_card_standardComponentOddCore _
  · rw [inf_comm, ← subgroupOf_map_subtype]
    apply map_mono
    refine le_sSup ⟨normal_subgroupOf, ?_⟩
    have hcard : Nat.card ((𝐎).subgroupOf (normalClosure (S : Set F))) =
        Nat.card (𝐎 ⊓ normalClosure (S : Set F) : Subgroup F) := by
      rw [← subgroupOf_map_subtype, card_subtype]
    rw [hcard]
    exact (odd_card_standardComponentOddCore F).of_dvd_nat (card_dvd_of_le inf_le_left)

theorem quotient_normalClosure (h : LayerHyp n e J V t u w) :
    ∃ e' : ↥(normalClosure (S : Set F)) ⧸ center ↥(normalClosure (S : Set F)) ≃*
        ↥(normalClosure ((S.map θ : Subgroup (F ⧸ 𝐎)) : Set (F ⧸ 𝐎))),
      ∀ y : normalClosure (S : Set F),
        (e' (y : ↥(normalClosure (S : Set F)) ⧸ center ↥(normalClosure (S : Set F))) :
          F ⧸ 𝐎) = θ y := by
  set Y := normalClosure (S : Set F)
  let ψ : Y →* F ⧸ 𝐎 := (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore F)).comp Y.subtype
  have hker : center Y = ψ.ker := by
    apply map_injective Y.subtype_injective
    have h1 : ψ.ker = (𝐎).subgroupOf Y := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      exact QuotientGroup.eq_one_iff (x : F)
    rw [center_normalClosure h, h1, subgroupOf_map_subtype, inf_comm]
  have hrange : ψ.range = normalClosure ((S.map θ : Subgroup (F ⧸ 𝐎)) : Set (F ⧸ 𝐎)) := by
    rw [MonoidHom.range_comp, range_subtype, map_normalClosure_S]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange)),
    fun _ => rfl⟩

theorem isSimpleGroup_layer (h : LayerHyp n e J V t u w) (hV : (2 ^ n) ^ 2 < Nat.card V) :
    IsSimpleGroup (normalClosure ((S.map θ : Subgroup (F ⧸ 𝐎)) : Set (F ⧸ 𝐎))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, halt, -⟩ := layer_conclusion h
  obtain ⟨-, hinj2, -⟩ := quotient_facts h
  rcases halt with ⟨⟨hs, -⟩, -⟩ | ⟨⟨D₁, D₂, -, -, -, -, -, -, -, -, -, -, -, -, ψ, -⟩, -⟩
  · exact hs
  · exfalso
    set D := normalClosure ((S.map θ : Subgroup (F ⧸ 𝐎)) : Set (F ⧸ 𝐎))
    have hVD : V.map θ ≤ D := (map_mono h.V_le).trans map_normalClosure_S.le
    obtain ⟨P, hP⟩ := exists_sylow_map h
    have hcD : Nat.card D = Nat.card (S.map θ) ^ 2 := by
      rw [Nat.card_congr ψ.toEquiv, Nat.card_prod, sq]
    have hSylD : ∃ Q : Sylow 2 ↥D, Nat.card Q = (2 ^ n) ^ 2 := by
      refine ⟨Classical.arbitrary _, ?_⟩
      rw [Sylow.card_eq_multiplicity, hcD, Nat.factorization_pow, ← hP,
        P.card_eq_multiplicity]
      simp only [Finsupp.smul_apply, smul_eq_mul]
      rw [← pow_mul, mul_comm]
    have h1 := card_le_of_sylow hSylD (h.V_pgroup.map θ) hVD
    rw [card_map_of_injOn θ (hinj2 V h.V_pgroup)] at h1
    exact absurd hV (not_lt.mpr h1)

end Quotient

end TorusLayer

end CFSG.LocalAnalysis.SymplecticFourStandard
