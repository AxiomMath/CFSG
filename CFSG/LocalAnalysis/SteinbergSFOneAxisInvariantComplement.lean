module

public import CFSG.LocalAnalysis.SteinbergSFOneAxisRadicalStructure
public import CFSG.LocalAnalysis.SteinbergSFFullCenterTorusComplementBase

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace OneAxisComplement

open Subgroup GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
  OneAxisRadicalStructure
open FullCenterTorus (zc zc_mul zc_mem exists_zc zc_inj zc_zero zc_inv coordG_one_eq
  coordG_two_eq zc_mem_U_one zc_mem_U_two conj_zc exists_conj_zc torus_comm
  torus_pow_card_sub_one axisTorus axisTorus_le axisTorus_cent axisTorus_mod U_inf_U
  exists_diagHom mem_of_telescope mem_of_mem_closure_delta card_eq_of_conj_surj)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.LocalAnalysis.SteinbergCD
open scoped commutatorElement Pointwise

section General

variable {G : Type*} [Group G]

theorem kappa_conj {t j : G} (hjt : j * t = t * j) (x : G) :
    t⁻¹ * ((j⁻¹ * x * j)⁻¹ * t * (j⁻¹ * x * j)) = j⁻¹ * (t⁻¹ * (x⁻¹ * t * x)) * j := by
  have e : j⁻¹ * t * j = t := by rw [mul_assoc, ← hjt, inv_mul_cancel_left]
  calc t⁻¹ * ((j⁻¹ * x * j)⁻¹ * t * (j⁻¹ * x * j))
      = (j⁻¹ * t * j)⁻¹ * ((j⁻¹ * x * j)⁻¹ * (j⁻¹ * t * j) * (j⁻¹ * x * j)) := by rw [e]
    _ = j⁻¹ * (t⁻¹ * (x⁻¹ * t * x)) * j := by group

theorem kappa_eq_one_iff {t x : G} :
    t⁻¹ * (x⁻¹ * t * x) = 1 ↔ x ∈ centralizer ({t} : Set G) := by
  rw [mem_centralizer_singleton_iff, inv_mul_eq_one]
  constructor
  · intro h
    calc x * t = x * (x⁻¹ * t * x) := by rw [← h]
      _ = t * x := by group
  · intro h
    rw [mul_assoc, ← h, inv_mul_cancel_left]

end General

section Torus

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {φ : L ≃* antiSp K}

local notation "𝐉ₐ" => pull φ (axisTorus K Axis.one)
local notation "𝐉ᵦ" => pull φ (axisTorus K Axis.two)

theorem exists_torus_elt {r s : K} (hr : r ≠ 0) (hs : s ≠ 0) :
    ∃ j ∈ pull φ (diagTorus K), ∀ b c : K, j⁻¹ * zc φ b c * j = zc φ (r * s * b) (r ^ 2 * c) := by
  obtain ⟨δ, hδ, hδm⟩ := exists_diagTorus (K := K) hr hs
  exact ⟨_, symm_mem_pull.mpr hδ, conj_zc hr hs hδm⟩

theorem exists_Ja_elt {r : K} (hr : r ≠ 0) :
    ∃ a ∈ 𝐉ₐ, ∀ b c : K, a⁻¹ * zc φ b c * a = zc φ b (r ^ 2 * c) := by
  obtain ⟨δ, -, hδm⟩ := exists_diagTorus (K := K) hr (inv_ne_zero hr)
  refine ⟨_, symm_mem_pull.mpr ⟨r, hr, hδm⟩, fun b c => ?_⟩
  rw [conj_zc hr (inv_ne_zero hr) hδm, mul_inv_cancel₀ hr, one_mul]

theorem exists_Jb_elt {s : K} (hs : s ≠ 0) :
    ∃ a ∈ 𝐉ᵦ, ∀ b c : K, a⁻¹ * zc φ b c * a = zc φ (s * b) c := by
  obtain ⟨δ, -, hδm⟩ := exists_diagTorus (K := K) one_ne_zero hs
  refine ⟨_, symm_mem_pull.mpr ⟨s, hs, hδm⟩, fun b c => ?_⟩
  rw [conj_zc one_ne_zero hs hδm, one_mul, one_pow, one_mul]

end Torus

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G}

local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ TG : Subgroup G)
local notation "𝐔₁" => pull φ (rootU K Axis.one)
local notation "𝐔₂" => pull φ (rootU K Axis.two)
local notation "𝐀₁" => pull φ (rootA K Axis.one)
local notation "𝐀₂" => pull φ (rootA K Axis.two)
local notation "𝐁₁" => (zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G)
local notation "𝐁₂" => (zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G)
local notation "𝐍₁" => normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G) : Set G)
local notation "𝐍₂" => normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐃₁" => (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) :
  Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) :
  Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐃₂" => (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐃" => (𝐃₁ ⊓ 𝐃₂ : Subgroup G)
set_option quotPrecheck false in
local notation "𝐒" => (pull φ (antiUnipotent K) ⊔ TG ⊔ 𝐃₂ : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
local notation "𝐉" => pull φ (diagTorus K)
local notation "𝐉ₐ" => pull φ (axisTorus K Axis.one)
local notation "𝐉ᵦ" => pull φ (axisTorus K Axis.two)

omit [Finite G] [Finite K] in
theorem ZP_le_A₁ : 𝐙 ≤ 𝐀₁ := pull_mono φ (center_le_rootA Axis.one)

omit [Finite G] [Finite K] in
theorem ZP_le_A₂ : 𝐙 ≤ 𝐀₂ := pull_mono φ (center_le_rootA Axis.two)

omit [Finite G] [Finite K] in
theorem U₁_le_ZP : 𝐔₁ ≤ 𝐙 := pull_mono φ (rootU_le_center Axis.one)

omit [Finite G] [Finite K] in
theorem U₂_le_ZP : 𝐔₂ ≤ 𝐙 := pull_mono φ (rootU_le_center Axis.two)

omit [Finite G] [Finite K] in
theorem A₁_inf_A₂ : 𝐀₁ ⊓ 𝐀₂ = 𝐙 := by
  rw [← pull_inf]
  exact congrArg (pull φ) radA1_inf_radA2

omit [Finite G] [Finite K] in
theorem A₁_le_D₁ (hh : HeisHyp L K n φ TG t) : 𝐀₁ ≤ 𝐃₁ := le_sup_right.trans (B₁_le_D₁ hh)

omit [Finite G] in
theorem A₂_le_D₂ (hh : HeisHyp L K n φ TG t) : 𝐀₂ ≤ 𝐃₂ :=
  le_sup_right.trans hh.sec.B_le_D

omit [Finite G] in
theorem t_mem_D (hh : HeisHyp L K n φ TG t) : t ∈ 𝐃 := ⟨t_mem_D₁ hh, t_mem_D₂ hh⟩

omit [Finite G] in
theorem ZP_le_D (hh : HeisHyp L K n φ TG t) : 𝐙 ≤ 𝐃 := fun _ hz =>
  ⟨A₁_le_D₁ hh (ZP_le_A₁ hz), A₂_le_D₂ hh (ZP_le_A₂ hz)⟩

theorem comm_ZP_of_mem_D (hh : HeisHyp L K n φ TG t) {x : G} (hx : x ∈ 𝐃) {z : G}
    (hz : z ∈ 𝐙) : x * z = z * x :=
  comm_ZP_of_mem_R hh (mem_sup_right hx.1) hz

omit [Finite G] [Finite K] in
theorem kappa_inv (hh : HeisHyp L K n φ TG t) {x : G} (hx : x ∈ 𝐃₁) :
    t⁻¹ * (x⁻¹⁻¹ * t * x⁻¹) = (t⁻¹ * (x⁻¹ * t * x))⁻¹ := by
  have h1 := hh.mul₁ _ (inv_mem hx) x hx
  rw [inv_mul_cancel, inv_one, one_mul, mul_one, inv_mul_cancel] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

omit [Finite K] in
theorem torus_le_normalizer_Q (hh : HeisHyp L K n φ TG t) : 𝐉 ≤ normalizer (𝐐 : Set G) :=
  hh.hyp.setup.diagTorus_le_normalizer

omit [Finite K] in
theorem conj_torus_mem_D₁ (hh : HeisHyp L K n φ TG t) {j : G} (hj : j ∈ 𝐉) {x : G}
    (hx : x ∈ 𝐃₁) : j⁻¹ * x * j ∈ 𝐃₁ := by
  have hjN : j ∈ 𝐍₁ := (hh.normQ (torus_le_normalizer_Q hh hj)).1
  simpa using conj_mem_pCore_map (inv_mem hjN) hx

omit [Finite K] in
theorem conj_torus_mem_D₂ (hh : HeisHyp L K n φ TG t) {j : G} (hj : j ∈ 𝐉) {x : G}
    (hx : x ∈ 𝐃₂) : j⁻¹ * x * j ∈ 𝐃₂ := by
  have hjN : j ∈ 𝐍₂ := (hh.normQ (torus_le_normalizer_Q hh hj)).2
  simpa using conj_mem_pCore_map (inv_mem hjN) hx

omit [Finite K] in
theorem conj_torus_mem_D (hh : HeisHyp L K n φ TG t) {j : G} (hj : j ∈ 𝐉) {x : G}
    (hx : x ∈ 𝐃) : j⁻¹ * x * j ∈ 𝐃 :=
  ⟨conj_torus_mem_D₁ hh hj hx.1, conj_torus_mem_D₂ hh hj hx.2⟩

omit [Finite G] [Finite K] in
theorem torus_comm_t (hh : HeisHyp L K n φ TG t) {j : G} (hj : j ∈ 𝐉) : j * t = t * j :=
  (hh.sec.two.comm (pull_le φ _ hj)).symm

omit [Finite G] [Finite K] in
theorem conj_torus_mem_ZP {j : G} (hj : j ∈ 𝐉) {z : G} (hz : z ∈ 𝐙) : j⁻¹ * z * j ∈ 𝐙 := by
  obtain ⟨r, s, -, -, hrs⟩ := exists_conj_zc hj
  obtain ⟨b, c, rfl⟩ := exists_zc hz
  rw [hrs]
  exact zc_mem _ _

omit [Finite G] in
theorem conj_torus_mem_U₁ {j : G} (hj : j ∈ 𝐉) {u : G} (hu : u ∈ 𝐔₁) : j⁻¹ * u * j ∈ 𝐔₁ := by
  obtain ⟨r, s, -, -, hrs⟩ := exists_conj_zc hj
  obtain ⟨b, rfl⟩ := exists_coordG_eq φ Axis.one hu
  rw [coordG_one_eq, hrs, mul_zero]
  exact zc_mem_U_one.mpr rfl

omit [Finite G] [Finite K] in
theorem B₁_inf_B₂ (hh : HeisHyp L K n φ TG t) : 𝐁₁ ⊓ 𝐁₂ = zpowers t ⊔ 𝐙 := by
  have hS := hh.sec.two
  apply le_antisymm
  · rintro x ⟨h1, h2⟩
    rcases (mem_zpowers_sup_iff hS.t_mul_t (TwoCoreSetup.comm_pull φ hS)).mp h1 with h1 | h1 <;>
      rcases (mem_zpowers_sup_iff hS.t_mul_t (TwoCoreSetup.comm_pull φ hS)).mp h2 with h2 | h2
    · exact mem_sup_right (A₁_inf_A₂.le ⟨h1, h2⟩)
    · exact absurd (by simpa using mul_mem (pull_le φ _ h2) (inv_mem (pull_le φ _ h1)))
        hS.t_not_mem
    · exact absurd (by simpa using mul_mem (pull_le φ _ h1) (inv_mem (pull_le φ _ h2)))
        hS.t_not_mem
    · exact (mem_zpowers_sup_iff hS.t_mul_t (TwoCoreSetup.comm_pull φ hS)).mpr
        (Or.inr (A₁_inf_A₂.le ⟨h1, h2⟩))
  · exact sup_le (le_inf le_sup_left le_sup_left)
      (le_inf (ZP_le_A₁.trans le_sup_right) (ZP_le_A₂.trans le_sup_right))

theorem mem_B₂_of_mem_Q_D₂ (hh : HeisHyp L K n φ TG t) {x : G} (hxQ : x ∈ 𝐐) (hxD : x ∈ 𝐃₂) :
    x ∈ 𝐁₂ := by
  obtain ⟨δ, hδ⟩ := hh.hAct_of_mem_Q hxQ
  have hxS : x ∈ 𝐒 := mem_sup_left hxQ
  obtain rfl : δ = 0 := (hh.mem_D₂_iff hxS hδ).mp hxD
  exact mem_B₂_of_hAct hh (hh.S_le_N₂ hxS) hδ

theorem D_inf_C (hh : HeisHyp L K n φ TG t) : 𝐃 ⊓ 𝐂 = zpowers t ⊔ 𝐙 := by
  apply le_antisymm
  · rintro x ⟨⟨hx1, hx2⟩, hxC⟩
    have hxB₁ := hh.mem_B₁ hx1 (mem_centralizer_singleton_iff.mp hxC)
    rw [← B₁_inf_B₂ hh]
    exact ⟨hxB₁, mem_B₂_of_mem_Q_D₂ hh (hh.hyp.B_le_Q Axis.one hxB₁) hx2⟩
  · refine le_inf (sup_le (zpowers_le.mpr (t_mem_D hh)) (ZP_le_D hh)) ?_
    exact sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
      fun z hz => hh.sec.two.L_le (pull_le φ _ hz)

theorem mem_A₁_mul_D (hh : HeisHyp L K n φ TG t) {d : G} (hd : d ∈ 𝐃₁) :
    ∃ a ∈ 𝐀₁, a⁻¹ * d ∈ 𝐃 := by
  obtain ⟨y, δ, h⟩ := hh.hAct_of_mem_D₁ hd
  have haA : ((φ.symm (uElt 0 0 0 δ) : L) : G) ∈ 𝐀₁ := symm_mem_pull.mpr ⟨0, 0, δ, rfl⟩
  have ha := hAct_symm_uElt (φ := φ) hh.sec.two 0 0 0 δ
  have hx : HAct φ t (((φ.symm (uElt 0 0 0 δ) : L) : G)⁻¹ * d) 0 y 0 :=
    ((hAct_inv ha).mul h).congr (by ring) (by ring) (CharTwo.add_self_eq_zero δ)
  have hxD₁ : ((φ.symm (uElt 0 0 0 δ) : L) : G)⁻¹ * d ∈ 𝐃₁ :=
    mul_mem (inv_mem (A₁_le_D₁ hh haA)) hd
  exact ⟨_, haA, hxD₁, (hh.mem_D₂_iff (hh.R_le_S (mem_sup_right hxD₁)) hx).mpr rfl⟩

theorem A₁_mul_D (hh : HeisHyp L K n φ TG t) : (𝐀₁ : Set G) * (𝐃 : Set G) = 𝐃₁ := by
  ext d
  constructor
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact mul_mem (A₁_le_D₁ hh ha) hx.1
  · intro hd
    obtain ⟨a, ha, hx⟩ := mem_A₁_mul_D hh hd
    exact ⟨a, ha, a⁻¹ * d, hx, by group⟩

theorem B₁_mul_D (hh : HeisHyp L K n φ TG t) : (𝐁₁ : Set G) * (𝐃 : Set G) = 𝐃₁ := by
  ext d
  constructor
  · rintro ⟨b, hb, x, hx, rfl⟩
    exact mul_mem (B₁_le_D₁ hh hb) hx.1
  · intro hd
    obtain ⟨a, ha, hx⟩ := mem_A₁_mul_D hh hd
    exact ⟨a, mem_sup_right ha, a⁻¹ * d, hx, by group⟩

theorem exists_kappa_eq_D (hh : HeisHyp L K n φ TG t) {u : G} (hu : u ∈ 𝐔₁) :
    ∃ d ∈ 𝐃, t⁻¹ * (d⁻¹ * t * d) = u := by
  obtain ⟨d, hd, hdu⟩ := hh.surj₁ u hu
  obtain ⟨a, ha, hx⟩ := mem_A₁_mul_D hh hd
  refine ⟨a⁻¹ * d, hx, ?_⟩
  have hk : t⁻¹ * (a⁻¹⁻¹ * t * a⁻¹) = 1 :=
    kappa_eq_one_iff.mpr (inv_mem (hh.sec.two.L_le (pull_le φ _ ha)))
  rw [hh.mul₁ _ (inv_mem (A₁_le_D₁ hh ha)) d hd, hk, one_mul, hdu]

theorem card_tZ (hh : HeisHyp L K n φ TG t) :
    Nat.card (zpowers t ⊔ 𝐙 : Subgroup G) = 2 * Nat.card K ^ 2 := by
  rw [card_sup_of_commute (fun y hy z hz => hh.sec.two.zpowers_comm hy (pull_le φ _ hz))
    (hh.sec.two.zpowers_inf (pull_le φ _)), Nat.card_zpowers, hh.hyp.setup.order_t, card_pull,
    (card_radicals (K := K)).2.2.2]

theorem card_D (hh : HeisHyp L K n φ TG t) : Nat.card 𝐃 = 2 * Nat.card K ^ 3 := by
  rw [card_eq_of_conj_surj (X := 𝐃) (U := 𝐔₁) (fun x hx => hh.conj₁ x hx.1)
    (fun u hu => exists_kappa_eq_D hh hu),
    show (𝐂 ⊓ 𝐃 : Subgroup G) = zpowers t ⊔ 𝐙 from (inf_comm _ _).trans (D_inf_C hh),
    card_tZ hh, card_U]
  ring

theorem commutator_D (hh : HeisHyp L K n φ TG t) :
    ⁅𝐃, 𝐃⁆ = 𝐔₁ ∧ closure {x : G | ∃ y ∈ 𝐃, x = y * y} = 𝐔₁ := by
  have hsq : closure {x : G | ∃ y ∈ 𝐃, x = y * y} ≤ 𝐔₁ :=
    (Subgroup.closure_mono (by rintro _ ⟨y, hy, rfl⟩; exact ⟨y, hy.1, rfl⟩)).trans (sq_D₁_le_U₁ hh)
  have hU : 𝐔₁ ≤ ⁅𝐃, 𝐃⁆ := by
    intro u hu
    obtain ⟨d, hd, rfl⟩ := exists_kappa_eq_D hh hu
    have e : t⁻¹ * (d⁻¹ * t * d) = ⁅t⁻¹, d⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact commutator_mem_commutator (inv_mem (t_mem_D hh)) (inv_mem hd)
  exact ⟨le_antisymm ((commutator_le_closure_sq _).trans hsq) hU,
    le_antisymm hsq (hU.trans (commutator_le_closure_sq _))⟩

theorem center_D (hh : HeisHyp L K n φ TG t) : (center 𝐃).map 𝐃.subtype = 𝐙 := by
  apply le_antisymm
  · intro z hz
    obtain ⟨hzD, hzc⟩ := mem_center_map_iff.mp hz
    have hzC : z ∈ 𝐂 := mem_centralizer_singleton_iff.mpr (hzc t (t_mem_D hh)).symm
    rcases (mem_zpowers_sup_iff hh.sec.two.t_mul_t (TwoCoreSetup.comm_pull φ hh.sec.two)).mp
      ((D_inf_C hh).le ⟨hzD, hzC⟩) with h | h
    · exact h
    · exfalso
      obtain ⟨d, hd, hdt⟩ := exists_kappa_eq_D hh (coordG_mem φ Axis.one 1)
      have h1 := hzc d hd
      have h2 := comm_ZP_of_mem_D hh hd h
      have hdt' : d * t = t * d := by
        calc d * t = d * (t * z) * z⁻¹ := by group
          _ = t * z * d * z⁻¹ := by rw [h2]
          _ = t * (z * d) * z⁻¹ := by group
          _ = t * (d * z) * z⁻¹ := by rw [h1]
          _ = t * d := by group
      have h3 := kappa_eq_one_iff.mpr (mem_centralizer_singleton_iff.mpr hdt')
      rw [hdt] at h3
      exact one_ne_zero (coordG_injective φ Axis.one (h3.trans (coordG_zero φ Axis.one).symm))
  · intro z hz
    exact mem_center_map_iff.mpr ⟨ZP_le_D hh hz, fun y hy => comm_ZP_of_mem_D hh hy hz⟩

omit [Finite G] in
theorem conj_eq_iff {x : G} : x⁻¹ * t * x = t ↔ x ∈ 𝐂 := by
  rw [← kappa_eq_one_iff, inv_mul_eq_one, eq_comm]

omit [Finite G] [Finite K] in
theorem odd_card_sub_one (hh : HeisHyp L K n φ TG t) : Odd (Nat.card K - 1) := by
  rw [hh.sec.two.card_K]
  exact Nat.Even.sub_odd Nat.one_le_two_pow
    (Nat.even_pow.mpr ⟨even_two, by have := hh.sec.two.two_le; omega⟩) odd_one

omit [Finite G] in
theorem exists_good (hh : HeisHyp L K n φ TG t) :
    ∃ j₀ ∈ 𝐉, (∀ z ∈ 𝐙, j₀⁻¹ * z * j₀ = z → z = 1) ∧
      (∀ z ∈ 𝐙, ∃ w ∈ 𝐙, w⁻¹ * (j₀⁻¹ * w * j₀) = z) ∧
      ∀ u ∈ 𝐔₁, ∃ w ∈ 𝐔₁, w⁻¹ * (j₀⁻¹ * w * j₀) = u := by
  obtain ⟨r, hr0, hr1⟩ := exists_ne_zero_ne (two_lt_card hh) (1 : K)
  obtain ⟨h1, h2⟩ := FullCenterTorus.one_add_ne_zero (Ne.symm hr1)
  obtain ⟨j, hj, hconj⟩ := exists_torus_elt (φ := φ) hr0 (one_ne_zero (α := K))
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨j, hj, fun z hz hzz => ?_, fun z hz => ?_, fun u hu => ?_⟩
  · obtain ⟨b, c, rfl⟩ := exists_zc hz
    rw [hconj] at hzz
    obtain ⟨hb, hc⟩ := zc_inj hzz
    have hb' : (1 + r) * b = 0 := by linear_combination hb + b * htwo
    have hc' : (1 + r ^ 2) * c = 0 := by linear_combination hc + c * htwo
    rw [(mul_eq_zero.mp hb').resolve_left h1, (mul_eq_zero.mp hc').resolve_left h2, zc_zero]
  · obtain ⟨b, c, rfl⟩ := exists_zc hz
    refine ⟨zc φ (b / (1 + r)) (c / (1 + r ^ 2)), zc_mem _ _, ?_⟩
    rw [hconj, zc_inv, zc_mul]
    congr 1
    · field_simp
    · field_simp
  · obtain ⟨b, rfl⟩ := exists_coordG_eq φ Axis.one hu
    refine ⟨zc φ (b / (1 + r)) 0, zc_mem_U_one.mpr rfl, ?_⟩
    rw [hconj, zc_inv, zc_mul, coordG_one_eq]
    congr 1
    · field_simp
    · ring

omit [Finite K] in
theorem kappa_delta (hh : HeisHyp L K n φ TG t) {j : G} (hj : j ∈ 𝐉) {x : G} (hx : x ∈ 𝐃₁) :
    t⁻¹ * ((x⁻¹ * (j⁻¹ * x * j))⁻¹ * t * (x⁻¹ * (j⁻¹ * x * j))) =
      (t⁻¹ * (x⁻¹ * t * x))⁻¹ * (j⁻¹ * (t⁻¹ * (x⁻¹ * t * x)) * j) := by
  rw [hh.mul₁ _ (inv_mem hx) _ (conj_torus_mem_D₁ hh hj hx), kappa_inv hh hx,
    kappa_conj (torus_comm_t hh hj)]

omit [Finite G] [Finite K] in
theorem delta_mem_ZP (hh : HeisHyp L K n φ TG t) {j : G} (hj : j ∈ 𝐉) {x : G}
    (hx : x ∈ zpowers t ⊔ 𝐙) : x⁻¹ * (j⁻¹ * x * j) ∈ 𝐙 := by
  have hS := hh.sec.two
  rcases (mem_zpowers_sup_iff hS.t_mul_t (TwoCoreSetup.comm_pull φ hS)).mp hx with h | h
  · exact mul_mem (inv_mem h) (conj_torus_mem_ZP hj h)
  · have hjt := torus_comm_t hh hj
    have e2 : x⁻¹ * (j⁻¹ * x * j) = (t * x)⁻¹ * (j⁻¹ * (t * x) * j) := by
      calc x⁻¹ * (j⁻¹ * x * j) = (t * x)⁻¹ * (t * j⁻¹) * x * j := by group
        _ = (t * x)⁻¹ * (j⁻¹ * t) * x * j := by
            rw [show t * j⁻¹ = j⁻¹ * t from ((Commute.inv_left hjt).eq).symm]
        _ = (t * x)⁻¹ * (j⁻¹ * (t * x) * j) := by group
    rw [e2]
    exact mul_mem (inv_mem h) (conj_torus_mem_ZP hj h)

section Complement

variable {j₀ : G}

set_option quotPrecheck false in
local notation "𝐌₀" => closure {x : G | ∃ d ∈ 𝐃, x = d⁻¹ * (j₀⁻¹ * d * j₀)}

theorem mem_M₀_iff (hh : HeisHyp L K n φ TG t) (hj : j₀ ∈ 𝐉)
    (hsZ : ∀ z ∈ 𝐙, ∃ w ∈ 𝐙, w⁻¹ * (j₀⁻¹ * w * j₀) = z) {x : G} :
    x ∈ 𝐌₀ ↔ ∃ d ∈ 𝐃, x = d⁻¹ * (j₀⁻¹ * d * j₀) := by
  refine ⟨fun hx => mem_of_mem_closure_delta le_rfl (ZP_le_D hh)
    (fun x hx z hz => comm_ZP_of_mem_D hh hx hz) (fun x hx y hy => ?_)
    (fun e he => conj_torus_mem_D hh hj he) hsZ hx, fun hx => subset_closure hx⟩
  have e : x⁻¹ * (y⁻¹ * x * y) = ⁅x⁻¹, y⁻¹⁆ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact U₁_le_ZP ((commutator_D hh).1.le (commutator_mem_commutator (inv_mem hx) (inv_mem hy)))

omit [Finite K] in
theorem M₀_le_D (hh : HeisHyp L K n φ TG t) (hj : j₀ ∈ 𝐉) : 𝐌₀ ≤ 𝐃 := by
  rw [closure_le]
  rintro _ ⟨d, hd, rfl⟩
  exact mul_mem (inv_mem hd) (conj_torus_mem_D hh hj hd)

omit [Finite G] in
theorem ZP_le_M₀ (hh : HeisHyp L K n φ TG t)
    (hsZ : ∀ z ∈ 𝐙, ∃ w ∈ 𝐙, w⁻¹ * (j₀⁻¹ * w * j₀) = z) : 𝐙 ≤ 𝐌₀ := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := hsZ z hz
  exact subset_closure ⟨w, ZP_le_D hh hw, rfl⟩

theorem conj_torus_mem_M₀ (hh : HeisHyp L K n φ TG t) (hj : j₀ ∈ 𝐉)
    (hsZ : ∀ z ∈ 𝐙, ∃ w ∈ 𝐙, w⁻¹ * (j₀⁻¹ * w * j₀) = z) {j : G} (hjJ : j ∈ 𝐉) {x : G}
    (hx : x ∈ 𝐌₀) : j⁻¹ * x * j ∈ 𝐌₀ := by
  obtain ⟨d, hd, rfl⟩ := (mem_M₀_iff hh hj hsZ).mp hx
  have e : j₀ * j = j * j₀ := torus_comm hj hjJ
  refine subset_closure ⟨j⁻¹ * d * j, conj_torus_mem_D hh hjJ hd, ?_⟩
  calc j⁻¹ * (d⁻¹ * (j₀⁻¹ * d * j₀)) * j = (j⁻¹ * d * j)⁻¹ * ((j₀ * j)⁻¹ * d * (j₀ * j)) := by
        group
    _ = (j⁻¹ * d * j)⁻¹ * (j₀⁻¹ * (j⁻¹ * d * j) * j₀) := by rw [e]; group

theorem torus_le_normalizer_M₀ (hh : HeisHyp L K n φ TG t) (hj : j₀ ∈ 𝐉)
    (hsZ : ∀ z ∈ 𝐙, ∃ w ∈ 𝐙, w⁻¹ * (j₀⁻¹ * w * j₀) = z) : 𝐉 ≤ normalizer (𝐌₀ : Set G) :=
  fun _ hjJ => mem_normalizer_of_conj_le fun x hx => by
    simpa using conj_torus_mem_M₀ hh hj hsZ (inv_mem hjJ) hx

theorem M₀_inf_C (hh : HeisHyp L K n φ TG t) (hj : j₀ ∈ 𝐉)
    (hfix : ∀ z ∈ 𝐙, j₀⁻¹ * z * j₀ = z → z = 1)
    (hsZ : ∀ z ∈ 𝐙, ∃ w ∈ 𝐙, w⁻¹ * (j₀⁻¹ * w * j₀) = z) : 𝐌₀ ⊓ 𝐂 = 𝐙 := by
  apply le_antisymm
  · rintro x ⟨hx, hxC⟩
    obtain ⟨d, hd, rfl⟩ := (mem_M₀_iff hh hj hsZ).mp hx
    have h1 := kappa_eq_one_iff.mpr hxC
    rw [kappa_delta hh hj hd.1, inv_mul_eq_one] at h1
    have h2 := hfix _ (U₁_le_ZP (hh.conj₁ d hd.1)) h1.symm
    have hdC : d ∈ 𝐂 := kappa_eq_one_iff.mp h2
    exact delta_mem_ZP hh hj ((D_inf_C hh).le ⟨hd, hdC⟩)
  · exact le_inf (ZP_le_M₀ hh hsZ) fun z hz => hh.sec.two.L_le (pull_le φ _ hz)

theorem t_not_mem_M₀ (hh : HeisHyp L K n φ TG t) (hj : j₀ ∈ 𝐉)
    (hfix : ∀ z ∈ 𝐙, j₀⁻¹ * z * j₀ = z → z = 1)
    (hsZ : ∀ z ∈ 𝐙, ∃ w ∈ 𝐙, w⁻¹ * (j₀⁻¹ * w * j₀) = z) : t ∉ 𝐌₀ := fun ht =>
  hh.sec.two.t_not_mem (pull_le φ _ ((M₀_inf_C hh hj hfix hsZ).le
    ⟨ht, mem_centralizer_singleton_iff.mpr rfl⟩))

theorem M₀_inf_tZ (hh : HeisHyp L K n φ TG t) (hj : j₀ ∈ 𝐉)
    (hfix : ∀ z ∈ 𝐙, j₀⁻¹ * z * j₀ = z → z = 1)
    (hsZ : ∀ z ∈ 𝐙, ∃ w ∈ 𝐙, w⁻¹ * (j₀⁻¹ * w * j₀) = z) : 𝐌₀ ⊓ (zpowers t ⊔ 𝐙) = 𝐙 := by
  refine le_antisymm (fun x hx => (M₀_inf_C hh hj hfix hsZ).le ⟨hx.1, ?_⟩)
    (le_inf (ZP_le_M₀ hh hsZ) le_sup_right)
  exact ((D_inf_C hh).ge hx.2).2

theorem M₀_inf_t (hh : HeisHyp L K n φ TG t) (hj : j₀ ∈ 𝐉)
    (hfix : ∀ z ∈ 𝐙, j₀⁻¹ * z * j₀ = z → z = 1)
    (hsZ : ∀ z ∈ 𝐙, ∃ w ∈ 𝐙, w⁻¹ * (j₀⁻¹ * w * j₀) = z) : 𝐌₀ ⊓ zpowers t = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxM, hxt⟩
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hxt
  rcases zpow_eq_one_or_eq hh.sec.two.t_mul_t j with h | h
  · rw [h]
    exact one_mem _
  · rw [h] at hxM
    exact absurd hxM (t_not_mem_M₀ hh hj hfix hsZ)

theorem exists_kappa_eq_M₀ (hh : HeisHyp L K n φ TG t) (hj : j₀ ∈ 𝐉)
    (hsZ : ∀ z ∈ 𝐙, ∃ w ∈ 𝐙, w⁻¹ * (j₀⁻¹ * w * j₀) = z)
    (hsU : ∀ u ∈ 𝐔₁, ∃ w ∈ 𝐔₁, w⁻¹ * (j₀⁻¹ * w * j₀) = u) {u : G} (hu : u ∈ 𝐔₁) :
    ∃ m ∈ 𝐌₀, t⁻¹ * (m⁻¹ * t * m) = u := by
  obtain ⟨w, hw, rfl⟩ := hsU u hu
  obtain ⟨d, hd, hdw⟩ := exists_kappa_eq_D hh hw
  refine ⟨d⁻¹ * (j₀⁻¹ * d * j₀), (mem_M₀_iff hh hj hsZ).mpr ⟨d, hd, rfl⟩, ?_⟩
  rw [kappa_delta hh hj hd.1, hdw]

theorem M₀_sup_t (hh : HeisHyp L K n φ TG t) (hj : j₀ ∈ 𝐉)
    (hsZ : ∀ z ∈ 𝐙, ∃ w ∈ 𝐙, w⁻¹ * (j₀⁻¹ * w * j₀) = z)
    (hsU : ∀ u ∈ 𝐔₁, ∃ w ∈ 𝐔₁, w⁻¹ * (j₀⁻¹ * w * j₀) = u) : 𝐌₀ ⊔ zpowers t = 𝐃 := by
  refine le_antisymm (sup_le (M₀_le_D hh hj) (zpowers_le.mpr (t_mem_D hh))) fun d hd => ?_
  obtain ⟨m, hm, hmd⟩ := exists_kappa_eq_M₀ hh hj hsZ hsU (hh.conj₁ d hd.1)
  have hmD := M₀_le_D hh hj hm
  have hmD₁ : m ∈ 𝐃₁ := (mem_inf.mp hmD).1
  have hdm : d * m⁻¹ ∈ 𝐂 := by
    rw [← kappa_eq_one_iff, hh.mul₁ _ (mem_inf.mp hd).1 _ (inv_mem hmD₁), kappa_inv hh hmD₁,
      hmd, mul_inv_cancel]
  have h1 : d * m⁻¹ ∈ zpowers t ⊔ 𝐙 := (D_inf_C hh).le (mem_inf.mpr ⟨mul_mem hd (inv_mem hmD), hdm⟩)
  have h2 : zpowers t ⊔ 𝐙 ≤ 𝐌₀ ⊔ zpowers t :=
    sup_le le_sup_right ((ZP_le_M₀ hh hsZ).trans le_sup_left)
  rw [show d = d * m⁻¹ * m by group]
  exact mul_mem (h2 h1) (mem_sup_left hm)

theorem card_M₀ (hh : HeisHyp L K n φ TG t) (hj : j₀ ∈ 𝐉)
    (hfix : ∀ z ∈ 𝐙, j₀⁻¹ * z * j₀ = z → z = 1)
    (hsZ : ∀ z ∈ 𝐙, ∃ w ∈ 𝐙, w⁻¹ * (j₀⁻¹ * w * j₀) = z)
    (hsU : ∀ u ∈ 𝐔₁, ∃ w ∈ 𝐔₁, w⁻¹ * (j₀⁻¹ * w * j₀) = u) : Nat.card 𝐌₀ = Nat.card K ^ 3 := by
  rw [card_eq_of_conj_surj (X := 𝐌₀) (U := 𝐔₁) (fun x hx => hh.conj₁ x (M₀_le_D hh hj hx).1)
    (fun u hu => exists_kappa_eq_M₀ hh hj hsZ hsU hu),
    show (𝐂 ⊓ 𝐌₀ : Subgroup G) = 𝐙 from (inf_comm _ _).trans (M₀_inf_C hh hj hfix hsZ),
    card_U, card_pull, (card_radicals (K := K)).2.2.2]
  ring

end Complement

theorem conj_mem_of_ZP_le (hh : HeisHyp L K n φ TG t) {M : Subgroup G} (hZM : 𝐙 ≤ M)
    {d : G} (hd : d ∈ 𝐃) {m : G} (hm : m ∈ M) (hmD : m ∈ 𝐃) : d * m * d⁻¹ ∈ M := by
  have h1 : ⁅d, m⁆ ∈ M :=
    hZM (U₁_le_ZP ((commutator_D hh).1.le (commutator_mem_commutator hd hmD)))
  rw [commutatorElement_def] at h1
  rw [show d * m * d⁻¹ = d * m * d⁻¹ * m⁻¹ * m by group]
  exact mul_mem h1 hm

theorem normal_of_ZP_le (hh : HeisHyp L K n φ TG t) {M : Subgroup G} (hZM : 𝐙 ≤ M)
    (hMD : M ≤ 𝐃) : (M.subgroupOf 𝐃).Normal :=
  ⟨fun _ hm d => mem_subgroupOf.mpr
    (conj_mem_of_ZP_le hh hZM d.2 (mem_subgroupOf.mp hm) (hMD (mem_subgroupOf.mp hm)))⟩

omit [Finite G] in
theorem exists_good_Ja (hh : HeisHyp L K n φ TG t) :
    ∃ a ∈ 𝐉ₐ, (∀ z ∈ 𝐙, a⁻¹ * z * a = z → z ∈ 𝐔₁) ∧
      ∀ u ∈ 𝐔₂, ∃ w ∈ 𝐔₂, w⁻¹ * (a⁻¹ * w * a) = u := by
  obtain ⟨r, hr0, hr1⟩ := exists_ne_zero_ne (two_lt_card hh) (1 : K)
  obtain ⟨-, h2⟩ := FullCenterTorus.one_add_ne_zero (Ne.symm hr1)
  obtain ⟨a, ha, hconj⟩ := exists_Ja_elt (φ := φ) hr0
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨a, ha, fun z hz hzz => ?_, fun u hu => ?_⟩
  · obtain ⟨b, c, rfl⟩ := exists_zc hz
    rw [hconj] at hzz
    have hc := (zc_inj hzz).2
    have hc' : (1 + r ^ 2) * c = 0 := by linear_combination hc + c * htwo
    rw [zc_mem_U_one]
    exact (mul_eq_zero.mp hc').resolve_left h2
  · obtain ⟨c, rfl⟩ := exists_coordG_eq φ Axis.two hu
    refine ⟨zc φ 0 (c / (1 + r ^ 2)), zc_mem_U_two.mpr rfl, ?_⟩
    rw [hconj, zc_inv, zc_mul, coordG_two_eq, add_zero]
    congr 1
    field_simp

omit [Finite G] in
theorem exists_good_Jb (hh : HeisHyp L K n φ TG t) :
    ∃ b ∈ 𝐉ᵦ, ∀ u ∈ 𝐔₁, b⁻¹ * u * b = u → u = 1 := by
  obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_ne (two_lt_card hh) (1 : K)
  obtain ⟨h1, -⟩ := FullCenterTorus.one_add_ne_zero (Ne.symm hs1)
  obtain ⟨b, hb, hconj⟩ := exists_Jb_elt (φ := φ) hs0
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨b, hb, fun u hu hub => ?_⟩
  obtain ⟨x, rfl⟩ := exists_coordG_eq φ Axis.one hu
  rw [coordG_one_eq, hconj] at hub
  have hx := (zc_inj hub).1
  have hx' : (1 + s) * x = 0 := by linear_combination hx + x * htwo
  rw [coordG_one_eq, (mul_eq_zero.mp hx').resolve_left h1, zc_zero]

omit [Finite G] [Finite K] in
theorem exists_coordEquiv :
    ∃ ι : Multiplicative K ≃* ↥𝐔₁, ∀ x : K,
      (ι (Multiplicative.ofAdd x) : G) = coordG φ Axis.one x := by
  let f : Multiplicative K →* ↥𝐔₁ :=
    { toFun := fun x => ⟨coordG φ Axis.one (Multiplicative.toAdd x), coordG_mem φ Axis.one _⟩
      map_one' := Subtype.ext (coordG_zero φ Axis.one)
      map_mul' := fun x y => Subtype.ext (by
        change coordG φ Axis.one (Multiplicative.toAdd x + Multiplicative.toAdd y) = _
        rw [coordG_add]
        rfl) }
  have hbij : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, fun u => ?_⟩
    · have h1 := congrArg (fun u : ↥𝐔₁ => (u : G)) hxy
      exact Multiplicative.toAdd.injective (coordG_injective φ Axis.one h1)
    · obtain ⟨x, hx⟩ := exists_coordG_eq φ Axis.one u.2
      exact ⟨Multiplicative.ofAdd x, Subtype.ext hx⟩
  exact ⟨MulEquiv.ofBijective f hbij, fun x => rfl⟩

omit [Finite G] in
theorem exists_torusHom :
    ∃ τ : Kˣ →* G, ∀ l : Kˣ, τ l ∈ 𝐉ᵦ ∧
      ∀ a : K, (τ l)⁻¹ * coordG φ Axis.one a * τ l = coordG φ Axis.one (l * a) := by
  obtain ⟨τX, hτX⟩ := exists_diagHom (K := K) 1 (MonoidHom.id Kˣ)
  have hδ : ∀ l : Kˣ, glMat (τX l : GL (Fin 4) K) = diagMat 1 (l : K) := fun l => by
    rw [hτX]
    simp
  refine ⟨(L.subtype.comp φ.symm.toMonoidHom).comp τX, fun l => ⟨?_, fun a => ?_⟩⟩
  · exact symm_mem_pull.mpr ⟨l, l.ne_zero, hδ l⟩
  · change ((φ.symm (τX l) : L) : G)⁻¹ * coordG φ Axis.one a * ((φ.symm (τX l) : L) : G) = _
    rw [coordG_one_eq, conj_zc one_ne_zero l.ne_zero (hδ l), coordG_one_eq, one_pow, mul_zero,
      one_mul]

omit [Finite G] in
theorem conj_coordG_diag {l : K} (hl : l ≠ 0) {δ : antiSp K}
    (hδ : glMat (δ : GL (Fin 4) K) = diagMat 1 l) (a : K) :
    ((φ.symm δ : L) : G)⁻¹ * coordG φ Axis.one a * ((φ.symm δ : L) : G) =
      coordG φ Axis.one (l * a) := by
  rw [coordG_one_eq, conj_zc one_ne_zero hl hδ, coordG_one_eq, one_pow, mul_zero, one_mul]

variable (φ t) in
structure CompHyp (M : Subgroup G) : Prop where
  le_D : M ≤ 𝐃
  torus : 𝐉 ≤ normalizer (M : Set G)
  ZP_le : 𝐙 ≤ M
  sup_t : M ⊔ zpowers t = 𝐃
  inf_tZ : M ⊓ (zpowers t ⊔ 𝐙) = 𝐙

namespace CompHyp

variable {M : Subgroup G}

set_option quotPrecheck false in
local notation "𝐇" => (M ⊓ centralizer (pull φ (axisTorus K Axis.one) : Set G) : Subgroup G)

theorem inf_C (hh : HeisHyp L K n φ TG t) (hM : CompHyp φ t M) : M ⊓ 𝐂 = 𝐙 := by
  refine le_antisymm (fun x hx => ?_) (le_inf hM.ZP_le fun z hz => hh.sec.two.L_le (pull_le φ _ hz))
  obtain ⟨hxM, hxC⟩ := mem_inf.mp hx
  rw [← hM.inf_tZ]
  exact mem_inf.mpr ⟨hxM, (D_inf_C hh).le (mem_inf.mpr ⟨hM.le_D hxM, hxC⟩)⟩

omit [Finite G] [Finite K] in
theorem conj_mem (hM : CompHyp φ t M) {j : G} (hj : j ∈ 𝐉) {m : G} (hm : m ∈ M) :
    j⁻¹ * m * j ∈ M := by
  simpa using (mem_normalizer_iff.mp (hM.torus (inv_mem hj)) m).mp hm

theorem t_mem_normalizer (hh : HeisHyp L K n φ TG t) (hM : CompHyp φ t M) :
    t ∈ normalizer (M : Set G) :=
  mem_normalizer_of_conj_le fun _ hm => conj_mem_of_ZP_le hh hM.ZP_le (t_mem_D hh) hm (hM.le_D hm)

theorem exists_kappa_eq (hh : HeisHyp L K n φ TG t) (hM : CompHyp φ t M) {u : G} (hu : u ∈ 𝐔₁) :
    ∃ m ∈ M, t⁻¹ * (m⁻¹ * t * m) = u := by
  obtain ⟨d, hd, hdu⟩ := exists_kappa_eq_D hh hu
  have hd' : d ∈ ((zpowers t : Subgroup G) : Set G) * (M : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ (zpowers_le.mpr (hM.t_mem_normalizer hh)),
      sup_comm, hM.sup_t]
    exact hd
  obtain ⟨c, hc, m, hm, rfl⟩ := hd'
  refine ⟨m, hm, ?_⟩
  have hcD₁ : c ∈ 𝐃₁ := (zpowers_le.mpr (t_mem_D₁ hh)) hc
  have hmD₁ : m ∈ 𝐃₁ := (mem_inf.mp (hM.le_D hm)).1
  have hcC : c ∈ 𝐂 := (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)) hc
  rw [← hdu, hh.mul₁ _ hcD₁ _ hmD₁, kappa_eq_one_iff.mpr hcC, one_mul]

theorem quotient (hh : HeisHyp L K n φ TG t) (hM : CompHyp φ t M) :
    ∃ _ : (𝐙.subgroupOf M).Normal, ∃ θ : (↥M ⧸ 𝐙.subgroupOf M) ≃* ↥𝐔₁,
      (∀ m : M, (θ m : G) = t⁻¹ * ((m : G)⁻¹ * t * m)) ∧
      ∀ j ∈ 𝐉, ∀ m : M, ∃ m' : M, (m' : G) = j⁻¹ * m * j ∧ (θ m' : G) = j⁻¹ * θ m * j := by
  have hn : (𝐙.subgroupOf M).Normal := ⟨fun z hz g => by
    rw [mem_subgroupOf] at hz ⊢
    rw [coe_mul, coe_mul, coe_inv, comm_ZP_of_mem_D hh (hM.le_D g.2) hz, mul_inv_cancel_right]
    exact hz⟩
  obtain ⟨θ, hθ⟩ := RootAxisTwoCore.exists_quotient_mulEquiv (D := M) (B := 𝐙) (U := 𝐔₁) (t := t)
    (fun d hd => hh.conj₁ d (mem_inf.mp (hM.le_D hd)).1)
    (fun d hd u hu => comm_ZP_of_mem_D hh (hM.le_D hd) (U₁_le_ZP hu))
    (fun u hu v hv => comm_ZP_of_mem_D hh (ZP_le_D hh (U₁_le_ZP hu)) (U₁_le_ZP hv))
    (fun d hd => by
      rw [conj_eq_iff]
      exact ⟨fun h => (hM.inf_C hh).le (mem_inf.mpr ⟨hd, h⟩),
        fun h => hh.sec.two.L_le (pull_le φ _ h)⟩)
    (fun u hu => hM.exists_kappa_eq hh hu)
  refine ⟨hn, θ, hθ, fun j hj m => ⟨⟨j⁻¹ * m * j, hM.conj_mem hj m.2⟩, rfl, ?_⟩⟩
  rw [hθ, hθ]
  exact kappa_conj (torus_comm_t hh hj) m

theorem mu_mem_ZP (hh : HeisHyp L K n φ TG t) (hM : CompHyp φ t M) {m : G} (hm : m ∈ M) {a : G}
    (ha : a ∈ 𝐉ₐ) : m⁻¹ * (a⁻¹ * m * a) ∈ 𝐙 := by
  have haJ : a ∈ 𝐉 := pull_mono φ (axisTorus_le Axis.one) ha
  have hmD₁ : m ∈ 𝐃₁ := (mem_inf.mp (hM.le_D hm)).1
  refine (hM.inf_C hh).le (mem_inf.mpr ⟨mul_mem (inv_mem hm) (hM.conj_mem haJ hm),
    kappa_eq_one_iff.mp ?_⟩)
  rw [kappa_delta hh haJ hmD₁, axisTorus_cent Axis.one ha (hh.conj₁ m hmD₁), inv_mul_cancel]

theorem mu_mem_U₂ (hh : HeisHyp L K n φ TG t) (hM : CompHyp φ t M) {m : G} (hm : m ∈ M) {a : G}
    (ha : a ∈ 𝐉ₐ) : m⁻¹ * (a⁻¹ * m * a) ∈ 𝐔₂ := by
  have haJ : a ∈ 𝐉 := pull_mono φ (axisTorus_le Axis.one) ha
  exact mem_of_telescope (Z := 𝐙) (U := 𝐔₂) (fun _ hz => Setup.ZP_mul_self hz)
    (odd_card_sub_one hh) (torus_pow_card_sub_one haJ) (fun _ hz => conj_torus_mem_ZP haJ hz)
    (fun _ hz => axisTorus_mod Axis.one ha hz) (hM.mu_mem_ZP hh hm ha)

omit [Finite G] in
theorem U₁_le_H (hM : CompHyp φ t M) : 𝐔₁ ≤ 𝐇 := fun u hu =>
  mem_inf.mpr ⟨hM.ZP_le (U₁_le_ZP hu), mem_centralizer_iff.mpr fun b hb => by
    have h := axisTorus_cent Axis.one hb hu
    calc b * u = b * (b⁻¹ * u * b) := by rw [h]
      _ = u * b := by group⟩

theorem mem_H_of_fix (hh : HeisHyp L K n φ TG t) (hM : CompHyp φ t M) {a : G} (ha : a ∈ 𝐉ₐ)
    (hfix : ∀ z ∈ 𝐙, a⁻¹ * z * a = z → z ∈ 𝐔₁) {m : G} (hm : m ∈ M) (hma : a⁻¹ * m * a = m) :
    m ∈ 𝐇 := by
  refine mem_inf.mpr ⟨hm, mem_centralizer_iff.mpr fun b hb => ?_⟩
  have hab : a * b = b * a := torus_comm (pull_mono φ (axisTorus_le Axis.one) ha)
    (pull_mono φ (axisTorus_le Axis.one) hb)
  have hν := hM.mu_mem_U₂ hh hm hb
  have hba : a⁻¹ * b * a = b := by rw [mul_assoc, ← hab, inv_mul_cancel_left]
  have hνa : a⁻¹ * (m⁻¹ * (b⁻¹ * m * b)) * a = m⁻¹ * (b⁻¹ * m * b) := by
    calc a⁻¹ * (m⁻¹ * (b⁻¹ * m * b)) * a =
        (a⁻¹ * m * a)⁻¹ * ((a⁻¹ * b * a)⁻¹ * (a⁻¹ * m * a) * (a⁻¹ * b * a)) := by group
      _ = _ := by rw [hma, hba]
  have h1 : m⁻¹ * (b⁻¹ * m * b) ∈ 𝐔₁ ⊓ 𝐔₂ := mem_inf.mpr ⟨hfix _ (U₂_le_ZP hν) hνa, hν⟩
  rw [U_inf_U, mem_bot] at h1
  have h2 : b⁻¹ * m * b = m := by
    calc b⁻¹ * m * b = m * (m⁻¹ * (b⁻¹ * m * b)) := by group
      _ = m := by rw [h1, mul_one]
  calc b * m = b * (b⁻¹ * m * b) := by rw [h2]
    _ = m * b := by group

theorem H_mul_U₂ (hh : HeisHyp L K n φ TG t) (hM : CompHyp φ t M) :
    (𝐇 : Set G) * (𝐔₂ : Set G) = M := by
  obtain ⟨a, ha, hfix, hsurj⟩ := exists_good_Ja hh
  ext m
  constructor
  · rintro ⟨h, hH, u, hu, rfl⟩
    exact mul_mem (mem_inf.mp hH).1 (hM.ZP_le (U₂_le_ZP hu))
  · intro hm
    have hμ := hM.mu_mem_U₂ hh hm ha
    obtain ⟨w, hw, hwμ⟩ := hsurj _ (inv_mem hμ)
    have hwZ := U₂_le_ZP hw
    have hcomm : m⁻¹ * (a⁻¹ * m * a) * w = w * (m⁻¹ * (a⁻¹ * m * a)) :=
      comm_ZP_of_mem_D hh (ZP_le_D hh (U₂_le_ZP hμ)) hwZ
    have e1 : a⁻¹ * w * a = w * (m⁻¹ * (a⁻¹ * m * a))⁻¹ := by
      rw [← hwμ]
      group
    have hmw : a⁻¹ * (m * w) * a = m * w := by
      calc a⁻¹ * (m * w) * a = (a⁻¹ * m * a) * (a⁻¹ * w * a) := by group
        _ = m * (m⁻¹ * (a⁻¹ * m * a)) * (w * (m⁻¹ * (a⁻¹ * m * a))⁻¹) := by rw [e1]; group
        _ = m * (m⁻¹ * (a⁻¹ * m * a) * w) * (m⁻¹ * (a⁻¹ * m * a))⁻¹ := by group
        _ = m * (w * (m⁻¹ * (a⁻¹ * m * a))) * (m⁻¹ * (a⁻¹ * m * a))⁻¹ := by rw [hcomm]
        _ = m * w := by group
    exact ⟨m * w, hM.mem_H_of_fix hh ha hfix (mul_mem hm (hM.ZP_le hwZ)) hmw, w⁻¹, inv_mem hw,
      by group⟩

omit [Finite G] in
theorem H_inf_ZP (hh : HeisHyp L K n φ TG t) (hM : CompHyp φ t M) : 𝐇 ⊓ 𝐙 = 𝐔₁ := by
  obtain ⟨a, ha, hfix, -⟩ := exists_good_Ja hh
  apply le_antisymm
  · intro x hx
    obtain ⟨hxH, hxZ⟩ := mem_inf.mp hx
    refine hfix x hxZ ?_
    rw [mul_assoc, ← mem_centralizer_iff.mp (mem_inf.mp hxH).2 a ha, inv_mul_cancel_left]
  · exact le_inf hM.U₁_le_H U₁_le_ZP

omit [Finite G] in
theorem H_inf_U₂ (hh : HeisHyp L K n φ TG t) (hM : CompHyp φ t M) : 𝐇 ⊓ 𝐔₂ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxH, hxU⟩ := mem_inf.mp hx
  have h1 : x ∈ 𝐔₁ ⊓ 𝐔₂ :=
    mem_inf.mpr ⟨(hM.H_inf_ZP hh).le (mem_inf.mpr ⟨hxH, U₂_le_ZP hxU⟩), hxU⟩
  rwa [U_inf_U] at h1

theorem H_inf_C (hh : HeisHyp L K n φ TG t) (hM : CompHyp φ t M) : 𝐇 ⊓ 𝐂 = 𝐔₁ := by
  rw [← hM.H_inf_ZP hh]
  apply le_antisymm
  · intro x hx
    obtain ⟨hxH, hxC⟩ := mem_inf.mp hx
    exact mem_inf.mpr ⟨hxH, (hM.inf_C hh).le (mem_inf.mpr ⟨(mem_inf.mp hxH).1, hxC⟩)⟩
  · intro x hx
    obtain ⟨hxH, hxZ⟩ := mem_inf.mp hx
    exact mem_inf.mpr ⟨hxH, hh.sec.two.L_le (pull_le φ _ hxZ)⟩

omit [Finite G] [Finite K] in
theorem conj_torus_mem_H (hM : CompHyp φ t M) {j : G} (hj : j ∈ 𝐉) {h : G} (hH : h ∈ 𝐇) :
    j⁻¹ * h * j ∈ 𝐇 := by
  obtain ⟨hm, hc⟩ := mem_inf.mp hH
  refine mem_inf.mpr ⟨hM.conj_mem hj hm, mem_centralizer_iff.mpr fun b hb => ?_⟩
  have hbj : Commute b j := (torus_comm hj (pull_mono φ (axisTorus_le Axis.one) hb)).symm
  have hbh : Commute b h := mem_centralizer_iff.mp hc b hb
  exact ((hbj.inv_right.mul_right hbh).mul_right hbj).eq

theorem t_mem_normalizer_H (hh : HeisHyp L K n φ TG t) (hM : CompHyp φ t M) :
    t ∈ normalizer (𝐇 : Set G) := by
  refine mem_normalizer_of_conj_le fun h hH => ?_
  obtain ⟨hm, hc⟩ := mem_inf.mp hH
  refine mem_inf.mpr ⟨conj_mem_of_ZP_le hh hM.ZP_le (t_mem_D hh) hm (hM.le_D hm),
    mem_centralizer_iff.mpr fun b hb => ?_⟩
  have hbt : Commute b t := (hh.sec.two.comm (pull_le φ _ hb)).symm
  have hbh : Commute b h := mem_centralizer_iff.mp hc b hb
  exact ((hbt.mul_right hbh).mul_right hbt.inv_right).eq

theorem kappa_H (hh : HeisHyp L K n φ TG t) (hM : CompHyp φ t M) :
    {x : G | ∃ h ∈ 𝐇, x = t⁻¹ * (h⁻¹ * t * h)} = 𝐔₁ := by
  ext x
  constructor
  · rintro ⟨h, hH, rfl⟩
    exact hh.conj₁ h (mem_inf.mp (hM.le_D (mem_inf.mp hH).1)).1
  · intro hx
    obtain ⟨m, hm, hmx⟩ := hM.exists_kappa_eq hh hx
    rw [← SetLike.mem_coe, ← hM.H_mul_U₂ hh] at hm
    obtain ⟨h, hH, u, hu, rfl⟩ := hm
    refine ⟨h, hH, ?_⟩
    have hhD₁ : h ∈ 𝐃₁ := (mem_inf.mp (hM.le_D (mem_inf.mp hH).1)).1
    have huD₁ : u ∈ 𝐃₁ := A₁_le_D₁ hh (ZP_le_A₁ (U₂_le_ZP hu))
    rw [← hmx, hh.mul₁ _ hhD₁ _ huD₁,
      kappa_eq_one_iff.mpr (hh.sec.two.L_le (pull_le φ _ hu)), mul_one]

theorem quotient_H (hh : HeisHyp L K n φ TG t) (hM : CompHyp φ t M) :
    ∃ _ : (𝐔₁.subgroupOf 𝐇).Normal, ∃ θ : (↥𝐇 ⧸ 𝐔₁.subgroupOf 𝐇) ≃* ↥𝐔₁,
      ∀ h : 𝐇, (θ h : G) = t⁻¹ * ((h : G)⁻¹ * t * h) := by
  have hHD : 𝐇 ≤ 𝐃 := fun _ hx => hM.le_D (mem_inf.mp hx).1
  have hn : (𝐔₁.subgroupOf 𝐇).Normal := ⟨fun z hz g => by
    rw [mem_subgroupOf] at hz ⊢
    rw [coe_mul, coe_mul, coe_inv, comm_ZP_of_mem_D hh (hHD g.2) (U₁_le_ZP hz),
      mul_inv_cancel_right]
    exact hz⟩
  obtain ⟨θ, hθ⟩ := RootAxisTwoCore.exists_quotient_mulEquiv (D := 𝐇) (B := 𝐔₁) (U := 𝐔₁)
    (t := t) (fun d hd => hh.conj₁ d (mem_inf.mp (hHD hd)).1)
    (fun d hd u hu => comm_ZP_of_mem_D hh (hHD hd) (U₁_le_ZP hu))
    (fun u hu v hv => comm_ZP_of_mem_D hh (ZP_le_D hh (U₁_le_ZP hu)) (U₁_le_ZP hv))
    (fun d hd => by
      rw [conj_eq_iff]
      exact ⟨fun h => (hM.H_inf_C hh).le (mem_inf.mpr ⟨hd, h⟩),
        fun h => hh.sec.two.L_le (pull_le φ _ (U₁_le_ZP h))⟩)
    (fun u hu => by
      have hu' : u ∈ ({x : G | ∃ h ∈ 𝐇, x = t⁻¹ * (h⁻¹ * t * h)} : Set G) := by
        rw [hM.kappa_H hh]
        exact hu
      obtain ⟨h, hH, rfl⟩ := hu'
      exact ⟨h, hH, rfl⟩)
  exact ⟨hn, θ, hθ⟩

theorem inf_Jb (hh : HeisHyp L K n φ TG t) (hM : CompHyp φ t M) :
    M ⊓ centralizer (𝐉ᵦ : Set G) = 𝐔₂ := by
  obtain ⟨b, hb, hfixb⟩ := exists_good_Jb hh
  have hbJ := pull_mono φ (axisTorus_le Axis.two) hb
  apply le_antisymm
  · intro x hx
    obtain ⟨hxM, hxc⟩ := mem_inf.mp hx
    rw [← SetLike.mem_coe, ← hM.H_mul_U₂ hh] at hxM
    obtain ⟨h, hH, u, hu, rfl⟩ := hxM
    have hbx : b * (h * u) = h * u * b := mem_centralizer_iff.mp hxc b hb
    have hbu : b⁻¹ * u * b = u := axisTorus_cent Axis.two hb hu
    have hbx' : b⁻¹ * (h * u) * b = h * u := by
      rw [mul_assoc, ← hbx, inv_mul_cancel_left]
    have hbh : b⁻¹ * h * b = h := by
      calc b⁻¹ * h * b = (b⁻¹ * (h * u) * b) * (b⁻¹ * u * b)⁻¹ := by group
        _ = h := by rw [hbx', hbu]; group
    have hhD₁ : h ∈ 𝐃₁ := (mem_inf.mp (hM.le_D (mem_inf.mp hH).1)).1
    have hk : b⁻¹ * (t⁻¹ * (h⁻¹ * t * h)) * b = t⁻¹ * (h⁻¹ * t * h) := by
      rw [← kappa_conj (torus_comm_t hh hbJ), hbh]
    have hhU : h ∈ 𝐔₁ := (hM.H_inf_C hh).le (mem_inf.mpr ⟨hH,
      kappa_eq_one_iff.mp (hfixb _ (hh.conj₁ h hhD₁) hk)⟩)
    obtain rfl : h = 1 := hfixb h hhU hbh
    simpa using hu
  · intro u hu
    refine mem_inf.mpr ⟨hM.ZP_le (U₂_le_ZP hu), mem_centralizer_iff.mpr fun c hc => ?_⟩
    have h := axisTorus_cent Axis.two hc hu
    calc c * u = c * (c⁻¹ * u * c) := by rw [h]
      _ = u * c := by group

theorem exists_alpha_beta (hh : HeisHyp L K n φ TG t) (hM : CompHyp φ t M) :
    ∃ α : ↥𝐔₁ ≃* Multiplicative K, (∀ (u : ↥𝐔₁) (c : K),
        Multiplicative.toAdd (α u) = c ↔ (u : G) = coordG φ Axis.one c) ∧
      ∃ _ : (𝐔₁.subgroupOf 𝐇).Normal, ∃ β : (↥𝐇 ⧸ 𝐔₁.subgroupOf 𝐇) ≃* Multiplicative K,
        ∀ (h : ↥𝐇) (c : K), Multiplicative.toAdd (β h) = c ↔
          t⁻¹ * ((h : G)⁻¹ * t * h) = coordG φ Axis.one c := by
  obtain ⟨hn, θq, hθq⟩ := hM.quotient_H hh
  obtain ⟨ι, hι⟩ := exists_coordEquiv (φ := φ)
  have hcoord : ∀ (u : ↥𝐔₁) (c : K),
      Multiplicative.toAdd (ι.symm u) = c ↔ (u : G) = coordG φ Axis.one c := by
    intro u c
    rw [← hι c, Subtype.coe_inj, ← MulEquiv.symm_apply_eq]
    exact ⟨fun e => by rw [← e]; rfl, fun e => by rw [e]; rfl⟩
  refine ⟨ι.symm, hcoord, hn, θq.trans ι.symm, fun h c => ?_⟩
  rw [← hθq h]
  exact hcoord _ c

theorem square_map (hh : HeisHyp L K n φ TG t) (hM : CompHyp φ t M) :
    (∀ x ∈ 𝐇, ∀ y ∈ 𝐇, x * y = y * x) ∧ Nat.card 𝐇 = (2 ^ n) ^ 2 ∧
    ∃ c : K, (∀ h ∈ 𝐇, ∀ b : K, t⁻¹ * (h⁻¹ * t * h) = coordG φ Axis.one b →
        h * h = coordG φ Axis.one (c * b)) ∧
      (∀ c' : K, (∀ h ∈ 𝐇, ∀ b : K, t⁻¹ * (h⁻¹ * t * h) = coordG φ Axis.one b →
        h * h = coordG φ Axis.one (c' * b)) → c' = c) ∧
      (c = 0 → IsElementaryAbelian 2 𝐇 ∧ Group.rank 𝐇 = 2 * n) ∧
      (c ≠ 0 → closure {x : G | ∃ y ∈ 𝐇, x = y * y} = 𝐔₁ ∧
        closure {x : G | x ∈ 𝐇 ∧ x * x = 1} = 𝐔₁ ∧ {x : G | x ∈ 𝐇 ∧ x * x = 1} = 𝐔₁ ∧
        Nonempty (Multiplicative (Fin n → ZMod 4) ≃* 𝐇)) := by
  obtain ⟨α, hαc, hn, β, hβc⟩ := hM.exists_alpha_beta hh
  obtain ⟨τ, hτ⟩ := exists_torusHom (φ := φ)
  have hτJ : ∀ l, τ l ∈ 𝐉 := fun l => pull_mono φ (axisTorus_le Axis.two) (hτ l).1
  let A' : Subgroup ↥𝐇 := 𝐔₁.subgroupOf 𝐇
  have : A'.Normal := hn
  have hAZ : A' ≤ center ↥𝐇 := fun a ha => mem_center_iff.mpr fun g => Subtype.ext
    (comm_ZP_of_mem_D hh (hM.le_D (mem_inf.mp g.2).1) (U₁_le_ZP (mem_subgroupOf.mp ha)))
  let α' : A' ≃* Multiplicative K := (subgroupOfEquivOfLe hM.U₁_le_H).trans α
  have hαc' : ∀ (a : A') (c : K), Multiplicative.toAdd (α' a) = c ↔
      ((a : ↥𝐇) : G) = coordG φ Axis.one c := fun a c => hαc _ c
  let θ' : Kˣ →* MulAut ↥𝐇 :=
    { toFun := fun l =>
        { toFun := fun w => ⟨(τ l)⁻¹ * w * τ l, hM.conj_torus_mem_H (hτJ l) w.2⟩
          invFun := fun w => ⟨τ l * w * (τ l)⁻¹, by
            simpa using hM.conj_torus_mem_H (inv_mem (hτJ l)) w.2⟩
          left_inv := fun w => Subtype.ext (by simp only; group)
          right_inv := fun w => Subtype.ext (by simp only; group)
          map_mul' := fun w w' => Subtype.ext (by simp only [coe_mul]; group) }
      map_one' := MulEquiv.ext fun w => Subtype.ext (by simp)
      map_mul' := fun l l' => MulEquiv.ext fun w => Subtype.ext (by
        change (τ (l * l'))⁻¹ * w * τ (l * l') = (τ l)⁻¹ * ((τ l')⁻¹ * w * τ l') * τ l
        rw [map_mul, torus_comm (hτJ l) (hτJ l')]
        group) }
  have hθ' : ∀ (l : Kˣ) (w : ↥𝐇), ((θ' l w : ↥𝐇) : G) = (τ l)⁻¹ * w * τ l := fun _ _ => rfl
  have hα : ∀ (l : Kˣ) (a a' : A'), (a' : ↥𝐇) = θ' l a →
      Multiplicative.toAdd (α' a') = l * Multiplicative.toAdd (α' a) := by
    intro l a a' ha'
    rw [hαc', ha', hθ', (hαc' a _).mp rfl, (hτ l).2]
  have hβ : ∀ (l : Kˣ) (w : ↥𝐇),
      Multiplicative.toAdd (β (θ' l w : ↥𝐇 ⧸ A')) = l * Multiplicative.toAdd (β w) := by
    intro l w
    rw [hβc, hθ', kappa_conj (torus_comm_t hh (hτJ l)), (hβc w _).mp rfl, (hτ l).2]
  obtain ⟨hcomm, hcard, hsq, c, hform, huniq, h0, hne⟩ :=
    SteinbergCD.scalar_equivariant_central_two_extension_square_map n K hh.sec.two.card_K ↥𝐇 A'
      hAZ α' β θ' hα hβ
  have hsqG : ∀ w : ↥𝐇, ((w ^ 2 : ↥𝐇) : G) = (w : G) * w := fun w => by
    rw [SubgroupClass.coe_pow, pow_two]
  refine ⟨fun x hx y hy => congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩), hcard, c, ?_, ?_, ?_,
    ?_⟩
  · intro w hw a hκ
    have h1 := hform ⟨w, hw⟩ ⟨_, hsq ⟨w, hw⟩⟩ rfl
    rw [(hβc ⟨w, hw⟩ a).mpr hκ, hαc'] at h1
    rw [← h1]
    exact (hsqG ⟨w, hw⟩).symm
  · intro lam' hlam'
    refine huniq lam' fun g a ha => ?_
    have h1 := hlam' g g.2 _ ((hβc g _).mp rfl)
    rw [hαc', ha, hsqG]
    exact h1
  · intro hc0
    have hE := h0 hc0
    refine ⟨hE, ?_⟩
    have h2 : ∀ x ∈ 𝐇, x * x = 1 := fun x hx => by
      rw [← pow_two]
      exact elemPow_eq_one_of_isElementaryAbelian x hx
    have h3 := CFSG.LocalAnalysis.SymplecticFourRankThompson.two_pow_rank_eq_card_of_elementary
      𝐇 h2
    rw [hcard, ← pow_mul, mul_comm] at h3
    exact Nat.pow_right_injective le_rfl h3
  · intro hc0
    obtain ⟨hcl, hom, -, -, φ', -⟩ := hne hc0
    have hU : 𝐔₁ ≤ 𝐇 := hM.U₁_le_H
    have hset : {x : G | x ∈ 𝐇 ∧ x * x = 1} = 𝐔₁ := by
      ext x
      constructor
      · rintro ⟨hxW, hx1⟩
        have hmem : (⟨x, hxW⟩ : ↥𝐇) ∈ {g : ↥𝐇 | g ^ 2 = 1} :=
          Subtype.ext (by rw [hsqG]; exact hx1)
        rw [hom] at hmem
        exact mem_subgroupOf.mp hmem
      · intro hxU
        have hmem : (⟨x, hU hxU⟩ : ↥𝐇) ∈ (A' : Set ↥𝐇) := mem_subgroupOf.mpr hxU
        rw [← hom] at hmem
        refine ⟨hU hxU, ?_⟩
        have := congrArg Subtype.val (hmem : (⟨x, hU hxU⟩ : ↥𝐇) ^ 2 = 1)
        rwa [hsqG] at this
    refine ⟨?_, by rw [hset]; exact closure_eq _, hset, ⟨φ'⟩⟩
    have h1 := congrArg (Subgroup.map 𝐇.subtype) hcl
    rw [MonoidHom.map_closure, subgroupOf_map_subtype, inf_of_le_left hU] at h1
    rw [← h1]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩ ^ 2, ⟨⟨y, hy⟩, rfl⟩, hsqG ⟨y, hy⟩⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, g.2, hsqG g⟩

theorem H_le_closure (hh : HeisHyp L K n φ TG t) (hM : CompHyp φ t M) :
    𝐇 ≤ closure {x : G | ∃ g ∈ centralizer (𝐉ₐ : Set G), ∃ y ∈ 𝐉ᵦ, x = g⁻¹ * y * g} := by
  obtain ⟨b, hb, hfixb⟩ := exists_good_Jb hh
  have hbJ := pull_mono φ (axisTorus_le Axis.two) hb
  have hfpf : ∀ x ∈ 𝐇, b⁻¹ * x * b = x → x = 1 := by
    intro x hx hxb
    have hxD₁ : x ∈ 𝐃₁ := (mem_inf.mp (hM.le_D (mem_inf.mp hx).1)).1
    have hk : b⁻¹ * (t⁻¹ * (x⁻¹ * t * x)) * b = t⁻¹ * (x⁻¹ * t * x) := by
      rw [← kappa_conj (torus_comm_t hh hbJ), hxb]
    have hxU : x ∈ 𝐔₁ := (hM.H_inf_C hh).le (mem_inf.mpr ⟨hx,
      kappa_eq_one_iff.mp (hfixb _ (hh.conj₁ x hxD₁) hk)⟩)
    exact hfixb x hxU hxb
  let f : ↥𝐇 → ↥𝐇 := fun x =>
    ⟨(x : G)⁻¹ * (b⁻¹ * x * b), mul_mem (inv_mem x.2) (hM.conj_torus_mem_H hbJ x.2)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have e : (x : G)⁻¹ * (b⁻¹ * x * b) = (y : G)⁻¹ * (b⁻¹ * y * b) :=
      congrArg (fun u : ↥𝐇 => (u : G)) hxy
    have e1 : (y : G) * ((x : G)⁻¹ * (b⁻¹ * x * b)) = b⁻¹ * y * b := by rw [e]; group
    have hfix' : b⁻¹ * ((y : G) * (x : G)⁻¹) * b = (y : G) * (x : G)⁻¹ := by
      calc b⁻¹ * ((y : G) * (x : G)⁻¹) * b = (b⁻¹ * y * b) * (b⁻¹ * x * b)⁻¹ := by group
        _ = (y : G) * ((x : G)⁻¹ * (b⁻¹ * x * b)) * (b⁻¹ * x * b)⁻¹ := by rw [e1]
        _ = (y : G) * (x : G)⁻¹ := by group
    have h1 := hfpf _ (mul_mem y.2 (inv_mem x.2)) hfix'
    exact Subtype.ext (mul_inv_eq_one.mp h1).symm
  intro w hw
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨w, hw⟩
  have hx' : (x : G)⁻¹ * (b⁻¹ * x * b) = w := congrArg Subtype.val hx
  have e : w = ((x : G)⁻¹ * b⁻¹ * x) * b := by
    rw [← hx']
    group
  rw [e]
  exact mul_mem (subset_closure ⟨x, (mem_inf.mp x.2).2, b⁻¹, inv_mem hb, rfl⟩)
    (subset_closure ⟨1, one_mem _, b, hb, by group⟩)

end CompHyp

theorem main (hh : HeisHyp L K n φ TG t) (ZP : Subgroup G)
    (hZP : ZP = pull φ (antiUnipotentCenter K)) :
    let C := centralizer ({t} : Set G)
    let U₁ := pull φ (rootU K Axis.one)
    let U₂ := pull φ (rootU K Axis.two)
    let A₁ := pull φ (rootA K Axis.one)
    let A₂ := pull φ (rootA K Axis.two)
    let B₁ := zpowers t ⊔ A₁
    let B₂ := zpowers t ⊔ A₂
    let N₁ := normalizer (B₁ : Set G)
    let N₂ := normalizer (B₂ : Set G)
    let D₁ := (CFSG.pCore 2 N₁).map N₁.subtype
    let D₂ := (CFSG.pCore 2 N₂).map N₂.subtype
    let D := D₁ ⊓ D₂
    let J₀ := pull φ (diagTorus K)
    let Ja := pull φ (axisTorus K Axis.one)
    let Jb := pull φ (axisTorus K Axis.two)
    let Z₁ : K → G := fun b => ((φ.symm (uElt 0 b 0 0) : L) : G)
    let IsComp : Subgroup G → Prop := fun M => M ≤ D ∧ J₀ ≤ normalizer (M : Set G) ∧
      Nat.card M = (2 ^ n) ^ 3 ∧ ZP ≤ M ∧ (M.subgroupOf D).Normal ∧ M ⊓ zpowers t = ⊥ ∧
      M ⊔ zpowers t = D ∧ M ⊓ (zpowers t ⊔ ZP) = ZP
    ((B₁ : Set G) * (D : Set G) = D₁ ∧ (A₁ : Set G) * (D : Set G) = D₁) ∧
      Nat.card D = 2 * (2 ^ n) ^ 3 ∧
      ⁅D, D⁆ = U₁ ∧ closure {x : G | ∃ y ∈ D, x = y * y} = U₁ ∧
      (center D).map D.subtype = ZP ∧
      (∃ M : Subgroup G, IsComp M) ∧
      ∀ M : Subgroup G, IsComp M →
        let H := M ⊓ centralizer (Ja : Set G)
        (H ⊓ U₂ = ⊥ ∧ (∀ x ∈ H, ∀ y ∈ U₂, x * y = y * x) ∧ (H : Set G) * (U₂ : Set G) = M) ∧
        M ⊓ centralizer (Jb : Set G) = U₂ ∧
        (∀ x ∈ H, ∀ y ∈ H, x * y = y * x) ∧ Nat.card H = (2 ^ n) ^ 2 ∧
        (t ∈ normalizer (H : Set G) ∧ H ⊓ C = U₁ ∧
          {x : G | ∃ h ∈ H, x = t⁻¹ * (h⁻¹ * t * h)} = U₁) ∧
        (∃ _ : (ZP.subgroupOf M).Normal, ∃ θ : (↥M ⧸ ZP.subgroupOf M) ≃* ↥U₁,
          (∀ m : M, (θ m : G) = t⁻¹ * ((m : G)⁻¹ * t * m)) ∧
          ∀ j ∈ J₀, ∀ m : M, ∃ m' : M, (m' : G) = j⁻¹ * m * j ∧ (θ m' : G) = j⁻¹ * θ m * j) ∧
        (∃ α : ↥U₁ ≃* Multiplicative K,
          (∀ (u : ↥U₁) (b : K), (u : G) = Z₁ b → Multiplicative.toAdd (α u) = b) ∧
          ∃ _ : (U₁.subgroupOf H).Normal, ∃ β : (↥H ⧸ U₁.subgroupOf H) ≃* Multiplicative K,
            (∀ (h : ↥H) (u : ↥U₁), (u : G) = t⁻¹ * ((h : G)⁻¹ * t * h) → β h = α u) ∧
            ∀ (l : K) (δ : antiSp K), l ≠ 0 → glMat (δ : GL (Fin 4) K) = diagMat 1 l →
              (∀ u : ↥U₁, ∃ u' : ↥U₁,
                (u' : G) = ((φ.symm δ : L) : G)⁻¹ * u * ((φ.symm δ : L) : G) ∧
                Multiplicative.toAdd (α u') = l * Multiplicative.toAdd (α u)) ∧
              (∀ h : ↥H, ∃ h' : ↥H,
                (h' : G) = ((φ.symm δ : L) : G)⁻¹ * h * ((φ.symm δ : L) : G) ∧
                Multiplicative.toAdd (β h') = l * Multiplicative.toAdd (β h))) ∧
        (∃ c : K,
          (∀ h ∈ H, ∀ b : K, t⁻¹ * (h⁻¹ * t * h) = Z₁ b → h * h = Z₁ (c * b)) ∧
          (∀ c' : K, (∀ h ∈ H, ∀ b : K, t⁻¹ * (h⁻¹ * t * h) = Z₁ b →
            h * h = Z₁ (c' * b)) → c' = c) ∧
          (c = 0 → IsElementaryAbelian 2 H ∧ Group.rank H = 2 * n) ∧
          (c ≠ 0 → closure {x : G | ∃ y ∈ H, x = y * y} = U₁ ∧
            closure {x : G | x ∈ H ∧ x * x = 1} = U₁ ∧ {x : G | x ∈ H ∧ x * x = 1} = U₁ ∧
            Nonempty (Multiplicative (Fin n → ZMod 4) ≃* H))) ∧
        H ≤ closure {x : G | ∃ g ∈ centralizer (Ja : Set G), ∃ y ∈ Jb, x = g⁻¹ * y * g} := by
  subst hZP
  intro C U₁ U₂ A₁ A₂ B₁ B₂ N₁ N₂ D₁ D₂ D J₀ Ja Jb Z₁ IsComp
  have hK := hh.sec.two.card_K
  refine ⟨⟨B₁_mul_D hh, A₁_mul_D hh⟩, (card_D hh).trans (by rw [hK]), (commutator_D hh).1,
    (commutator_D hh).2, center_D hh, ?_, fun M hM => ?_⟩
  · obtain ⟨j₀, hj, hfix, hsZ, hsU⟩ := exists_good hh
    exact ⟨_, M₀_le_D hh hj, torus_le_normalizer_M₀ hh hj hsZ,
      (card_M₀ hh hj hfix hsZ hsU).trans (by rw [hK]), ZP_le_M₀ hh hsZ,
      normal_of_ZP_le hh (ZP_le_M₀ hh hsZ) (M₀_le_D hh hj), M₀_inf_t hh hj hfix hsZ,
      M₀_sup_t hh hj hsZ hsU, M₀_inf_tZ hh hj hfix hsZ⟩
  · obtain ⟨hMD, hMJ, -, hZM, -, -, hMt, hMZ⟩ := hM
    have hC : CompHyp φ t M := ⟨hMD, hMJ, hZM, hMt, hMZ⟩
    intro H
    obtain ⟨hcomm, hcard, c, hc1, hc2, hc3, hc4⟩ := hC.square_map hh
    obtain ⟨α, hαc, hn, β, hβc⟩ := hC.exists_alpha_beta hh
    refine ⟨⟨hC.H_inf_U₂ hh, fun x hx y hy =>
      comm_ZP_of_mem_D hh (hMD (mem_inf.mp hx).1) (U₂_le_ZP hy), hC.H_mul_U₂ hh⟩,
      hC.inf_Jb hh, hcomm, hcard, ⟨hC.t_mem_normalizer_H hh, hC.H_inf_C hh, hC.kappa_H hh⟩,
      hC.quotient hh, ⟨α, fun u b hu => (hαc u b).mpr hu, hn, β, fun h u hu => ?_,
      fun l δ hl hδ => ⟨fun u => ?_, fun h => ?_⟩⟩, ⟨c, hc1, hc2, hc3, hc4⟩, hC.H_le_closure hh⟩
    · exact Multiplicative.toAdd.injective
        ((hβc h _).mpr (hu.symm.trans ((hαc u _).mp rfl)))
    · have hjJ : ((φ.symm δ : L) : G) ∈ J₀ := symm_mem_pull.mpr ⟨1, l, one_ne_zero, hl, hδ⟩
      refine ⟨⟨_, conj_torus_mem_U₁ hjJ u.2⟩, rfl, (hαc _ _).mpr ?_⟩
      change ((φ.symm δ : L) : G)⁻¹ * u * ((φ.symm δ : L) : G) = _
      rw [(hαc u _).mp rfl, conj_coordG_diag hl hδ]
    · have hjJ : ((φ.symm δ : L) : G) ∈ J₀ := symm_mem_pull.mpr ⟨1, l, one_ne_zero, hl, hδ⟩
      refine ⟨⟨_, hC.conj_torus_mem_H hjJ h.2⟩, rfl, (hβc _ _).mpr ?_⟩
      change t⁻¹ * ((((φ.symm δ : L) : G)⁻¹ * h * ((φ.symm δ : L) : G))⁻¹ * t *
        (((φ.symm δ : L) : G)⁻¹ * h * ((φ.symm δ : L) : G))) = _
      rw [kappa_conj (torus_comm_t hh hjJ), (hβc h _).mp rfl, conj_coordG_diag hl hδ]

end Main

end OneAxisComplement

open Subgroup GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
open FullCenterTorus (axisTorus)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.PartOne.KCRootAxis
open scoped Pointwise

end CFSG.LocalAnalysis.SymplecticFourStandard
