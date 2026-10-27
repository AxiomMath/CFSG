module

public import CFSG.LocalAnalysis.SteinbergSFOneAxisSecondAxis
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace OneAxisWeakClosure

open Subgroup GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
  OneAxisRadicalStructure OneAxisSecondAxis
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.LocalAnalysis.SteinbergCD
open scoped commutatorElement Pointwise

section General

theorem maximal_iff_eq_or_eq {α : Type*} [PartialOrder α] {P : α → Prop} {X₁ X₂ : α}
    (h₁ : P X₁) (h₂ : P X₂) (hle : ∀ F, P F → F ≤ X₁ ∨ F ≤ X₂) (h₁₂ : ¬ X₁ ≤ X₂)
    (h₂₁ : ¬ X₂ ≤ X₁) (F : α) : Maximal P F ↔ F = X₁ ∨ F = X₂ := by
  constructor
  · rintro ⟨hF, hmax⟩
    rcases hle F hF with h | h
    · exact Or.inl (le_antisymm h (hmax h₁ h))
    · exact Or.inr (le_antisymm h (hmax h₂ h))
  · rintro (rfl | rfl)
    · refine ⟨h₁, fun F hF hXF => ?_⟩
      rcases hle F hF with h | h
      · exact h
      · exact absurd (hXF.trans h) h₁₂
    · refine ⟨h₂, fun F hF hXF => ?_⟩
      rcases hle F hF with h | h
      · exact absurd (hXF.trans h) h₂₁
      · exact h

variable {G G' : Type*} [Group G] [Group G']

theorem elemAb_of_comm_of_mul_self {H : Subgroup G} (hc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hs : ∀ x ∈ H, x * x = 1) : IsElementaryAbelian 2 H :=
  CFSG.IsElementaryAbelian.two_of_forall_mul_self hc hs

theorem elemAb_comm {H : Subgroup G} (hH : IsElementaryAbelian 2 H) {x y : G} (hx : x ∈ H)
    (hy : y ∈ H) : x * y = y * x :=
  congrArg Subtype.val (hH.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem elemAb_mul_self {H : Subgroup G} (hH : IsElementaryAbelian 2 H) {x : G} (hx : x ∈ H) :
    x * x = 1 := by
  have := hH
  have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := H) x hx
  rwa [pow_two] at h

theorem elemAb_map {H : Subgroup G} (hH : IsElementaryAbelian 2 H) (f : G →* G') :
    IsElementaryAbelian 2 (H.map f) := CFSG.IsElementaryAbelian.subgroup_map hH _

theorem elemAb_subgroupOf {H X : Subgroup G} (hX : IsElementaryAbelian 2 X) :
    IsElementaryAbelian 2 (X.subgroupOf H) :=
  elemAb_of_comm_of_mul_self
    (fun _ ha _ hb => Subtype.ext (elemAb_comm hX (mem_subgroupOf.mp ha) (mem_subgroupOf.mp hb)))
    fun _ ha => Subtype.ext (elemAb_mul_self hX (mem_subgroupOf.mp ha))

theorem characteristic_of_unique_elemAb {H X : Subgroup G} (hXH : X ≤ H)
    (hX : IsElementaryAbelian 2 X)
    (huniq : ∀ Y : Subgroup G, Y ≤ H → IsElementaryAbelian 2 Y → Nat.card Y = Nat.card X →
      Y = X) :
    (X.subgroupOf H).Characteristic := by
  rw [characteristic_iff_map_eq]
  intro α
  have hY := huniq (((X.subgroupOf H).map α.toMonoidHom).map H.subtype) (map_subtype_le _)
    (elemAb_map (elemAb_map (elemAb_subgroupOf hX) _) _) (by
      rw [card_map_of_injective H.subtype_injective, card_map_of_injective α.injective,
        Nat.card_congr (subgroupOfEquivOfLe hXH).toEquiv])
  apply map_injective H.subtype_injective
  rw [hY, subgroupOf_map_subtype, inf_of_le_left hXH]

theorem comm_mod_sup_of_conj {H N A B : Subgroup G} (hN : ∀ h ∈ H, ∀ z ∈ N, h * z * h⁻¹ ∈ N)
    {x : G} (hA : A ≤ H) (hB : B ≤ H) (h₁ : ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ N)
    (h₂ : ∀ b ∈ B, x * b * x⁻¹ * b⁻¹ ∈ N) : ∀ y ∈ A ⊔ B, x * y * x⁻¹ * y⁻¹ ∈ N := by
  let C : Subgroup G :=
    { carrier := {y | y ∈ H ∧ x * y * x⁻¹ * y⁻¹ ∈ N}
      mul_mem' := by
        rintro y y' ⟨hy, hyz⟩ ⟨hy', hyz'⟩
        refine ⟨mul_mem hy hy', ?_⟩
        have e : x * (y * y') * x⁻¹ * (y * y')⁻¹ =
            (x * y * x⁻¹ * y⁻¹) * (y * (x * y' * x⁻¹ * y'⁻¹) * y⁻¹) := by group
        rw [e]
        exact mul_mem hyz (hN y hy _ hyz')
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := by
        rintro y ⟨hy, hyz⟩
        refine ⟨inv_mem hy, ?_⟩
        have e : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
        rw [e]
        exact hN y⁻¹ (inv_mem hy) _ (inv_mem hyz) }
  have hle : A ⊔ B ≤ C := sup_le (fun a ha => ⟨hA ha, h₁ a ha⟩) fun b hb => ⟨hB hb, h₂ b hb⟩
  exact fun y hy => (hle hy).2

theorem comm_mod_of_sup_of_conj {H N A B : Subgroup G} (hN : ∀ h ∈ H, ∀ z ∈ N, h * z * h⁻¹ ∈ N)
    (hA : A ≤ H) (hB : B ≤ H) (hAA : ∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ N)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ N)
    (hBB : ∀ b ∈ B, ∀ b' ∈ B, b * b' * b⁻¹ * b'⁻¹ ∈ N) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y * x⁻¹ * y⁻¹ ∈ N := by
  have hsym : ∀ {x y : G}, x * y * x⁻¹ * y⁻¹ ∈ N → y * x * y⁻¹ * x⁻¹ ∈ N := fun {x y} h => by
    have e : (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ := by group
    rw [← e]
    exact inv_mem h
  have hfirst : ∀ y ∈ A ⊔ B, ∀ a, (a ∈ A ∨ a ∈ B) → a * y * a⁻¹ * y⁻¹ ∈ N := by
    rintro y hy a (ha | ha)
    · exact comm_mod_sup_of_conj hN hA hB (hAA a ha) (hAB a ha) y hy
    · exact comm_mod_sup_of_conj hN hA hB (fun a' ha' => hsym (hAB a' ha' a ha)) (hBB a ha) y hy
  intro x hx y hy
  exact hsym (comm_mod_sup_of_conj hN hA hB
    (fun a ha => hsym (hfirst y hy a (Or.inl ha)))
    (fun b hb => hsym (hfirst y hy b (Or.inr hb))) x hx)

end General

section Model

variable {K : Type} [Field K] [CharP K 2]

theorem mul_eq_zero_of_mul_self_mem {a b c d : K}
    (h : uElt a b c d * uElt a b c d ∈ rootU₂ K) : a * d = 0 := by
  rw [uElt_mul_self] at h
  obtain ⟨c', hc'⟩ := h
  exact (uElt_inj hc').2.1

end Model

section Main

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {n : ℕ}
  {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G} {M : Subgroup G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐔₁" => pull φ (rootU K Axis.one)
local notation "𝐔₂" => pull φ (rootU K Axis.two)
local notation "𝐀₁" => pull φ (rootA K Axis.one)
local notation "𝐀₂" => pull φ (rootA K Axis.two)
local notation "𝐁₂" => (zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐃₂" => (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐒" => (pull φ (antiUnipotent K) ⊔ TG ⊔ (CFSG.pCore 2 (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.two) : Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.two) : Subgroup G) : Set G)).subtype : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₁" => (M ⊔ pull φ (rootA K Axis.one) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₂" =>
  (M ⊔ M.map (MulAut.conj ((φ.symm (sElt swapSL) : L) : G)⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₀" => (M ⊔ pull φ (rootA K Axis.two) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐄" => (M ⊔ pull φ (antiUnipotent K) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐕" => (M ⊔ pull φ (rootA K Axis.one) ⊔
  (M ⊔ M.map (MulAut.conj ((φ.symm (sElt swapSL) : L) : G)⁻¹).toMonoidHom) : Subgroup G)

theorem elemAb_M (ax : AxisHyp L K n φ TG t M) : IsElementaryAbelian 2 M :=
  elemAb_of_comm_of_mul_self ax.comm ax.mul_self

theorem elemAb_A₂ (ax : AxisHyp L K n φ TG t M) : IsElementaryAbelian 2 𝐀₂ :=
  elemAb_of_comm_of_mul_self
    (fun _ hx _ hy => B_comm φ ax.heis.sec.two (mem_sup_right hx) (mem_sup_right hy))
    fun _ hx => ax.heis.hyp.mul_self_of_mem_B Axis.two (mem_sup_right hx)

theorem M₀_le_M₂ (ax : AxisHyp L K n φ TG t M) : 𝐌₀ ≤ 𝐌₂ := sup_le le_sup_left ax.A₂_le_M₂

theorem M₀_le_D₂ [Finite K] (ax : AxisHyp L K n φ TG t M) : 𝐌₀ ≤ 𝐃₂ :=
  sup_le ax.le_D₂ (le_sup_right.trans ax.heis.sec.B_le_D)

theorem M_le_V : M ≤ 𝐕 := le_sup_left.trans le_sup_left

theorem U₂_le_V (ax : AxisHyp L K n φ TG t M) : 𝐔₂ ≤ 𝐕 := ax.U₂_le.trans M_le_V

theorem U₁_le_M (ax : AxisHyp L K n φ TG t M) : 𝐔₁ ≤ M :=
  (pull_mono φ (rootU_le_center Axis.one)).trans ax.ZP_le

theorem U₁_le_A₂ : 𝐔₁ ≤ 𝐀₂ := pull_mono φ rootU_one_le_rootA_two

theorem M₁_le_E : 𝐌₁ ≤ 𝐄 :=
  sup_le le_sup_left ((pull_mono φ radA1_le_antiUnipotent).trans le_sup_right)

theorem A₂_le_E : 𝐀₂ ≤ 𝐄 := (pull_mono φ radA2_le_antiUnipotent).trans le_sup_right

theorem not_M₁_le_M₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : ¬ 𝐌₁ ≤ 𝐌₂ :=
  fun h => by
    have h1 := ax.M₁_inf_M₂
    rw [inf_of_le_left h] at h1
    have h2 := ax.card₁
    rw [h1, ax.card] at h2
    have h4 := ax.four_le
    have : (2 ^ n) ^ 3 < (2 ^ n) ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega

theorem not_M₂_le_M₁ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : ¬ 𝐌₂ ≤ 𝐌₁ :=
  fun h => by
    have h1 := ax.M₁_inf_M₂
    rw [inf_of_le_right h] at h1
    have h2 := ax.card_M₂
    rw [h1, ax.card] at h2
    have h4 := ax.four_le
    have : (2 ^ n) ^ 3 < (2 ^ n) ^ 5 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega

theorem not_M_le_A₂ (ax : AxisHyp L K n φ TG t M) : ¬ M ≤ 𝐀₂ := fun h => by
  have h1 := ax.M_inf_A₂
  rw [inf_of_le_left h] at h1
  have h2 := ax.card
  rw [h1, ax.card_ZP] at h2
  have h4 := ax.four_le
  have : (2 ^ n) ^ 2 < (2 ^ n) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem not_A₂_le_M (ax : AxisHyp L K n φ TG t M) : ¬ 𝐀₂ ≤ M := fun h => by
  have h1 := ax.M_inf_A₂
  rw [inf_of_le_right h] at h1
  have h2 := ax.card_A₂
  rw [h1, ax.card_ZP] at h2
  have h4 := ax.four_le
  have : (2 ^ n) ^ 2 < (2 ^ n) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem not_M₁_le_A₂ (ax : AxisHyp L K n φ TG t M) : ¬ 𝐌₁ ≤ 𝐀₂ := fun h =>
  not_M_le_A₂ ax (le_sup_left.trans h)

theorem not_A₂_le_M₁ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : ¬ 𝐀₂ ≤ 𝐌₁ :=
  fun h => by
    apply not_A₂_le_M ax
    rw [← ax.M₁_inf_M₂]
    exact le_inf h ax.A₂_le_M₂

theorem mem_A₁_or_A₂_of_mul_self {p : G} (hp : p ∈ 𝐏) (hsq : p * p ∈ 𝐔₂) :
    p ∈ 𝐀₁ ∨ p ∈ 𝐀₂ := by
  obtain ⟨u, ⟨a, b, c, d, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hp
  rw [symm_mul_symm, symm_mem_pull] at hsq
  rcases mul_eq_zero.mp (mul_eq_zero_of_mul_self_mem hsq) with ha | hd
  · subst ha
    exact Or.inl (symm_mem_pull.mpr ⟨b, c, d, rfl⟩)
  · subst hd
    exact Or.inr (symm_mem_pull.mpr ⟨a, b, c, rfl⟩)

theorem mem_M₁_or_M₀ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {e : G} (he : e ∈ 𝐄)
    (hsq : e * e ∈ 𝐔₂) : e ∈ 𝐌₁ ∨ e ∈ 𝐌₀ := by
  rw [← SetLike.mem_coe, ← ax.coe_E] at he
  obtain ⟨m, hm, p, hp, rfl⟩ := Set.mem_mul.mp he
  have hinv : m⁻¹ = m := inv_eq_of_mul_eq_one_right (ax.mul_self m hm)
  have hpp : p * p ∈ 𝐔₂ := by
    have e1 : p * p = (m * p * m⁻¹ * p⁻¹)⁻¹ * (m * p * (m * p)) := by
      rw [hinv]
      group
    rw [e1]
    exact mul_mem (inv_mem (ax.comm_M_P hm p hp)) hsq
  rcases mem_A₁_or_A₂_of_mul_self hp hpp with h | h
  · exact Or.inl (mul_mem (mem_sup_left hm) (mem_sup_right h))
  · exact Or.inr (mul_mem (mem_sup_left hm) (mem_sup_right h))

theorem mem_M₁_or_M₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {v : G} (hv : v ∈ 𝐕)
    (hsq : v * v ∈ 𝐔₂) : v ∈ 𝐌₁ ∨ v ∈ 𝐌₂ := by
  have hh := ax.heis
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hvS := ax.V_le_S hv
  obtain ⟨x, y, d, h⟩ := hh.exists_hAct_of_mem_S hvS
  have hB : v * v ∈ 𝐁₂ := ((pull_mono φ rootU₂_le_radA2).trans le_sup_right) hsq
  obtain ⟨-, e, -⟩ := HAct.unique hh.sec.two (h.mul h) (hAct_of_mem_B hh.sec hB)
  have hdx : d * x = 0 := by linear_combination e - y * h2
  rcases mul_eq_zero.mp hdx with hd | hx
  · right
    rw [← ax.V_inf_D₂]
    exact mem_inf.mpr ⟨hv, (hh.mem_D₂_iff hvS h).mpr hd⟩
  · have hvE : v ∈ 𝐄 := by
      rw [← ax.V_inf_R]
      exact mem_inf.mpr ⟨hv, (hh.mem_R_iff hvS h).mpr hx⟩
    rcases mem_M₁_or_M₀ ax hvE hsq with h' | h'
    · exact Or.inl h'
    · exact Or.inr (M₀_le_M₂ ax h')

theorem mem_M_or_A₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {x : G} (hx : x ∈ 𝐌₀)
    (hsq : x * x = 1) : x ∈ M ∨ x ∈ 𝐀₂ := by
  have hS := ax.heis.sec.two
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨m, hm, a, ha, y, rfl, hmy, -⟩ := ax.exists_of_mem_M₀ hx
  obtain ⟨X, Y, Z, rfl⟩ := exists_coord_zero_eq (t := t) ha
  have hinv : m⁻¹ = m := inv_eq_of_mul_eq_one_right (ax.mul_self m hm)
  have e : m * coord φ t ((0, X, Y, Z) : QGSpace K) * (m * coord φ t ((0, X, Y, Z) : QGSpace K)) =
      coord φ t (((0, X + 0 * Y, Y, Z + 0 * X + (y + 0 * 0) * Y + 0 * Y ^ 2) : QGSpace K) +
        (0, X, Y, Z)) := by
    rw [coord_add φ hS.t_mul_t (fun _ hx => hS.comm hx), ← conj_coord_zero hS hmy X Y Z, hinv]
    group
  rw [e, coord_eq_one_iff φ hS.t_not_mem] at hsq
  have h4 : Z + 0 * X + (y + 0 * 0) * Y + 0 * Y ^ 2 + Z = 0 :=
    congrArg (fun e : QGSpace K => e.2.2.2) hsq
  have hyY : y * Y = 0 := by linear_combination h4 - Z * h2
  rcases mul_eq_zero.mp hyY with hy | hY
  · subst hy
    exact Or.inr (mul_mem (pull_mono φ (center_le_rootA Axis.two) (ax.mem_ZP_of_hAct hm hmy)) ha)
  · subst hY
    exact Or.inl (mul_mem hm (ax.ZP_le (coord_zero_mem_center_iff.mpr rfl)))

theorem mem_M₁_or_A₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {x : G} (hx : x ∈ 𝐄)
    (hsq : x * x = 1) : x ∈ 𝐌₁ ∨ x ∈ 𝐀₂ := by
  have hsq' : x * x ∈ 𝐔₂ := by
    rw [hsq]
    exact one_mem _
  rcases mem_M₁_or_M₀ ax hx hsq' with h | h
  · exact Or.inl h
  · rcases mem_M_or_A₂ ax h hsq with h' | h'
    · exact Or.inl (mem_sup_left h')
    · exact Or.inr h'

theorem maximal_quot_V [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M)
    (hM₁ : IsElementaryAbelian 2 𝐌₁) :
    ∃ _ : (𝐔₂.subgroupOf 𝐕).Normal, ∀ F : Subgroup (↥𝐕 ⧸ 𝐔₂.subgroupOf 𝐕),
      Maximal (fun F' : Subgroup (↥𝐕 ⧸ 𝐔₂.subgroupOf 𝐕) => IsElementaryAbelian 2 F') F ↔
        F = (𝐌₁.subgroupOf 𝐕).map (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐕)) ∨
        F = (𝐌₂.subgroupOf 𝐕).map (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐕)) := by
  have hn : (𝐔₂.subgroupOf 𝐕).Normal := ⟨fun u hu v => by
    rw [mem_subgroupOf] at hu ⊢
    rw [coe_mul, coe_mul, comm_U₂ ax.heis (ax.V_le_S v.2) hu, coe_inv, mul_inv_cancel_right]
    exact hu⟩
  refine ⟨hn, ?_⟩
  have himg : ∀ H : Subgroup G, (∀ x ∈ H, ∀ y ∈ H, x * y * x⁻¹ * y⁻¹ ∈ 𝐔₂) →
      (∀ x ∈ H, x * x ∈ 𝐔₂) →
        IsElementaryAbelian 2 ((H.subgroupOf 𝐕).map (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐕))) := by
    intro H hc hs
    refine elemAb_of_comm_of_mul_self ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, mem_subgroupOf]
      have h := hc _ (inv_mem (mem_subgroupOf.mp hy)) _ (inv_mem (mem_subgroupOf.mp hx))
      rw [inv_inv, inv_inv] at h
      convert h using 1
      simp only [coe_mul, coe_inv]
      group
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact hs _ (mem_subgroupOf.mp hx)
  have h₁ := himg 𝐌₁
    (fun x hx y hy => by
      rw [elemAb_comm hM₁ hx hy, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _)
    fun x hx => by
      rw [elemAb_mul_self hM₁ hx]
      exact one_mem _
  have h₂ := himg 𝐌₂ ax.M₂_comm fun x hx => ax.M₂_sq hx
  have hle : ∀ F : Subgroup (↥𝐕 ⧸ 𝐔₂.subgroupOf 𝐕), IsElementaryAbelian 2 F →
      F ≤ (𝐌₁.subgroupOf 𝐕).map (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐕)) ∨
        F ≤ (𝐌₂.subgroupOf 𝐕).map (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐕)) := by
    intro F hF
    refine subgroup_le_of_subset_union fun g hg => ?_
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective g
    have hv : (v : G) * v ∈ 𝐔₂ := by
      have h := elemAb_mul_self hF hg
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf] at h
      exact h
    rcases mem_M₁_or_M₂ ax v.2 hv with h | h
    · exact Or.inl ⟨v, mem_subgroupOf.mpr h, rfl⟩
    · exact Or.inr ⟨v, mem_subgroupOf.mpr h, rfl⟩
  have hU₁ : 𝐔₂ ≤ 𝐌₁ := ax.U₂_le.trans le_sup_left
  have hU₂ : 𝐔₂ ≤ 𝐌₂ := ax.U₂_le.trans le_sup_left
  have h₁₂ : ¬ (𝐌₁.subgroupOf 𝐕).map (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐕)) ≤
      (𝐌₂.subgroupOf 𝐕).map (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐕)) := fun h =>
    not_M₁_le_M₂ ax fun x hx => (mem_map_mk_iff hU₂ ⟨x, mem_sup_left hx⟩).mp
      (h ⟨⟨x, mem_sup_left hx⟩, mem_subgroupOf.mpr hx, rfl⟩)
  have h₂₁ : ¬ (𝐌₂.subgroupOf 𝐕).map (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐕)) ≤
      (𝐌₁.subgroupOf 𝐕).map (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐕)) := fun h =>
    not_M₂_le_M₁ ax fun x hx => (mem_map_mk_iff hU₁ ⟨x, mem_sup_right hx⟩).mp
      (h ⟨⟨x, mem_sup_right hx⟩, mem_subgroupOf.mpr hx, rfl⟩)
  exact fun F => maximal_iff_eq_or_eq
    (P := fun F' : Subgroup (↥𝐕 ⧸ 𝐔₂.subgroupOf 𝐕) => IsElementaryAbelian 2 F') h₁ h₂ hle h₁₂ h₂₁ F

theorem maximal_M₀ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) (F : Subgroup G) :
    Maximal (fun F' : Subgroup G => F' ≤ 𝐌₀ ∧ IsElementaryAbelian 2 F') F ↔ F = M ∨ F = 𝐀₂ :=
  maximal_iff_eq_or_eq ⟨le_sup_left, elemAb_M ax⟩ ⟨le_sup_right, elemAb_A₂ ax⟩
    (fun _ ⟨hF, hFe⟩ => subgroup_le_of_subset_union fun _ hx =>
      mem_M_or_A₂ ax (hF hx) (elemAb_mul_self hFe hx))
    (not_M_le_A₂ ax) (not_A₂_le_M ax) F

theorem maximal_E [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M)
    (hM₁ : IsElementaryAbelian 2 𝐌₁) (F : Subgroup G) :
    Maximal (fun F' : Subgroup G => F' ≤ 𝐄 ∧ IsElementaryAbelian 2 F') F ↔
      F = 𝐌₁ ∨ F = 𝐀₂ :=
  maximal_iff_eq_or_eq ⟨M₁_le_E, hM₁⟩ ⟨A₂_le_E, elemAb_A₂ ax⟩
    (fun _ ⟨hF, hFe⟩ => subgroup_le_of_subset_union fun _ hx =>
      mem_M₁_or_A₂ ax (hF hx) (elemAb_mul_self hFe hx))
    (not_M₁_le_A₂ ax) (not_A₂_le_M₁ ax) F

theorem M_le_centralizer_U₁ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    M ≤ centralizer (𝐔₁ : Set G) := fun _ hm => mem_centralizer_iff.mpr fun _ hu =>
  (comm_ZP_of_mem_R ax.heis (mem_sup_right (ax.le_D₁ hm))
    (pull_mono φ (rootU_le_center Axis.one) hu)).symm

theorem A₂_le_centralizer_U₁ (ax : AxisHyp L K n φ TG t M) :
    𝐀₂ ≤ centralizer (𝐔₁ : Set G) := fun _ ha => mem_centralizer_iff.mpr fun _ hu =>
  B_comm φ ax.heis.sec.two (mem_sup_right (U₁_le_A₂ hu)) (mem_sup_right ha)

theorem M₂_inf_centralizer [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    𝐌₂ ⊓ centralizer (𝐔₁ : Set G) = 𝐌₀ := by
  have hS := ax.heis.sec.two
  refine le_antisymm (fun v hv => ?_) (le_inf (M₀_le_M₂ ax)
    (sup_le (M_le_centralizer_U₁ ax) (A₂_le_centralizer_U₁ ax)))
  obtain ⟨hvM, hvc⟩ := mem_inf.mp hv
  obtain ⟨m, hm, m', hm', a, b, rfl, -, ha, hv'⟩ := ax.exists_of_mem_M₂ hvM
  have hu : coord φ t ((0, 1, 0, 0) : QGSpace K) ∈ 𝐔₁ := coord_zero_mem_U₁_iff.mpr ⟨rfl, rfl⟩
  have e1 : m * m' * coord φ t ((0, 1, 0, 0) : QGSpace K) * (m * m')⁻¹ =
      coord φ t ((0, 1, 0, 0) : QGSpace K) := by
    rw [← mem_centralizer_iff.mp hvc _ hu, mul_inv_cancel_right]
  rw [conj_coord_U₁ hS hv'] at e1
  have e2 := coord_injective φ hS.t_mul_t (fun _ hx => hS.comm hx) hS.t_not_mem e1
  have ha0 : a = 0 := by
    simpa using (congrArg (fun e : QGSpace K => e.2.2.2) e2 : a * 1 = 0)
  subst ha0
  have hm'A : m' ∈ 𝐀₂ :=
    mem_A₂_of_conj_mem_ZP (ax.mem_ZP_of_hAct (mem_map_conj_inv_iff.mp hm') (hAct_w_conj hS ha))
  exact mul_mem (mem_sup_left hm) (mem_sup_right hm'A)

theorem not_comm_M₀ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    ¬ ∀ x ∈ 𝐌₀, ∀ y ∈ 𝐌₀, x * y = y * x := by
  intro h
  have hS := ax.heis.sec.two
  obtain ⟨m, hm, hmZ⟩ := ax.exists_not_mem_ZP
  obtain ⟨y, hy⟩ := ax.hAct_of_mem hm
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hmZ (ax.mem_ZP_of_hAct hm hy)
  have ha : coord φ t ((0, 0, 1, 0) : QGSpace K) ∈ 𝐌₀ := mem_sup_right (coord_zero_mem_A _ _ _)
  have hc := conj_coord_zero hS hy 0 1 0
  rw [h m (mem_sup_left hm) _ ha, mul_inv_cancel_right] at hc
  have e := coord_injective φ hS.t_mul_t (fun _ hx => hS.comm hx) hS.t_not_mem hc
  have e4 : (0 : K) = 0 + 0 * 0 + (y + 0 * 0) * 1 + 0 * 1 ^ 2 :=
    congrArg (fun e : QGSpace K => e.2.2.2) e
  exact hy0 (by linear_combination -e4)

theorem eq_M₁ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {X : Subgroup G}
    (hXV : X ≤ 𝐕) (hX : IsElementaryAbelian 2 X) (hcard : Nat.card X = (2 ^ n) ^ 4) :
    X = 𝐌₁ := by
  have hXs : ∀ x ∈ X, x * x = 1 := fun x hx => elemAb_mul_self hX hx
  rcases subgroup_le_of_subset_union (E := X) fun x hx => mem_M₁_or_M₂ ax (hXV hx)
      (by rw [hXs x hx]; exact one_mem _) with h | h
  · exact eq_of_le_of_card_ge h (by rw [hcard, ax.card₁])
  exfalso
  have hN : X ≤ normalizer (𝐌₀ : Set G) :=
    h.trans (ax.M₂_le_D₂.trans (D₂_le_normalizer ax.heis le_sup_right (M₀_le_D₂ ax)))
  have hprod := card_sup_mul_card_inf hN
  have hle := card_le_of_le (sup_le h (M₀_le_M₂ ax))
  rw [ax.card_M₂] at hle
  rw [hcard, ax.card_M₀] at hprod
  have hge : (2 ^ n) ^ 3 ≤ Nat.card (X ⊓ 𝐌₀ : Subgroup G) := by
    have h1 : (2 ^ n) ^ 5 * (2 ^ n) ^ 3 ≤ (2 ^ n) ^ 5 * Nat.card (X ⊓ 𝐌₀ : Subgroup G) :=
      calc (2 ^ n) ^ 5 * (2 ^ n) ^ 3 = (2 ^ n) ^ 4 * (2 ^ n) ^ 4 := by ring
        _ = Nat.card (X ⊔ 𝐌₀ : Subgroup G) * Nat.card (X ⊓ 𝐌₀ : Subgroup G) := hprod.symm
        _ ≤ (2 ^ n) ^ 5 * Nat.card (X ⊓ 𝐌₀ : Subgroup G) := Nat.mul_le_mul_right _ hle
    exact Nat.le_of_mul_le_mul_left h1 (by positivity)
  have hU : 𝐔₁ ≤ X ⊓ 𝐌₀ := by
    rcases subgroup_le_of_subset_union (E := X ⊓ 𝐌₀) fun x hx =>
        mem_M_or_A₂ ax (mem_inf.mp hx).2 (hXs x (mem_inf.mp hx).1) with h' | h'
    · rw [eq_of_le_of_card_ge h' (by rw [ax.card]; exact hge)]
      exact U₁_le_M ax
    · rw [eq_of_le_of_card_ge h' (by rw [ax.card_A₂]; exact hge)]
      exact U₁_le_A₂
  have hXM₀ : X ≤ 𝐌₀ := by
    rw [← M₂_inf_centralizer ax]
    exact fun x hx => mem_inf.mpr ⟨h hx, mem_centralizer_iff.mpr fun u hu =>
      elemAb_comm hX (hU hu).1 hx⟩
  have hXeq : X = 𝐌₀ := eq_of_le_of_card_ge hXM₀ (by rw [hcard, ax.card_M₀])
  exact not_comm_M₀ ax fun x hx y hy => by
    rw [← hXeq] at hx hy
    exact elemAb_comm hX hx hy

theorem characteristic_M₁ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M)
    (hM₁ : IsElementaryAbelian 2 𝐌₁) : (𝐌₁.subgroupOf 𝐕).Characteristic :=
  characteristic_of_unique_elemAb le_sup_left hM₁ fun _ hYV hY hYc =>
    eq_M₁ ax hYV hY (hYc.trans ax.card₁)

theorem conj_eq_M₁ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M)
    (hM₁ : IsElementaryAbelian 2 𝐌₁) {g : G} (hg : 𝐌₁.map (MulAut.conj g⁻¹).toMonoidHom ≤ 𝐕) :
    𝐌₁.map (MulAut.conj g⁻¹).toMonoidHom = 𝐌₁ :=
  eq_M₁ ax hg (elemAb_map hM₁ _) (by
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective, ax.card₁])

theorem comm_M_V [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M)
    (hM₁ : IsElementaryAbelian 2 𝐌₁) {m : G} (hm : m ∈ M) :
    ∀ v ∈ 𝐕, m * v * m⁻¹ * v⁻¹ ∈ 𝐔₂ :=
  comm_mod_sup (U₂_central ax.heis) (ax.le_S hm) ax.M₁_le_S ax.M₂_le_S
    (fun a ha => by
      rw [elemAb_comm hM₁ (mem_sup_left hm) ha, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _)
    (ax.M₂_comm m (mem_sup_left hm))

theorem mem_M_of_comm [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M)
    (hM₁ : IsElementaryAbelian 2 𝐌₁) {z : G} (hz : z ∈ 𝐕)
    (hc : ∀ v ∈ 𝐕, z * v * z⁻¹ * v⁻¹ ∈ 𝐔₂) : z ∈ M := by
  have hzsq : z * z ∈ 𝐔₂ := by
    have hz' : z ∈ (𝐌₁ : Set G) * (𝐌₂ : Set G) := by
      rw [ax.coe_V]
      exact hz
    obtain ⟨m₁, hm₁, m₂, hm₂, hzm⟩ := Set.mem_mul.mp hz'
    have e : z * z = (z * m₁ * z⁻¹ * m₁⁻¹) * (m₁ * m₁) * (m₂ * m₂) := by
      rw [← hzm]
      group
    rw [e, elemAb_mul_self hM₁ hm₁, mul_one]
    exact mul_mem (hc m₁ (mem_sup_left hm₁)) (ax.M₂_sq hm₂)
  have hmul : ∀ x ∈ 𝐕, x * x ∈ 𝐔₂ → x * z * (x * z) ∈ 𝐔₂ := by
    intro x hx hxx
    have hcx := hc x hx
    have e : x * z * (x * z) = (x * (z * x * z⁻¹ * x⁻¹) * x⁻¹) * (x * x) * (z * z) := by group
    rw [e]
    refine mul_mem (mul_mem ?_ hxx) hzsq
    rw [comm_U₂ ax.heis (ax.V_le_S hx) hcx, mul_inv_cancel_right]
    exact hcx
  have hz₁ : z ∈ 𝐌₁ := by
    by_contra hz₁
    have hzM₂ : z ∈ 𝐌₂ := (mem_M₁_or_M₂ ax hz hzsq).resolve_left hz₁
    apply not_M₁_le_M₂ ax
    intro x hx
    have hxV : x ∈ 𝐕 := mem_sup_left hx
    rcases mem_M₁_or_M₂ ax (mul_mem hxV hz)
        (hmul x hxV (by rw [elemAb_mul_self hM₁ hx]; exact one_mem _)) with h | h
    · exact absurd (by simpa using mul_mem (inv_mem hx) h) hz₁
    · simpa using mul_mem h (inv_mem hzM₂)
  have hz₂ : z ∈ 𝐌₂ := by
    by_contra hz₂
    apply not_M₂_le_M₁ ax
    intro x hx
    have hxV : x ∈ 𝐕 := mem_sup_right hx
    rcases mem_M₁_or_M₂ ax (mul_mem hxV hz) (hmul x hxV (ax.M₂_sq hx)) with h | h
    · simpa using mul_mem h (inv_mem hz₁)
    · exact absurd (by simpa using mul_mem (inv_mem hx) h) hz₂
  rw [← ax.M₁_inf_M₂]
  exact mem_inf.mpr ⟨hz₁, hz₂⟩

theorem center_V [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M)
    (hM₁ : IsElementaryAbelian 2 𝐌₁) : (center 𝐕).map 𝐕.subtype = 𝐔₂ := by
  apply le_antisymm
  · intro z hz
    obtain ⟨hzV, hzc⟩ := mem_center_map_iff.mp hz
    have hzM : z ∈ M := mem_M_of_comm ax hM₁ hzV fun v hv => by
      rw [← hzc v hv, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    rw [← ax.center_M₂]
    exact mem_center_map_iff.mpr ⟨mem_sup_left hzM, fun y hy => hzc y (mem_sup_right hy)⟩
  · intro u hu
    exact mem_center_map_iff.mpr ⟨U₂_le_V ax hu, fun v hv => comm_U₂ ax.heis (ax.V_le_S hv) hu⟩

theorem comm_V_mem_M [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M)
    (hM₁ : IsElementaryAbelian 2 𝐌₁) {x y : G} (hx : x ∈ 𝐕) (hy : y ∈ 𝐕) :
    x * y * x⁻¹ * y⁻¹ ∈ M := by
  refine comm_mod_of_sup_of_conj (H := 𝐒) (fun s hs z hz => ax.conj_mem hs hz) ax.M₁_le_S
    ax.M₂_le_S (fun a ha a' ha' => ?_) (fun a ha b hb => ?_) (fun b hb b' hb' => ?_) x hx y hy
  · rw [elemAb_comm hM₁ ha ha', mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  · rw [← ax.M₁_inf_M₂]
    refine mem_inf.mpr ⟨?_, mul_mem (ax.conj_mem_M₂ (ax.M₁_le_S ha) hb) (inv_mem hb)⟩
    have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [e]
    exact mul_mem ha (ax.conj₁ b (ax.M₂_le_S hb) a⁻¹ (inv_mem ha))
  · exact ax.U₂_le (ax.M₂_comm b hb b' hb')

theorem upper_V [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M)
    (hM₁ : IsElementaryAbelian 2 𝐌₁) :
    (Subgroup.upperCentralSeries 𝐕 2).map 𝐕.subtype = M := by
  ext x
  rw [mem_upperCentralSeries_two_iff, center_V ax hM₁]
  exact ⟨fun ⟨hxV, hx⟩ => mem_M_of_comm ax hM₁ hxV hx,
    fun hx => ⟨M_le_V hx, comm_M_V ax hM₁ hx⟩⟩

theorem upper_three_V [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M)
    (hM₁ : IsElementaryAbelian 2 𝐌₁) : Subgroup.upperCentralSeries 𝐕 3 = ⊤ := by
  refine eq_top_iff.mpr fun x _ =>
    (Subgroup.mem_upperCentralSeries_succ_iff (n := 2)).mpr fun y => ?_
  have h : 𝐕.subtype ⁅x, y⁆ ∈ (Subgroup.upperCentralSeries 𝐕 2).map 𝐕.subtype := by
    rw [upper_V ax hM₁]
    exact comm_V_mem_M ax hM₁ x.2 y.2
  exact (mem_map_iff_mem 𝐕.subtype_injective).mp h

theorem conj_mem_U₂_of_normalizer_V [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M)
    (hM₁ : IsElementaryAbelian 2 𝐌₁) {g : G} (hg : g ∈ normalizer (𝐕 : Set G)) {u : G}
    (hu : u ∈ 𝐔₂) : g * u * g⁻¹ ∈ 𝐔₂ := by
  rw [← center_V ax hM₁] at hu ⊢
  obtain ⟨huV, huc⟩ := mem_center_map_iff.mp hu
  refine mem_center_map_iff.mpr ⟨(mem_normalizer_iff.mp hg u).mp huV, fun v hv => ?_⟩
  have h := huc _ ((mem_normalizer_iff''.mp hg v).mp hv)
  calc v * (g * u * g⁻¹) = g * ((g⁻¹ * v * g) * u) * g⁻¹ := by group
    _ = g * (u * (g⁻¹ * v * g)) * g⁻¹ := by rw [h]
    _ = g * u * g⁻¹ * v := by group

theorem normalizer_V [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M)
    (hM₁ : IsElementaryAbelian 2 𝐌₁) :
    normalizer (𝐕 : Set G) = normalizer (𝐌₁ : Set G) ⊓ normalizer (𝐌₂ : Set G) := by
  refine le_antisymm (fun g hg => ⟨?_, ?_⟩) (le_normalizer_sup inf_le_left inf_le_right)
  · have hX := eq_M₁ ax (X := 𝐌₁.map (MulAut.conj g).toMonoidHom) ?_ (elemAb_map hM₁ _)
      (by rw [card_map_of_injective (MulAut.conj g).injective, ax.card₁])
    · refine mem_normalizer_of_conj_le fun x hx => ?_
      rw [← hX]
      exact ⟨x, hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.mp hg x).mp (mem_sup_left hx)
  · have hcard : Nat.card (𝐌₂.map (MulAut.conj g).toMonoidHom) = (2 ^ n) ^ 5 := by
      rw [card_map_of_injective (MulAut.conj g).injective, ax.card_M₂]
    rcases subgroup_le_of_subset_union (E := 𝐌₂.map (MulAut.conj g).toMonoidHom) (P := 𝐌₁)
        (Q := 𝐌₂) (by
          rintro _ ⟨x, hx, rfl⟩
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          refine mem_M₁_or_M₂ ax ((mem_normalizer_iff.mp hg x).mp (mem_sup_right hx)) ?_
          have e : g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
          rw [e]
          exact conj_mem_U₂_of_normalizer_V ax hM₁ hg (ax.M₂_sq hx)) with h | h
    · exfalso
      have hle := card_le_of_le h
      rw [hcard, ax.card₁] at hle
      have h4 := ax.four_le
      have : (2 ^ n) ^ 4 < (2 ^ n) ^ 5 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      omega
    · have hX := eq_of_le_of_card_ge h (by rw [hcard, ax.card_M₂])
      refine mem_normalizer_of_conj_le fun x hx => ?_
      rw [← hX]
      exact ⟨x, hx, rfl⟩

theorem main [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) (Q ZP PG : Subgroup G)
    (hPG : PG = pull φ (antiUnipotent K)) (hQ : Q = PG ⊔ TG)
    (hZP : ZP = pull φ (antiUnipotentCenter K)) (w : antiSp K)
    (hw : glMat (w : GL (Fin 4) K) = !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1])
    (M : Subgroup G) :
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
    let S := Q ⊔ D₂
    let J₀ := pull φ (diagTorus K)
    let w₂ : G := ((φ.symm w : L) : G)
    let Mw := M.map (MulAut.conj w₂⁻¹).toMonoidHom
    let M₁ := M ⊔ A₁
    let M₀ := M ⊔ A₂
    let M₂ := M ⊔ Mw
    let E := M ⊔ PG
    let V := M₁ ⊔ M₂
    J₀ ≤ normalizer (M : Set G) → M ≤ D₁ ⊓ D₂ → IsElementaryAbelian 2 M →
    Nat.card M = (2 ^ n) ^ 3 → ZP ≤ M → IsElementaryAbelian 2 M₁ →
    Nat.card M₁ = (2 ^ n) ^ 4 → (M₁ ≤ S ∧ (M₁.subgroupOf S).Normal) →
    (M₁ ≤ D₁ ∧ (M₁.subgroupOf D₁).Normal ∧ M₁ ⊓ zpowers t = ⊥ ∧ M₁ ⊔ zpowers t = D₁) →
      (U₂ ≤ V ∧ ∀ z ∈ U₂, ∀ v ∈ V, z * v = v * z) ∧
      (∃ _ : (U₂.subgroupOf V).Normal, ∀ F : Subgroup (↥V ⧸ U₂.subgroupOf V),
        Maximal (fun F' : Subgroup (↥V ⧸ U₂.subgroupOf V) => IsElementaryAbelian 2 F') F ↔
          F = (M₁.subgroupOf V).map (QuotientGroup.mk' (U₂.subgroupOf V)) ∨
          F = (M₂.subgroupOf V).map (QuotientGroup.mk' (U₂.subgroupOf V))) ∧
      (∀ F : Subgroup G,
        Maximal (fun F' : Subgroup G => F' ≤ M₀ ∧ IsElementaryAbelian 2 F') F ↔
          F = M ∨ F = A₂) ∧
      (∀ F : Subgroup G,
        Maximal (fun F' : Subgroup G => F' ≤ E ∧ IsElementaryAbelian 2 F') F ↔
          F = M₁ ∨ F = A₂) ∧
      M₂ ⊓ centralizer (U₁ : Set G) = M₀ ∧
      (∀ X : Subgroup G, X ≤ V → IsElementaryAbelian 2 X → Nat.card X = (2 ^ n) ^ 4 →
        X = M₁) ∧
      (M₁.subgroupOf V).Characteristic ∧
      (∀ g : G, M₁.map (MulAut.conj g⁻¹).toMonoidHom ≤ V →
        M₁.map (MulAut.conj g⁻¹).toMonoidHom = M₁) ∧
      ((center V).map V.subtype = U₂ ∧
        (Subgroup.upperCentralSeries V 2).map V.subtype = M ∧
        Subgroup.upperCentralSeries V 3 = ⊤) ∧
      normalizer (V : Set G) = normalizer (M₁ : Set G) ⊓ normalizer (M₂ : Set G) ∧
      (∀ v ∈ V, v * v ∈ U₂ → v ∈ M₁ ∨ v ∈ M₂) ∧
      (∀ x ∈ M₀, x * x = 1 → x ∈ M ∨ x ∈ A₂) ∧
      (∀ x ∈ E, x * x = 1 → x ∈ M₁ ∨ x ∈ A₂) := by
  subst hQ hPG hZP
  obtain rfl : w = sElt swapSL := antiSp_ext (hw.trans glMat_sElt_swap.symm)
  intro U₁ U₂ A₁ A₂ B₁ B₂ N₁ N₂ D₁ D₂ S J₀ w₂ Mw M₁ M₀ M₂ E V _ hMD hMab hMcard hZM hM₁
    hM₁card hM₁S hM₁D
  have hM₁n := (normal_subgroupOf_iff_le_normalizer hM₁S.1).mp hM₁S.2
  have ax : AxisHyp L K n φ TG t M :=
    { heis := hh
      le_D₁ := hMD.trans inf_le_left
      le_D₂ := hMD.trans inf_le_right
      comm := fun _ hx _ hy => elemAb_comm hMab hx hy
      mul_self := fun _ hx => elemAb_mul_self hMab hx
      card := hMcard
      ZP_le := hZM
      card₁ := hM₁card
      conj₁ := fun s hs x hx => (mem_normalizer_iff.mp (hM₁n hs) x).mp hx
      t_not_mem₁ := fun h => by
        have h1 : t ∈ M₁ ⊓ zpowers t := mem_inf.mpr ⟨h, mem_zpowers t⟩
        rw [hM₁D.2.2.1, mem_bot] at h1
        exact hh.hyp.setup.t_ne_one h1 }
  exact ⟨⟨U₂_le_V ax, fun z hz v hv => U₂_central hh z hz v (ax.V_le_S hv)⟩,
    maximal_quot_V ax hM₁, maximal_M₀ ax, maximal_E ax hM₁, M₂_inf_centralizer ax,
    fun X hXV hX hXc => eq_M₁ ax hXV hX hXc, characteristic_M₁ ax hM₁,
    fun g hg => conj_eq_M₁ ax hM₁ hg, ⟨center_V ax hM₁, upper_V ax hM₁, upper_three_V ax hM₁⟩,
    normalizer_V ax hM₁, fun v hv hsq => mem_M₁_or_M₂ ax hv hsq,
    fun x hx hsq => mem_M_or_A₂ ax hx hsq, fun x hx hsq => mem_M₁_or_A₂ ax hx hsq⟩

end Main

end OneAxisWeakClosure

open Subgroup GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.PartOne.KCRootAxis
open scoped Pointwise

theorem standard_symplectic_four_given_first_overgroup_original_weak_closure
    {G : Type} [Group G] [Finite G] (hO : CFSG.Open.standardComponentOddCore G = ⊥)
    {L : Subgroup G} (hL : CFSG.Open.standardComponentIsStandard L) (hLn : ¬ L.Normal)
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htT : t ∈ T) (ht : orderOf t = 2)
    (hcore : CFSG.Open.standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥)
    (P : Sylow 2 L) (φ : L ≃* antiSp K)
    (hφP : (P : Subgroup L).map φ.toMonoidHom = antiUnipotent K) (w : antiSp K)
    (hw : glMat (w : GL (Fin 4) K) = !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1])
    (M : Subgroup G) :
    let TG := (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    let PG := (P : Subgroup L).map L.subtype
    let Q := PG ⊔ TG
    let ZP := (center PG).map PG.subtype
    let U₁ := ((rootU K Axis.one).comap φ.toMonoidHom).map L.subtype
    let U₂ := ((rootU K Axis.two).comap φ.toMonoidHom).map L.subtype
    let A₁ := ((rootA K Axis.one).comap φ.toMonoidHom).map L.subtype
    let A₂ := ((rootA K Axis.two).comap φ.toMonoidHom).map L.subtype
    let B₁ := zpowers (t : G) ⊔ A₁
    let B₂ := zpowers (t : G) ⊔ A₂
    let N₁ := normalizer (B₁ : Set G)
    let N₂ := normalizer (B₂ : Set G)
    let D₁ := (CFSG.pCore 2 N₁).map N₁.subtype
    let D₂ := (CFSG.pCore 2 N₂).map N₂.subtype
    let S := Q ⊔ D₂
    let J₀ := ((diagTorus K).comap φ.toMonoidHom).map L.subtype
    let w₂ : G := ((φ.symm w : L) : G)
    let Mw := M.map (MulAut.conj w₂⁻¹).toMonoidHom
    let M₁ := M ⊔ A₁
    let M₀ := M ⊔ A₂
    let M₂ := M ⊔ Mw
    let E := M ⊔ PG
    let V := M₁ ⊔ M₂
    {x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ u ∈ U₁, x = t * u} →
    J₀ ≤ normalizer (M : Set G) → M ≤ D₁ ⊓ D₂ → IsElementaryAbelian 2 M →
    Nat.card M = (2 ^ n) ^ 3 → ZP ≤ M → IsElementaryAbelian 2 M₁ →
    Nat.card M₁ = (2 ^ n) ^ 4 → (M₁ ≤ S ∧ (M₁.subgroupOf S).Normal) →
    (M₁ ≤ D₁ ∧ (M₁.subgroupOf D₁).Normal ∧ M₁ ⊓ zpowers (t : G) = ⊥ ∧
      M₁ ⊔ zpowers (t : G) = D₁) →
      (U₂ ≤ V ∧ ∀ z ∈ U₂, ∀ v ∈ V, z * v = v * z) ∧
      (∃ _ : (U₂.subgroupOf V).Normal, ∀ F : Subgroup (↥V ⧸ U₂.subgroupOf V),
        Maximal (fun F' : Subgroup (↥V ⧸ U₂.subgroupOf V) => IsElementaryAbelian 2 F') F ↔
          F = (M₁.subgroupOf V).map (QuotientGroup.mk' (U₂.subgroupOf V)) ∨
          F = (M₂.subgroupOf V).map (QuotientGroup.mk' (U₂.subgroupOf V))) ∧
      (∀ F : Subgroup G,
        Maximal (fun F' : Subgroup G => F' ≤ M₀ ∧ IsElementaryAbelian 2 F') F ↔
          F = M ∨ F = A₂) ∧
      (∀ F : Subgroup G,
        Maximal (fun F' : Subgroup G => F' ≤ E ∧ IsElementaryAbelian 2 F') F ↔
          F = M₁ ∨ F = A₂) ∧
      M₂ ⊓ centralizer (U₁ : Set G) = M₀ ∧
      (∀ X : Subgroup G, X ≤ V → IsElementaryAbelian 2 X → Nat.card X = (2 ^ n) ^ 4 →
        X = M₁) ∧
      (M₁.subgroupOf V).Characteristic ∧
      (∀ g : G, M₁.map (MulAut.conj g⁻¹).toMonoidHom ≤ V →
        M₁.map (MulAut.conj g⁻¹).toMonoidHom = M₁) ∧
      ((center V).map V.subtype = U₂ ∧
        (Subgroup.upperCentralSeries V 2).map V.subtype = M ∧
        Subgroup.upperCentralSeries V 3 = ⊤) ∧
      normalizer (V : Set G) = normalizer (M₁ : Set G) ⊓ normalizer (M₂ : Set G) ∧
      (∀ v ∈ V, v * v ∈ U₂ → v ∈ M₁ ∨ v ∈ M₂) ∧
      (∀ x ∈ M₀, x * x = 1 → x ∈ M ∨ x ∈ A₂) ∧
      (∀ x ∈ E, x * x = 1 → x ∈ M₁ ∨ x ∈ A₂) := by
  intro TG PG Q ZP U₁ U₂ A₁ A₂ B₁ B₂ N₁ N₂ D₁ D₂ S J₀ w₂ Mw M₁ M₀ M₂ E V hone
  have hS := setup_of_standard hL hn hK φ T hT htT ht hcore
  have hT' := hS.T_eq_zpowers hO hLn
  have hS2 : TwoCoreSetup L K n (t : G) :=
    { two_le := hn
      card_K := hK
      t_mul_t := hS.t_mul_t
      L_le := hS.L_le
      cent_le := hS.cent_le
      cent_inf := hS.cent_inf.trans hT'
      not_conj := hS.conj_not_mem_L hO hLn }
  have hPG : PG = pull φ (antiUnipotent K) := by
    change (P : Subgroup L).map L.subtype = ((antiUnipotent K).comap φ.toMonoidHom).map L.subtype
    rw [← hφP, comap_map_eq_self_of_injective φ.injective]
  have hQ : Q = pull φ (antiUnipotent K) ⊔ TG := by
    show PG ⊔ TG = _
    rw [hPG]
  have hZP : ZP = pull φ (antiUnipotentCenter K) := by
    have h := center_pull_antiUnipotent (G := G) φ
    rw [← hPG] at h
    exact h
  have hH : Hyp L K n φ TG t := ⟨hS, hS2, hT', by rw [← hQ]; exact hone⟩
  have hNQ := hH.normalizer_Q_le
  have hNC := (hS.orbits hO hLn).2.2.2.2
  have hmove : ∃ g ∈ N₂, g * t ≠ t * g := by
    obtain ⟨m, hm, hmC⟩ := Set.not_subset.mp hNC
    exact ⟨m, (hNQ hm).2, fun hmt => hmC (mem_centralizer_singleton_iff.mpr hmt)⟩
  have h2 : SecondHyp L K n φ (t : G) := ⟨hS2, hH.fus_two.1, hmove⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hinf₁, -, _, e, he, -, -, -⟩ :=
    standard_symplectic_four_one_axis_radical_fusion_normalizers hO hL hLn hn hK T hT htT ht
      hcore P φ hφP hone
  have hh : HeisHyp L K n φ TG t :=
    { hyp := hH
      sec := h2
      normQ := hNQ
      inf₁ := hinf₁
      conj₁ := fun d hd => by
        rw [← he ⟨d, hd⟩]
        exact (e (⟨d, hd⟩ : D₁)).2
      mul₁ := fun d hd d' hd' => by
        have h1 := he (⟨d, hd⟩ * ⟨d', hd'⟩)
        rw [QuotientGroup.mk_mul, map_mul, Subgroup.coe_mul, he, he] at h1
        exact h1.symm
      surj₁ := fun u hu => by
        obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm ⟨u, hu⟩)
        refine ⟨x, x.2, ?_⟩
        have h1 := he x
        rw [hx, MulEquiv.apply_symm_apply] at h1
        exact h1.symm }
  exact OneAxisWeakClosure.main hh Q ZP PG hPG rfl hZP w hw M

end CFSG.LocalAnalysis.SymplecticFourStandard
