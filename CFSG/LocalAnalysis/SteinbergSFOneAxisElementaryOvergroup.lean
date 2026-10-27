module

public import CFSG.LocalAnalysis.SteinbergSFOneAxisElementaryOvergroupBase
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace OneAxisOvergroup

open Subgroup GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
  OneAxisRadicalStructure OneAxisComplement
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped commutatorElement Pointwise

section Pi

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  (φ : L ≃* antiSp K) (M : Subgroup G)

local notation "𝐮[" a ", " b ", " c ", " d "]" => ((φ.symm (uElt a b c d) : L) : G)

noncomputable def piE (e : G) : K × K :=
  ((Classical.epsilon fun p : K × K × K × K =>
      e * (𝐮[p.1, p.2.1, p.2.2.1, p.2.2.2])⁻¹ ∈ M).1,
    (Classical.epsilon fun p : K × K × K × K =>
      e * (𝐮[p.1, p.2.1, p.2.2.1, p.2.2.2])⁻¹ ∈ M).2.2.2)

variable {φ M}

theorem piE_eq (hMP : ∀ x ∈ M, x ∈ pull φ (antiUnipotent K) →
      x ∈ pull φ (antiUnipotentCenter K))
    {m : G} (hm : m ∈ M) (a b c d : K) : piE φ M (m * 𝐮[a, b, c, d]) = (a, d) := by
  have hex : ∃ p : K × K × K × K, m * 𝐮[a, b, c, d] * (𝐮[p.1, p.2.1, p.2.2.1, p.2.2.2])⁻¹ ∈ M :=
    ⟨(a, b, c, d), by rw [mul_inv_cancel_right]; exact hm⟩
  have hpM := Classical.epsilon_spec hex
  set p := Classical.epsilon fun p : K × K × K × K =>
    m * 𝐮[a, b, c, d] * (𝐮[p.1, p.2.1, p.2.2.1, p.2.2.2])⁻¹ ∈ M with hp
  have h1 : 𝐮[a, b, c, d] * (𝐮[p.1, p.2.1, p.2.2.1, p.2.2.2])⁻¹ ∈ M := by
    have := mul_mem (inv_mem hm) hpM
    rwa [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul] at this
  have h2 := hMP _ h1 (mul_mem (u_mem_P _ _ _ _) (inv_mem (u_mem_P _ _ _ _)))
  rw [u_inv, u_mul] at h2
  obtain ⟨ha, hd⟩ := u_mem_Z_iff.mp h2
  have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
  show (p.1, p.2.2.2) = (a, d)
  refine Prod.ext ?_ ?_
  · change p.1 = a
    linear_combination ha - a * h2'
  · change p.2.2.2 = d
    linear_combination hd - d * h2'

end Pi

theorem commutator_mul_left {G : Type*} [Group G] (x y z : G) :
    ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutator_mul_right {G : Type*} [Group G] (x y z : G) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
  simp only [commutatorElement_def]
  group

namespace OvHyp

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G} {M : Subgroup G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
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
local notation "𝐑" => (pull φ (antiUnipotent K) ⊔ TG ⊔ (CFSG.pCore 2 (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.one) : Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.one) : Subgroup G) : Set G)).subtype : Subgroup G)
set_option quotPrecheck false in
local notation "𝐒" => (pull φ (antiUnipotent K) ⊔ TG ⊔ (CFSG.pCore 2 (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.two) : Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.two) : Subgroup G) : Set G)).subtype : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
set_option quotPrecheck false in
local notation "𝐇" =>
  (M ⊓ centralizer (pull φ (FullCenterTorus.axisTorus K Axis.one) : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₁" => (M ⊔ pull φ (rootA K Axis.one) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₀" => (M ⊔ pull φ (rootA K Axis.two) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐄" => (M ⊔ pull φ (antiUnipotent K) : Subgroup G)
local notation "𝐮[" a ", " b ", " c ", " d "]" => ((φ.symm (uElt a b c d) : L) : G)
local notation "𝐰₂" => ((φ.symm (weylElt₂ K) : L) : G)

section E

omit [Finite G] [Finite K] in
theorem P_eq : 𝐏 = 𝐀₁ ⊔ 𝐀₂ := by
  rw [← pull_sup]
  exact congrArg (pull φ) antiUnipotent_eq_radA1_sup_radA2

theorem comm_A₂_mem (h : OvHyp L K n φ TG t M) {a m : G} (ha : a ∈ 𝐀₂) (hm : m ∈ M) :
    ⁅a, m⁆ ∈ 𝐔₂ := by
  have := (mem_upperCentralSeries_two_iff.mp ((upper_D₂ h.heis).ge ha)).2 m (h.M_le_D₂ hm)
  rwa [center_D₂ h.heis, ← commutatorElement_def] at this

theorem P_le_N (h : OvHyp L K n φ TG t M) : 𝐏 ≤ normalizer (M : Set G) := by
  rw [P_eq]
  refine sup_le (le_normalizer_of_commute fun a ha m hm => (h.comm_A₁ (h.M_le_D₁ hm) ha).symm)
    fun a ha => mem_normalizer_of_conj_le fun m hm => ?_
  have hc := h.comp.ZP_le (U₂_le_ZP (h.comm_A₂_mem ha hm))
  rw [commutatorElement_def] at hc
  rw [show a * m * a⁻¹ = a * m * a⁻¹ * m⁻¹ * m by group]
  exact mul_mem hc hm

theorem coe_E (h : OvHyp L K n φ TG t M) :
    ((𝐄 : Subgroup G) : Set G) = (M : Set G) * (𝐏 : Set G) :=
  coe_mul_of_right_le_normalizer_left M 𝐏 h.P_le_N

theorem M_inf_P (h : OvHyp L K n φ TG t M) : M ⊓ 𝐏 = 𝐙 :=
  h.inf_eq_Z (pull_le φ _) (pull_mono φ antiUnipotentCenter_le)

theorem card_E (h : OvHyp L K n φ TG t M) : Nat.card 𝐄 = (2 ^ n) ^ 5 := by
  have h1 := card_sup_mul_card_inf (A := 𝐏) (N := M) h.P_le_N
  rw [sup_comm, inf_comm, h.M_inf_P, h.card_M, card_pull φ (antiUnipotent K),
    (card_radicals (K := K)).1, card_pull φ (antiUnipotentCenter K),
    (card_radicals (K := K)).2.2.2, h.two.card_K] at h1
  have hpos : 0 < (2 ^ n) ^ 2 := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1]; ring)

omit [Finite G] [Finite K] in
theorem E_le_R (h : OvHyp L K n φ TG t M) : 𝐄 ≤ 𝐑 :=
  sup_le (fun _ hm => mem_sup_right (h.M_le_D₁ hm)) (le_sup_left.trans le_sup_left)

theorem t_not_mem_E (h : OvHyp L K n φ TG t M) : t ∉ 𝐄 :=
  h.t_not_mem_sup (pull_le φ _) h.P_le_N

theorem t_mem_N_E (h : OvHyp L K n φ TG t M) : t ∈ normalizer (𝐄 : Set G) :=
  mem_normalizer_of_conj_le fun _ hx => conj_mem_sup
    (fun y hy => (mem_normalizer_iff.mp h.t_mem_N y).mp hy)
    (fun p hp => by rw [h.two.comm (pull_le φ _ hp), mul_inv_cancel_right]; exact hp) hx

theorem E_sup_t (h : OvHyp L K n φ TG t M) : 𝐄 ⊔ zpowers t = 𝐑 := by
  refine le_antisymm (sup_le h.E_le_R (zpowers_le.mpr (mem_sup_left (t_mem_Q h.heis)))) ?_
  have hM₁ : 𝐌₁ ≤ 𝐄 := sup_le le_sup_left ((pull_mono φ (rootA_le_antiUnipotent Axis.one)).trans
    le_sup_right)
  refine sup_le (sup_le (le_sup_right.trans le_sup_left) ?_) ?_
  · rw [h.heis.hyp.T_eq]
    exact le_sup_right
  · rw [← h.M₁_sup_t]
    exact sup_le_sup_right hM₁ _

theorem card_R (h : OvHyp L K n φ TG t M) :
    Nat.card 𝐑 = 2 * (2 ^ n) ^ 5 ∧ 𝐄.relIndex 𝐑 = 2 := by
  have h1 := card_sup_zpowers h.two.t_mul_t h.t_mem_N_E h.t_not_mem_E
  rw [h.E_sup_t, h.card_E] at h1
  exact h1

theorem normal_E_R (h : OvHyp L K n φ TG t M) : (𝐄.subgroupOf 𝐑).Normal :=
  (normal_subgroupOf_iff_le_normalizer h.E_le_R).mpr
    (h.E_sup_t ▸ sup_le le_normalizer (zpowers_le.mpr h.t_mem_N_E))

theorem conj_R (h : OvHyp L K n φ TG t M) {s r : G} (hs : s ∈ 𝐒) (hr : r ∈ 𝐑) :
    s * r * s⁻¹ ∈ 𝐑 := by
  have hrS := h.heis.R_le_S hr
  obtain ⟨x, y, d, hs'⟩ := h.heis.exists_hAct_of_mem_S hs
  obtain ⟨x', y', d', hr'⟩ := h.heis.exists_hAct_of_mem_S hrS
  obtain rfl := (h.heis.mem_R_iff hrS hr').mp hr
  exact (h.heis.mem_R_iff (mul_mem (mul_mem hs hrS) (inv_mem hs)) (hAct_conj hs' hr')).mpr rfl

theorem conj_U₂_iff (h : OvHyp L K n φ TG t M) {s x : G} (hs : s ∈ 𝐒) :
    s * x * s⁻¹ ∈ 𝐔₂ ↔ x ∈ 𝐔₂ := by
  constructor
  · intro hx
    have hc := comm_U₂ h.heis hs hx
    have e : x = s * x * s⁻¹ := by
      calc x = s⁻¹ * ((s * x * s⁻¹) * s) := by group
        _ = s⁻¹ * (s * (s * x * s⁻¹)) := by rw [← hc]
        _ = s * x * s⁻¹ := by group
    rw [e]
    exact hx
  · intro hx
    rw [comm_U₂ h.heis hs hx, mul_inv_cancel_right]
    exact hx

omit [Finite G] [Finite K] in
theorem M_le_S (h : OvHyp L K n φ TG t M) : M ≤ 𝐒 := fun _ hm => mem_sup_right (h.M_le_D₂ hm)

omit [Finite G] [Finite K] in
theorem P_le_S : 𝐏 ≤ 𝐒 := le_sup_left.trans le_sup_left

omit [Finite G] [Finite K] in
theorem u_split₁ (a b c d : K) : 𝐮[a, b, c, d] = 𝐮[0, b, c + a * b, d] * 𝐮[a, 0, 0, 0] := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e : uElt (0 : K) b (c + a * b) d * uElt a 0 0 0 = uElt a b c d := by
    rw [uElt_mul]
    congr 1 <;> first | ring1 | linear_combination (a * b) * h2
  rw [← coe_mul, ← map_mul, e]

theorem comm_M_P (h : OvHyp L K n φ TG t M) {m p : G} (hm : m ∈ M) (hp : p ∈ 𝐏) :
    ⁅m, p⁆ ∈ 𝐔₂ := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_u_eq hp
  rw [u_split₁, commutator_mul_right]
  have h1 : ⁅m, 𝐮[0, b, c + a * b, d]⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact h.comm_A₁ (h.M_le_D₁ hm) (u_mem_A₁_iff.mpr rfl)
  have h2 : ⁅m, 𝐮[a, 0, 0, 0]⁆ ∈ 𝐔₂ := by
    rw [← commutatorElement_inv]
    exact inv_mem (h.comm_A₂_mem (u_mem_A₂_iff.mpr rfl) hm)
  rw [h1, one_mul, h.conj_U₂_iff (P_le_S (u_mem_P _ _ _ _))]
  exact h2

theorem exists_dec (h : OvHyp L K n φ TG t M) {e : G} (he : e ∈ 𝐄) :
    ∃ m ∈ M, ∃ a b c d : K, m * 𝐮[a, b, c, d] = e := by
  rw [← SetLike.mem_coe, h.coe_E] at he
  obtain ⟨m, hm, p, hp, rfl⟩ := he
  obtain ⟨a, b, c, d, rfl⟩ := exists_u_eq hp
  exact ⟨m, hm, a, b, c, d, rfl⟩

theorem comm_M_E (h : OvHyp L K n φ TG t M) {m e : G} (hm : m ∈ M) (he : e ∈ 𝐄) :
    ⁅m, e⁆ ∈ 𝐔₂ := by
  obtain ⟨m', hm', a, b, c, d, rfl⟩ := h.exists_dec he
  rw [commutator_mul_right, (commutatorElement_eq_one_iff_mul_comm.mpr (h.comm_M hm hm')), one_mul,
    h.conj_U₂_iff (h.M_le_S hm')]
  exact h.comm_M_P hm (u_mem_P _ _ _ _)

theorem comm_left_iff (h : OvHyp L K n φ TG t M) {m g e : G} (hm : m ∈ M) (he : e ∈ 𝐄) :
    ⁅m * g, e⁆ ∈ 𝐔₂ ↔ ⁅g, e⁆ ∈ 𝐔₂ := by
  rw [commutator_mul_left, mul_mem_cancel_right (h.comm_M_E hm he), h.conj_U₂_iff (h.M_le_S hm)]

theorem comm_right_iff (h : OvHyp L K n φ TG t M) {g m e : G} (hg : g ∈ 𝐄) (hm : m ∈ M) :
    ⁅g, m * e⁆ ∈ 𝐔₂ ↔ ⁅g, e⁆ ∈ 𝐔₂ := by
  have hc : ⁅g, m⁆ ∈ 𝐔₂ := by
    rw [← commutatorElement_inv]
    exact inv_mem (h.comm_M_E hm hg)
  rw [commutator_mul_right, mul_mem_cancel_left hc, h.conj_U₂_iff (h.M_le_S hm)]

omit [Finite G] [Finite K] in
theorem comm_u_iff (a b c d A B C D : K) :
    ⁅𝐮[a, b, c, d], 𝐮[A, B, C, D]⁆ ∈ 𝐔₂ ↔ a * D + A * d = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [commutatorElement_def, u_inv, u_inv, u_mul, u_mul, u_mul, u_mem_U₂_iff]
  constructor
  · rintro ⟨-, hb, -⟩
    linear_combination hb - (b + B + a * D + a * d + A * D) * h2
  · intro hd
    exact ⟨by linear_combination (a + A) * h2,
      by linear_combination hd + (b + B + a * D + a * d + A * D) * h2,
      by linear_combination (d + D) * h2⟩

theorem piE_mul_u (h : OvHyp L K n φ TG t M) {m : G} (hm : m ∈ M) (a b c d : K) :
    piE φ M (m * 𝐮[a, b, c, d]) = (a, d) :=
  piE_eq (fun _ hx hxP => h.M_inf_P.le ⟨hx, hxP⟩) hm a b c d

theorem piE_u (h : OvHyp L K n φ TG t M) (a b c d : K) : piE φ M 𝐮[a, b, c, d] = (a, d) := by
  simpa using h.piE_mul_u (one_mem M) a b c d

theorem piE_mul (h : OvHyp L K n φ TG t M) {e e' : G} (he : e ∈ 𝐄) (he' : e' ∈ 𝐄) :
    piE φ M (e * e') = piE φ M e + piE φ M e' := by
  obtain ⟨m, hm, a, b, c, d, rfl⟩ := h.exists_dec he
  obtain ⟨m', hm', A, B, C, D, rfl⟩ := h.exists_dec he'
  have hc : 𝐮[a, b, c, d] * m' * (𝐮[a, b, c, d])⁻¹ ∈ M :=
    (mem_normalizer_iff.mp (h.P_le_N (u_mem_P a b c d)) m').mp hm'
  have e : m * 𝐮[a, b, c, d] * (m' * 𝐮[A, B, C, D]) =
      (m * (𝐮[a, b, c, d] * m' * (𝐮[a, b, c, d])⁻¹)) * (𝐮[a, b, c, d] * 𝐮[A, B, C, D]) := by
    group
  rw [e, u_mul, h.piE_mul_u (mul_mem hm hc), h.piE_mul_u hm, h.piE_mul_u hm', Prod.mk_add_mk]

theorem piE_eq_zero_iff (h : OvHyp L K n φ TG t M) {e : G} (he : e ∈ 𝐄) :
    piE φ M e = 0 ↔ e ∈ M := by
  obtain ⟨m, hm, a, b, c, d, rfl⟩ := h.exists_dec he
  rw [h.piE_mul_u hm, Prod.mk_eq_zero]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact mul_mem hm (h.comp.ZP_le (u_mem_Z_iff.mpr ⟨rfl, rfl⟩))
  · intro hx
    have hu : 𝐮[a, b, c, d] ∈ 𝐙 := h.M_inf_P.le ⟨by simpa using mul_mem (inv_mem hm) hx,
      u_mem_P a b c d⟩
    exact u_mem_Z_iff.mp hu

theorem piE_fst_eq_zero_iff (h : OvHyp L K n φ TG t M) {e : G} (he : e ∈ 𝐄) :
    (piE φ M e).1 = 0 ↔ e ∈ 𝐌₁ := by
  constructor
  · intro h0
    obtain ⟨m, hm, a, b, c, d, rfl⟩ := h.exists_dec he
    rw [h.piE_mul_u hm] at h0
    exact mul_mem (mem_sup_left hm) (mem_sup_right (u_mem_A₁_iff.mpr h0))
  · intro hx
    rw [← SetLike.mem_coe, h.coe_M₁] at hx
    obtain ⟨m, hm, a, ha, rfl⟩ := hx
    obtain ⟨b, c, d, rfl⟩ := exists_u_eq_of_A₁ ha
    rw [h.piE_mul_u hm]

theorem piE_snd_of_mem_M₀ (h : OvHyp L K n φ TG t M) {e : G} (he : e ∈ 𝐌₀) :
    e ∈ 𝐄 ∧ (piE φ M e).2 = 0 := by
  have hA₂ : 𝐀₂ ≤ 𝐏 := pull_mono φ (rootA_le_antiUnipotent Axis.two)
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left M 𝐀₂ (hA₂.trans h.P_le_N)] at he
  obtain ⟨m, hm, a, ha, rfl⟩ := he
  obtain ⟨a, b, c, rfl⟩ := exists_u_eq_of_A₂ ha
  exact ⟨mul_mem (mem_sup_left hm) (mem_sup_right (u_mem_P _ _ _ _)), by rw [h.piE_mul_u hm]⟩

theorem comm_E_iff (h : OvHyp L K n φ TG t M) {e e' : G} (he : e ∈ 𝐄) (he' : e' ∈ 𝐄) :
    ⁅e, e'⁆ ∈ 𝐔₂ ↔ (piE φ M e).1 * (piE φ M e').2 + (piE φ M e').1 * (piE φ M e).2 = 0 := by
  obtain ⟨m, hm, a, b, c, d, rfl⟩ := h.exists_dec he
  obtain ⟨m', hm', A, B, C, D, rfl⟩ := h.exists_dec he'
  rw [h.piE_mul_u hm, h.piE_mul_u hm', h.comm_left_iff hm he',
    h.comm_right_iff (mem_sup_right (u_mem_P a b c d)) hm', comm_u_iff]

omit [Finite G] [Finite K] in
theorem M₁_le_E : 𝐌₁ ≤ 𝐄 :=
  sup_le le_sup_left ((pull_mono φ (rootA_le_antiUnipotent Axis.one)).trans le_sup_right)

theorem card_M₀ (h : OvHyp L K n φ TG t M) : Nat.card 𝐌₀ = (2 ^ n) ^ 4 := by
  have hA₂ : 𝐀₂ ≤ normalizer (M : Set G) :=
    (pull_mono φ (rootA_le_antiUnipotent Axis.two)).trans h.P_le_N
  have h1 := card_sup_mul_card_inf (A := 𝐀₂) (N := M) hA₂
  rw [sup_comm, inf_comm, h.inf_eq_Z (pull_le φ _) ZP_le_A₂, h.card_M,
    card_pull φ (rootA K Axis.two), FullCenter.card_rootA, card_pull φ (antiUnipotentCenter K),
    (card_radicals (K := K)).2.2.2, h.two.card_K] at h1
  have hpos : 0 < (2 ^ n) ^ 2 := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1]; ring)

end E

section Normal

theorem mem_Z_of_comm_t (h : OvHyp L K n φ TG t M) {y : G} (hy : y ∈ M) (hyt : ⁅t, y⁆ ∈ 𝐔₂) :
    y ∈ 𝐙 := by
  have h1 : ⁅t, y⁆ ∈ 𝐔₁ := by
    have := h.heis.conj₁ y⁻¹ (inv_mem (h.M_le_D₁ hy))
    rw [inv_inv, h.two.t_inv] at this
    rwa [commutatorElement_def, h.two.t_inv, show t * y * t * y⁻¹ = t * (y * t * y⁻¹) by group]
  have h2 : ⁅t, y⁆ = 1 := by
    have := mem_inf.mpr ⟨h1, hyt⟩
    rwa [FullCenterTorus.U_inf_U, mem_bot] at this
  exact h.mem_Z_of_comm hy (commutatorElement_eq_one_iff_mul_comm.mp h2).symm

theorem le_E (h : OvHyp L K n φ TG t M) {X : Subgroup G} (hXR : X ≤ 𝐑)
    (hX : ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ 𝐔₂) (hcard : (2 ^ n) ^ 4 ≤ Nat.card X) : X ≤ 𝐄 := by
  by_contra hle
  obtain ⟨x₁, hx₁X, hx₁E⟩ := Set.not_subset.mp hle
  have he₁ : t * x₁ ∈ 𝐄 := (mem_or_mul_mem h.two.t_mul_t h.t_mem_N_E
    (h.E_sup_t.ge (hXR hx₁X))).resolve_left hx₁E
  have htS : t ∈ 𝐒 := mem_sup_left (t_mem_Q h.heis)
  have hXM : X ⊓ M ≤ 𝐙 := by
    intro y hy
    obtain ⟨hyX, hyM⟩ := mem_inf.mp hy
    refine h.mem_Z_of_comm_t hyM ?_
    have h2 : t * ⁅t * x₁, y⁆ * t⁻¹ ∈ 𝐔₂ := by
      rw [h.conj_U₂_iff htS, ← commutatorElement_inv]
      exact inv_mem (h.comm_M_E hyM he₁)
    have h1 := hX x₁ hx₁X y hyX
    have e : x₁ = t * (t * x₁) := by rw [← mul_assoc, h.two.t_mul_t, one_mul]
    rw [e, commutator_mul_left, mul_mem_cancel_left h2] at h1
    exact h1
  have hq : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two.two_le
  have hYc : Nat.card (X ⊓ 𝐄 ⊓ M : Subgroup G) ≤ (2 ^ n) ^ 2 := by
    have := card_le_of_le (fun y hy => hXM (mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hy).1).1,
      (mem_inf.mp hy).2⟩) : X ⊓ 𝐄 ⊓ M ≤ 𝐙)
    rwa [card_pull, (card_radicals (K := K)).2.2.2, h.two.card_K] at this
  have hadd : ∀ x ∈ X ⊓ 𝐄, ∀ y ∈ X ⊓ 𝐄, piE φ M (x * y) = piE φ M x + piE φ M y :=
    fun x hx y hy => h.piE_mul (mem_inf.mp hx).2 (mem_inf.mp hy).2
  have hcount : Nat.card (X ⊓ 𝐄 : Subgroup G) ≤ (2 ^ n) ^ 2 * 2 ^ n := by
    have hK : Nat.card K = 2 ^ n := h.two.card_K
    by_cases hall : ∀ y ∈ X ⊓ 𝐄, piE φ M y = 0
    · have hle' : X ⊓ 𝐄 ≤ M := fun y hy => (h.piE_eq_zero_iff (mem_inf.mp hy).2).mp (hall y hy)
      calc Nat.card (X ⊓ 𝐄 : Subgroup G) = Nat.card (X ⊓ 𝐄 ⊓ M : Subgroup G) := by
            rw [inf_of_le_left hle']
        _ ≤ (2 ^ n) ^ 2 := hYc
        _ ≤ (2 ^ n) ^ 2 * 2 ^ n := Nat.le_mul_of_pos_right _ (by positivity)
    · push Not at hall
      obtain ⟨y₀, hy₀, hne⟩ := hall
      have hy₀E := (mem_inf.mp hy₀).2
      have hdet : ∀ x ∈ X ⊓ 𝐄, (piE φ M y₀).1 * (piE φ M x).2 +
          (piE φ M x).1 * (piE φ M y₀).2 = 0 := fun x hx =>
        (h.comm_E_iff hy₀E (mem_inf.mp hx).2).mp (hX y₀ (mem_inf.mp hy₀).1 x (mem_inf.mp hx).1)
      by_cases ha₀ : (piE φ M y₀).1 = 0
      · have hd₀ : (piE φ M y₀).2 ≠ 0 := fun hd => hne (Prod.ext ha₀ hd)
        have hc := (card_le_of_coord (X := X ⊓ 𝐄) (Y := M) (fun g => (piE φ M g).2)
          (fun x hx y hy => by rw [hadd x hx y hy]; rfl) fun x hx hx0 => ?_).1
        · rw [hK] at hc
          exact hc.trans (Nat.mul_le_mul_right _ hYc)
        · have h1 := hdet x hx
          rw [ha₀, hx0, zero_mul, zero_add] at h1
          have hx1 : (piE φ M x).1 = 0 := (mul_eq_zero.mp h1).resolve_right hd₀
          exact (h.piE_eq_zero_iff (mem_inf.mp hx).2).mp (Prod.ext hx1 hx0)
      · have hc := (card_le_of_coord (X := X ⊓ 𝐄) (Y := M) (fun g => (piE φ M g).1)
          (fun x hx y hy => by rw [hadd x hx y hy]; rfl) fun x hx hx0 => ?_).1
        · rw [hK] at hc
          exact hc.trans (Nat.mul_le_mul_right _ hYc)
        · have h1 := hdet x hx
          rw [hx0, zero_mul, add_zero] at h1
          have hx2 : (piE φ M x).2 = 0 := (mul_eq_zero.mp h1).resolve_left ha₀
          exact (h.piE_eq_zero_iff (mem_inf.mp hx).2).mp (Prod.ext hx0 hx2)
  have h1 := card_le_two_mul h.card_R.2 hXR
  rw [inf_comm] at h1
  have h3 : 0 < (2 ^ n) ^ 3 := by positivity
  have h4 : (2 ^ n) ^ 4 = 2 ^ n * (2 ^ n) ^ 3 := by ring
  have h5 : (2 ^ n) ^ 2 * 2 ^ n = (2 ^ n) ^ 3 := by ring
  nlinarith

theorem conj_E (h : OvHyp L K n φ TG t M) {s : G} (hs : s ∈ 𝐒) {e : G} (he : e ∈ 𝐄) :
    s * e * s⁻¹ ∈ 𝐄 := by
  have hconj : ∀ X : Subgroup G, X ≤ 𝐑 → (∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ 𝐔₂) →
      Nat.card X = (2 ^ n) ^ 4 → X.map (MulAut.conj s).toMonoidHom ≤ 𝐄 := by
    intro X hXR hXc hXcard
    refine h.le_E ?_ ?_ (by rw [card_map_conj, hXcard])
    · rintro _ ⟨x, hx, rfl⟩
      exact h.conj_R hs (hXR hx)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show ⁅s * x * s⁻¹, s * y * s⁻¹⁆ = s * ⁅x, y⁆ * s⁻¹ by
        simp only [commutatorElement_def]; group, h.conj_U₂_iff hs]
      exact hXc x hx y hy
  have h₁ := hconj 𝐌₁ (h.M₁_le_D₁.trans le_sup_right) (fun x hx y hy => by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (h.comm_M₁ hx hy)]
    exact one_mem _) h.card_M₁
  have h₀ := hconj 𝐌₀ (sup_le (h.M_le_D₁.trans le_sup_right)
    (le_sup_right.trans ((h.heis.hyp.B_le_Q Axis.two).trans le_sup_left)))
    (fun x hx y hy => (h.comm_E_iff (h.piE_snd_of_mem_M₀ hx).1 (h.piE_snd_of_mem_M₀ hy).1).mpr
      (by rw [(h.piE_snd_of_mem_M₀ hx).2, (h.piE_snd_of_mem_M₀ hy).2]; ring)) h.card_M₀
  have hE : 𝐄 ≤ 𝐌₁ ⊔ 𝐌₀ := by
    refine sup_le (le_sup_left.trans le_sup_left) ?_
    rw [P_eq]
    exact sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right)
  exact ((map_sup 𝐌₁ 𝐌₀ (MulAut.conj s).toMonoidHom).le.trans (sup_le h₁ h₀)) ⟨e, hE he, rfl⟩

theorem conj_M (h : OvHyp L K n φ TG t M) {s : G} (hs : s ∈ 𝐒) {m : G} (hm : m ∈ M) :
    s * m * s⁻¹ ∈ M := by
  have hx : s * m * s⁻¹ ∈ 𝐄 := h.conj_E hs (mem_sup_left hm)
  have hc : ∀ e ∈ 𝐄, ⁅s * m * s⁻¹, e⁆ ∈ 𝐔₂ := by
    intro e he
    have he' : s⁻¹ * e * s ∈ 𝐄 := by simpa using h.conj_E (inv_mem hs) he
    rw [show ⁅s * m * s⁻¹, e⁆ = s * ⁅m, s⁻¹ * e * s⁆ * s⁻¹ by
      simp only [commutatorElement_def]; group, h.conj_U₂_iff hs]
    exact h.comm_M_E hm he'
  have hP : ∀ a b c d : K, 𝐮[a, b, c, d] ∈ 𝐄 := fun a b c d => mem_sup_right (u_mem_P a b c d)
  have e1 := (h.comm_E_iff hx (hP 1 0 0 0)).mp (hc _ (hP 1 0 0 0))
  have e2 := (h.comm_E_iff hx (hP 0 0 0 1)).mp (hc _ (hP 0 0 0 1))
  rw [h.piE_u] at e1 e2
  simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] at e1 e2
  exact (h.piE_eq_zero_iff hx).mp (Prod.ext e2 e1)

theorem conj_M₁ (h : OvHyp L K n φ TG t M) {s : G} (hs : s ∈ 𝐒) {x : G} (hx : x ∈ 𝐌₁) :
    s * x * s⁻¹ ∈ 𝐌₁ := by
  by_contra hnot
  have hXE : 𝐌₁.map (MulAut.conj s).toMonoidHom ≤ 𝐄 := by
    rintro _ ⟨y, hy, rfl⟩
    exact h.conj_E hs (M₁_le_E hy)
  have hMX : M ≤ 𝐌₁.map (MulAut.conj s).toMonoidHom := by
    intro m hm
    refine ⟨s⁻¹ * m * s, mem_sup_left (by simpa using h.conj_M (inv_mem hs) hm), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hXc : ∀ a ∈ 𝐌₁.map (MulAut.conj s).toMonoidHom,
      ∀ b ∈ 𝐌₁.map (MulAut.conj s).toMonoidHom, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h.comm_M₁ ha hb]
  have hy₀ : s * x * s⁻¹ ∈ 𝐌₁.map (MulAut.conj s).toMonoidHom := ⟨x, hx, rfl⟩
  have ha₀ : (piE φ M (s * x * s⁻¹)).1 ≠ 0 :=
    fun h0 => hnot ((h.piE_fst_eq_zero_iff (hXE hy₀)).mp h0)
  have hker : ∀ a ∈ 𝐌₁.map (MulAut.conj s).toMonoidHom, (piE φ M a).1 = 0 → a ∈ M := by
    intro a ha ha0
    have h1 := (h.comm_E_iff (hXE hy₀) (hXE ha)).mp (by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hXc _ hy₀ a ha)]
      exact one_mem _)
    rw [ha0, zero_mul, add_zero] at h1
    exact (h.piE_eq_zero_iff (hXE ha)).mp
      (Prod.ext ha0 ((mul_eq_zero.mp h1).resolve_left ha₀))
  have hcard : Nat.card (𝐌₁.map (MulAut.conj s).toMonoidHom ⊓ M : Subgroup G) * Nat.card K ≤
      Nat.card (𝐌₁.map (MulAut.conj s).toMonoidHom) := by
    rw [inf_of_le_right hMX, card_map_conj, h.card_M, h.card_M₁, h.two.card_K]
    exact le_of_eq (by ring)
  have hsurj := (card_le_of_coord (X := 𝐌₁.map (MulAut.conj s).toMonoidHom) (Y := M)
    (fun g => (piE φ M g).1) (fun a ha b hb => by rw [h.piE_mul (hXE ha) (hXE hb)]; rfl)
    hker).2 hcard
  have hcomm : ∀ m ∈ M, ∀ e ∈ 𝐄, m * e = e * m := by
    intro m hm e he
    obtain ⟨x', hx'X, hx'⟩ := hsurj (piE φ M e).1
    have hx'E := hXE hx'X
    have hex : e * x'⁻¹ ∈ 𝐌₁ := by
      have h1 := h.piE_mul (mul_mem he (inv_mem hx'E)) hx'E
      rw [inv_mul_cancel_right] at h1
      have h2 := congrArg Prod.fst h1
      rw [Prod.fst_add, ← hx'] at h2
      exact (h.piE_fst_eq_zero_iff (mul_mem he (inv_mem hx'E))).mp
        (by linear_combination -h2)
    have c1 := h.comm_M₁ (mem_sup_left hm) hex
    have c2 := hXc m (hMX hm) x' hx'X
    calc m * e = m * (e * x'⁻¹) * x' := by group
      _ = e * x'⁻¹ * m * x' := by rw [c1]
      _ = e * x'⁻¹ * (x' * m) := by rw [mul_assoc, c2]
      _ = e * m := by group
  have hD : 𝐃₂ ≤ centralizer ({𝐮[1, 0, 0, 0]} : Set G) := by
    rw [← h.M₂_sup_t]
    refine sup_le (sup_le (fun m hm => mem_centralizer_singleton_iff.mpr
      (hcomm m hm _ (mem_sup_right (u_mem_P 1 0 0 0)))) (fun y hy => ?_))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (h.two.comm (pull_le φ _
        (u_mem_P 1 0 0 0)))))
    rw [mem_centralizer_singleton_iff]
    have c := hcomm _ (mem_map_conj_inv_iff.mp hy) _ (mem_sup_right (u_mem_P 0 1 0 0))
    rw [← w₂_conj 1 0 0] at c
    have e : 𝐰₂ * (y * 𝐮[1, 0, 0, 0]) * 𝐰₂⁻¹ = 𝐰₂ * (𝐮[1, 0, 0, 0] * y) * 𝐰₂⁻¹ := by
      calc 𝐰₂ * (y * 𝐮[1, 0, 0, 0]) * 𝐰₂⁻¹ =
          (𝐰₂ * y * 𝐰₂⁻¹) * (𝐰₂ * 𝐮[1, 0, 0, 0] * 𝐰₂⁻¹) := by group
        _ = (𝐰₂ * 𝐮[1, 0, 0, 0] * 𝐰₂⁻¹) * (𝐰₂ * y * 𝐰₂⁻¹) := c
        _ = 𝐰₂ * (𝐮[1, 0, 0, 0] * y) * 𝐰₂⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  have hZ : 𝐮[1, 0, 0, 0] ∈ 𝐔₂ := (center_D₂ h.heis).le (mem_center_map_iff.mpr
    ⟨A₂_le_D₂ h.heis (u_mem_A₂_iff.mpr rfl), fun y hy => mem_centralizer_singleton_iff.mp (hD hy)⟩)
  exact one_ne_zero (u_mem_U₂_iff.mp hZ).1

end Normal

section Elementary

omit [Finite G] [Finite K] in
theorem isElementaryAbelian_of {F : Subgroup G} (hc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x)
    (hs : ∀ x ∈ F, x * x = 1) : IsElementaryAbelian 2 F :=
  CFSG.IsElementaryAbelian.two_of_forall_mul_self hc hs

theorem sq_M₁ (h : OvHyp L K n φ TG t M) {x : G} (hx : x ∈ 𝐌₁) : x * x = 1 := by
  obtain ⟨-, -, c, -, -, hc0, hc1⟩ := h.comp.square_map h.heis
  have hdec : ∀ x ∈ 𝐌₁, ∃ y ∈ 𝐇, ∃ a ∈ 𝐀₁, x = y * a := by
    intro x hx
    rw [← SetLike.mem_coe, h.coe_M₁] at hx
    obtain ⟨m, hm, a, ha, rfl⟩ := hx
    have hm' : m ∈ (𝐇 : Set G) * (𝐔₂ : Set G) := by rw [h.comp.H_mul_U₂ h.heis]; exact hm
    obtain ⟨y, hy, u, hu, rfl⟩ := hm'
    refine ⟨y, hy, u * a, mul_mem (ZP_le_A₁ (U₂_le_ZP hu)) ha, ?_⟩
    show y * u * a = y * (u * a)
    group
  have haa : ∀ a ∈ 𝐀₁, a * a = 1 := fun a ha =>
    h.heis.hyp.mul_self_of_mem_B Axis.one (mem_sup_right ha)
  have hsq : ∀ y ∈ 𝐇, ∀ a ∈ 𝐀₁, (y * a) * (y * a) = y * y := by
    intro y hy a ha
    have hya : y * a = a * y := h.comm_A₁ (h.M_le_D₁ (mem_inf.mp hy).1) ha
    calc y * a * (y * a) = y * (a * y) * a := by group
      _ = y * (y * a) * a := by rw [hya]
      _ = y * y * (a * a) := by group
      _ = y * y := by rw [haa a ha, mul_one]
  by_cases hc : c = 0
  · obtain ⟨hE, -⟩ := hc0 hc
    obtain ⟨y, hy, a, ha, rfl⟩ := hdec x hx
    rw [hsq y hy a ha, ← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian y hy
  · exfalso
    obtain ⟨-, -, hset, -⟩ := hc1 hc
    have hΩ : ∀ x ∈ 𝐌₁, x * x = 1 → x ∈ 𝐀₁ := by
      intro x hx hxx
      obtain ⟨y, hy, a, ha, rfl⟩ := hdec x hx
      rw [hsq y hy a ha] at hxx
      have hyU : y ∈ 𝐔₁ := by
        have : y ∈ {x : G | x ∈ 𝐇 ∧ x * x = 1} := ⟨hy, hxx⟩
        rw [hset] at this
        exact this
      exact mul_mem (ZP_le_A₁ (U₁_le_ZP hyU)) ha
    have hN : 𝐒 ≤ normalizer (𝐀₁ : Set G) := fun s hs => mem_normalizer_of_conj_le fun a ha => by
      refine hΩ _ (h.conj_M₁ hs (mem_sup_right ha)) ?_
      calc s * a * s⁻¹ * (s * a * s⁻¹) = s * (a * a) * s⁻¹ := by group
        _ = 1 := by rw [haa a ha]; group
    have hlt : 𝐙 < 𝐀₁ := lt_of_le_of_ne ZP_le_A₁ fun e => by
      have : 𝐮[0, 0, 0, 1] ∈ 𝐙 := e ▸ u_mem_A₁_iff.mpr rfl
      exact one_ne_zero (u_mem_Z_iff.mp this).2
    have hSR := normalizer_le_A₁ h.heis hlt le_rfl
    obtain ⟨s, hs, hs1⟩ := h.heis.exists_mem_S_hAct 1 0 0
    exact one_ne_zero ((h.heis.mem_R_iff hs hs1).mp (hSR.le (mem_inf.mpr ⟨hs, hN hs⟩)))

theorem elementary_M₁ (h : OvHyp L K n φ TG t M) : IsElementaryAbelian 2 𝐌₁ :=
  isElementaryAbelian_of (fun _ hx _ hy => h.comm_M₁ hx hy) fun _ hx => h.sq_M₁ hx

theorem comm_B₁ (h : OvHyp L K n φ TG t M) {x y : G} (hx : x ∈ 𝐁₁) (hy : y ∈ 𝐁₁) :
    x * y = y * x := by
  have hxD := B₁_le_D₁ h.heis hx
  rcases (mem_zpowers_sup_iff h.two.t_mul_t (TwoCoreSetup.comm_pull φ h.two)).mp hy with
    hy' | hy'
  · exact h.comm_A₁ hxD hy'
  · have c1 := h.comm_A₁ hxD hy'
    have hxC : x ∈ 𝐂 := (sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
      ((pull_le φ _).trans h.two.L_le) : 𝐁₁ ≤ 𝐂) hx
    have c2 : x * t = t * x := mem_centralizer_singleton_iff.mp hxC
    have e : y = t * (t * y) := by rw [← mul_assoc, h.two.t_mul_t, one_mul]
    rw [e]
    calc x * (t * (t * y)) = (x * t) * (t * y) := by group
      _ = t * (x * (t * y)) := by rw [c2]; group
      _ = t * (t * y) * x := by rw [c1]; group

theorem elementary_B₁ (h : OvHyp L K n φ TG t M) : IsElementaryAbelian 2 𝐁₁ :=
  isElementaryAbelian_of (fun _ hx _ hy => h.comm_B₁ hx hy) fun _ hx =>
    h.heis.hyp.mul_self_of_mem_B Axis.one hx

theorem le_B₁_or_le_M₁ (h : OvHyp L K n φ TG t M) {F : Subgroup G} (hFD : F ≤ 𝐃₁)
    (hF : IsElementaryAbelian 2 F) : F ≤ 𝐁₁ ∨ F ≤ 𝐌₁ := by
  by_cases hle : F ≤ 𝐌₁
  · exact Or.inr hle
  · left
    obtain ⟨f, hfF, hfM⟩ := Set.not_subset.mp hle
    have hFsq : ∀ x ∈ F, x * x = 1 := fun x hx => by
      rw [← pow_two]
      exact elemPow_eq_one_of_isElementaryAbelian x hx
    have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hF.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have htm : ∀ y ∈ F, y ∉ 𝐌₁ → t * y ∈ 𝐌₁ := fun y hyF hyM =>
      (mem_or_mul_mem h.two.t_mul_t h.t_mem_N_M₁ (h.M₁_sup_t.ge (hFD hyF))).resolve_left hyM
    have hout : ∀ y ∈ F, y ∉ 𝐌₁ → y ∈ 𝐁₁ := by
      intro y hyF hyM
      have hm := htm y hyF hyM
      have hyt : y * t = t * y := by
        have e1 := h.sq_M₁ hm
        calc y * t = (t * t) * y * t * (y * y) := by rw [h.two.t_mul_t, hFsq y hyF]; group
          _ = t * (t * y * (t * y)) * y := by group
          _ = t * y := by rw [e1]; group
      have hA := h.mem_A₁_of_comm hm (by rw [mul_assoc, ← hyt, ← mul_assoc])
      rw [show y = t * (t * y) by rw [← mul_assoc, h.two.t_mul_t, one_mul]]
      exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right hA)
    intro y hyF
    by_cases hyM : y ∈ 𝐌₁
    · have hm := htm f hfF hfM
      have e1 := hFc y hyF f hfF
      have e2 := h.comm_M₁ hyM hm
      have hyt : y * t = t * y := mul_right_cancel (b := f) (by
        calc y * t * f = y * (t * f) := by group
          _ = t * f * y := e2
          _ = t * (f * y) := by group
          _ = t * (y * f) := by rw [← e1]
          _ = t * y * f := by group)
      exact mem_sup_right (h.mem_A₁_of_comm hyM hyt)
    · exact hout y hyF hyM

theorem not_M₁_le_B₁ (h : OvHyp L K n φ TG t M) : ¬ 𝐌₁ ≤ 𝐁₁ := by
  intro hle
  have h1 := card_le_of_le hle
  have h2 : Nat.card 𝐁₁ = 2 * (2 ^ n) ^ 3 := by
    rw [card_sup_of_commute (fun y hy z hz => h.two.zpowers_comm hy (pull_le φ _ hz))
      (h.two.zpowers_inf (pull_le φ _)), Nat.card_zpowers, h.heis.hyp.setup.order_t, card_pull,
      FullCenter.card_rootA, h.two.card_K]
  rw [h.card_M₁, h2] at h1
  have hq : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two.two_le
  have h3 : 0 < (2 ^ n) ^ 3 := by positivity
  have h4 : (2 ^ n) ^ 4 = 2 ^ n * (2 ^ n) ^ 3 := by ring
  nlinarith

theorem maximal_iff (h : OvHyp L K n φ TG t M) (F : Subgroup G) :
    Maximal (fun F : Subgroup G => F ≤ 𝐃₁ ∧ IsElementaryAbelian 2 F) F ↔ F = 𝐁₁ ∨ F = 𝐌₁ := by
  have hB : 𝐁₁ ≤ 𝐃₁ ∧ IsElementaryAbelian 2 𝐁₁ := ⟨B₁_le_D₁ h.heis, h.elementary_B₁⟩
  have hM : 𝐌₁ ≤ 𝐃₁ ∧ IsElementaryAbelian 2 𝐌₁ := ⟨h.M₁_le_D₁, h.elementary_M₁⟩
  have hBM : ¬ 𝐁₁ ≤ 𝐌₁ := fun hle => h.t_not_mem_M₁ (hle (mem_sup_left (mem_zpowers t)))
  constructor
  · rintro ⟨⟨hFD, hFel⟩, hmax⟩
    rcases h.le_B₁_or_le_M₁ hFD hFel with hle | hle
    · exact Or.inl (le_antisymm hle (hmax hB hle))
    · exact Or.inr (le_antisymm hle (hmax hM hle))
  · rintro (rfl | rfl)
    · refine ⟨hB, fun F hF hle => ?_⟩
      rcases h.le_B₁_or_le_M₁ hF.1 hF.2 with h1 | h1
      · exact h1
      · exact absurd (hle.trans h1) hBM
    · refine ⟨hM, fun F hF hle => ?_⟩
      rcases h.le_B₁_or_le_M₁ hF.1 hF.2 with h1 | h1
      · exact absurd (hle.trans h1) h.not_M₁_le_B₁
      · exact h1

theorem normalizer_B₁_eq (h : OvHyp L K n φ TG t M) :
    normalizer (𝐁₁ : Set G) = normalizer (𝐃₁ : Set G) := by
  refine le_antisymm le_normalizer_pCore_map fun g hg => ?_
  have hgM := h.normalizer_D₁_le hg
  have hFD : 𝐁₁.map (MulAut.conj g).toMonoidHom ≤ 𝐃₁ := by
    rintro _ ⟨b, hb, rfl⟩
    exact (mem_normalizer_iff.mp hg b).mp (B₁_le_D₁ h.heis hb)
  have hFel : IsElementaryAbelian 2 (𝐁₁.map (MulAut.conj g).toMonoidHom) := by
    refine isElementaryAbelian_of ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, h.comm_B₁ ha hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, h.heis.hyp.mul_self_of_mem_B Axis.one ha, map_one]
  rcases h.le_B₁_or_le_M₁ hFD hFel with h1 | h1
  · exact mem_normalizer_of_conj_le fun b hb => h1 ⟨b, hb, rfl⟩
  · exfalso
    apply h.t_not_mem_M₁
    exact (mem_normalizer_iff.mp hgM t).mpr (h1 ⟨t, mem_sup_left (mem_zpowers t), rfl⟩)

end Elementary

end OvHyp

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G}

theorem main (hh : HeisHyp L K n φ TG t) (PG Q ZP : Subgroup G)
    (hPG : PG = pull φ (antiUnipotent K)) (hQ : Q = PG ⊔ TG)
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
    let R := Q ⊔ D₁
    let S := Q ⊔ D₂
    let D := D₁ ⊓ D₂
    let J₀ := pull φ (diagTorus K)
    let Ja := pull φ (FullCenterTorus.axisTorus K Axis.one)
    let w₁ : G := ((φ.symm (weylElt₁ K) : L) : G)
    let w₂ : G := ((φ.symm (weylElt₂ K) : L) : G)
    let IsComp : Subgroup G → Prop := fun M => M ≤ D ∧ J₀ ≤ normalizer (M : Set G) ∧
      Nat.card M = (2 ^ n) ^ 3 ∧ ZP ≤ M ∧ (M.subgroupOf D).Normal ∧ M ⊓ zpowers t = ⊥ ∧
      M ⊔ zpowers t = D ∧ M ⊓ (zpowers t ⊔ ZP) = ZP
    (∃ M : Subgroup G, IsComp M) ∧
    ∀ M : Subgroup G, IsComp M →
      let H := M ⊓ centralizer (Ja : Set G)
      let Mw₁ := M.map (MulAut.conj w₁⁻¹).toMonoidHom
      let Mw₂ := M.map (MulAut.conj w₂⁻¹).toMonoidHom
      let M₁ := M ⊔ Mw₁
      let M₂ := M ⊔ Mw₂
      let E := M ⊔ PG
      IsElementaryAbelian 2 M ∧
      ((M : Set G) * Mw₁ = M₁ ∧ (M : Set G) * Mw₂ = M₂ ∧ (M : Set G) * PG = E) ∧
      (H ⊓ U₂ = ⊥ ∧ (∀ x ∈ H, ∀ y ∈ U₂, x * y = y * x) ∧ (H : Set G) * U₂ = M) ∧
      Nat.card H = (2 ^ n) ^ 2 ∧ H ⊓ C = U₁ ∧
      {x : G | ∃ h ∈ H, x = t⁻¹ * (h⁻¹ * t * h)} = U₁ ∧
      M ⊓ Mw₁ = H ∧ M ⊓ Mw₂ = U₂ ∧
      (M₁ = M ⊔ A₁ ∧ (M : Set G) * A₁ = M₁ ∧ IsElementaryAbelian 2 M₁ ∧
        Nat.card M₁ = (2 ^ n) ^ 4 ∧ (M₁.subgroupOf D₁).Characteristic ∧
        (M₁ ≤ S ∧ (M₁.subgroupOf S).Normal) ∧
        ((M₁.subgroupOf D₁).Normal ∧ M₁ ⊓ zpowers t = ⊥ ∧ M₁ ⊔ zpowers t = D₁) ∧
        M₁ ⊓ B₁ = A₁) ∧
      (Nat.card M₂ = (2 ^ n) ^ 5 ∧ M₂.relIndex D₂ = 2 ∧
        ((M₂.subgroupOf D₂).Normal ∧ M₂ ⊓ zpowers t = ⊥ ∧ M₂ ⊔ zpowers t = D₂) ∧
        M₂ ⊓ B₂ = A₂) ∧
      M₁ ⊓ M₂ = M ∧
      (Nat.card E = (2 ^ n) ^ 5 ∧ (E ≤ S ∧ (E.subgroupOf S).Normal) ∧
        ((E.subgroupOf R).Normal ∧ E ⊓ zpowers t = ⊥ ∧ E ⊔ zpowers t = R)) ∧
      (∀ F : Subgroup G, Maximal (fun F : Subgroup G => F ≤ D₁ ∧ IsElementaryAbelian 2 F) F ↔
        F = B₁ ∨ F = M₁) ∧
      normalizer (B₁ : Set G) = normalizer (D₁ : Set G) ∧
      normalizer (D₁ : Set G) ≤ normalizer (M₁ : Set G) := by
  subst hQ hPG hZP
  intro C U₁ U₂ A₁ A₂ B₁ B₂ N₁ N₂ D₁ D₂ R S D J₀ Ja w₁ w₂ IsComp
  obtain ⟨-, -, -, -, -, hex, hall⟩ :=
    OneAxisComplement.main hh (pull φ (antiUnipotentCenter K)) rfl
  refine ⟨hex, fun M hM => ?_⟩
  intro H Mw₁ Mw₂ M₁ M₂ E
  obtain ⟨hHU, -, -, hHcard, ⟨-, hHC, hκ⟩, -⟩ := hall M hM
  obtain ⟨hMD, hMJ, -, hZM, -, -, hMt, hMZ⟩ := hM
  have h : OvHyp L K n φ TG t M := ⟨hh, ⟨hMD, hMJ, hZM, hMt, hMZ⟩⟩
  have hM₁ : M₁ = M ⊔ A₁ := h.sup_Mw₁
  have hM₁S : M ⊔ A₁ ≤ S := h.M₁_le_D₁.trans ((le_sup_right).trans hh.R_le_S)
  have hES : E ≤ S := h.E_le_R.trans hh.R_le_S
  refine ⟨OvHyp.isElementaryAbelian_of (fun _ hx _ hy => h.comm_M hx hy)
      fun _ hx => h.sq_M₁ (mem_sup_left hx),
    ⟨by rw [hM₁]; exact h.mul_Mw₁, h.coe_M₂.symm, h.coe_E.symm⟩, hHU, hHcard, hHC, hκ,
    h.M_inf_Mw₁, h.M_inf_Mw₂, ?_, ⟨h.card_M₂.1, h.card_M₂.2, ⟨h.normal_M₂,
      inf_zpowers_eq_bot h.two.t_mul_t h.t_not_mem_M₂, h.M₂_sup_t⟩, h.M₂_inf_B₂⟩,
    by rw [hM₁]; exact h.M₁_inf_M₂,
    ⟨h.card_E, ⟨hES, (normal_subgroupOf_iff hES).mpr fun _ _ he hs => h.conj_E hs he⟩,
      ⟨h.normal_E_R, inf_zpowers_eq_bot h.two.t_mul_t h.t_not_mem_E, h.E_sup_t⟩⟩,
    fun F => by rw [hM₁]; exact h.maximal_iff F, h.normalizer_B₁_eq,
    by rw [hM₁]; exact h.normalizer_D₁_le⟩
  rw [hM₁]
  exact ⟨rfl, h.coe_M₁.symm, h.elementary_M₁, h.card_M₁, h.characteristic_M₁,
    ⟨hM₁S, (normal_subgroupOf_iff hM₁S).mpr fun _ _ hx hs => h.conj_M₁ hs hx⟩,
    ⟨h.normal_M₁, inf_zpowers_eq_bot h.two.t_mul_t h.t_not_mem_M₁, h.M₁_sup_t⟩, h.M₁_inf_B₁⟩

end Main

end OneAxisOvergroup

open Subgroup GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
open FullCenterTorus (axisTorus)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.PartOne.KCRootAxis
open scoped Pointwise

theorem standard_symplectic_four_one_axis_elementary_overgroup_normalizer
    {G : Type} [Group G] [Finite G] (hO : CFSG.Open.standardComponentOddCore G = ⊥)
    {L : Subgroup G} (hL : CFSG.Open.standardComponentIsStandard L) (hLn : ¬ L.Normal)
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htT : t ∈ T) (ht : orderOf t = 2)
    (hcore : CFSG.Open.standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥)
    (P : Sylow 2 L) (φ : L ≃* antiSp K)
    (hφP : (P : Subgroup L).map φ.toMonoidHom = antiUnipotent K) :
    let TG := (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    let PG := (P : Subgroup L).map L.subtype
    let Q := PG ⊔ TG
    let ZP := (center PG).map PG.subtype
    let C := centralizer ({(t : G)} : Set G)
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
    let R := Q ⊔ D₁
    let S := Q ⊔ D₂
    let D := D₁ ⊓ D₂
    let J₀ := ((diagTorus K).comap φ.toMonoidHom).map L.subtype
    let Ja := ((axisTorus K Axis.one).comap φ.toMonoidHom).map L.subtype
    let w₁ : G := ((φ.symm (OneAxisOvergroup.weylElt₁ K) : L) : G)
    let w₂ : G := ((φ.symm (OneAxisOvergroup.weylElt₂ K) : L) : G)
    let IsComp : Subgroup G → Prop := fun M => M ≤ D ∧ J₀ ≤ normalizer (M : Set G) ∧
      Nat.card M = (2 ^ n) ^ 3 ∧ ZP ≤ M ∧ (M.subgroupOf D).Normal ∧ M ⊓ zpowers (t : G) = ⊥ ∧
      M ⊔ zpowers (t : G) = D ∧ M ⊓ (zpowers (t : G) ⊔ ZP) = ZP
    {x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ u ∈ U₁, x = t * u} →
      (∃ M : Subgroup G, IsComp M) ∧
      ∀ M : Subgroup G, IsComp M →
        let H := M ⊓ centralizer (Ja : Set G)
        let Mw₁ := M.map (MulAut.conj w₁⁻¹).toMonoidHom
        let Mw₂ := M.map (MulAut.conj w₂⁻¹).toMonoidHom
        let M₁ := M ⊔ Mw₁
        let M₂ := M ⊔ Mw₂
        let E := M ⊔ PG
        IsElementaryAbelian 2 M ∧
        ((M : Set G) * Mw₁ = M₁ ∧ (M : Set G) * Mw₂ = M₂ ∧ (M : Set G) * PG = E) ∧
        (H ⊓ U₂ = ⊥ ∧ (∀ x ∈ H, ∀ y ∈ U₂, x * y = y * x) ∧ (H : Set G) * U₂ = M) ∧
        Nat.card H = (2 ^ n) ^ 2 ∧ H ⊓ C = U₁ ∧
        {x : G | ∃ h ∈ H, x = (t : G)⁻¹ * (h⁻¹ * t * h)} = U₁ ∧
        M ⊓ Mw₁ = H ∧ M ⊓ Mw₂ = U₂ ∧
        (M₁ = M ⊔ A₁ ∧ (M : Set G) * A₁ = M₁ ∧ IsElementaryAbelian 2 M₁ ∧
          Nat.card M₁ = (2 ^ n) ^ 4 ∧ (M₁.subgroupOf D₁).Characteristic ∧
          (M₁ ≤ S ∧ (M₁.subgroupOf S).Normal) ∧
          ((M₁.subgroupOf D₁).Normal ∧ M₁ ⊓ zpowers (t : G) = ⊥ ∧ M₁ ⊔ zpowers (t : G) = D₁) ∧
          M₁ ⊓ B₁ = A₁) ∧
        (Nat.card M₂ = (2 ^ n) ^ 5 ∧ M₂.relIndex D₂ = 2 ∧
          ((M₂.subgroupOf D₂).Normal ∧ M₂ ⊓ zpowers (t : G) = ⊥ ∧ M₂ ⊔ zpowers (t : G) = D₂) ∧
          M₂ ⊓ B₂ = A₂) ∧
        M₁ ⊓ M₂ = M ∧
        (Nat.card E = (2 ^ n) ^ 5 ∧ (E ≤ S ∧ (E.subgroupOf S).Normal) ∧
          ((E.subgroupOf R).Normal ∧ E ⊓ zpowers (t : G) = ⊥ ∧ E ⊔ zpowers (t : G) = R)) ∧
        (∀ F : Subgroup G, Maximal (fun F : Subgroup G => F ≤ D₁ ∧ IsElementaryAbelian 2 F) F ↔
          F = B₁ ∨ F = M₁) ∧
        normalizer (B₁ : Set G) = normalizer (D₁ : Set G) ∧
        normalizer (D₁ : Set G) ≤ normalizer (M₁ : Set G) := by
  intro TG PG Q ZP C U₁ U₂ A₁ A₂ B₁ B₂ N₁ N₂ D₁ D₂ R S D J₀ Ja w₁ w₂ IsComp hone
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
  exact OneAxisOvergroup.main hh PG Q ZP hPG rfl hZP

end CFSG.LocalAnalysis.SymplecticFourStandard
