module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixFNontrivial

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SixF

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm NextCores RootStandard
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
local notation "𝐍[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) :
  Subgroup G) : Set G)
local notation "𝐌[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) :
  Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐐[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐃[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐑[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐄[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐇" => (𝐐[Axis.one] ⊔ 𝐐[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
local notation "𝐉" => pull φ (diagTorus K)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐉[" i "]" => pull φ (axisTorus K i)
set_option quotPrecheck false in
local notation "𝐖[" i "]" => (𝐅 ⊓ centralizer (𝐉[i] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊[" i "]" => (𝐀[i] ⊔ (𝐅 ⊓ 𝐃[i]) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐋[" i "]" => (𝐅 ⊔ 𝐀[i] : Subgroup G)
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐅ʷ[" i "]" => (𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅ʷ[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐃𝐧[" i "]" => normalizer ((𝐃[i] : Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐏₁[" i "]" => (CFSG.pCore 2 (normalizer ((𝐃[i] : Subgroup G) : Set G))).map
  (normalizer ((𝐃[i] : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄𝐧[" i "]" => (normalizer ((𝐄[i] : Subgroup G) : Set G) ⊓
  normalizer ((𝐊[i] : Subgroup G) : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐏₂[" i "]" => (CFSG.pCore 2 𝐄𝐧[i]).map 𝐄𝐧[i].subtype
set_option quotPrecheck false in
local notation "𝐏₀[" i "]" => (𝐏₁[i] ⊓ 𝐏₂[Axis.swap i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₀[" i "]" => closure {x : G | ∃ p ∈ 𝐏₀[i], ∃ j ∈ pull φ (diagTorus K),
  x = p⁻¹ * (j⁻¹ * p * j)}
set_option quotPrecheck false in
local notation "𝐕[" i "," k "]" => (𝐌₀[i] ⊓ centralizer (𝐉[k] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝛋[" x "]" => t⁻¹ * ((t⁻¹ * (x⁻¹ * t * x))⁻¹ * t * (t⁻¹ * (x⁻¹ * t * x)))
set_option quotPrecheck false in
local notation "𝐌ʷ[" i "," k "]" => (𝐌₀[i].map (MulAut.conj 𝐰[k]⁻¹).toMonoidHom : Subgroup G)

theorem conj_X_mem_P₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {p : G} (hp : p ∈ 𝐏₂[i.swap]) {x : G}
    (hx : x ∈ 𝐗[i.swap]) : p * x * p⁻¹ ∈ 𝐗[i.swap] := by
  have := mul_mem (K_le_X h i.swap (comm_P₂_X h i hne hbot hp hx)) hx
  rwa [inv_mul_cancel_right] at this

theorem comm_P₂_mem_X (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x y : G} (hx : x ∈ 𝐏₂[i.swap]) (hy : y ∈ 𝐏₂[i.swap]) :
    x⁻¹ * y⁻¹ * x * y ∈ 𝐗[i.swap] := by
  have h1 := sq_P₂_mem_X h i hne hbot (mul_mem hy hx)
  have h2 := conj_X_mem_P₂ h i hne hbot hy (sq_P₂_mem_X h i hne hbot hx)
  have h3 := sq_P₂_mem_X h i hne hbot hy
  rw [show x⁻¹ * y⁻¹ * x * y = ((y * x) * (y * x))⁻¹ * (y * (x * x) * y⁻¹) * (y * y) by group]
  exact mul_mem (mul_mem (inv_mem h1) h2) h3

theorem M_le_P₂ (h : FCHyp L K n φ t) (i : Axis) : 𝐌₀[i] ≤ 𝐏₂[i.swap] :=
  (M_le_P₀ h i).trans inf_le_right

theorem w_mem_En (h : FCHyp L K n φ t) (k : Axis) : 𝐰[k] ∈ 𝐄𝐧[k] :=
  mem_inf.mpr ⟨mem_normalizer_of_conj_le fun _ he => conj_w_mem_E h k he,
    mem_normalizer_of_conj_le fun _ hx => conj_w_mem_K h k hx⟩

theorem Mw_le_P₂ (h : FCHyp L K n φ t) (i : Axis) : 𝐌ʷ[i, i.swap] ≤ 𝐏₂[i.swap] := by
  intro x hx
  rw [mem_map_conj_inv] at hx
  have := conj_mem_P₂ i.swap (inv_mem (w_mem_En h i.swap)) (M_le_P₂ h i hx)
  rwa [show 𝐰[i.swap]⁻¹ * (𝐰[i.swap] * x * 𝐰[i.swap]⁻¹) * 𝐰[i.swap]⁻¹⁻¹ = x by group] at this

theorem M_mul_Mw_swap (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    ((𝐌₀[i] : Subgroup G) : Set G) * ((𝐌ʷ[i, i.swap] : Subgroup G) : Set G) =
      ((𝐌₀[i] ⊔ 𝐌ʷ[i, i.swap] : Subgroup G) : Set G) :=
  mul_eq_sup_of_comm_mod (X_le_P₂ h i hne hbot)
    (fun _ hx _ hy => comm_P₂_mem_X h i hne hbot hx hy) (M_le_P₂ h i) (Mw_le_P₂ h i) (by
      rw [← F_mul_Fw' h i.swap]
      rintro _ ⟨f, hf, f', hf', rfl⟩
      exact ⟨f, F_le_M h i hne hbot hf, f', map_mono (F_le_M h i hne hbot) hf', rfl⟩)

theorem kappa_mem_M (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {m : G} (hm : m ∈ 𝐌₀[i]) :
    t⁻¹ * (m⁻¹ * t * m) ∈ 𝐌₀[i] := by
  have h1 := (mem_normalizer_iff.mp (inv_mem (t_mem_normalizer_M h i hne hbot)) _).mp
    (inv_mem hm)
  have := mul_mem h1 hm
  rwa [show t⁻¹ * m⁻¹ * t⁻¹⁻¹ * m = t⁻¹ * (m⁻¹ * t * m) by group] at this

theorem kappa2_mem_Z (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {m : G} (hm : m ∈ 𝐌₀[i]) : 𝛋[m] ∈ 𝐙 := by
  rw [← M_inf_C h i hne hbot]
  exact mem_inf.mpr ⟨kappa_mem_M h i hne hbot (kappa_mem_M h i hne hbot hm),
    A_le_C h i.swap (kappa2_mem_A h i hbot (P₂_le _ (M_le_P₂ h i hm)))⟩

omit [Finite G] in
theorem kappa2_conj_C {c : G} (hc : c ∈ 𝐂) (x : G) : 𝛋[c * x * c⁻¹] = c * 𝛋[x] * c⁻¹ := by
  rw [kappa_conj_C hc x, kappa_conj_C hc]

theorem mem_E_of_kappa2 (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {m m₀ : G} (hm : m ∈ 𝐌₀[i]) (hm₀ : m₀ ∈ 𝐌₀[i])
    (hu : 𝛋[m] * 𝛋[𝐰[i.swap]⁻¹ * m₀ * 𝐰[i.swap]] ∈ 𝐔[i.swap]) :
    m ∈ 𝐄[i.swap] ∧ m₀ ∈ 𝐄[i.swap] := by
  have hz := kappa2_mem_Z h i hne hbot hm
  have hz₀ := kappa2_mem_Z h i hne hbot hm₀
  have e1 : 𝛋[𝐰[i.swap]⁻¹ * m₀ * 𝐰[i.swap]] = 𝐰[i.swap]⁻¹ * 𝛋[m₀] * 𝐰[i.swap] := by
    have := kappa2_conj_C (inv_mem (w_facts h i.swap).1) m₀
    rwa [inv_inv] at this
  rw [e1] at hu
  have hUZ : 𝐔[i.swap] ≤ 𝐙 := pull_mono φ (rootU_le_center i.swap)
  have h1 : 𝐰[i.swap]⁻¹ * 𝛋[m₀] * 𝐰[i.swap] ∈ 𝐙 := by
    have := mul_mem (inv_mem hz) (hUZ hu)
    rwa [inv_mul_cancel_left] at this
  have h2 : 𝛋[m₀] ∈ 𝐔[i.swap] := mem_U_of_conj_w h i.swap hz₀ (by
    rw [w_inv] at h1 ⊢
    exact h1)
  have h3 : 𝐰[i.swap]⁻¹ * 𝛋[m₀] * 𝐰[i.swap] ∈ 𝐔[i.swap] := by
    have := (mem_normalizer_iff.mp (inv_mem (w_facts h i.swap).2.2.1) _).mp h2
    rwa [inv_inv] at this
  have h4 : 𝛋[m] ∈ 𝐔[i.swap] := by
    have := mul_mem hu (inv_mem h3)
    rwa [mul_inv_cancel_right] at this
  exact ⟨(kappa2_mem_U_iff h i hne hbot (M_le_P₂ h i hm)).mp h4,
    (kappa2_mem_U_iff h i hne hbot (M_le_P₂ h i hm₀)).mp h2⟩

theorem M_inf_E_swap (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐌₀[i] ⊓ 𝐄[i.swap] = 𝐅 := by
  refine le_antisymm (fun x hx => ?_)
    (le_inf (F_le_M h i hne hbot) ((F_le_E0 h).trans (E0_le_E i.swap)))
  have hx0 : x ∈ 𝐄₀ := (E_swap_inf_P₁ h i hne hbot).le ⟨hx.2, M_le_P₁ h i hx.1⟩
  exact (M_inf_E0 h i hne hbot).le ⟨hx.1, hx0⟩

omit [Finite G] in
theorem kappa2_one : 𝛋[(1 : G)] = 1 := by group

theorem M_inf_Mw_swap (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐌₀[i] ⊓ 𝐌ʷ[i, i.swap] = 𝐖[i.swap] := by
  refine le_antisymm (fun z hz => ?_) (le_inf (W_le_M h i hne hbot _) fun x hx =>
    mem_map_conj_inv.mpr (W_le_M h i hne hbot _ (conj_w_mem_W h i.swap hx)))
  obtain ⟨hzM, hzw⟩ := mem_inf.mp hz
  rw [mem_map_conj_inv] at hzw
  have hκ : 𝛋[z⁻¹] * 𝛋[𝐰[i.swap]⁻¹ * (𝐰[i.swap] * z * 𝐰[i.swap]⁻¹) * 𝐰[i.swap]] ∈
      𝐔[i.swap] := by
    rw [show 𝐰[i.swap]⁻¹ * (𝐰[i.swap] * z * 𝐰[i.swap]⁻¹) * 𝐰[i.swap] = z by group]
    have h1 := kappa2_mul h i hne hbot (M_le_P₂ h i (inv_mem hzM)) (M_le_P₂ h i hzM)
    rw [show z⁻¹ * z = 1 from inv_mul_cancel z, kappa2_one, mul_one] at h1
    exact inv_mem_iff.mp h1
  obtain ⟨h1, h2⟩ := mem_E_of_kappa2 h i hne hbot (inv_mem hzM) hzw hκ
  have hzF : z ∈ 𝐅 := (M_inf_E_swap h i hne hbot).le (mem_inf.mpr ⟨hzM, inv_mem_iff.mp h1⟩)
  have hwzF : 𝐰[i.swap] * z * 𝐰[i.swap]⁻¹ ∈ 𝐅 := (M_inf_E_swap h i hne hbot).le ⟨hzw, h2⟩
  exact (F_inf_Fw h i.swap).le ⟨hzF, mem_map_conj_inv.mpr hwzF⟩

theorem card_M_mul_Mw_swap (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    Nat.card ↥(((𝐌₀[i] : Subgroup G) : Set G) * ((𝐌ʷ[i, i.swap] : Subgroup G) : Set G)) =
      Nat.card K ^ 8 := by
  have h1 := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf 𝐌₀[i] 𝐌ʷ[i, i.swap]
  rw [M_inf_Mw_swap h i hne hbot, card_W h i.swap, card_Mw, card_M h i hne hbot] at h1
  have hq : 0 < Nat.card K ^ 2 := pow_pos Nat.card_pos 2
  exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)

theorem card_Mhat_swap (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    Nat.card (𝐌₀[i] ⊔ 𝐌ʷ[i, i.swap] : Subgroup G) = Nat.card K ^ 8 := by
  have := card_M_mul_Mw_swap h i hne hbot
  rwa [M_mul_Mw_swap h i hne hbot, SetLike.coe_sort_coe] at this

theorem Mhat_inf_E_swap (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    (𝐌₀[i] ⊔ 𝐌ʷ[i, i.swap]) ⊓ 𝐄[i.swap] = 𝐗[i.swap] := by
  refine le_antisymm (fun y hy => ?_) (le_inf (sup_le ((F_le_M h i hne hbot).trans le_sup_left)
    ((map_mono (F_le_M h i hne hbot)).trans le_sup_right)) (X_le_E h i.swap))
  obtain ⟨hyM, hyE⟩ := mem_inf.mp hy
  rw [← SetLike.mem_coe, ← M_mul_Mw_swap h i hne hbot] at hyM
  obtain ⟨m, hm, m', hm', rfl⟩ := hyM
  have hm₀ := mem_map_conj_inv.mp hm'
  have hκ : 𝛋[m] * 𝛋[𝐰[i.swap]⁻¹ * (𝐰[i.swap] * m' * 𝐰[i.swap]⁻¹) * 𝐰[i.swap]] ∈
      𝐔[i.swap] := by
    rw [show 𝐰[i.swap]⁻¹ * (𝐰[i.swap] * m' * 𝐰[i.swap]⁻¹) * 𝐰[i.swap] = m' by group]
    have h1 := kappa2_mul h i hne hbot (M_le_P₂ h i hm) (Mw_le_P₂ h i hm')
    have h2 := (kappa2_mem_U_iff h i hne hbot
      (mul_mem (M_le_P₂ h i hm) (Mw_le_P₂ h i hm'))).mpr hyE
    have e : 𝛋[m] * 𝛋[m'] = 𝛋[m * m'] * ((𝛋[m] * 𝛋[m'])⁻¹ * 𝛋[m * m'])⁻¹ := by group
    rw [e]
    exact mul_mem h2 (inv_mem h1)
  obtain ⟨h1, h2⟩ := mem_E_of_kappa2 h i hne hbot hm hm₀ hκ
  exact mul_mem (mem_sup_left ((M_inf_E_swap h i hne hbot).le ⟨hm, h1⟩))
    (mem_sup_right (mem_map_conj_inv.mpr ((M_inf_E_swap h i hne hbot).le ⟨hm₀, h2⟩)))

theorem Mhat_le_P₂ (h : FCHyp L K n φ t) (i : Axis) :
    𝐌₀[i] ⊔ 𝐌ʷ[i, i.swap] ≤ 𝐏₂[i.swap] :=
  sup_le (M_le_P₂ h i) (Mw_le_P₂ h i)

theorem P₂_le_normalizer_E (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐏₂[i.swap] ≤ normalizer ((𝐄[i.swap] : Subgroup G) : Set G) := by
  obtain ⟨hN, -, -⟩ := quotient_P₂ h i hne hbot (U_normal_A h i.swap)
  refine fun p hp => mem_normalizer_of_conj_le fun e he => ?_
  have := hN.conj_mem ⟨e, E_le_P₂ h i hne hbot he⟩ (mem_subgroupOf.mpr he) ⟨p, hp⟩
  rw [mem_subgroupOf] at this
  exact this

theorem Mhat_mul_E_swap (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    ((𝐌₀[i] ⊔ 𝐌ʷ[i, i.swap] : Subgroup G) : Set G) * ((𝐄[i.swap] : Subgroup G) : Set G) =
      ((𝐏₂[i.swap] : Subgroup G) : Set G) := by
  have hle := (Mhat_le_P₂ h i).trans (P₂_le_normalizer_E h i hne hbot)
  rw [← coe_mul_of_left_le_normalizer_right _ _ hle]
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := 𝐄[i.swap]) (B := 𝐌₀[i] ⊔ 𝐌ʷ[i, i.swap]) hle
  rw [sup_comm 𝐄[i.swap] (𝐌₀[i] ⊔ 𝐌ʷ[i, i.swap]), inf_comm 𝐄[i.swap] (𝐌₀[i] ⊔ 𝐌ʷ[i, i.swap]),
    Mhat_inf_E_swap h i hne hbot, card_E h i.swap, card_Mhat_swap h i hne hbot,
    card_X h i.swap] at h1
  have h2 : Nat.card (𝐌₀[i] ⊔ 𝐌ʷ[i, i.swap] ⊔ 𝐄[i.swap] : Subgroup G) = 2 * Nat.card K ^ 8 := by
    have hq : 0 < Nat.card K ^ 6 := pow_pos Nat.card_pos 6
    exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)
  rw [eq_of_le_of_card_ge (sup_le (Mhat_le_P₂ h i) (E_le_P₂ h i hne hbot))
    (by rw [h2, card_P₂ h i hne hbot])]

omit [Finite G] [Finite K] in
theorem conj_mem_Mw (i k : Axis) {g : G} (hg : 𝐰[k] * g * 𝐰[k]⁻¹ ∈ normalizer (𝐌₀[i] : Set G))
    {y : G} (hy : y ∈ 𝐌ʷ[i, k]) : g * y * g⁻¹ ∈ 𝐌ʷ[i, k] := by
  rw [mem_map_conj_inv] at hy ⊢
  have := (mem_normalizer_iff.mp hg _).mp hy
  rwa [show 𝐰[k] * g * 𝐰[k]⁻¹ * (𝐰[k] * y * 𝐰[k]⁻¹) * (𝐰[k] * g * 𝐰[k]⁻¹)⁻¹ =
    𝐰[k] * (g * y * g⁻¹) * 𝐰[k]⁻¹ by group] at this

theorem t_mem_normalizer_Mhat_swap (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    t ∈ normalizer ((𝐌₀[i] ⊔ 𝐌ʷ[i, i.swap] : Subgroup G) : Set G) := by
  have htM := t_mem_normalizer_M h i hne hbot
  have hwt : 𝐰[i.swap] * t * 𝐰[i.swap]⁻¹ = t := by
    rw [mem_centralizer_singleton_iff.mp (w_facts h i.swap).1, mul_inv_cancel_right]
  exact mem_normalizer_of_conj_le fun _ hy => conj_mem_sup
    (fun m hm => (mem_normalizer_iff.mp htM m).mp hm)
    (fun _ hy => conj_mem_Mw i i.swap (by rw [hwt]; exact htM) hy) hy

theorem J_le_normalizer_Mhat_swap (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐉 ≤ normalizer ((𝐌₀[i] ⊔ 𝐌ʷ[i, i.swap] : Subgroup G) : Set G) :=
  fun _ hj => mem_normalizer_of_conj_le fun _ hy => conj_mem_sup
    (fun m hm => (mem_normalizer_iff.mp (J_le_normalizer_M h i hne hbot hj) m).mp hm)
    (fun _ hy => conj_mem_Mw i i.swap
      (J_le_normalizer_M h i hne hbot (conj_w_mem_J i.swap hj)) hy) hy

omit [Finite K] in
theorem w_mem_normalizer_Mhat' (i k : Axis) :
    𝐰[k] ∈ normalizer ((𝐌₀[i] ⊔ 𝐌ʷ[i, k] : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_le fun y hy => ?_
  have hle : 𝐌₀[i] ⊔ 𝐌ʷ[i, k] ≤
      (𝐌₀[i] ⊔ 𝐌ʷ[i, k]).comap (MulAut.conj 𝐰[k]).toMonoidHom := by
    refine sup_le (fun m hm => mem_comap.mpr (mem_sup_right ?_))
      (fun m hm => mem_comap.mpr (mem_sup_left (mem_map_conj_inv.mp hm)))
    change 𝐰[k] * m * 𝐰[k]⁻¹ ∈ 𝐌ʷ[i, k]
    rw [mem_map_conj_inv, w_inv]
    rwa [show 𝐰[k] * (𝐰[k] * m * 𝐰[k]) * 𝐰[k] = (𝐰[k] * 𝐰[k]) * m * (𝐰[k] * 𝐰[k]) by group,
      w_mul_self, one_mul, mul_one]
  exact hle hy

theorem Mhat_sup_t_swap (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    (𝐌₀[i] ⊔ 𝐌ʷ[i, i.swap]) ⊔ zpowers t = 𝐏₂[i.swap] := by
  refine le_antisymm (sup_le (Mhat_le_P₂ h i) (zpowers_le.mpr (t_mem_P₂ h i hne hbot)))
    fun p hp => ?_
  rw [← SetLike.mem_coe, ← Mhat_mul_E_swap h i hne hbot] at hp
  obtain ⟨m, hm, e, he, rfl⟩ := hp
  refine mul_mem (mem_sup_left hm) ?_
  rcases mem_X_or_of_mem_E h i.swap he with hx | hx
  · exact mem_sup_left ((Mhat_inf_E_swap h i hne hbot).ge hx).1
  · rw [show e = t⁻¹ * (t * e) by group]
    exact mul_mem (mem_sup_right (inv_mem (mem_zpowers t)))
      (mem_sup_left ((Mhat_inf_E_swap h i hne hbot).ge hx).1)

theorem Mhat_inf_t_swap (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : (𝐌₀[i] ⊔ 𝐌ʷ[i, i.swap]) ⊓ zpowers t = ⊥ := by
  have hle : (𝐌₀[i] ⊔ 𝐌ʷ[i, i.swap]) ⊓ zpowers t ≤ 𝐗[i.swap] ⊓ zpowers t := fun _ hy =>
    ⟨(Mhat_inf_E_swap h i hne hbot).le ⟨hy.1, zpowers_le.mpr (t_mem_E h i.swap) hy.2⟩, hy.2⟩
  exact le_bot_iff.mp (hle.trans (X_sup_t h i.swap).1.le)

theorem P₂_le_normalizer_Mhat (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐏₂[i.swap] ≤ normalizer ((𝐌₀[i] ⊔ 𝐌ʷ[i, i.swap] : Subgroup G) : Set G) :=
  (Mhat_sup_t_swap h i hne hbot).symm.le.trans
    (sup_le le_normalizer (zpowers_le.mpr (t_mem_normalizer_Mhat_swap h i hne hbot)))

theorem P₂_inf_C (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐏₂[i.swap] ⊓ 𝐂 = 𝐁[i.swap] := by
  refine le_antisymm (fun c hc => ?_)
    ((E_inf_C h i.swap).ge.trans (inf_le_inf_right _ (E_le_P₂ h i hne hbot)))
  obtain ⟨hcP, hcC⟩ := mem_inf.mp hc
  have hcK : c ∈ normalizer (𝐊[i.swap] : Set G) := (mem_inf.mp (P₂_le _ hcP)).2
  have hct : c * t * c⁻¹ = t := by
    rw [mem_centralizer_singleton_iff.mp hcC, mul_inv_cancel_right]
  have hcD : c ∈ normalizer (𝐃[i.swap] : Set G) :=
    mem_normalizer_D_of h i.swap hcK (by rw [hct]; exact mem_sup_left (mem_zpowers t))
  have hcN : c ∈ 𝐍[i.swap] := by
    have := normalizer_D_swap_eq h i hne hbot
    rw [this] at hcD
    exact hcD
  exact (E_inf_C h i.swap).le ⟨(P₂_inf_N h i hne hbot).le ⟨hcP, hcN⟩, hcC⟩

theorem Mhat_inf_C_swap (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : (𝐌₀[i] ⊔ 𝐌ʷ[i, i.swap]) ⊓ 𝐂 = 𝐀[i.swap] := by
  refine le_antisymm (fun c hc => ?_) (le_inf ?_ (A_le_C h i.swap))
  · obtain ⟨hcM, hcC⟩ := mem_inf.mp hc
    have hcB : c ∈ 𝐁[i.swap] := (P₂_inf_C h i hne hbot).le ⟨Mhat_le_P₂ h i hcM, hcC⟩
    have hcX : c ∈ 𝐗[i.swap] :=
      (Mhat_inf_E_swap h i hne hbot).le ⟨hcM, ((E_inf_C h i.swap).ge hcB).1⟩
    have htA : t ∈ normalizer (𝐀[i.swap] : Set G) := mem_normalizer_of_conj_le fun a ha => by
      rw [← mem_centralizer_singleton_iff.mp (A_le_C h i.swap ha), mul_inv_cancel_right]
      exact ha
    rcases mem_or_mul_mem (t_mul_t h) htA ((sup_comm (zpowers t) 𝐀[i.swap]).le hcB) with
      hA | hA
    · exact hA
    · exfalso
      apply t_not_mem_X h i.swap
      have := mul_mem (L_le_X h i.swap (mem_sup_right hA)) (inv_mem hcX)
      rwa [mul_inv_cancel_right] at this
  · refine fun a ha => ((Mhat_inf_E_swap h i hne hbot).ge ?_).1
    exact L_le_X h i.swap (mem_sup_right ha)

theorem weylProductConclusion_elementary (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    WeylProductConclusion 𝐌₀[i] 𝐌ʷ[i, i.swap] 𝐏₂[i.swap] 𝐄[i.swap] 𝐗[i.swap] 𝐀[i.swap]
      𝐕[i, i.swap] 𝐂 𝐉 t 𝐰[i.swap] (Nat.card K) 8 :=
  ⟨M_mul_Mw_swap h i hne hbot, Mhat_le_P₂ h i,
    (M_inf_Mw_swap h i hne hbot).trans (V_swap_eq h i hne hbot).symm,
    Mhat_mul_E_swap h i hne hbot, Mhat_inf_E_swap h i hne hbot, card_Mhat_swap h i hne hbot,
    ⟨P₂_le_normalizer_Mhat h i hne hbot, Mhat_sup_t_swap h i hne hbot,
      Mhat_inf_t_swap h i hne hbot⟩,
    Mhat_inf_C_swap h i hne hbot, J_le_normalizer_Mhat_swap h i hne hbot,
    t_mem_normalizer_Mhat_swap h i hne hbot, w_mem_normalizer_Mhat' i i.swap⟩

theorem weylProductConclusion_both (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    WeylProductConclusion 𝐌₀[i] 𝐌ʷ[i, i] 𝐏₁[i] 𝐄[i] 𝐗[i] 𝐀[i] 𝐕[i, i] 𝐂 𝐉 t 𝐰[i]
      (Nat.card K) 7 ∧
    WeylProductConclusion 𝐌₀[i] 𝐌ʷ[i, i.swap] 𝐏₂[i.swap] 𝐄[i.swap] 𝐗[i.swap] 𝐀[i.swap]
      𝐕[i, i.swap] 𝐂 𝐉 t 𝐰[i.swap] (Nat.card K) 8 ∧
    Nat.card 𝐕[i, i] = Nat.card K ^ 3 ∧ Nat.card 𝐕[i, i.swap] = Nat.card K ^ 2 ∧
    (∀ x ∈ 𝐕[i, i.swap], ∀ y ∈ 𝐕[i, i.swap], x * y = y * x) ∧
    ∀ x ∈ 𝐕[i, i.swap], x * x = 1 := by
  have hV := V_swap_eq h i hne hbot
  refine ⟨weylProductConclusion_nontrivial h i hne hbot,
    weylProductConclusion_elementary h i hne hbot, card_V h i hne hbot, ?_, ?_, ?_⟩
  · rw [hV]
    exact card_W h i.swap
  · intro x hx y hy
    rw [hV] at hx hy
    exact F_comm h (W_le_F _ hx) (W_le_F _ hy)
  · intro x hx
    rw [hV] at hx
    exact sq_W_swap h i hne hbot hx

end SixF

end CFSG.LocalAnalysis.SymplecticFourStandard
