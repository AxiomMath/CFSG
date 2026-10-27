module

public import CFSG.LocalAnalysis.SteinbergSFBothTrivialClosureSetupBase

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace BothTrivialClosure

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial BothTrivialHeisenberg
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

section Closure

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐒" => (𝐗[Axis.one] ⊔ 𝐗[Axis.two] : Subgroup G)
local notation "𝐉" => pull φ (diagTorus K)
local notation "𝐉[" i "]" => pull φ (axisTorus K i)
set_option quotPrecheck false in
local notation "𝐖[" i "]" => (𝐅 ⊓ centralizer (𝐉[i] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐍𝐂[" i "]" => closure {x : G | ∃ g ∈ normalizer (𝐗[i] : Set G),
  ∃ y ∈ (L ⊓ centralizer (𝐔[i] : Set G) : Subgroup G) ⊔ 𝐗[i], x = g⁻¹ * y * g}
set_option quotPrecheck false in
local notation "𝐖'[" i "]" =>
  (𝐖[i].map (MulAut.conj 𝐰[Axis.swap i]⁻¹).toMonoidHom : Subgroup G)

omit [Finite G] [Finite K] in
theorem X_le_S (i : Axis) : 𝐗[i] ≤ 𝐒 := by
  cases i
  · exact le_sup_left
  · exact le_sup_right

theorem S_le_normalizer_X (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : 𝐒 ≤ normalizer (𝐗[i] : Set G) :=
  (S_le_T h).trans (T_le_normalizer_X h hbt i)

theorem card_barS (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : Nat.card (barSub 𝐗[i] 𝐒) = Nat.card K ^ 2 := by
  have h1 := card_barSub (X_le_S i) (S_le_normalizer_X h hbt i)
  rw [card_X h i, card_S h hbt] at h1
  have hq : 0 < Nat.card K ^ 6 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)

theorem mul_self_mem_X (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) {s : G} (hs : s ∈ 𝐒) : s * s ∈ 𝐗[i] := by
  rw [← SetLike.mem_coe, ← X_mul_X h hbt] at hs
  obtain ⟨x, hx, y, hy, rfl⟩ := hs
  cases i
  · have h1 : y * x * y⁻¹ ∈ 𝐗[Axis.one] := conj_T_mem_X h hbt _ (X_le_T h _ hy) hx
    rw [show x * y * (x * y) = x * (y * x * y⁻¹) * (y * y) by group, X_mul_self h hbt _ hy,
      mul_one]
    exact mul_mem hx h1
  · have h1 : x * y * x⁻¹ ∈ 𝐗[Axis.two] := conj_T_mem_X h hbt _ (X_le_T h _ hx) hy
    rw [show x * y * (x * y) = x * y * x⁻¹ * (x * x) * y by group, X_mul_self h hbt _ hx,
      mul_one]
    exact mul_mem h1 hy

theorem barS_elem (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : IsElementaryAbelian 2 (barSub 𝐗[i] 𝐒) := by
  refine isElementaryAbelian_of (fun x hx y hy => ?_) (fun x hx => ?_)
  · obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨s', hs', rfl⟩ := hy
    rw [← map_mul, ← map_mul, barMap_eq_iff]
    have := commutator_mem h hbt (inv_mem (mem_subgroupOf.mp hs')) (inv_mem (mem_subgroupOf.mp hs))
    rw [inv_inv, inv_inv] at this
    have e : ((s * s' : ↥(normalizer (𝐗[i] : Set G))) : G)⁻¹ * ((s' * s : ↥(normalizer
        (𝐗[i] : Set G))) : G) = (s' : G)⁻¹ * (s : G)⁻¹ * s' * s := by
      rw [coe_mul, coe_mul]
      group
    rw [e]
    exact mem_sup_left this
  · obtain ⟨s, hs, rfl⟩ := hx
    rw [← map_mul, barMap_eq_one_iff, coe_mul]
    exact mul_self_mem_X h hbt i (mem_subgroupOf.mp hs)

theorem rank_barS (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : Group.rank (barSub 𝐗[i] 𝐒) = 2 * n := by
  have hE := barS_elem h hbt i
  have h3 := CFSG.LocalAnalysis.SymplecticFourRankThompson.two_pow_rank_eq_card_of_elementary
    (barSub 𝐗[i] 𝐒) fun x hx => mul_self_of_elem hE hx
  rw [card_barS h hbt i, h.setup.card_K, ← pow_mul, mul_comm n 2] at h3
  exact Nat.pow_right_injective le_rfl h3

theorem tau_mem_normalizer_barS (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis) :
    barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩ ∈ normalizer (barSub 𝐗[i] 𝐒 : Set (BarM 𝐗[i])) := by
  refine mem_normalizer_of_conj_le fun x hx => ?_
  obtain ⟨s, hs, rfl⟩ := hx
  rw [← map_inv, ← map_mul, ← map_mul]
  refine ⟨_, mem_subgroupOf.mpr ?_, rfl⟩
  exact (mem_normalizer_iff.mp (T_le_normalizer_S h hbt (t_mem_T h)) _).mp (mem_subgroupOf.mp hs)

omit [Finite G] in
theorem J_le_CU (i : Axis) : 𝐉[i] ≤ L ⊓ centralizer (𝐔[i] : Set G) := fun j hj =>
  ⟨pull_le φ _ hj, mem_centralizer_iff.mpr fun u hu => by
    have h1 := axisTorus_cent i hj hu
    calc u * j = j * (j⁻¹ * u * j) := by group
      _ = j * u := by rw [h1]⟩

theorem J_le_normalizer (h : FCHyp L K n φ t) (i : Axis) :
    𝐉[i] ≤ normalizer (𝐗[i] : Set G) ⊓ normalizer (𝐒 : Set G) := fun _ hj =>
  have hj0 := axisTorus_le_J0 i hj
  ⟨J_le_normalizer_X h i hj0, mem_normalizer_of_conj_le fun _ hx => conj_mem_sup
    (fun y hy => (mem_normalizer_iff.mp (J_le_normalizer_X h Axis.one hj0) y).mp hy)
    (fun y hy => (mem_normalizer_iff.mp (J_le_normalizer_X h Axis.two hj0) y).mp hy) hx⟩

theorem F_eq_W_sup (h : FCHyp L K n φ t) (i : Axis) : 𝐅 = 𝐖[i] ⊔ 𝐖[i.swap] := by
  have h1 : 𝐅 = 𝐖[Axis.one] ⊔ 𝐖[Axis.two] := by
    refine le_antisymm (fun f hf => ?_) (sup_le (W_le_F _) (W_le_F _))
    rw [← SetLike.mem_coe, ← W_mul_W h] at hf
    obtain ⟨a, ha, b, hb, rfl⟩ := hf
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)
  cases i
  · exact h1
  · exact h1.trans (sup_comm _ _)

omit [Finite G] [Finite K] in
theorem W'_le_X (i : Axis) : 𝐖'[i] ≤ 𝐗[i.swap] := (map_mono (W_le_F i)).trans le_sup_right

theorem Fw_le (h : FCHyp L K n φ t) (i : Axis) :
    𝐅.map (MulAut.conj 𝐰[i.swap]⁻¹).toMonoidHom ≤ 𝐖'[i] ⊔ 𝐅 := by
  intro f hf
  rw [mem_map_conj_inv] at hf
  have hf' : 𝐰[i.swap] * f * 𝐰[i.swap]⁻¹ ∈ 𝐖[i] ⊔ 𝐖[i.swap] := by
    rw [← F_eq_W_sup h i]
    exact hf
  obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_of_commute fun x hx y hy =>
    F_comm h (W_le_F i hx) (W_le_F i.swap hy)).mp hf'
  have e : f = (𝐰[i.swap]⁻¹ * a * 𝐰[i.swap]) * (𝐰[i.swap]⁻¹ * b * 𝐰[i.swap]) := by
    rw [show 𝐰[i.swap]⁻¹ * a * 𝐰[i.swap] * (𝐰[i.swap]⁻¹ * b * 𝐰[i.swap]) =
      𝐰[i.swap]⁻¹ * (a * b) * 𝐰[i.swap] by group, hab]
    group
  rw [e]
  refine mul_mem (mem_sup_left (mem_map_conj_inv.mpr ?_)) (mem_sup_right ?_)
  · rw [show 𝐰[i.swap] * (𝐰[i.swap]⁻¹ * a * 𝐰[i.swap]) * 𝐰[i.swap]⁻¹ = a by group]
    exact ha
  have := conj_w_mem_W h i.swap hb
  rw [w_inv] at this ⊢
  exact W_le_F _ this

theorem X_swap_le (h : FCHyp L K n φ t) (i : Axis) : 𝐗[i.swap] ≤ 𝐗[i] ⊔ 𝐖'[i] :=
  sup_le (le_sup_left.trans le_sup_left)
    ((Fw_le h i).trans (sup_le le_sup_right (le_sup_left.trans le_sup_left)))

theorem S_le_X_sup_W' (h : FCHyp L K n φ t) (i : Axis) : 𝐒 ≤ 𝐗[i] ⊔ 𝐖'[i] := by
  cases i
  · exact sup_le le_sup_left (X_swap_le h Axis.one)
  · exact sup_le (X_swap_le h Axis.two) le_sup_left

theorem W_inf_W_swap (h : FCHyp L K n φ t) (i : Axis) : 𝐖[i] ⊓ 𝐖[i.swap] = ⊥ := by
  cases i
  · exact W_inf_W h
  · rw [inf_comm]
    exact W_inf_W h

theorem X_inf_W' (h : FCHyp L K n φ t) (i : Axis) : 𝐗[i] ⊓ 𝐖'[i] = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyX, hyW⟩ := mem_inf.mp hy
  have hyF : y ∈ 𝐅 := (X_inf_X_swap h i).le ⟨hyX, W'_le_X i hyW⟩
  have hyWj : y ∈ 𝐖[i.swap] := (F_inf_Fw h i.swap).le ⟨hyF, map_mono (W_le_F i) hyW⟩
  rw [mem_map_conj_inv] at hyW
  have h3 : 𝐰[i.swap] * y * 𝐰[i.swap]⁻¹ ∈ 𝐖[i] ⊓ 𝐖[i.swap] := ⟨hyW, conj_w_mem_W h i.swap hyWj⟩
  rw [W_inf_W_swap h i, mem_bot] at h3
  rw [mem_bot]
  calc y = 𝐰[i.swap]⁻¹ * (𝐰[i.swap] * y * 𝐰[i.swap]⁻¹) * 𝐰[i.swap] := by group
    _ = 1 := by rw [h3]; group

theorem conj_J_mem_W' (h : FCHyp L K n φ t) (i : Axis) {j : G} (hj : j ∈ 𝐉) {y : G}
    (hy : y ∈ 𝐖'[i]) : j⁻¹ * y * j ∈ 𝐖'[i] := by
  rw [mem_map_conj_inv] at hy ⊢
  have := conj_torus_mem_W h i (conj_w_mem_J i.swap hj) hy
  rwa [show (𝐰[i.swap] * j * 𝐰[i.swap]⁻¹)⁻¹ * (𝐰[i.swap] * y * 𝐰[i.swap]⁻¹) *
    (𝐰[i.swap] * j * 𝐰[i.swap]⁻¹) = 𝐰[i.swap] * (j⁻¹ * y * j) * 𝐰[i.swap]⁻¹ by group] at this

omit [Finite G] [Finite K] in
theorem fix_U_eq_one (i : Axis) {j : G} (hj : j ∈ 𝐉[i]) (hj1 : j ≠ 1) {u : G} (hu : u ∈ 𝐔[i])
    (hfix : (𝐰[i.swap] * j * 𝐰[i.swap]⁻¹)⁻¹ * u * (𝐰[i.swap] * j * 𝐰[i.swap]⁻¹) = u) :
    u = 1 := by
  obtain ⟨δ, hδ, rfl⟩ := exists_eq_symm_of_mem_pull hj
  rw [symm_conj_eq] at hfix
  obtain ⟨x, rfl⟩ := exists_coordG_eq φ i hu
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  cases i
  · obtain ⟨r, hr, hδm⟩ := hδ
    have hr1 : r ≠ 1 := by
      rintro rfl
      refine hj1 ?_
      have : δ = 1 := antiSp_ext (by rw [hδm, inv_one, diagMat_one]; rfl)
      rw [this, map_one]
      rfl
    have hm : glMat ((weylElt K Axis.two * δ * (weylElt K Axis.two)⁻¹ : antiSp K) :
        GL (Fin 4) K) = diagMat r r := by
      rw [weylElt_inv]
      change glMat (weylElt K _ : GL (Fin 4) K) * glMat (δ : GL (Fin 4) K) *
        glMat (weylElt K _ : GL (Fin 4) K) = _
      rw [glMat_weylElt, hδm, weylMat_two_conj, inv_inv]
    change zc φ x 0 = 1
    change ((φ.symm (weylElt K Axis.two * δ * (weylElt K Axis.two)⁻¹) : L) : G)⁻¹ * zc φ x 0 *
      ((φ.symm (weylElt K Axis.two * δ * (weylElt K Axis.two)⁻¹) : L) : G) = zc φ x 0 at hfix
    rw [conj_zc hr hr hm] at hfix
    have hb := (zc_inj hfix).1
    have hx : (1 + r ^ 2) * x = 0 := by linear_combination hb + x * h2
    rw [(mul_eq_zero.mp hx).resolve_left (one_add_ne_zero hr1).2, zc_zero]
  · obtain ⟨s, hs, hδm⟩ := hδ
    have hs1 : s ≠ 1 := by
      rintro rfl
      refine hj1 ?_
      have : δ = 1 := antiSp_ext (by rw [hδm, diagMat_one]; rfl)
      rw [this, map_one]
      rfl
    have hm : glMat ((weylElt K Axis.one * δ * (weylElt K Axis.one)⁻¹ : antiSp K) :
        GL (Fin 4) K) = diagMat s 1 := by
      rw [weylElt_inv]
      change glMat (weylElt K _ : GL (Fin 4) K) * glMat (δ : GL (Fin 4) K) *
        glMat (weylElt K _ : GL (Fin 4) K) = _
      rw [glMat_weylElt, hδm, weylMat_one_conj]
    change zc φ 0 x = 1
    change ((φ.symm (weylElt K Axis.one * δ * (weylElt K Axis.one)⁻¹) : L) : G)⁻¹ * zc φ 0 x *
      ((φ.symm (weylElt K Axis.one * δ * (weylElt K Axis.one)⁻¹) : L) : G) = zc φ 0 x at hfix
    rw [conj_zc hs one_ne_zero hm] at hfix
    have hc := (zc_inj hfix).2
    have hx : (1 + s ^ 2) * x = 0 := by linear_combination hc + x * h2
    rw [(mul_eq_zero.mp hx).resolve_left (one_add_ne_zero hs1).2, zc_zero]

theorem fix_W_eq_one (h : FCHyp L K n φ t) (i : Axis) {j : G} (hj : j ∈ 𝐉[i]) (hj1 : j ≠ 1)
    {a : G} (ha : a ∈ 𝐖[i])
    (hfix : (𝐰[i.swap] * j * 𝐰[i.swap]⁻¹)⁻¹ * a * (𝐰[i.swap] * j * 𝐰[i.swap]⁻¹) = a) :
    a = 1 := by
  have hj' : 𝐰[i.swap] * j * 𝐰[i.swap]⁻¹ ∈ 𝐉 := conj_w_mem_J i.swap (axisTorus_le_J0 i hj)
  have hκU : t⁻¹ * (a⁻¹ * t * a) ∈ 𝐔[i] := kappa_mem_U h i (mem_inf.mp (W_le_Fi h i ha)).2
  have hκ1 : t⁻¹ * (a⁻¹ * t * a) = 1 := by
    refine fix_U_eq_one i hj hj1 hκU ?_
    rw [← kappa_conj_torus h hj', hfix]
  have haU : a ∈ 𝐔[i] := (W_inf_C h i).le ⟨ha, kappa_eq_one_iff.mp hκ1⟩
  exact fix_U_eq_one i hj hj1 haU hfix

theorem fix_W'_eq_one (h : FCHyp L K n φ t) (i : Axis) {j : G} (hj : j ∈ 𝐉[i]) (hj1 : j ≠ 1)
    {v : G} (hv : v ∈ 𝐖'[i]) (hfix : j⁻¹ * v * j = v) : v = 1 := by
  rw [mem_map_conj_inv] at hv
  have h1 := fix_W_eq_one h i hj hj1 hv (by
    rw [show (𝐰[i.swap] * j * 𝐰[i.swap]⁻¹)⁻¹ * (𝐰[i.swap] * v * 𝐰[i.swap]⁻¹) *
      (𝐰[i.swap] * j * 𝐰[i.swap]⁻¹) = 𝐰[i.swap] * (j⁻¹ * v * j) * 𝐰[i.swap]⁻¹ by group, hfix])
  calc v = 𝐰[i.swap]⁻¹ * (𝐰[i.swap] * v * 𝐰[i.swap]⁻¹) * 𝐰[i.swap] := by group
    _ = 1 := by rw [h1]; group

theorem exists_X_mul_W' (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) {s : G} (hs : s ∈ 𝐒) : ∃ x ∈ 𝐗[i], ∃ v ∈ 𝐖'[i], s = x * v := by
  have hW'N : 𝐖'[i] ≤ normalizer (𝐗[i] : Set G) :=
    ((W'_le_X i).trans (X_le_S i.swap)).trans (S_le_normalizer_X h hbt i)
  have hs' := S_le_X_sup_W' h i hs
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hW'N] at hs'
  obtain ⟨x, hx, v, hv, rfl⟩ := hs'
  exact ⟨x, hx, v, hv, rfl⟩

theorem J_fpf (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) {j : G} (hj : j ∈ 𝐉[i]) (hj1 : j ≠ 1) {s : G} (hs : s ∈ 𝐒)
    (hfix : s⁻¹ * (j⁻¹ * s * j) ∈ 𝐗[i]) : s ∈ 𝐗[i] := by
  obtain ⟨x, hx, v, hv, rfl⟩ := exists_X_mul_W' h hbt i hs
  have hjX := J_le_normalizer_X h i (axisTorus_le_J0 i hj)
  have hvN : v ∈ normalizer (𝐗[i] : Set G) :=
    S_le_normalizer_X h hbt i (X_le_S i.swap (W'_le_X i hv))
  have hjv : v⁻¹ * (j⁻¹ * v * j) ∈ 𝐗[i] := by
    have h1 : j⁻¹ * x * j ∈ 𝐗[i] := by
      have := (mem_normalizer_iff.mp (inv_mem hjX) x).mp hx
      rwa [inv_inv] at this
    have h2 : v * ((x * v)⁻¹ * (j⁻¹ * (x * v) * j)) * v⁻¹ ∈ 𝐗[i] :=
      (mem_normalizer_iff.mp hvN _).mp hfix
    have h3 : v * ((x * v)⁻¹ * (j⁻¹ * (x * v) * j)) * v⁻¹ =
        x⁻¹ * (j⁻¹ * x * j) * (j⁻¹ * v * j * v⁻¹) := by group
    rw [h3] at h2
    have h4 : j⁻¹ * v * j * v⁻¹ ∈ 𝐗[i] := by
      have := mul_mem (inv_mem (mul_mem (inv_mem hx) h1)) h2
      rwa [inv_mul_cancel_left] at this
    have h5 := (mem_normalizer_iff.mp (inv_mem hvN) _).mp h4
    rwa [show v⁻¹ * (j⁻¹ * v * j * v⁻¹) * v⁻¹⁻¹ = v⁻¹ * (j⁻¹ * v * j) by group] at h5
  have hjW : v⁻¹ * (j⁻¹ * v * j) ∈ 𝐖'[i] :=
    mul_mem (inv_mem hv) (conj_J_mem_W' h i (axisTorus_le_J0 i hj) hv)
  have h6 : v⁻¹ * (j⁻¹ * v * j) ∈ 𝐗[i] ⊓ 𝐖'[i] := ⟨hjv, hjW⟩
  rw [X_inf_W' h i, mem_bot] at h6
  have hv1 : v = 1 := fix_W'_eq_one h i hj hj1 hv (by
    calc j⁻¹ * v * j = v * (v⁻¹ * (j⁻¹ * v * j)) := by group
      _ = v := by rw [h6, mul_one])
  rw [hv1, mul_one]
  exact hx

omit [Finite G] [Finite K] in
theorem exists_ne_one_J (h : FCHyp L K n φ t) (i : Axis) : ∃ j ∈ 𝐉[i], j ≠ 1 := by
  have hK2 : 2 < Nat.card K := by have := h.four_le_card; omega
  obtain ⟨r, hr0, hr1⟩ := exists_ne_zero_ne hK2 (1 : K)
  have hne : ∀ δ : antiSp K, δ ∈ axisTorus K i → ((φ.symm δ : L) : G) = 1 → δ = 1 := by
    intro δ _ e
    have : φ.symm δ = 1 := Subtype.ext e
    rwa [MulEquiv.symm_apply_eq, map_one] at this
  cases i
  · obtain ⟨δ, -, hδm⟩ := exists_diagTorus (K := K) hr0 (inv_ne_zero hr0)
    refine ⟨_, symm_mem_pull.mpr ⟨r, hr0, hδm⟩, fun e => hr1 ?_⟩
    have h1 := hne δ ⟨r, hr0, hδm⟩ e
    rw [h1] at hδm
    have h2 := congrFun (congrFun hδm 3) 3
    simp [diagMat] at h2
    exact h2
  · obtain ⟨δ, -, hδm⟩ := exists_diagTorus (K := K) one_ne_zero hr0
    refine ⟨_, symm_mem_pull.mpr ⟨r, hr0, hδm⟩, fun e => hr1 ?_⟩
    have h1 := hne δ ⟨r, hr0, hδm⟩ e
    rw [h1] at hδm
    have h2 := congrFun (congrFun hδm 2) 2
    simp [diagMat] at h2
    exact h2

omit [Finite G] [Finite K] in
theorem sup_le_NC (i : Axis) : (L ⊓ centralizer (𝐔[i] : Set G)) ⊔ 𝐗[i] ≤ 𝐍𝐂[i] :=
  fun y hy => subset_closure ⟨1, one_mem _, y, hy, by group⟩

theorem NC_le_normalizer_X (h : FCHyp L K n φ t) (i : Axis) :
    𝐍𝐂[i] ≤ normalizer (𝐗[i] : Set G) := by
  refine closure_le _ |>.mpr ?_
  rintro _ ⟨g, hg, y, hy, rfl⟩
  exact mul_mem (mul_mem (inv_mem hg) (sup_le (CU_le_normalizer_X h i) le_normalizer hy)) hg

omit [Finite G] [Finite K] in
theorem conj_mem_NC (i : Axis) {m : G} (hm : m ∈ normalizer (𝐗[i] : Set G)) {z : G}
    (hz : z ∈ 𝐍𝐂[i]) : m * z * m⁻¹ ∈ 𝐍𝐂[i] := by
  have hle : 𝐍𝐂[i] ≤ (𝐍𝐂[i]).comap (MulAut.conj m).toMonoidHom := by
    refine closure_le _ |>.mpr ?_
    rintro _ ⟨g, hg, y, hy, rfl⟩
    refine subset_closure ⟨g * m⁻¹, mul_mem hg (inv_mem hm), y, hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  exact hle hz

theorem normal_NC (h : FCHyp L K n φ t) (i : Axis) :
    ((𝐍𝐂[i]).subgroupOf (normalizer (𝐗[i] : Set G))).Normal :=
  (normal_subgroupOf_iff (NC_le_normalizer_X h i)).mpr fun _ _ hz hm => conj_mem_NC i hm hz

theorem S_le_NC (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : 𝐒 ≤ 𝐍𝐂[i] := by
  obtain ⟨j, hj, hj1⟩ := exists_ne_one_J h i
  have hjN : j ∈ 𝐍𝐂[i] := sup_le_NC i (mem_sup_left (J_le_CU i hj))
  have hj0 := axisTorus_le_J0 i hj
  let f : ↥𝐖'[i] → ↥𝐖'[i] := fun v =>
    ⟨(v : G)⁻¹ * (j⁻¹ * v * j), mul_mem (inv_mem v.2) (conj_J_mem_W' h i hj0 v.2)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have e : (x : G)⁻¹ * (j⁻¹ * x * j) = (y : G)⁻¹ * (j⁻¹ * y * j) :=
      congrArg (fun u : ↥𝐖'[i] => (u : G)) hxy
    have e1 : (y : G) * ((x : G)⁻¹ * (j⁻¹ * x * j)) = j⁻¹ * y * j := by rw [e]; group
    have hfix' : j⁻¹ * ((y : G) * (x : G)⁻¹) * j = (y : G) * (x : G)⁻¹ := by
      calc j⁻¹ * ((y : G) * (x : G)⁻¹) * j = (j⁻¹ * y * j) * (j⁻¹ * x * j)⁻¹ := by group
        _ = (y : G) * ((x : G)⁻¹ * (j⁻¹ * x * j)) * (j⁻¹ * x * j)⁻¹ := by rw [e1]
        _ = (y : G) * (x : G)⁻¹ := by group
    have h1 := fix_W'_eq_one h i hj hj1 (mul_mem y.2 (inv_mem x.2)) hfix'
    exact Subtype.ext (mul_inv_eq_one.mp h1).symm
  intro s hs
  obtain ⟨x, hx, v, hv, rfl⟩ := exists_X_mul_W' h hbt i hs
  obtain ⟨v₀, hv₀⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨v, hv⟩
  have hv' : (v₀ : G)⁻¹ * (j⁻¹ * v₀ * j) = v := congrArg Subtype.val hv₀
  have hv₀N : (v₀ : G)⁻¹ ∈ normalizer (𝐗[i] : Set G) :=
    inv_mem (S_le_normalizer_X h hbt i (X_le_S i.swap (W'_le_X i v₀.2)))
  have h1 : (v₀ : G)⁻¹ * j⁻¹ * (v₀ : G)⁻¹⁻¹ ∈ 𝐍𝐂[i] := conj_mem_NC i hv₀N (inv_mem hjN)
  refine mul_mem (sup_le_NC i (mem_sup_right hx)) ?_
  rw [← hv', show (v₀ : G)⁻¹ * (j⁻¹ * v₀ * j) = (v₀ : G)⁻¹ * j⁻¹ * (v₀ : G)⁻¹⁻¹ * j by group]
  exact mul_mem h1 hjN

theorem K_not_normal (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : ¬ (barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))).Normal := by
  intro hK
  have hNC : 𝐍𝐂[i] ≤ ((barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))).comap
      (barMap 𝐗[i])).map (normalizer (𝐗[i] : Set G)).subtype := by
    refine closure_le _ |>.mpr ?_
    rintro _ ⟨g, hg, y, hy, rfl⟩
    have hy' : y ∈ (𝐗[i] : Set G) * ((L ⊓ centralizer (𝐔[i] : Set G) : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (CU_le_normalizer_X h i), sup_comm]
      exact hy
    obtain ⟨x, hx, c, hc, rfl⟩ := hy'
    refine ⟨⟨g, hg⟩⁻¹ * (⟨x, le_normalizer hx⟩ * ⟨c, CU_le_normalizer_X h i hc⟩) * ⟨g, hg⟩, ?_, ?_⟩
    · refine mem_comap.mpr ?_
      have h1 : barMap 𝐗[i] ⟨x, le_normalizer hx⟩ = 1 := barMap_eq_one_iff.mpr hx
      have e : barMap 𝐗[i] (⟨g, hg⟩⁻¹ * (⟨x, le_normalizer hx⟩ * ⟨c, CU_le_normalizer_X h i hc⟩) *
          ⟨g, hg⟩) = (barMap 𝐗[i] ⟨g, hg⟩)⁻¹ * barMap 𝐗[i] ⟨c, CU_le_normalizer_X h i hc⟩ *
            ((barMap 𝐗[i] ⟨g, hg⟩)⁻¹)⁻¹ := by
        simp only [map_mul, map_inv, h1, one_mul, inv_inv]
      rw [e]
      exact hK.conj_mem _ ⟨⟨c, CU_le_normalizer_X h i hc⟩, mem_subgroupOf.mpr hc, rfl⟩ _
    · rfl
  have hle : barSub 𝐗[i] 𝐒 ≤ barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G)) := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨m', hm', e⟩ := hNC (S_le_NC h hbt i (mem_subgroupOf.mp hm))
    rw [show m' = m from Subtype.ext e] at hm'
    exact hm'
  have hd := card_dvd_of_le hle
  rw [card_barS h hbt i, card_K h i] at hd
  have hq := h.four_le_card
  have hq0 : 0 < Nat.card K := by omega
  have h1 : Nat.card K ∣ Nat.card K ^ 2 - 1 :=
    Nat.dvd_of_mul_dvd_mul_left hq0 (by rw [← pow_two]; exact hd)
  have h2 : Nat.card K ∣ Nat.card K ^ 2 - (Nat.card K ^ 2 - 1) :=
    Nat.dvd_sub (Dvd.intro_left _ (pow_two _).symm) h1
  have h3 : Nat.card K ^ 2 - (Nat.card K ^ 2 - 1) = 1 := by
    have : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ hq0
    omega
  rw [h3] at h2
  have := Nat.le_of_dvd one_pos h2
  omega

end Closure

structure ClosureSetupFacts {G : Type} [Group G] [Finite G] (n : ℕ) (K : Type) [Field K]
    (t : G) (C A B E X S CU J NC : Subgroup G) (s : SL₂ K →* G) (d : Kˣ →* G) : Prop where
  card_X : Nat.card X = (2 ^ n) ^ 6
  card_B : Nat.card B = 2 * (2 ^ n) ^ 3
  maximal_E : ∀ W : Subgroup G,
    Maximal (fun W : Subgroup G => W ≤ E ∧ IsElementaryAbelian 2 W) W ↔ W = X ∨ W = B
  normalizer_E : normalizer (E : Set G) = normalizer (B : Set G)
  normalizer_B_le : normalizer (B : Set G) ≤ normalizer (X : Set G)
  t_mem : t ∈ normalizer (X : Set G)
  orderOf_tau : orderOf (barMap X ⟨t, t_mem⟩) = 2
  centralizer_tau : centralizer ({barMap X ⟨t, t_mem⟩} : Set (BarM X)) =
    barSub X (normalizer (B : Set G))
  quotient_C : ∃ _ : (A.subgroupOf (C ⊓ normalizer (B : Set G))).Normal,
    ∃ e : (↥(C ⊓ normalizer (B : Set G)) ⧸ A.subgroupOf (C ⊓ normalizer (B : Set G))) ≃*
      ↥(centralizer ({barMap X ⟨t, t_mem⟩} : Set (BarM X))),
      ∀ (c : ↥(C ⊓ normalizer (B : Set G))) (m : ↥(normalizer (X : Set G))), (c : G) = m →
        (e c : BarM X) = barMap X m
  CU_le : CU ≤ normalizer (X : Set G)
  equiv_K : ∃ e : SL₂ K ≃* ↥(barSub X CU), ∀ (M : SL₂ K) (m : ↥(normalizer (X : Set G))),
    (m : G) = s M → (e M : BarM X) = barMap X m
  simple_K : IsSimpleGroup ↥(barSub X CU)
  K_le : barSub X CU ≤ centralizer ({barMap X ⟨t, t_mem⟩} : Set (BarM X))
  K_normal :
    ((barSub X CU).subgroupOf (centralizer ({barMap X ⟨t, t_mem⟩} : Set (BarM X)))).Normal
  centralizer_K : centralizer ({barMap X ⟨t, t_mem⟩} : Set (BarM X)) ⊓
      centralizer (barSub X CU : Set (BarM X)) = zpowers (barMap X ⟨t, t_mem⟩) ⊔ barSub X d.range
  d_le : barSub X d.range ≤ centralizer ({barMap X ⟨t, t_mem⟩} : Set (BarM X))
  tau_inf_d : zpowers (barMap X ⟨t, t_mem⟩) ⊓ barSub X d.range = ⊥
  card_d : Nat.card (barSub X d.range) = 2 ^ n - 1
  card_centralizer_K :
    Nat.card ↥(zpowers (barMap X ⟨t, t_mem⟩) ⊔ barSub X d.range) = 2 * (2 ^ n - 1)
  sylow_Y : ∃ V : Sylow 2 ↥(centralizer (barSub X CU : Set (BarM X))),
    (V : Subgroup _).map (centralizer (barSub X CU : Set (BarM X))).subtype =
      zpowers (barMap X ⟨t, t_mem⟩)
  even_Y : Even (Nat.card (centralizer (barSub X CU : Set (BarM X))))
  tight_Y : ∀ g : BarM X,
    g ∉ normalizer (centralizer (barSub X CU : Set (BarM X)) : Set (BarM X)) →
      Odd (Nat.card (centralizer (barSub X CU : Set (BarM X)) ⊓
        (centralizer (barSub X CU : Set (BarM X))).map (MulAut.conj g).toMonoidHom :
          Subgroup (BarM X)))
  normalizer_K : normalizer (barSub X CU : Set (BarM X)) =
    normalizer (centralizer (barSub X CU : Set (BarM X)) : Set (BarM X))
  standard_K : CFSG.Open.standardComponentIsStandard (barSub X CU)
  not_normal_K : ¬ (barSub X CU).Normal
  J_le : J ≤ CU
  J_le_normalizer : J ≤ normalizer (X : Set G) ⊓ normalizer (S : Set G)
  J_fpf : ∀ j ∈ J, j ≠ 1 → ∀ x ∈ S, x⁻¹ * (j⁻¹ * x * j) ∈ X → x ∈ X
  X_le_S : X ≤ S
  S_le : S ≤ normalizer (X : Set G)
  card_S : Nat.card (barSub X S) = (2 ^ n) ^ 2
  elem_S : IsElementaryAbelian 2 ↥(barSub X S)
  rank_S : Group.rank ↥(barSub X S) = 2 * n
  tau_S : barMap X ⟨t, t_mem⟩ ∈ normalizer (barSub X S : Set (BarM X))
  NC_normal : X ≤ NC ∧ NC ≤ normalizer (X : Set G) ∧
    (NC.subgroupOf (normalizer (X : Set G))).Normal
  S_le_NC : S ≤ NC

section Facts

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)

theorem closureSetupFacts (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) :
    ClosureSetupFacts n K t (centralizer ({t} : Set G)) 𝐀[i]
      (zpowers t ⊔ pull φ (rootA K i)) 𝐄[i] 𝐗[i] (𝐗[Axis.one] ⊔ 𝐗[Axis.two])
      (L ⊓ centralizer (𝐔[i] : Set G)) (pull φ (axisTorus K i))
      (closure {x : G | ∃ g ∈ normalizer (𝐗[i] : Set G),
        ∃ y ∈ (L ⊓ centralizer (𝐔[i] : Set G) : Subgroup G) ⊔ 𝐗[i], x = g⁻¹ * y * g})
      (L.subtype.comp (φ.symm.toMonoidHom.comp (sHom K i)))
      (L.subtype.comp (φ.symm.toMonoidHom.comp (dHom K i))) := by
  have hq := h.setup.card_K
  obtain ⟨hV, hstd⟩ := standard_K h hbt i
  obtain ⟨-, heven, htight, hnorm, -⟩ := hstd
  refine
    { card_X := by rw [card_X h i, hq]
      card_B := by rw [FCHyp.card_B h i, hq]
      maximal_E := maximal_E h hbt i
      normalizer_E := normalizer_E h hbt i
      normalizer_B_le := N_le_normalizer_X h hbt i
      t_mem := t_mem_normalizer_X h i
      orderOf_tau := orderOf_tau h i
      centralizer_tau := centralizer_tau h hbt i
      quotient_C := quotient_C h hbt i
      CU_le := CU_le_normalizer_X h i
      equiv_K := equiv_K h i
      simple_K := simple_K h i
      K_le := K_le_centralizer_tau h hbt i
      K_normal := K_normal h hbt i
      centralizer_K := centralizer_K h hbt i
      d_le := dbar_le_centralizer_tau h hbt i
      tau_inf_d := tau_inf_dbar h i
      card_d := by rw [card_dbar h hbt i, hq]
      card_centralizer_K := by rw [card_centralizer_K h hbt i, hq]
      sylow_Y := hV
      even_Y := heven
      tight_Y := htight
      normalizer_K := hnorm.symm
      standard_K := (standard_K h hbt i).2
      not_normal_K := K_not_normal h hbt i
      J_le := J_le_CU i
      J_le_normalizer := J_le_normalizer h i
      J_fpf := fun j hj hj1 x hx hfix => J_fpf h hbt i hj hj1 hx hfix
      X_le_S := X_le_S i
      S_le := S_le_normalizer_X h hbt i
      card_S := by rw [card_barS h hbt i, hq]
      elem_S := barS_elem h hbt i
      rank_S := rank_barS h hbt i
      tau_S := tau_mem_normalizer_barS h hbt i
      NC_normal := ⟨le_sup_right.trans (sup_le_NC i), NC_le_normalizer_X h i, normal_NC h i⟩
      S_le_NC := S_le_NC h hbt i }

end Facts

end BothTrivialClosure

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial BothTrivialHeisenberg
  BothTrivialClosure
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

end CFSG.LocalAnalysis.SymplecticFourStandard
