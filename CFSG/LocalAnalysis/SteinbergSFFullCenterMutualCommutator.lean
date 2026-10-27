module

public import CFSG.LocalAnalysis.SteinbergSFFullCenterWeylOvergroups

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace FullCenterMutual

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

theorem swap_swap_axis (i : Axis) : i.swap.swap = i := by
  cases i <;> rfl

section Mutual

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
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
local notation "𝐐[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐃[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐑[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐄[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐇" => (𝐐[Axis.one] ⊔ 𝐐[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐉[" i "]" => pull φ (axisTorus K i)
set_option quotPrecheck false in
local notation "𝐖[" i "]" => (𝐅 ⊓ centralizer (𝐉[i] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊[" i "]" => (𝐀[i] ⊔ (𝐅 ⊓ 𝐃[i]) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊⋆" => (𝐊[Axis.one] ⊔ 𝐊[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐋[" i "]" => (𝐅 ⊔ 𝐀[i] : Subgroup G)

omit [Finite G] [Finite K] in
theorem P_eq_A_sup_A_swap (i : Axis) : 𝐏 = 𝐀[i] ⊔ 𝐀[i.swap] := by
  cases i
  · exact P_eq_A_sup_A
  · rw [P_eq_A_sup_A, sup_comm]
    rfl

theorem A_le_Ks (h : FCHyp L K n φ t) (i : Axis) : 𝐀[i] ≤ 𝐊⋆ := by
  rw [Ks_eq h]
  exact (pull_mono φ (rootA_le_antiUnipotent i)).trans le_sup_right

theorem conj_R_mem_Ks (h : FCHyp L K n φ t) (i : Axis) {r : G} (hr : r ∈ 𝐑[i]) {k : G}
    (hk : k ∈ 𝐊⋆) : r * k * r⁻¹ ∈ 𝐊⋆ := by
  obtain ⟨hKR, hKn⟩ := Ks_normal_R h i
  exact mem_subgroupOf.mp (hKn.conj_mem ⟨k, hKR hk⟩ (mem_subgroupOf.mpr hk) ⟨r, hr⟩)

theorem exists_W_swap_mul (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ 𝐅) :
    ∃ w ∈ 𝐖[i], ∃ w' ∈ 𝐖[i.swap], w * w' = x := by
  rw [← SetLike.mem_coe, ← W_mul_W h] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  cases i
  · exact ⟨a, ha, b, hb, rfl⟩
  · exact ⟨b, hb, a, ha, (W_comm h ha hb).symm⟩

theorem comm_Ks_Fi (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ 𝐅 ⊓ 𝐃[i]) {k : G}
    (hk : k ∈ 𝐊⋆) : k * x * k⁻¹ * x⁻¹ ∈ 𝐔[i.swap] := by
  let S : Subgroup G :=
    { carrier := {k | k ∈ 𝐇 ∧ k * x * k⁻¹ * x⁻¹ ∈ 𝐔[i.swap]}
      mul_mem' := by
        rintro a b ⟨haH, ha⟩ ⟨hbH, hb⟩
        refine ⟨mul_mem haH hbH, ?_⟩
        have hbZ : b * x * b⁻¹ * x⁻¹ ∈ 𝐙 := pull_mono φ (rootU_le_center _) hb
        have e1 : a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ = b * x * b⁻¹ * x⁻¹ := by
          rw [comm_ZP h haH hbZ, mul_inv_cancel_right]
        rw [show a * b * x * (a * b)⁻¹ * x⁻¹ =
          (a * (b * x * b⁻¹ * x⁻¹) * a⁻¹) * (a * x * a⁻¹ * x⁻¹) by group, e1]
        exact mul_mem hb ha
      one_mem' := ⟨one_mem _, by
        rw [one_mul, inv_one, mul_one, mul_inv_cancel]
        exact one_mem _⟩
      inv_mem' := by
        rintro a ⟨haH, ha⟩
        refine ⟨inv_mem haH, ?_⟩
        have haZ : a * x * a⁻¹ * x⁻¹ ∈ 𝐙 := pull_mono φ (rootU_le_center _) ha
        have e1 : a⁻¹ * (a * x * a⁻¹ * x⁻¹) * a = a * x * a⁻¹ * x⁻¹ := by
          rw [comm_ZP h (inv_mem haH) haZ, inv_mul_cancel_right]
        rw [show a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ = (a⁻¹ * (a * x * a⁻¹ * x⁻¹) * a)⁻¹ by group, e1]
        exact inv_mem ha }
  have hcomm : ∀ {a : G}, a ∈ 𝐇 → a * x = x * a → a ∈ S := fun {a} haH hax => ⟨haH, by
    rw [hax, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _⟩
  have hFS : 𝐅 ≤ S := fun f hf => hcomm (F_le_H h hf) (F_comm h hf hx.1)
  have hAS : 𝐀[i] ≤ S := fun a ha => hcomm (A_le_H h i ha) (A_comm_D h i ha hx.2)
  have hAS' : 𝐀[i.swap] ≤ S := fun a ha => ⟨A_le_H h i.swap ha, by
    have := inv_mem (commE_mem_U h i.swap (F_le_E h i.swap hx.1) ha)
    rwa [show (x * a * x⁻¹ * a⁻¹)⁻¹ = a * x * a⁻¹ * x⁻¹ by group] at this⟩
  have hKS : 𝐊⋆ ≤ S := by
    rw [Ks_eq h, P_eq_A_sup_A_swap i]
    exact sup_le hFS (sup_le hAS hAS')
  exact (hKS hk).2

theorem conj_R_ZP (h : FCHyp L K n φ t) (i : Axis) {r : G} (hr : r ∈ 𝐑[i]) {z : G}
    (hz : z ∈ 𝐙) : r * z * r⁻¹ * z⁻¹ ∈ 𝐔[i] := by
  rw [← SetLike.mem_coe, ← R_mul h i] at hr
  obtain ⟨q, hq, e, he, rfl⟩ := hr
  have hc := commE_mem_U h i he (pull_mono φ (center_le_rootA i) hz)
  have hcZ : e * z * e⁻¹ * z⁻¹ ∈ 𝐙 := pull_mono φ (rootU_le_center i) hc
  have hez : e * z * e⁻¹ = (e * z * e⁻¹ * z⁻¹) * z := by group
  have h1 : q * (e * z * e⁻¹) * q⁻¹ = e * z * e⁻¹ := by
    rw [h.Q_comm_ZP hq (hez ▸ mul_mem hcZ hz), mul_inv_cancel_right]
  rw [show q * e * z * (q * e)⁻¹ * z⁻¹ = q * (e * z * e⁻¹) * q⁻¹ * z⁻¹ by group, h1]
  exact hc

theorem eq_one_of_conj_R_mem_U (h : FCHyp L K n φ t) (i : Axis) {r : G} (hr : r ∈ 𝐑[i])
    {u : G} (hu : u ∈ 𝐔[i.swap]) (hru : r * u * r⁻¹ ∈ 𝐔[i]) : u = 1 := by
  have hc := conj_R_ZP h i hr (pull_mono φ (rootU_le_center i.swap) hu)
  have huU : u ∈ 𝐔[i] := by
    have := mul_mem (inv_mem hc) hru
    rwa [show (r * u * r⁻¹ * u⁻¹)⁻¹ * (r * u * r⁻¹) = u by group] at this
  have := mem_inf.mpr ⟨huU, hu⟩
  rwa [U_inf_U_swap i, mem_bot] at this

theorem conj_R_mem_Fi (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    {r : G} (hr : r ∈ 𝐑[i]) {x : G} (hx : x ∈ 𝐅 ⊓ 𝐃[i]) : r * x * r⁻¹ ∈ 𝐅 ⊓ 𝐃[i] := by
  obtain ⟨-, -, hcent⟩ := centers_of_ne_bot h i hne
  have hkey : ∀ y ∈ 𝐊⋆, r * x * r⁻¹ * y * (r * x * r⁻¹)⁻¹ * y⁻¹ ∈ 𝐔[i] →
      r * x * r⁻¹ * y = y * (r * x * r⁻¹) := by
    intro y hy hyU
    have hy' : r⁻¹ * y * r⁻¹⁻¹ ∈ 𝐊⋆ := conj_R_mem_Ks h i (inv_mem hr) hy
    rw [inv_inv] at hy'
    have hc := inv_mem (comm_Ks_Fi h i hx hy')
    rw [show (r⁻¹ * y * r * x * (r⁻¹ * y * r)⁻¹ * x⁻¹)⁻¹ =
      x * (r⁻¹ * y * r) * x⁻¹ * (r⁻¹ * y * r)⁻¹ by group] at hc
    have e1 : r * x * r⁻¹ * y * (r * x * r⁻¹)⁻¹ * y⁻¹ =
        r * (x * (r⁻¹ * y * r) * x⁻¹ * (r⁻¹ * y * r)⁻¹) * r⁻¹ := by group
    rw [e1] at hyU
    have h1 := eq_one_of_conj_R_mem_U h i hr hc hyU
    calc r * x * r⁻¹ * y = r * (x * (r⁻¹ * y * r) * x⁻¹ * (r⁻¹ * y * r)⁻¹) * r⁻¹ *
          (y * (r * x * r⁻¹)) := by group
      _ = y * (r * x * r⁻¹) := by rw [h1, mul_one, mul_inv_cancel, one_mul]
  have hxL : r * x * r⁻¹ ∈ 𝐋[i] := conj_R_mem_L h i hr (F_le_L i hx.1)
  rw [← SetLike.mem_coe, ← L_mul h i] at hxL
  obtain ⟨f, hf, a, ha, hfa⟩ := hxL
  obtain ⟨y, hy, hyZ⟩ := exists_Fi_not_ZP h i.swap
  have hay : y * a = a * y := by
    have hc := inv_mem (commE_mem_U h i (F_le_E h i hy.1) ha)
    rw [show (y * a * y⁻¹ * a⁻¹)⁻¹ = a * y * a⁻¹ * y⁻¹ by group] at hc
    have hcZ : a * y * a⁻¹ * y⁻¹ ∈ 𝐙 := pull_mono φ (rootU_le_center i) hc
    have e1 : r * x * r⁻¹ * y * (r * x * r⁻¹)⁻¹ * y⁻¹ = a * y * a⁻¹ * y⁻¹ := by
      rw [← hfa]
      calc f * a * y * (f * a)⁻¹ * y⁻¹ = f * (a * y * a⁻¹ * y⁻¹) * (y * f⁻¹ * y⁻¹) := by group
        _ = (a * y * a⁻¹ * y⁻¹) * (f * y * f⁻¹ * y⁻¹) := by
          rw [comm_ZP h (F_le_H h hf) hcZ]
          group
        _ = a * y * a⁻¹ * y⁻¹ := by
          rw [F_comm h hf hy.1, mul_inv_cancel_right, mul_inv_cancel, mul_one]
    have hyK : y ∈ 𝐊⋆ := by
      rw [Ks_eq h]
      exact mem_sup_left hy.1
    have h1 := hkey y hyK (e1 ▸ hc)
    have h2 : a * y * a⁻¹ * y⁻¹ = 1 := by
      rw [← e1, h1]
      group
    calc y * a = (a * y * a⁻¹ * y⁻¹)⁻¹ * (a * y) := by group
      _ = a * y := by rw [h2, inv_one, one_mul]
  have haZ : a ∈ 𝐙 := by
    rw [← hcent y hy hyZ]
    exact mem_inf.mpr ⟨ha, mem_centralizer_singleton_iff.mpr hay.symm⟩
  have hxF : r * x * r⁻¹ ∈ 𝐅 := by
    rw [← hfa]
    exact mul_mem hf (ZP_le_F h haZ)
  have hxA : ∀ b ∈ 𝐀[i], r * x * r⁻¹ * b = b * (r * x * r⁻¹) := fun b hb =>
    hkey b (A_le_Ks h i hb) (commE_mem_U h i (F_le_E h i hxF) hb)
  obtain ⟨w, hw, w', hw', hww'⟩ := exists_W_swap_mul h i hxF
  have hw'Z : w' ∈ 𝐙 := by
    by_contra hw'Z
    have h1 := hcent w' (W_le_Fi h i.swap hw') hw'Z
    have hle : 𝐀[i] ≤ 𝐙 := fun b hb => by
      rw [← h1]
      refine mem_inf.mpr ⟨hb, mem_centralizer_singleton_iff.mpr ?_⟩
      have h2 := hxA b hb
      rw [← hww'] at h2
      have h3 : w * b = b * w := (A_comm_D h i hb (W_le_Fi h i hw).2).symm
      have h4 : w * (w' * b) = w * (b * w') := by
        calc w * (w' * b) = w * w' * b := by group
          _ = b * (w * w') := h2
          _ = (b * w) * w' := by group
          _ = (w * b) * w' := by rw [h3]
          _ = w * (b * w') := by group
      exact (mul_left_cancel h4).symm
    have h5 := card_le_of_le hle
    rw [card_pull, card_rootA, FCHyp.card_ZP] at h5
    have h6 := h.four_le_card
    have h7 : Nat.card K ^ 2 < Nat.card K ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  rw [← hww']
  exact mul_mem (W_le_Fi h i hw) (ZP_le_Fi h i hw'Z)

theorem false_of_ne_bot (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hne' : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ ≠ ⊥) : False := by
  obtain ⟨-, hZR, -⟩ := centers_of_ne_bot h i hne
  have hU : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = 𝐔[i.swap] := by
    have h1 := cross_dich h i.swap
    rw [swap_swap_axis] at h1
    exact (h1.resolve_left hne').1
  have hUZ : 𝐔[i.swap] ≤ (center 𝐑[i]).map 𝐑[i].subtype := by
    intro u hu
    have huZ : u ∈ 𝐙 := pull_mono φ (rootU_le_center _) hu
    refine mem_center_map_iff.mpr ⟨mem_sup_left (mem_sup_left (Setup.ZP_le_PG huZ)),
      fun r hr => ?_⟩
    have h1 : r * u * r⁻¹ ∈ 𝐔[i.swap] := by
      have h2 : r * u * r⁻¹ ∈ (⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆).map (MulAut.conj r).toMonoidHom :=
        ⟨u, hU ▸ hu, rfl⟩
      rw [map_commutator] at h2
      refine (commutator_le.mpr ?_) h2
      rintro _ ⟨a, ha, rfl⟩ _ ⟨x, hx, rfl⟩
      rw [commutatorElement_def]
      exact comm_Ks_Fi h i (conj_R_mem_Fi h i hne hr hx)
        (conj_R_mem_Ks h i hr (A_le_Ks h i.swap ha))
    have h3 := conj_R_ZP h i hr huZ
    have h4 := mem_inf.mpr ⟨h3, mul_mem h1 (inv_mem hu)⟩
    rw [U_inf_U_swap i, mem_bot] at h4
    calc r * u = r * u * r⁻¹ * u⁻¹ * (u * r) := by group
      _ = u * r := by rw [h4, one_mul]
  rw [hZR] at hUZ
  have h7 : 𝐔[i.swap] ≤ 𝐔[i] ⊓ 𝐔[i.swap] := le_inf hUZ le_rfl
  rw [U_inf_U_swap i] at h7
  have h8 := card_le_of_le h7
  rw [FCHyp.card_U, card_bot] at h8
  have := h.four_le_card
  omega

theorem bot_or_bot (h : FCHyp L K n φ t) (i : Axis) :
    ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥ ∨ ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥ := by
  by_contra hcon
  obtain ⟨h1, h2⟩ := not_or.mp hcon
  exact false_of_ne_bot h i h1 h2

end Mutual

end FullCenterMutual

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

theorem standard_symplectic_four_full_center_mutual_commutator_exclusion
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
    let U : Axis → Subgroup G := fun i => ((rootU K i).comap φ.toMonoidHom).map L.subtype
    let A : Axis → Subgroup G := fun i => ((rootA K i).comap φ.toMonoidHom).map L.subtype
    let V : Axis → Subgroup G := fun i => zpowers (t : G) ⊔ U i
    let B : Axis → Subgroup G := fun i => zpowers (t : G) ⊔ A i
    let M : Axis → Subgroup G := fun i => normalizer (V i : Set G)
    let N : Axis → Subgroup G := fun i => normalizer (B i : Set G)
    let D : Axis → Subgroup G := fun i => (CFSG.pCore 2 (M i)).map (M i).subtype
    let E : Axis → Subgroup G := fun i => (CFSG.pCore 2 (N i)).map (N i).subtype
    let E₀ := E Axis.one ⊓ E Axis.two
    let J₀ := ((diagTorus K).comap φ.toMonoidHom).map L.subtype
    let F := closure {x : G | ∃ e ∈ E₀, ∃ j ∈ J₀, x = e⁻¹ * (j⁻¹ * e * j)}
    let Fi : Axis → Subgroup G := fun i => F ⊓ D i
    {x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ z ∈ ZP, x = t * z} →
    ⁅A Axis.one, Fi Axis.two⁆ = ⊥ ∨ ⁅A Axis.two, Fi Axis.one⁆ = ⊥ := by
  intro TG PG Q ZP U A V B M N D E E₀ J₀ F Fi hfull
  have hS := setup_of_standard hL hn hK φ T hT htT ht hcore
  have hPG : PG = pull φ (antiUnipotent K) := by
    change (P : Subgroup L).map L.subtype = ((antiUnipotent K).comap φ.toMonoidHom).map L.subtype
    rw [← hφP, comap_map_eq_self_of_injective φ.injective]
  have hZP : ZP = pull φ (antiUnipotentCenter K) := by
    change (center ↥PG).map PG.subtype = _
    rw [hPG, center_pull_antiUnipotent]
  have hfull' : {x : G | ∃ m ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) :
      Set G), x = m⁻¹ * t * m} = {x | ∃ z ∈ pull φ (antiUnipotentCenter K), x = t * z} := by
    rw [← hPG, ← hZP]
    exact hfull
  obtain ⟨hTG₀, hF⟩ := FCHyp.of_setup hS (hO := hO) hLn hfull'
  have hTG : TG = zpowers (t : G) := hTG₀
  clear_value ZP PG TG
  subst hTG hPG hZP
  exact FullCenterMutual.bot_or_bot hF Axis.one

end CFSG.LocalAnalysis.SymplecticFourStandard
