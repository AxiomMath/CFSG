module

public import CFSG.LocalAnalysis.SteinbergSFFullCenterWeylOvergroupsProducts

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace FullCenterWeyl

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

section Cross

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
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
local notation "𝐋[" i "]" => (𝐅 ⊔ 𝐀[i] : Subgroup G)
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐅ʷ[" i "]" => (𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)

theorem commutator_A_F (h : FCHyp L K n φ t) (i : Axis) : ⁅𝐀[i], 𝐅⁆ ≤ 𝐔[i] := by
  rw [commutator_comm]
  exact (commutator_mono (F_le_E h i) le_rfl).trans (commutator_E_A h i)

theorem commE_mem_U (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ 𝐄[i]) {a : G}
    (ha : a ∈ 𝐀[i]) : x * a * x⁻¹ * a⁻¹ ∈ 𝐔[i] := by
  have := commutator_le.mp (commutator_E_A h i) x hx a ha
  rwa [commutatorElement_def] at this

theorem L_quot_comm (h : FCHyp L K n φ t) (i : Axis) :
    𝐔[i] ≤ 𝐋[i] ∧ ∃ _ : ((𝐔[i]).subgroupOf 𝐋[i]).Normal,
      IsMulCommutative (↥𝐋[i] ⧸ (𝐔[i]).subgroupOf 𝐋[i]) := by
  have hUL : 𝐔[i] ≤ 𝐋[i] := (pull_mono φ (rootU_le_rootA i)).trans (A_le_L i)
  have hc : ∀ {e u : G}, e ∈ 𝐄[i] → u ∈ 𝐔[i] → e * u = u * e := fun {e u} he hu => by
    calc e * u = (e * u * e⁻¹) * e := by group
      _ = u * e := by rw [E_comm_U h i he hu]
  have hcomm : ∀ x ∈ 𝐋[i], ∀ y ∈ 𝐋[i], x * y * x⁻¹ * y⁻¹ ∈ 𝐔[i] := by
    have hmulL : ∀ {a b c : G}, a ∈ 𝐄[i] → a * c * a⁻¹ * c⁻¹ ∈ 𝐔[i] →
        b * c * b⁻¹ * c⁻¹ ∈ 𝐔[i] → (a * b) * c * (a * b)⁻¹ * c⁻¹ ∈ 𝐔[i] := by
      intro a b c ha h1 h2
      rw [show (a * b) * c * (a * b)⁻¹ * c⁻¹ =
        (a * (b * c * b⁻¹ * c⁻¹) * a⁻¹) * (a * c * a⁻¹ * c⁻¹) by group, E_comm_U h i ha h2]
      exact mul_mem h2 h1
    have hmulR : ∀ {a b c : G}, b ∈ 𝐄[i] → a * b * a⁻¹ * b⁻¹ ∈ 𝐔[i] →
        a * c * a⁻¹ * c⁻¹ ∈ 𝐔[i] → a * (b * c) * a⁻¹ * (b * c)⁻¹ ∈ 𝐔[i] := by
      intro a b c hb h1 h2
      rw [show a * (b * c) * a⁻¹ * (b * c)⁻¹ =
        (a * b * a⁻¹ * b⁻¹) * (b * (a * c * a⁻¹ * c⁻¹) * b⁻¹) by group, E_comm_U h i hb h2]
      exact mul_mem h1 h2
    have hcomm1 : ∀ {a b : G}, a * b = b * a → a * b * a⁻¹ * b⁻¹ ∈ 𝐔[i] := fun hab => by
      rw [hab, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    intro x hx y hy
    rw [← SetLike.mem_coe, ← L_mul h i] at hx hy
    obtain ⟨f, hf, a, ha, rfl⟩ := hx
    obtain ⟨g, hg, b, hb, rfl⟩ := hy
    have hfE := F_le_E h i hf
    have hgE := F_le_E h i hg
    have hfb : f * b * f⁻¹ * b⁻¹ ∈ 𝐔[i] := commE_mem_U h i hfE hb
    have hag : a * g * a⁻¹ * g⁻¹ ∈ 𝐔[i] := by
      have := inv_mem (commE_mem_U h i hgE ha)
      rwa [show (g * a * g⁻¹ * a⁻¹)⁻¹ = a * g * a⁻¹ * g⁻¹ by group] at this
    refine hmulL hfE (hmulR hgE (hcomm1 (F_comm h hf hg)) hfb)
      (hmulR hgE hag (hcomm1 (A_mul_comm h i ha hb)))
  have hn : ((𝐔[i]).subgroupOf 𝐋[i]).Normal := ⟨fun u hu x => by
    rw [mem_subgroupOf] at hu ⊢
    rw [coe_mul, coe_mul, coe_inv, E_comm_U h i (L_le_E h i x.2) hu]
    exact hu⟩
  refine ⟨hUL, hn, ⟨⟨fun q₁ q₂ => ?_⟩⟩⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q₁
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q₂
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
  set c := (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ with hc_def
  have h1 : c ∈ 𝐔[i] := hcomm _ x.2 _ y.2
  have hyx : (y : G) * x ∈ 𝐄[i] := mul_mem (L_le_E h i y.2) (L_le_E h i x.2)
  have e1 : ((x : G) * y)⁻¹ * (y * x) = c⁻¹ := by
    have e2 : ((x : G) * y)⁻¹ * (y * x) = ((y : G) * x)⁻¹ * c⁻¹ * (y * x) := by
      rw [hc_def]
      group
    rw [e2, mul_assoc, ← hc hyx (inv_mem h1), inv_mul_cancel_left]
  simp only [coe_mul, coe_inv]
  rw [e1]
  exact inv_mem h1

theorem comm_A_of (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ 𝐅 ⊓ 𝐃[i.swap]) {a₀ : G}
    (ha₀ : a₀ ∈ 𝐀[i]) (ha₀Z : a₀ ∉ 𝐙) (hxa₀ : x * a₀ = a₀ * x) {a : G} (ha : a ∈ 𝐀[i]) :
    x * a = a * x := by
  have hxH : x ∈ 𝐇 := F_le_H h hx.1
  by_cases haZ : a ∈ 𝐙
  · exact comm_ZP h hxH haZ
  obtain ⟨g, hgJ, hgz⟩ := exists_Jswap_conj h i ha₀ ha ha₀Z haZ
  have hgJ0 : g ∈ 𝐉 := axisTorus_le_J0 _ hgJ
  have hz' : x⁻¹ * (g⁻¹ * x * g) ∈ 𝐙 := mu_mem_ZP h i.swap hx hgJ
  have hga₀ : g⁻¹ * a₀ * g ∈ 𝐀[i] := by
    have := (mem_normalizer_iff.mp (FCHyp.torus_le_normalizer_A i (inv_mem hgJ0)) a₀).mp ha₀
    rwa [inv_inv] at this
  set b := g⁻¹ * a₀ * g with hb
  set z' := x⁻¹ * (g⁻¹ * x * g) with hz'def
  have h1 : (x * z') * b = b * (x * z') := by
    rw [hz'def, hb]
    calc x * (x⁻¹ * (g⁻¹ * x * g)) * (g⁻¹ * a₀ * g) = g⁻¹ * (x * a₀) * g := by group
      _ = g⁻¹ * (a₀ * x) * g := by rw [hxa₀]
      _ = g⁻¹ * a₀ * g * (x * (x⁻¹ * (g⁻¹ * x * g))) := by group
  have hcz : z' * b = b * z' := (comm_ZP h (A_le_H h i hga₀) hz').symm
  have h2 : x * b = b * x := by
    have h3 : x * b * z' = b * x * z' := by
      calc x * b * z' = x * (z' * b) := by rw [mul_assoc, ← hcz]
        _ = (x * z') * b := by group
        _ = b * (x * z') := h1
        _ = b * x * z' := by group
    exact mul_right_cancel h3
  have hxz : x * ((b)⁻¹ * a) = (b⁻¹ * a) * x := comm_ZP h hxH hgz
  have e : a = b * (b⁻¹ * a) := by group
  rw [e]
  calc x * (b * (b⁻¹ * a)) = (x * b) * (b⁻¹ * a) := by group
    _ = (b * x) * (b⁻¹ * a) := by rw [h2]
    _ = b * (x * (b⁻¹ * a)) := by group
    _ = b * ((b⁻¹ * a) * x) := by rw [hxz]
    _ = b * (b⁻¹ * a) * x := by group

theorem comm_F_of (h : FCHyp L K n φ t) (i : Axis) {x₀ : G} (hx₀ : x₀ ∈ 𝐅 ⊓ 𝐃[i.swap])
    (hx₀Z : x₀ ∉ 𝐙) (hx₀A : ∀ a ∈ 𝐀[i], x₀ * a = a * x₀) {x : G} (hx : x ∈ 𝐅 ⊓ 𝐃[i.swap])
    {a : G} (ha : a ∈ 𝐀[i]) : x * a = a * x := by
  have hxH : x ∈ 𝐇 := F_le_H h hx.1
  by_cases hxZ : x ∈ 𝐙
  · exact (comm_ZP h (A_le_H h i ha) hxZ).symm
  have hκ₀ := kappa_mem_U h i.swap hx₀.2
  have hκ := kappa_mem_U h i.swap hx.2
  obtain ⟨c₀, hc₀⟩ := exists_coordG_eq φ i.swap hκ₀
  obtain ⟨c, hc⟩ := exists_coordG_eq φ i.swap hκ
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [coordG_zero] at hc₀
    exact hx₀Z (mem_ZP_of_mem_F h hx₀.1 (kappa_eq_one_iff.mp hc₀.symm))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [coordG_zero] at hc
    exact hxZ (mem_ZP_of_mem_F h hx.1 (kappa_eq_one_iff.mp hc.symm))
  obtain ⟨δ, hδ, hδc⟩ := FCHyp.torus_trans (φ := φ) i.swap hc₀0 hc0
  set y := δ * x₀ * δ⁻¹ with hy_def
  have hy : y ∈ 𝐅 ⊓ 𝐃[i.swap] := by
    have h1 := conj_torus_mem_F h (inv_mem hδ) hx₀.1
    have h2 := conj_torus_mem_D h i.swap (inv_mem hδ) hx₀.2
    rw [inv_inv] at h1 h2
    exact mem_inf.mpr ⟨h1, h2⟩
  have hyκ : t⁻¹ * (y⁻¹ * t * y) = t⁻¹ * (x⁻¹ * t * x) := by
    have := kappa_conj_torus h (inv_mem hδ) x₀
    rw [inv_inv] at this
    rw [hy_def, this, ← hc₀, hδc, hc]
  have hyH := F_le_H h hy.1
  have hz : y⁻¹ * x ∈ 𝐙 := by
    refine mem_ZP_of_mem_F h (mul_mem (inv_mem hy.1) hx.1) (kappa_eq_one_iff.mp ?_)
    rw [kappa_mul h (inv_mem hyH) hxH, kappa_inv h hyH, hyκ, inv_mul_cancel]
  have hδa : δ⁻¹ * a * δ ∈ 𝐀[i] := by
    have := (mem_normalizer_iff.mp (FCHyp.torus_le_normalizer_A i (inv_mem hδ)) a).mp ha
    rwa [inv_inv] at this
  have hya : y * a = a * y := by
    rw [hy_def]
    calc δ * x₀ * δ⁻¹ * a = δ * (x₀ * (δ⁻¹ * a * δ)) * δ⁻¹ := by group
      _ = δ * ((δ⁻¹ * a * δ) * x₀) * δ⁻¹ := by rw [hx₀A _ hδa]
      _ = a * (δ * x₀ * δ⁻¹) := by group
  have hza : (y⁻¹ * x) * a = a * (y⁻¹ * x) := (comm_ZP h (A_le_H h i ha) hz).symm
  have e : x = y * (y⁻¹ * x) := by group
  rw [e]
  calc y * (y⁻¹ * x) * a = y * ((y⁻¹ * x) * a) := by group
    _ = y * (a * (y⁻¹ * x)) := by rw [hza]
    _ = (y * a) * (y⁻¹ * x) := by group
    _ = (a * y) * (y⁻¹ * x) := by rw [hya]
    _ = a * (y * (y⁻¹ * x)) := by group

theorem exists_Fi_not_ZP (h : FCHyp L K n φ t) (i : Axis) :
    ∃ x ∈ 𝐅 ⊓ 𝐃[i], x ∉ 𝐙 := by
  have hnle : ¬ (𝐅 ⊓ 𝐃[i] : Subgroup G) ≤ 𝐙 := fun hle => by
    have h1 := card_le_of_le hle
    rw [card_Fi h, FCHyp.card_ZP] at h1
    have h4 := h.four_le_card
    have h5 : Nat.card K ^ 2 < Nat.card K ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  exact IsConcreteLE.not_le_iff_exists.mp hnle

theorem cross_dich (h : FCHyp L K n φ t) (i : Axis) :
    ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥ ∨ (⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = 𝐔[i] ∧
      ∀ x ∈ 𝐅 ⊓ 𝐃[i.swap], x ∉ 𝐙 → 𝐀[i] ⊓ centralizer ({x} : Set G) = 𝐙) := by
  by_cases hex : ∃ x₀ ∈ 𝐅 ⊓ 𝐃[i.swap], x₀ ∉ 𝐙 ∧ ∀ a ∈ 𝐀[i], x₀ * a = a * x₀
  · left
    obtain ⟨x₀, hx₀, hx₀Z, hx₀A⟩ := hex
    exact commutator_eq_bot_iff_le_centralizer.mpr fun a ha =>
      mem_centralizer_iff.mpr fun x hx => comm_F_of h i hx₀ hx₀Z hx₀A hx ha
  · right
    push Not at hex
    have hcent : ∀ x ∈ 𝐅 ⊓ 𝐃[i.swap], x ∉ 𝐙 → 𝐀[i] ⊓ centralizer ({x} : Set G) = 𝐙 := by
      intro x hx hxZ
      refine le_antisymm (fun a ha => ?_) (le_inf (pull_mono φ (center_le_rootA i)) fun z hz =>
        mem_centralizer_singleton_iff.mpr (comm_ZP h (F_le_H h hx.1) hz).symm)
      obtain ⟨haA, hax⟩ := mem_inf.mp ha
      by_contra haZ
      obtain ⟨a', ha', hne⟩ := hex x hx hxZ
      exact hne (comm_A_of h i hx haA haZ (mem_centralizer_singleton_iff.mp hax).symm ha')
    refine ⟨le_antisymm ((commutator_mono le_rfl inf_le_left).trans (commutator_A_F h i))
      fun u hu => ?_, hcent⟩
    obtain ⟨x₀, hx₀, hx₀Z⟩ := exists_Fi_not_ZP h i.swap
    have hx₀E : x₀⁻¹ ∈ 𝐄[i] := F_le_E h i (inv_mem hx₀.1)
    have hU : ∀ a ∈ 𝐀[i], x₀⁻¹ * (a⁻¹ * x₀ * a) ∈ 𝐔[i] := fun a ha => by
      have := commE_mem_U h i hx₀E (inv_mem ha)
      rwa [inv_inv, inv_inv, show x₀⁻¹ * a⁻¹ * x₀ * a = x₀⁻¹ * (a⁻¹ * x₀ * a) by group] at this
    have hcard : Nat.card 𝐀[i] =
        Nat.card 𝐔[i] * Nat.card (centralizer ({x₀} : Set G) ⊓ 𝐀[i] : Subgroup G) := by
      rw [inf_comm (centralizer ({x₀} : Set G)) 𝐀[i], hcent x₀ hx₀ hx₀Z, card_pull, card_rootA,
        FCHyp.card_U, FCHyp.card_ZP]
      ring
    obtain ⟨a, ha, hau⟩ := exists_conj_eq_of_card hU hcard hu
    rw [← hau, commutator_comm]
    have := commutator_mem_commutator (inv_mem hx₀) (inv_mem ha)
    rwa [commutatorElement_def, inv_inv, inv_inv,
      show x₀⁻¹ * a⁻¹ * x₀ * a = x₀⁻¹ * (a⁻¹ * x₀ * a) by group] at this

theorem center_E_le_A (h : FCHyp L K n φ t) (i : Axis) :
    (center 𝐄[i]).map 𝐄[i].subtype ≤ 𝐀[i] := by
  intro z hz
  obtain ⟨hzE, hzc⟩ := mem_center_map_iff.mp hz
  have hzC : z ∈ 𝐂 := mem_centralizer_singleton_iff.mpr (hzc t (t_mem_E h i)).symm
  have hzB : z ∈ 𝐁[i] := by
    rw [← E_inf_C h i]
    exact mem_inf.mpr ⟨hzE, hzC⟩
  rcases (mem_zpowers_sup_iff h.setup.t_mul_t (TwoCoreSetup.comm_pull φ h.twoCore)).mp hzB with
    hzA | htz
  · exact hzA
  exfalso
  have hza : z = t * (t * z) := by rw [← mul_assoc, h.setup.t_mul_t, one_mul]
  set a := t * z with ha_def
  obtain ⟨a₁, ha₁, hψ₁⟩ := exists_psiG_eq h.twoCore φ i ![1, 0]
  have ha₁U : a₁ ∉ 𝐔[i] := fun hu => by
    have h1 := (psiG_eq_zero_iff h.twoCore φ i ha₁).mpr hu
    rw [hψ₁] at h1
    have h2 := congrFun h1 0
    simp at h2
  have hmem : t * a₁ ∈ {x : G | ∃ e ∈ 𝐄[i], x = e⁻¹ * t * e} := by
    rw [orbit_E h i]
    exact ⟨a₁, ha₁, rfl⟩
  obtain ⟨e, he, hea⟩ := hmem
  have hez : e⁻¹ * z * e = z := by rw [mul_assoc, ← hzc e he, inv_mul_cancel_left]
  have h1 : e⁻¹ * a * e = a₁⁻¹ * a := by
    have h3 : e⁻¹ * (t * a) * e = t * a := by rw [← hza]; exact hez
    calc e⁻¹ * a * e = (e⁻¹ * t * e)⁻¹ * (e⁻¹ * (t * a) * e) := by group
      _ = (t * a₁)⁻¹ * (t * a) := by rw [← hea, h3]
      _ = a₁⁻¹ * a := by group
  have h2 : a⁻¹ * (e⁻¹ * a * e) ∈ 𝐔[i] := by
    have := (kernel_A h i (inv_mem (map_subtype_le _ he))).mpr (inv_mem he) a htz
    rwa [inv_inv] at this
  have e3 : a⁻¹ * (a₁⁻¹ * a) = a₁⁻¹ := by
    rw [A_mul_comm h i (inv_mem ha₁) htz]
    group
  rw [h1, e3] at h2
  exact ha₁U (by simpa using inv_mem h2)

theorem center_R_le (h : FCHyp L K n φ t) (i : Axis) {z : G}
    (hz : z ∈ (center 𝐑[i]).map 𝐑[i].subtype) :
    z ∈ (center 𝐄[i]).map 𝐄[i].subtype ∧ z ∈ zpowers t ⊔ 𝐙 := by
  obtain ⟨hzR, hzc⟩ := mem_center_map_iff.mp hz
  have htR : t ∈ 𝐑[i] := mem_sup_left (mem_sup_right (mem_zpowers t))
  have hzC : z ∈ 𝐂 := mem_centralizer_singleton_iff.mpr (hzc t htR).symm
  have hzQ : z ∈ 𝐐 := by
    rw [← R_inf_C h i]
    exact mem_inf.mpr ⟨hzR, hzC⟩
  have hzZQ : z ∈ zpowers t ⊔ 𝐙 := by
    rw [← center_Q h]
    exact mem_center_map_iff.mpr ⟨hzQ, fun y hy => hzc y (mem_sup_left hy)⟩
  have hzE : z ∈ 𝐄[i] := ((sup_le_sup_left (pull_mono φ (center_le_rootA i)) _).trans
    ((h.B_le_D i).trans (h.D_le_E i))) hzZQ
  exact ⟨mem_center_map_iff.mpr ⟨hzE, fun y hy => hzc y (mem_sup_right hy)⟩, hzZQ⟩

theorem centers_of_bot (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    (center 𝐄[i]).map 𝐄[i].subtype = 𝐀[i] ∧ (center 𝐑[i]).map 𝐑[i].subtype = 𝐙 := by
  have hAFj : ∀ a ∈ 𝐀[i], ∀ x ∈ 𝐅 ⊓ 𝐃[i.swap], x * a = a * x := fun a ha x hx =>
    mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hbot ha) x hx
  have hAF : ∀ a ∈ 𝐀[i], ∀ f ∈ 𝐅, f * a = a * f := by
    intro a ha f hf
    rw [← SetLike.mem_coe, ← W_mul_W h] at hf
    obtain ⟨x, hx, y, hy, rfl⟩ := hf
    have hx' : x * a = a * x := by
      cases i
      · exact (A_comm_D h _ ha (W_le_Fi h _ hx).2).symm
      · exact hAFj a ha x (W_le_Fi h _ hx)
    have hy' : y * a = a * y := by
      cases i
      · exact hAFj a ha y (W_le_Fi h _ hy)
      · exact (A_comm_D h _ ha (W_le_Fi h _ hy).2).symm
    exact (Commute.mul_left hx' hy').eq
  have hAFw : ∀ a ∈ 𝐀[i], ∀ f ∈ 𝐅ʷ[i], f * a = a * f := by
    intro a ha f hf
    rw [mem_map_conj_inv] at hf
    have h1 := hAF _ (conj_w_mem_A h i ha) _ hf
    have h2 : 𝐰[i] * (f * a) * 𝐰[i]⁻¹ = 𝐰[i] * (a * f) * 𝐰[i]⁻¹ := by
      calc 𝐰[i] * (f * a) * 𝐰[i]⁻¹ = (𝐰[i] * f * 𝐰[i]⁻¹) * (𝐰[i] * a * 𝐰[i]⁻¹) := by group
        _ = (𝐰[i] * a * 𝐰[i]⁻¹) * (𝐰[i] * f * 𝐰[i]⁻¹) := h1
        _ = 𝐰[i] * (a * f) * 𝐰[i]⁻¹ := by group
    simpa using h2
  have hAE : 𝐀[i] ≤ (center 𝐄[i]).map 𝐄[i].subtype := by
    intro a ha
    refine mem_center_map_iff.mpr ⟨h.D_le_E i (A_le_D h i ha), fun y hy => ?_⟩
    rw [← SetLike.mem_coe, ← X_mul_D h i] at hy
    obtain ⟨x, hx, d, hd, rfl⟩ := hy
    rw [← F_mul_Fw' h i] at hx
    obtain ⟨f, hf, f', hf', rfl⟩ := hx
    exact (Commute.mul_left (Commute.mul_left (hAF a ha f hf) (hAFw a ha f' hf'))
      (A_comm_D h i ha hd).symm).eq
  refine ⟨le_antisymm (center_E_le_A h i) hAE, le_antisymm (fun z hz => ?_) fun z hz => ?_⟩
  · obtain ⟨hzE, hzt⟩ := center_R_le h i hz
    have hzA := center_E_le_A h i hzE
    rcases (mem_zpowers_sup_iff h.setup.t_mul_t (TwoCoreSetup.comm_pull φ h.twoCore)).mp hzt with
      h1 | h1
    · exact h1
    · exfalso
      apply h.twoCore.t_not_mem
      have := mul_mem (pull_le φ _ h1) (inv_mem (pull_le φ _ hzA))
      rwa [mul_inv_cancel_right] at this
  · refine mem_center_map_iff.mpr ⟨mem_sup_left (mem_sup_left (Setup.ZP_le_PG hz)), fun y hy => ?_⟩
    rw [← SetLike.mem_coe, ← R_mul h i] at hy
    obtain ⟨q, hq, e, he, rfl⟩ := hy
    have h1 : q * z = z * q := h.Q_comm_ZP hq hz
    have h2 : e * z = z * e :=
      (mem_center_map_iff.mp (hAE (pull_mono φ (center_le_rootA i) hz))).2 e he
    exact (Commute.mul_left h1 h2).eq

theorem centers_of_ne_bot (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) :
    (center 𝐄[i]).map 𝐄[i].subtype = 𝐔[i] ∧ (center 𝐑[i]).map 𝐑[i].subtype = 𝐔[i] ∧
      ∀ x ∈ 𝐅 ⊓ 𝐃[i.swap], x ∉ 𝐙 → 𝐀[i] ⊓ centralizer ({x} : Set G) = 𝐙 := by
  obtain ⟨-, hcent⟩ := (cross_dich h i).resolve_left hne
  obtain ⟨x₀, hx₀, hx₀Z⟩ := exists_Fi_not_ZP h i.swap
  have hEZ : (center 𝐄[i]).map 𝐄[i].subtype ≤ 𝐙 := by
    intro z hz
    have hzx : z ∈ centralizer ({x₀} : Set G) := mem_centralizer_singleton_iff.mpr
      ((mem_center_map_iff.mp hz).2 x₀ (F_le_E h i hx₀.1)).symm
    rw [← hcent x₀ hx₀ hx₀Z]
    exact mem_inf.mpr ⟨center_E_le_A h i hz, hzx⟩
  have hEU : (center 𝐄[i]).map 𝐄[i].subtype ≤ 𝐔[i] := by
    intro z hz
    have hwz : 𝐰[i] * z * 𝐰[i]⁻¹ ∈ (center 𝐄[i]).map 𝐄[i].subtype := by
      obtain ⟨hzE, hzc⟩ := mem_center_map_iff.mp hz
      refine mem_center_map_iff.mpr ⟨conj_w_mem_E h i hzE, fun y hy => ?_⟩
      have hy' : 𝐰[i]⁻¹ * y * 𝐰[i] ∈ 𝐄[i] := by simpa only [w_inv] using conj_w_mem_E h i hy
      have h1 := hzc _ hy'
      calc y * (𝐰[i] * z * 𝐰[i]⁻¹) = 𝐰[i] * ((𝐰[i]⁻¹ * y * 𝐰[i]) * z) * 𝐰[i]⁻¹ := by group
        _ = 𝐰[i] * (z * (𝐰[i]⁻¹ * y * 𝐰[i])) * 𝐰[i]⁻¹ := by rw [h1]
        _ = 𝐰[i] * z * 𝐰[i]⁻¹ * y := by group
    exact mem_U_of_conj_w h i (hEZ hz) (hEZ hwz)
  refine ⟨le_antisymm hEU (U_le_center_E h i),
    le_antisymm (fun z hz => hEU (center_R_le h i hz).1) fun u hu => ?_, hcent⟩
  have huZ : u ∈ 𝐙 := pull_mono φ (rootU_le_center i) hu
  refine mem_center_map_iff.mpr ⟨mem_sup_left (mem_sup_left (Setup.ZP_le_PG huZ)),
    fun y hy => ?_⟩
  rw [← SetLike.mem_coe, ← R_mul h i] at hy
  obtain ⟨q, hq, e, he, rfl⟩ := hy
  have h1 : q * u = u * q := h.Q_comm_ZP hq huZ
  have h2 : e * u = u * e := (mem_center_map_iff.mp (U_le_center_E h i hu)).2 e he
  exact (Commute.mul_left h1 h2).eq

end Cross

end FullCenterWeyl

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

end CFSG.LocalAnalysis.SymplecticFourStandard
