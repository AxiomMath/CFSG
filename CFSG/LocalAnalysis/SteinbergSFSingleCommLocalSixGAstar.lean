module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixGStar

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SixG

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm NextCores
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

section General

variable {G : Type} [Group G]

theorem sq_mul_mem_iff {Z : Subgroup G} {m y : G} (hmZ : m ∈ normalizer (Z : Set G))
    (hmm : m * m ∈ Z) (hc : y * m * y⁻¹ * m⁻¹ ∈ Z) : m * y * (m * y) ∈ Z ↔ y * y ∈ Z := by
  have e : m * y * (m * y) = (m * m) * (m⁻¹ * (y * m * y⁻¹ * m⁻¹) * m) * (y * y) := by group
  have h1 : m⁻¹ * (y * m * y⁻¹ * m⁻¹) * m ∈ Z := by
    have := (mem_normalizer_iff.mp (inv_mem hmZ) _).mp hc
    rwa [inv_inv] at this
  rw [e]
  constructor
  · intro h2
    have := mul_mem (inv_mem (mul_mem hmm h1)) h2
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  · exact fun h2 => mul_mem (mul_mem hmm h1) h2

theorem comm_mul_left_mem_iff {Z : Subgroup G} {m y w : G} (hmZ : m ∈ normalizer (Z : Set G))
    (hc : m * w * m⁻¹ * w⁻¹ ∈ Z) :
    m * y * w * (m * y)⁻¹ * w⁻¹ ∈ Z ↔ y * w * y⁻¹ * w⁻¹ ∈ Z := by
  have e : m * y * w * (m * y)⁻¹ * w⁻¹ =
      m * (y * w * y⁻¹ * w⁻¹) * m⁻¹ * (m * w * m⁻¹ * w⁻¹) := by group
  rw [e]
  constructor
  · intro h2
    have h3 := mul_mem h2 (inv_mem hc)
    rw [mul_inv_cancel_right] at h3
    exact (mem_normalizer_iff.mp hmZ _).mpr h3
  · exact fun h2 => mul_mem ((mem_normalizer_iff.mp hmZ _).mp h2) hc

theorem comm_mul_right_mem_iff {Z : Subgroup G} {m y w : G} (hmZ : m ∈ normalizer (Z : Set G))
    (hc : w * m * w⁻¹ * m⁻¹ ∈ Z) :
    w * (m * y) * w⁻¹ * (m * y)⁻¹ ∈ Z ↔ w * y * w⁻¹ * y⁻¹ ∈ Z := by
  have e : w * (m * y) * w⁻¹ * (m * y)⁻¹ =
      (w * m * w⁻¹ * m⁻¹) * (m * (w * y * w⁻¹ * y⁻¹) * m⁻¹) := by group
  rw [e]
  constructor
  · intro h2
    have h3 := mul_mem (inv_mem hc) h2
    rw [inv_mul_cancel_left] at h3
    exact (mem_normalizer_iff.mp hmZ _).mpr h3
  · exact fun h2 => mul_mem hc ((mem_normalizer_iff.mp hmZ _).mp h2)

theorem comm_mem_swap {Z : Subgroup G} {a b : G} (hab : a * b * a⁻¹ * b⁻¹ ∈ Z) :
    b * a * b⁻¹ * a⁻¹ ∈ Z := by
  have := inv_mem hab
  rwa [show (a * b * a⁻¹ * b⁻¹)⁻¹ = b * a * b⁻¹ * a⁻¹ by group] at this

theorem comm_mem_of_mem_right {Z : Subgroup G} {g z : G} (hg : g ∈ normalizer (Z : Set G))
    (hz : z ∈ Z) : g * z * g⁻¹ * z⁻¹ ∈ Z :=
  mul_mem ((mem_normalizer_iff.mp hg z).mp hz) (inv_mem hz)

end General

theorem heis_comm_eq {K : Type} [Field K] (p q : Heis K) :
    p * q * p⁻¹ * q⁻¹ = ⟨p.z * q.y - q.z * p.y, 0, 0⟩ := by
  ext
  · simp
    ring
  · simp
  · simp

section Astar

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐕[" i "]" => (zpowers t ⊔ pull φ (rootU K i) : Subgroup G)
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
local notation "𝐊⋆" => (𝐊[Axis.one] ⊔ 𝐊[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐋[" i "]" => (𝐅 ⊔ 𝐀[i] : Subgroup G)
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐅ʷ[" i "]" => (𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅ʷ[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐍ₕ[" i "]" => (normalizer ((𝐇 : Subgroup G) : Set G) ⊓
  normalizer (𝐔[i] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐘[" i "," k "]" => (𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[k] : Subgroup G) : Set G) :
  Subgroup G)
set_option quotPrecheck false in
local notation "𝐍𝐑[" k "]" => (normalizer (𝐑[k] : Set G) ⊓ normalizer (𝐁[k] : Set G) :
  Subgroup G)
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
local notation "𝐓₁[" i "]" => (𝐑[i] ⊔ 𝐏₁[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓₀[" j "]" => (𝐑[j] ⊔ 𝐏₂[j] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓₂[" j "]" => (𝐓₀[j] ⊓ normalizer (𝐑[j] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓₃[" i "]" => (𝐓₁[i] ⊓ 𝐓₂[Axis.swap i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓̄[" i "]" => (𝐓₁[i] ⊔ 𝐓₂[Axis.swap i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐏₀[" i "]" => (𝐏₁[i] ⊓ 𝐏₂[Axis.swap i] : Subgroup G)

set_option quotPrecheck false in
local notation "𝐌₀[" i "]" => closure {x : G | ∃ p ∈ 𝐏₀[i], ∃ j ∈ pull φ (diagTorus K),
  x = p⁻¹ * (j⁻¹ * p * j)}

set_option quotPrecheck false in
local notation "𝐁⋆[" i "]" => (𝐌₀[i] ⊔ 𝐊⋆ : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂⋆[" i "]" => (𝐌₀[i] ⊔ 𝐅ʷ[Axis.swap i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐀⋆[" i "]" => (𝐌₀[i] ⊔ 𝐊⋆ ⊔ 𝐅ʷ[Axis.swap i] : Subgroup G)

omit [Finite G] [Finite K] in
theorem ZP_le_K (k : Axis) : 𝐙 ≤ 𝐊[k] := (pull_mono φ (center_le_rootA k)).trans le_sup_left

omit [Finite G] [Finite K] in
theorem U_le_K (i k : Axis) : 𝐔[i] ≤ 𝐊[k] := (pull_mono φ (rootU_le_center i)).trans (ZP_le_K k)

theorem X_le_R (h : FCHyp L K n φ t) (k : Axis) : 𝐗[k] ≤ 𝐑[k] := (X_le_E h k).trans le_sup_right

theorem T₂_le_normalizer_K (h : FCHyp L K n φ t) (k : Axis) :
    𝐓₂[k] ≤ normalizer (𝐊[k] : Set G) :=
  fun _ hg => (mem_inf.mp (T₀_le_En h k (mem_inf.mp hg).1)).2

omit [Finite G] [Finite K] in
theorem L_eq_F_sup_K (k : Axis) : 𝐋[k] = 𝐅 ⊔ 𝐊[k] :=
  le_antisymm (sup_le le_sup_left (le_sup_left.trans le_sup_right))
    (sup_le le_sup_left (K_le_L k))

omit [Finite G] [Finite K] in
theorem mem_or_mul_t_mem (h : FCHyp L K n φ t) {N : Subgroup G}
    (htN : t ∈ normalizer (N : Set G)) {x : G} (hx : x ∈ N ⊔ zpowers t) : x ∈ N ∨ x * t ∈ N := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ (zpowers_le.mpr htN)] at hx
  obtain ⟨y, hy, c, hc, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
  dsimp only
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [← zpow_mod_orderOf, h.setup.order_t, Nat.cast_ofNat, hk, zpow_zero, mul_one]
    exact hy
  · right
    rw [← zpow_mod_orderOf, h.setup.order_t, Nat.cast_ofNat, hk, zpow_one, mul_assoc,
      SixF.t_mul_t h, mul_one]
    exact hy

theorem Cstar_eq (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐂⋆[i] = 𝐌₀[i] ⊔ 𝐗[i.swap] :=
  le_antisymm (sup_le le_sup_left ((le_sup_right : 𝐅ʷ[i.swap] ≤ 𝐗[i.swap]).trans le_sup_right))
    (sup_le le_sup_left (sup_le ((F_le_M h i hne hbot).trans le_sup_left) le_sup_right))

theorem Astar_eq (h : FCHyp L K n φ t) (i : Axis) : 𝐀⋆[i] = 𝐁⋆[i] ⊔ 𝐗[i.swap] :=
  le_antisymm (sup_le le_sup_left ((le_sup_right : 𝐅ʷ[i.swap] ≤ 𝐗[i.swap]).trans le_sup_right))
    (sup_le le_sup_left (sup_le ((F_le_Ks h).trans (le_sup_right.trans le_sup_left))
      le_sup_right))

theorem M_inf_R_swap (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐌₀[i] ⊓ 𝐑[i.swap] = 𝐅 := by
  refine le_antisymm (fun x hx => ?_) (le_inf (F_le_M h i hne hbot)
    ((F_le_Ks h).trans ((Ks_le_H h).trans (H_le_R h _))))
  have hxT : x ∈ 𝐑[i.swap] ⊓ 𝐓₁[i] :=
    mem_inf.mpr ⟨(mem_inf.mp hx).2, (mem_inf.mp (M_le_T₃ h i hne hbot (mem_inf.mp hx).1)).1⟩
  rw [R_swap_inf_T₁ h i hne hbot] at hxT
  exact (M_inf_H h i hne hbot).le (mem_inf.mpr ⟨(mem_inf.mp hx).1, hxT⟩)

theorem M_inf_X_swap (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐌₀[i] ⊓ 𝐗[i.swap] = 𝐅 :=
  le_antisymm (fun _ hx => (SixF.M_inf_E_swap h i hne hbot).le
      (mem_inf.mpr ⟨(mem_inf.mp hx).1, X_le_E h _ (mem_inf.mp hx).2⟩))
    (le_inf (F_le_M h i hne hbot) le_sup_left)

theorem M_le_normalizer_X (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐌₀[i] ≤ normalizer (𝐗[i.swap] : Set G) := fun _ hm =>
  mem_normalizer_of_conj_le fun _ hx => SixF.conj_X_mem_P₂ h i hne hbot (SixF.M_le_P₂ h i hm) hx

theorem card_Cstar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : Nat.card 𝐂⋆[i] = Nat.card K ^ 7 := by
  rw [Cstar_eq h i hne hbot]
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := 𝐗[i.swap]) (B := 𝐌₀[i]) (M_le_normalizer_X h i hne hbot)
  rw [sup_comm 𝐗[i.swap] 𝐌₀[i], inf_comm 𝐗[i.swap] 𝐌₀[i], M_inf_X_swap h i hne hbot,
    card_X h, card_M h i hne hbot, card_F h] at h1
  have hq : 0 < Nat.card K ^ 4 := pow_pos Nat.card_pos 4
  exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)

theorem mem_Cstar_iff (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {y : G} :
    y ∈ 𝐂⋆[i] ↔ ∃ m ∈ 𝐌₀[i], ∃ x ∈ 𝐗[i.swap], m * x = y := by
  rw [Cstar_eq h i hne hbot, ← SetLike.mem_coe,
    coe_mul_of_left_le_normalizer_right _ _ (M_le_normalizer_X h i hne hbot), Set.mem_mul]
  simp only [SetLike.mem_coe]

theorem Bstar_inf_X (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐁⋆[i] ⊓ 𝐗[i.swap] = 𝐋[i.swap] := by
  refine le_antisymm (fun x hx => ?_) (le_inf ((L_le_Ks h _).trans le_sup_right) (L_le_X h _))
  obtain ⟨hxB, hxX⟩ := mem_inf.mp hx
  obtain ⟨m, hm, k, hk, rfl⟩ := (mem_Bstar_iff h i hne hbot).mp hxB
  have hkR : k ∈ 𝐑[i.swap] := H_le_R h _ (Ks_le_H h hk)
  have hmR : m ∈ 𝐑[i.swap] := by
    have := mul_mem (X_le_R h _ hxX) (inv_mem hkR)
    rwa [mul_inv_cancel_right] at this
  have hmF : m ∈ 𝐅 := (M_inf_R_swap h i hne hbot).le (mem_inf.mpr ⟨hm, hmR⟩)
  exact SixF.mem_L_of_mem_X_of_mem_H h _ hxX (Ks_le_H h (mul_mem (F_le_Ks h hmF) hk))

theorem Bstar_le_normalizer_X (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐁⋆[i] ≤ normalizer (𝐗[i.swap] : Set G) :=
  sup_le (M_le_normalizer_X h i hne hbot) fun _ hk => mem_normalizer_of_conj_le fun _ hx =>
    conj_mem_X_of_En h i hbot (R_le_En h _ (H_le_R h _ (Ks_le_H h hk))) hx

theorem card_Astar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : Nat.card 𝐀⋆[i] = Nat.card K ^ 8 := by
  rw [Astar_eq h i]
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := 𝐗[i.swap]) (B := 𝐁⋆[i]) (Bstar_le_normalizer_X h i hne hbot)
  rw [sup_comm 𝐗[i.swap] 𝐁⋆[i], inf_comm 𝐗[i.swap] 𝐁⋆[i], Bstar_inf_X h i hne hbot,
    card_X h, card_Bstar h i hne hbot, card_L h] at h1
  have hq : 0 < Nat.card K ^ 5 := pow_pos Nat.card_pos 5
  exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)

theorem mem_Astar_iff (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {y : G} :
    y ∈ 𝐀⋆[i] ↔ ∃ m ∈ 𝐌₀[i], ∃ k ∈ 𝐊⋆, ∃ x ∈ 𝐗[i.swap], m * k * x = y := by
  rw [Astar_eq h i, ← SetLike.mem_coe,
    coe_mul_of_left_le_normalizer_right _ _ (Bstar_le_normalizer_X h i hne hbot), Set.mem_mul]
  simp only [SetLike.mem_coe]
  constructor
  · rintro ⟨b, hb, x, hx, rfl⟩
    obtain ⟨m, hm, k, hk, rfl⟩ := (mem_Bstar_iff h i hne hbot).mp hb
    exact ⟨m, hm, k, hk, x, hx, rfl⟩
  · rintro ⟨m, hm, k, hk, x, hx, rfl⟩
    exact ⟨m * k, (mem_Bstar_iff h i hne hbot).mpr ⟨m, hm, k, hk, rfl⟩, x, hx, rfl⟩

theorem Astar_mul (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    (𝐌₀[i] : Set G) * (𝐊⋆ : Set G) * (𝐅ʷ[i.swap] : Set G) = (𝐀⋆[i] : Set G) := by
  refine le_antisymm ?_ fun y hy => ?_
  · rintro _ ⟨_, ⟨m, hm, k, hk, rfl⟩, f, hf, rfl⟩
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left hm)) (mem_sup_left (mem_sup_right hk)))
      (mem_sup_right hf)
  obtain ⟨m, hm, k, hk, x, hx, rfl⟩ := (mem_Astar_iff h i hne hbot).mp hy
  rw [← SetLike.mem_coe, ← F_mul_Fw' h] at hx
  obtain ⟨f, hf, f', hf', rfl⟩ := hx
  exact ⟨m * (k * f), ⟨m, hm, k * f, mul_mem hk (F_le_Ks h hf), rfl⟩, f', hf', by group⟩

theorem Bstar_mul (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    (𝐌₀[i] : Set G) * (𝐊⋆ : Set G) = (𝐁⋆[i] : Set G) :=
  (coe_mul_of_left_le_normalizer_right _ _ (M_le_normalizer_Ks h i hne hbot)).symm

theorem Astar_le_T₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐀⋆[i] ≤ 𝐓₂[i.swap] := by
  rw [Astar_eq h i]
  exact sup_le (sup_le ((M_le_T₃ h i hne hbot).trans inf_le_right)
    ((Ks_le_H h).trans (H_le_T₂ h _))) ((X_le_R h _).trans (R_le_T₂ _))

theorem Astar_le_normalizer_K (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐀⋆[i] ≤ normalizer (𝐊[i.swap] : Set G) :=
  (Astar_le_T₂ h i hne hbot).trans (T₂_le_normalizer_K h _)

theorem t_mem_normalizer_X (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : t ∈ normalizer (𝐗[i.swap] : Set G) :=
  mem_normalizer_of_conj_le fun _ hx =>
    conj_mem_X_of_En h i hbot (P₂_le _ (t_mem_P₂ h i hne hbot)) hx

theorem t_mem_normalizer_Astar (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    t ∈ normalizer (𝐀⋆[i] : Set G) := by
  rw [Astar_eq h i]
  exact mem_normalizer_of_conj_le fun _ hx => conj_mem_sup
    (fun _ hy => (mem_normalizer_iff.mp (t_mem_normalizer_Bstar h i hne hbot) _).mp hy)
    (fun _ hy => (mem_normalizer_iff.mp (t_mem_normalizer_X h i hne hbot) _).mp hy) hx

theorem t_not_mem_Astar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : t ∉ 𝐀⋆[i] := fun ht => by
  obtain ⟨m, hm, k, hk, x, hx, hmkx⟩ := (mem_Astar_iff h i hne hbot).mp ht
  have htR : t ∈ 𝐑[i.swap] := H_le_R h _ t_mem_H
  have hmR : m ∈ 𝐑[i.swap] := by
    rw [show m = t * x⁻¹ * k⁻¹ by rw [← hmkx]; group]
    exact mul_mem (mul_mem htR (inv_mem (X_le_R h _ hx)))
      (inv_mem (H_le_R h _ (Ks_le_H h hk)))
  have hmk : m * k ∈ 𝐊⋆ :=
    mul_mem (F_le_Ks h ((M_inf_R_swap h i hne hbot).le (mem_inf.mpr ⟨hm, hmR⟩))) hk
  have hxH : x ∈ 𝐇 := by
    rw [show x = (m * k)⁻¹ * t by rw [← hmkx]; group]
    exact mul_mem (inv_mem (Ks_le_H h hmk)) t_mem_H
  have hmkx' : m * k * x ∈ 𝐊⋆ :=
    mul_mem hmk (L_le_Ks h _ (SixF.mem_L_of_mem_X_of_mem_H h _ hx hxH))
  exact t_not_mem_Ks h (hmkx ▸ hmkx')

theorem Astar_sup_t (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐀⋆[i] ⊔ zpowers t = 𝐓₂[i.swap] ∧ 𝐀⋆[i] ⊓ zpowers t = ⊥ := by
  have hinf : 𝐀⋆[i] ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp (mem_inf.mp hx).2
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · rw [← zpow_mod_orderOf, h.setup.order_t, Nat.cast_ofNat, hk, zpow_zero]
      exact one_mem _
    · exfalso
      have := (mem_inf.mp hx).1
      rw [← zpow_mod_orderOf, h.setup.order_t, Nat.cast_ofNat, hk, zpow_one] at this
      exact t_not_mem_Astar h i hne hbot this
  refine ⟨?_, hinf⟩
  have hle : 𝐀⋆[i] ⊔ zpowers t ≤ 𝐓₂[i.swap] :=
    sup_le (Astar_le_T₂ h i hne hbot) ((zpowers_le).2 (H_le_T₂ h _ t_mem_H))
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := 𝐀⋆[i]) (B := zpowers t) ((zpowers_le).2 (t_mem_normalizer_Astar h i hne hbot))
  rw [hinf, card_bot, mul_one, card_Astar h i hne hbot, Nat.card_zpowers, h.setup.order_t] at h1
  rw [card_T₂ h i hne hbot, h1, mul_comm]

theorem Astar_inf_T₃ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐀⋆[i] ⊓ 𝐓₃[i] = 𝐁⋆[i] := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left (Bstar_le_T₃ h i hne hbot))
  obtain ⟨hxA, hxT⟩ := mem_inf.mp hx
  rw [← (Bstar_sup_t h i hne hbot).1] at hxT
  rcases mem_or_mul_t_mem h (t_mem_normalizer_Bstar h i hne hbot) hxT with h1 | h1
  · exact h1
  · exfalso
    have h2 := mul_mem (inv_mem hxA) ((le_sup_left : 𝐁⋆[i] ≤ 𝐀⋆[i]) h1)
    rw [inv_mul_cancel_left] at h2
    exact t_not_mem_Astar h i hne hbot h2

theorem Ks_inf_P₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐊⋆ ⊓ 𝐏₂[i.swap] = 𝐋[i.swap] := by
  refine le_antisymm (fun x hx => ?_)
    (le_inf (L_le_Ks h _) ((L_le_X h _).trans (X_le_P₂ h i hne hbot)))
  have hxN : x ∈ 𝐍[i.swap] := R_le_N h _ (H_le_R h _ (Ks_le_H h (mem_inf.mp hx).1))
  have hxE : x ∈ 𝐄[i.swap] :=
    (P₂_inf_N h i hne hbot).le (mem_inf.mpr ⟨(mem_inf.mp hx).2, hxN⟩)
  exact mem_L_of_mem_Ks h _ (mem_inf.mp hx).1 hxE

theorem Cstar_le_P₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐂⋆[i] ≤ 𝐏₂[i.swap] := by
  rw [Cstar_eq h i hne hbot]
  exact sup_le (SixF.M_le_P₂ h i) (X_le_P₂ h i hne hbot)

omit [Finite G] [Finite K] in
theorem Cstar_le_Astar (i : Axis) : 𝐂⋆[i] ≤ 𝐀⋆[i] :=
  sup_le (le_sup_left.trans le_sup_left) le_sup_right

theorem Astar_inf_P₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐀⋆[i] ⊓ 𝐏₂[i.swap] = 𝐂⋆[i] := by
  refine le_antisymm (fun y hy => ?_) (le_inf (Cstar_le_Astar i) (Cstar_le_P₂ h i hne hbot))
  obtain ⟨hyA, hyP⟩ := mem_inf.mp hy
  obtain ⟨m, hm, k, hk, x, hx, rfl⟩ := (mem_Astar_iff h i hne hbot).mp hyA
  have hkP : k ∈ 𝐏₂[i.swap] := by
    rw [show k = m⁻¹ * (m * k * x) * x⁻¹ by group]
    exact mul_mem (mul_mem (inv_mem (SixF.M_le_P₂ h i hm)) hyP)
      (inv_mem (X_le_P₂ h i hne hbot hx))
  have hkL := (Ks_inf_P₂ h i hne hbot).le (mem_inf.mpr ⟨hk, hkP⟩)
  rw [Cstar_eq h i hne hbot, mul_assoc]
  exact mul_mem (mem_sup_left hm) (mem_sup_right (mul_mem (L_le_X h _ hkL) hx))

theorem comm_M_Astar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {m : G}
    (hm : m ∈ 𝐌₀[i]) {y : G} (hy : y ∈ 𝐀⋆[i]) : m * y * m⁻¹ * y⁻¹ ∈ 𝐊[i.swap] := by
  have hZ : 𝐁⋆[i] ⊔ 𝐗[i.swap] ≤ normalizer (𝐊[i.swap] : Set G) := by
    rw [← Astar_eq h i]
    exact Astar_le_normalizer_K h i hne hbot
  rw [Astar_eq h i] at hy
  refine comm_mem_sup hZ (comm_mem_sup (le_sup_left.trans hZ) (fun a ha => ?_) (fun a ha => ?_))
    (fun x hx => comm_P₂_X h i hne hbot (SixF.M_le_P₂ h i hm) hx) y hy
  · exact U_le_K i _ (comm_mem_of_sq hM2 hm ha)
  · exact ZP_le_K _ (comm_T₃_Ks h i hne hbot (M_le_T₃ h i hne hbot hm) ha)

theorem sq_X_mem_K (h : FCHyp L K n φ t) (k : Axis) {x : G} (hx : x ∈ 𝐗[k]) :
    x * x ∈ 𝐊[k] := by
  refine (psiX_eq_zero_iff h k (mul_mem hx hx)).mp ?_
  rw [psiX_mul h k (X_le_E h k hx) (X_le_E h k hx)]
  funext l
  rw [Pi.add_apply, Pi.zero_apply, CharTwo.add_self_eq_zero]

omit [Finite G] [Finite K] in
theorem M_le_Astar (i : Axis) : 𝐌₀[i] ≤ 𝐀⋆[i] := le_sup_left.trans le_sup_left

omit [Finite G] [Finite K] in
theorem Ks_le_Astar (i : Axis) : 𝐊⋆ ≤ 𝐀⋆[i] := le_sup_right.trans le_sup_left

theorem X_le_Astar (h : FCHyp L K n φ t) (i : Axis) : 𝐗[i.swap] ≤ 𝐀⋆[i] := by
  rw [Astar_eq h i]
  exact le_sup_right

theorem M_le_normalizer_K_swap (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐌₀[i] ≤ normalizer (𝐊[i.swap] : Set G) :=
  (M_le_Astar i).trans (Astar_le_normalizer_K h i hne hbot)

theorem elem_Cstar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {x y : G}
    (hx : x ∈ 𝐂⋆[i]) (hy : y ∈ 𝐂⋆[i]) :
    x * y * x⁻¹ * y⁻¹ ∈ 𝐊[i.swap] ∧ x * x ∈ 𝐊[i.swap] := by
  refine ⟨?_, ?_⟩
  · have hZ : 𝐌₀[i] ⊔ 𝐗[i.swap] ≤ normalizer (𝐊[i.swap] : Set G) := by
      rw [← Cstar_eq h i hne hbot]
      exact (Cstar_le_Astar i).trans (Astar_le_normalizer_K h i hne hbot)
    rw [Cstar_eq h i hne hbot] at hx hy
    exact comm_sup_of_comm hZ
      (fun a ha b hb => comm_M_Astar h i hne hbot hM2 ha (M_le_Astar i hb))
      (fun a ha b hb => comm_M_Astar h i hne hbot hM2 ha (X_le_Astar h i hb))
      (fun a ha b hb => comm_P₂_X h i hne hbot (X_le_P₂ h i hne hbot ha) hb) hx hy
  · obtain ⟨m, hm, z, hz, rfl⟩ := (mem_Cstar_iff h i hne hbot).mp hx
    exact (sq_mul_mem_iff (M_le_normalizer_K_swap h i hne hbot hm) (U_le_K i _ (hM2 m hm))
      (comm_mem_swap (comm_M_Astar h i hne hbot hM2 hm (X_le_Astar h i hz)))).mpr
        (sq_X_mem_K h _ hz)

theorem elem_Bstar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {x y : G}
    (hx : x ∈ 𝐁⋆[i]) (hy : y ∈ 𝐁⋆[i]) :
    x * y * x⁻¹ * y⁻¹ ∈ 𝐊[i.swap] ∧ x * x ∈ 𝐊[i.swap] :=
  ⟨ZP_le_K _ (comm_Bstar h i hne hbot hM2 hx hy), ZP_le_K _ (sq_Bstar h i hne hbot hM2 hx)⟩

theorem mem_D_iff_parabolic (h : FCHyp L K n φ t) (k : Axis) (r : 𝐑[k]) :
    (r : G) ∈ 𝐃[k] ↔ parabolicHom h k r = 1 := by
  rw [← MonoidHom.mem_ker, ker_parabolicHom h k, mem_subgroupOf]

theorem Ks_le_R (h : FCHyp L K n φ t) (k : Axis) : 𝐊⋆ ≤ 𝐑[k] := (Ks_le_H h).trans (H_le_R h k)

theorem parabolic_Ks_y (h : FCHyp L K n φ t) (k : Axis) {a : G} (ha : a ∈ 𝐊⋆) :
    (parabolicHom h k ⟨a, Ks_le_R h k ha⟩).y = 0 :=
  (mem_H_iff h k _).mp (Ks_le_H h ha)

theorem parabolic_X_z (h : FCHyp L K n φ t) (k : Axis) {x : G} (hx : x ∈ 𝐗[k]) :
    (parabolicHom h k ⟨x, X_le_R h k hx⟩).z = 0 :=
  (parabolicHom_z_eq_zero_iff h k _).mpr (X_le_E h k hx)

theorem parabolic_Ks_z_eq_zero_iff (h : FCHyp L K n φ t) (k : Axis) {a : G} (ha : a ∈ 𝐊⋆) :
    (parabolicHom h k ⟨a, Ks_le_R h k ha⟩).z = 0 ↔ a ∈ 𝐋[k] := by
  rw [parabolicHom_z_eq_zero_iff]
  exact ⟨mem_L_of_mem_Ks h k ha, fun hl => X_le_E h k (L_le_X h k hl)⟩

theorem parabolic_X_y_eq_zero_iff (h : FCHyp L K n φ t) (k : Axis) {x : G} (hx : x ∈ 𝐗[k]) :
    (parabolicHom h k ⟨x, X_le_R h k hx⟩).y = 0 ↔ x ∈ 𝐋[k] := by
  rw [← mem_H_iff]
  exact ⟨SixF.mem_L_of_mem_X_of_mem_H h k hx, fun hl => Ks_le_H h (L_le_Ks h k hl)⟩

theorem parabolic_KX (h : FCHyp L K n φ t) (k : Axis) {a x : G} (ha : a ∈ 𝐊⋆) (hx : x ∈ 𝐗[k]) :
    (parabolicHom h k ⟨a * x, mul_mem (Ks_le_R h k ha) (X_le_R h k hx)⟩).y =
        (parabolicHom h k ⟨x, X_le_R h k hx⟩).y ∧
      (parabolicHom h k ⟨a * x, mul_mem (Ks_le_R h k ha) (X_le_R h k hx)⟩).z =
        (parabolicHom h k ⟨a, Ks_le_R h k ha⟩).z := by
  have e : (⟨a * x, mul_mem (Ks_le_R h k ha) (X_le_R h k hx)⟩ : 𝐑[k]) =
      ⟨a, Ks_le_R h k ha⟩ * ⟨x, X_le_R h k hx⟩ := rfl
  rw [e, map_mul, Heis.mul_y, Heis.mul_z, parabolic_Ks_y h k ha, parabolic_X_z h k hx,
    zero_add, add_zero]
  exact ⟨rfl, rfl⟩

theorem mem_L_or_of_sq_mem_D (h : FCHyp L K n φ t) (k : Axis) {a x : G} (ha : a ∈ 𝐊⋆)
    (hx : x ∈ 𝐗[k]) (hD : a * x * (a * x) ∈ 𝐃[k]) : a ∈ 𝐋[k] ∨ x ∈ 𝐋[k] := by
  have h1 := (mem_D_iff_parabolic h k
    (⟨a * x, mul_mem (Ks_le_R h k ha) (X_le_R h k hx)⟩ *
      ⟨a * x, mul_mem (Ks_le_R h k ha) (X_le_R h k hx)⟩)).mp hD
  rw [map_mul, Heis.mul_self] at h1
  have h2 := congrArg Heis.x h1
  simp only [Heis.one_x] at h2
  obtain ⟨hy, hz⟩ := parabolic_KX h k ha hx
  rw [hy, hz] at h2
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact Or.inl ((parabolic_Ks_z_eq_zero_iff h k ha).mp h3)
  · exact Or.inr ((parabolic_X_y_eq_zero_iff h k hx).mp h3)

theorem parabolic_eq_of_comm_mem_D (h : FCHyp L K n φ t) (k : Axis) {a x b y : G}
    (ha : a ∈ 𝐊⋆) (hx : x ∈ 𝐗[k]) (hb : b ∈ 𝐊⋆) (hy : y ∈ 𝐗[k])
    (hD : a * x * (b * y) * (a * x)⁻¹ * (b * y)⁻¹ ∈ 𝐃[k]) :
    (parabolicHom h k ⟨a, Ks_le_R h k ha⟩).z * (parabolicHom h k ⟨y, X_le_R h k hy⟩).y =
      (parabolicHom h k ⟨b, Ks_le_R h k hb⟩).z * (parabolicHom h k ⟨x, X_le_R h k hx⟩).y := by
  have h1 := (mem_D_iff_parabolic h k
    (⟨a * x, mul_mem (Ks_le_R h k ha) (X_le_R h k hx)⟩ *
      ⟨b * y, mul_mem (Ks_le_R h k hb) (X_le_R h k hy)⟩ *
      ⟨a * x, mul_mem (Ks_le_R h k ha) (X_le_R h k hx)⟩⁻¹ *
      ⟨b * y, mul_mem (Ks_le_R h k hb) (X_le_R h k hy)⟩⁻¹)).mp hD
  simp only [map_mul, map_inv] at h1
  rw [heis_comm_eq] at h1
  have h2 := congrArg Heis.x h1
  simp only [Heis.one_x] at h2
  obtain ⟨hy1, hz1⟩ := parabolic_KX h k ha hx
  obtain ⟨hy2, hz2⟩ := parabolic_KX h k hb hy
  rw [hy1, hz1, hy2, hz2] at h2
  exact sub_eq_zero.mp h2

omit [Finite G] [Finite K] in
theorem one_lt_card_K (h : FCHyp L K n φ t) : 1 < Nat.card K := by
  rw [h.setup.card_K]
  exact Nat.one_lt_two_pow (by have := h.setup.two_le; omega)

theorem exists_Ks_not_mem_L (h : FCHyp L K n φ t) (k : Axis) : ∃ a ∈ 𝐊⋆, a ∉ 𝐋[k] := by
  refine IsConcreteLE.not_le_iff_exists.mp fun hle => ?_
  have := Subgroup.card_le_of_le hle
  rw [card_Ks h, card_L h] at this
  exact absurd this (not_le.mpr (Nat.pow_lt_pow_right (one_lt_card_K h) (by norm_num)))

theorem exists_X_not_mem_L (h : FCHyp L K n φ t) (k : Axis) : ∃ x ∈ 𝐗[k], x ∉ 𝐋[k] := by
  refine IsConcreteLE.not_le_iff_exists.mp fun hle => ?_
  have := Subgroup.card_le_of_le hle
  rw [card_X h, card_L h] at this
  exact absurd this (not_le.mpr (Nat.pow_lt_pow_right (one_lt_card_K h) (by norm_num)))

theorem sq_M_mul_mem_iff (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {m y : G}
    (hm : m ∈ 𝐌₀[i]) (hy : y ∈ 𝐀⋆[i]) : m * y * (m * y) ∈ 𝐊[i.swap] ↔ y * y ∈ 𝐊[i.swap] :=
  sq_mul_mem_iff (M_le_normalizer_K_swap h i hne hbot hm) (U_le_K i _ (hM2 m hm))
    (comm_mem_swap (comm_M_Astar h i hne hbot hM2 hm hy))

theorem mem_L_or_of_sq_mem_K (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {m a x : G} (hm : m ∈ 𝐌₀[i]) (ha : a ∈ 𝐊⋆)
    (hx : x ∈ 𝐗[i.swap]) (hsq : m * a * x * (m * a * x) ∈ 𝐊[i.swap]) :
    a ∈ 𝐋[i.swap] ∨ x ∈ 𝐋[i.swap] := by
  have hax : a * x ∈ 𝐀⋆[i] := mul_mem (Ks_le_Astar i ha) (X_le_Astar h i hx)
  rw [mul_assoc m a x, sq_M_mul_mem_iff h i hne hbot hM2 hm hax] at hsq
  exact mem_L_or_of_sq_mem_D h _ ha hx (K_le_D h _ hsq)

theorem elem_le_Bstar_or_Cstar (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {E : Subgroup G} (hEA : E ≤ 𝐀⋆[i])
    (hsq : ∀ x ∈ E, x * x ∈ 𝐊[i.swap])
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ 𝐊[i.swap]) : E ≤ 𝐁⋆[i] ∨ E ≤ 𝐂⋆[i] := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨e₁, he₁, he₁B⟩ := IsConcreteLE.not_le_iff_exists.mp hcon.1
  obtain ⟨e₂, he₂, he₂C⟩ := IsConcreteLE.not_le_iff_exists.mp hcon.2
  obtain ⟨m₁, hm₁, a₁, ha₁, x₁, hx₁, rfl⟩ := (mem_Astar_iff h i hne hbot).mp (hEA he₁)
  obtain ⟨m₂, hm₂, a₂, ha₂, x₂, hx₂, rfl⟩ := (mem_Astar_iff h i hne hbot).mp (hEA he₂)
  have hx₁L : x₁ ∉ 𝐋[i.swap] := fun hl => he₁B
    (mul_mem (mul_mem (mem_sup_left hm₁) (mem_sup_right ha₁)) (mem_sup_right (L_le_Ks h _ hl)))
  have ha₁L : a₁ ∈ 𝐋[i.swap] :=
    (mem_L_or_of_sq_mem_K h i hne hbot hM2 hm₁ ha₁ hx₁ (hsq _ he₁)).resolve_right hx₁L
  have ha₂L : a₂ ∉ 𝐋[i.swap] := fun hl => he₂C (by
    rw [Cstar_eq h i hne hbot, mul_assoc]
    exact mul_mem (mem_sup_left hm₂) (mem_sup_right (mul_mem (L_le_X h _ hl) hx₂)))
  have hx₂L : x₂ ∈ 𝐋[i.swap] :=
    (mem_L_or_of_sq_mem_K h i hne hbot hM2 hm₂ ha₂ hx₂ (hsq _ he₂)).resolve_left ha₂L
  have hc := hcomm _ he₁ _ he₂
  have hA₁ : a₁ * x₁ ∈ 𝐀⋆[i] := mul_mem (Ks_le_Astar i ha₁) (X_le_Astar h i hx₁)
  rw [mul_assoc m₁, comm_mul_left_mem_iff (M_le_normalizer_K_swap h i hne hbot hm₁)
    (comm_M_Astar h i hne hbot hM2 hm₁ (hEA he₂)), mul_assoc m₂,
    comm_mul_right_mem_iff (M_le_normalizer_K_swap h i hne hbot hm₂)
      (comm_mem_swap (comm_M_Astar h i hne hbot hM2 hm₂ hA₁))] at hc
  have h1 := parabolic_eq_of_comm_mem_D h _ ha₁ hx₁ ha₂ hx₂ (K_le_D h _ hc)
  rw [(parabolic_Ks_z_eq_zero_iff h _ ha₁).mpr ha₁L,
    (parabolic_X_y_eq_zero_iff h _ hx₂).mpr hx₂L, zero_mul] at h1
  exact mul_ne_zero (mt (parabolic_Ks_z_eq_zero_iff h _ ha₂).mp ha₂L)
    (mt (parabolic_X_y_eq_zero_iff h _ hx₁).mp hx₁L) h1.symm

theorem not_Bstar_le_Cstar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : ¬ 𝐁⋆[i] ≤ 𝐂⋆[i] := fun hle => by
  obtain ⟨a, ha, haL⟩ := exists_Ks_not_mem_L h i.swap
  exact haL ((Ks_inf_P₂ h i hne hbot).le
    (mem_inf.mpr ⟨ha, Cstar_le_P₂ h i hne hbot (hle (mem_sup_right ha))⟩))

theorem not_Cstar_le_Bstar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : ¬ 𝐂⋆[i] ≤ 𝐁⋆[i] := fun hle => by
  obtain ⟨x, hx, hxL⟩ := exists_X_not_mem_L h i.swap
  have hxC : x ∈ 𝐂⋆[i] := by
    rw [Cstar_eq h i hne hbot]
    exact mem_sup_right hx
  exact hxL ((Bstar_inf_X h i hne hbot).le (mem_inf.mpr ⟨hle hxC, hx⟩))

theorem K_le_Bstar (h : FCHyp L K n φ t) (i : Axis) : 𝐊[i.swap] ≤ 𝐁⋆[i] :=
  (K_le_Ks h _).trans le_sup_right

theorem K_le_Cstar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐊[i.swap] ≤ 𝐂⋆[i] := by
  rw [Cstar_eq h i hne hbot]
  exact (K_le_X h _).trans le_sup_right

theorem M_sup_L (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐌₀[i] ⊔ 𝐋[i.swap] = 𝐌₀[i] ⊔ 𝐊[i.swap] := by
  rw [L_eq_F_sup_K, ← sup_assoc, sup_of_le_left (F_le_M h i hne hbot)]

theorem card_M_sup_K (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : Nat.card (𝐌₀[i] ⊔ 𝐊[i.swap] : Subgroup G) =
      Nat.card K ^ 6 := by
  rw [← M_sup_L h i hne hbot]
  have hML : 𝐌₀[i] ⊓ 𝐋[i.swap] = 𝐅 :=
    le_antisymm (fun x hx => (M_inf_Ks h i hne hbot).le
        (mem_inf.mpr ⟨(mem_inf.mp hx).1, L_le_Ks h _ (mem_inf.mp hx).2⟩))
      (le_inf (F_le_M h i hne hbot) le_sup_left)
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := 𝐋[i.swap]) (B := 𝐌₀[i])
    (((M_le_T₃ h i hne hbot).trans (T₃_le_Nhat h i hne hbot)).trans
      (Nhat_le_normalizer_L h i hne hbot _))
  rw [sup_comm 𝐋[i.swap] 𝐌₀[i], inf_comm 𝐋[i.swap] 𝐌₀[i], hML, card_L h,
    card_M h i hne hbot, card_F h] at h1
  have hq : 0 < Nat.card K ^ 4 := pow_pos Nat.card_pos 4
  exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)

theorem M_sup_K_le_Astar (h : FCHyp L K n φ t) (i : Axis) : 𝐌₀[i] ⊔ 𝐊[i.swap] ≤ 𝐀⋆[i] :=
  sup_le (M_le_Astar i) ((K_le_Ks h _).trans (Ks_le_Astar i))

theorem center_Astar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {y : G}
    (hy : y ∈ 𝐀⋆[i]) :
    (∀ b ∈ 𝐀⋆[i], y * b * y⁻¹ * b⁻¹ ∈ 𝐊[i.swap]) ↔ y ∈ 𝐌₀[i] ⊔ 𝐊[i.swap] := by
  constructor
  · intro hc
    obtain ⟨m, hm, a, ha, x, hx, rfl⟩ := (mem_Astar_iff h i hne hbot).mp hy
    have hred : ∀ b ∈ 𝐀⋆[i], a * x * b * (a * x)⁻¹ * b⁻¹ ∈ 𝐊[i.swap] := fun b hb => by
      have := hc b hb
      rwa [mul_assoc m a x, comm_mul_left_mem_iff (M_le_normalizer_K_swap h i hne hbot hm)
        (comm_M_Astar h i hne hbot hM2 hm hb)] at this
    obtain ⟨a', ha', ha'L⟩ := exists_Ks_not_mem_L h i.swap
    obtain ⟨x', hx', hx'L⟩ := exists_X_not_mem_L h i.swap
    have h1 := hred (a' * 1) (by rw [mul_one]; exact Ks_le_Astar i ha')
    have h2 := hred (1 * x') (by rw [one_mul]; exact X_le_Astar h i hx')
    have e1 := parabolic_eq_of_comm_mem_D h _ ha hx ha' (one_mem _) (K_le_D h _ h1)
    have e2 := parabolic_eq_of_comm_mem_D h _ ha hx (one_mem _) hx' (K_le_D h _ h2)
    have hy1 : (parabolicHom h i.swap ⟨1, X_le_R h _ (one_mem _)⟩).y = 0 :=
      (parabolic_X_y_eq_zero_iff h _ (one_mem _)).mpr (one_mem _)
    have hz1 : (parabolicHom h i.swap ⟨1, Ks_le_R h _ (one_mem _)⟩).z = 0 :=
      (parabolic_Ks_z_eq_zero_iff h _ (one_mem _)).mpr (one_mem _)
    rw [hy1, mul_zero] at e1
    rw [hz1, zero_mul] at e2
    have hxL : x ∈ 𝐋[i.swap] := (parabolic_X_y_eq_zero_iff h _ hx).mp
      ((mul_eq_zero.mp e1.symm).resolve_left
        (mt (parabolic_Ks_z_eq_zero_iff h _ ha').mp ha'L))
    have haL : a ∈ 𝐋[i.swap] := (parabolic_Ks_z_eq_zero_iff h _ ha).mp
      ((mul_eq_zero.mp e2).resolve_right (mt (parabolic_X_y_eq_zero_iff h _ hx').mp hx'L))
    rw [← M_sup_L h i hne hbot, mul_assoc]
    exact mul_mem (mem_sup_left hm) (mem_sup_right (mul_mem haL hxL))
  · intro hyM b hb
    refine comm_mem_swap (comm_mem_sup ((M_sup_K_le_Astar h i).trans
      (Astar_le_normalizer_K h i hne hbot))
      (fun m hm => comm_mem_swap (comm_M_Astar h i hne hbot hM2 hm hb))
      (fun k hk => comm_mem_of_mem_right (Astar_le_normalizer_K h i hne hbot hb) hk) y hyM)

theorem mem_F_of_comm_t_mem_K (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {m : G}
    (hm : m ∈ 𝐌₀[i]) (hc : t * m * t⁻¹ * m⁻¹ ∈ 𝐊[i.swap]) : m ∈ 𝐅 := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (SixF.t_mul_t h)
  have hκ : t⁻¹ * (m⁻¹⁻¹ * t * m⁻¹) = t * m * t⁻¹ * m⁻¹ := by rw [inv_inv, hti]; group
  have hcM : t * m * t⁻¹ * m⁻¹ ∈ 𝐌₀[i] := by
    rw [← hκ]
    exact SixF.kappa_mem_M h i hne hbot (inv_mem hm)
  have hcF : t * m * t⁻¹ * m⁻¹ ∈ 𝐅 :=
    (M_inf_Ks h i hne hbot).le (mem_inf.mpr ⟨hcM, K_le_Ks h _ hc⟩)
  have hsq1 : (t * m * t⁻¹ * m⁻¹) * (t * m * t⁻¹ * m⁻¹) ∈ 𝐔[i] :=
    SixF.sq_F_mem_U h i hne hbot hcF
  have hsq2 : (t * m * t⁻¹ * m⁻¹) * (t * m * t⁻¹ * m⁻¹) ∈ 𝐔[i.swap] := by
    rw [← closure_sq_D h i.swap]
    exact subset_closure ⟨_, K_le_D h _ hc, rfl⟩
  have hsq : (t * m * t⁻¹ * m⁻¹) * (t * m * t⁻¹ * m⁻¹) = 1 := by
    have := mem_inf.mpr ⟨hsq1, hsq2⟩
    rwa [U_inf_U_swap i, mem_bot] at this
  have hE : m⁻¹ ∈ 𝐄[i] := by
    refine (sq_kappa_eq_one_iff h i hne hbot (SixF.M_le_P₁ h i (inv_mem hm))).mp ?_
    rw [hκ]
    exact hsq
  have := (M_inf_E h i hne hbot).le (mem_inf.mpr ⟨inv_mem hm, hE⟩)
  rwa [inv_mem_iff] at this

end Astar

end SixG

end CFSG.LocalAnalysis.SymplecticFourStandard
