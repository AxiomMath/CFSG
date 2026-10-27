module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixGAstar

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

theorem comm_mul_right_mem_iff' {Z : Subgroup G} {m y w : G} (hmZ : m ∈ normalizer (Z : Set G))
    (hc : w * y * w⁻¹ * y⁻¹ ∈ Z) :
    w * (m * y) * w⁻¹ * (m * y)⁻¹ ∈ Z ↔ w * m * w⁻¹ * m⁻¹ ∈ Z := by
  have e : w * (m * y) * w⁻¹ * (m * y)⁻¹ =
      (w * m * w⁻¹ * m⁻¹) * (m * (w * y * w⁻¹ * y⁻¹) * m⁻¹) := by group
  have h1 : m * (w * y * w⁻¹ * y⁻¹) * m⁻¹ ∈ Z := (mem_normalizer_iff.mp hmZ _).mp hc
  rw [e]
  constructor
  · intro h2
    have h3 := mul_mem h2 (inv_mem h1)
    rwa [mul_inv_cancel_right] at h3
  · exact fun h2 => mul_mem h2 h1

theorem mem_normalizer_of_map_eq [Finite G] {S : Subgroup G} {g : G}
    (hg : S.map (MulAut.conj g).toMonoidHom = S) : g ∈ normalizer (S : Set G) :=
  mem_normalizer_of_conj_le fun s hs => by
    rw [← hg]
    exact ⟨s, hs, rfl⟩

theorem mem_normalizer_closure_sq [Finite G] {S : Subgroup G} {g : G}
    (hg : g ∈ normalizer (S : Set G)) :
    g ∈ normalizer ((closure {x : G | ∃ y ∈ S, x = y * y} : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_le fun a ha => ?_
  have hle : (closure {x : G | ∃ y ∈ S, x = y * y}).map (MulAut.conj g).toMonoidHom ≤
      closure {x : G | ∃ y ∈ S, x = y * y} := by
    rw [MonoidHom.map_closure]
    refine closure_mono ?_
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨g * y * g⁻¹, (mem_normalizer_iff.mp hg y).mp hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  exact hle ⟨a, ha, rfl⟩

theorem conj_mem_of_sup {X Y S : Subgroup G} {g : G} (hX : ∀ x ∈ X, g * x * g⁻¹ ∈ S)
    (hY : ∀ y ∈ Y, g * y * g⁻¹ ∈ S) {z : G} (hz : z ∈ X ⊔ Y) : g * z * g⁻¹ ∈ S := by
  have hle : X ⊔ Y ≤ S.comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun x hx => by simpa using hX x hx) (fun y hy => by simpa using hY y hy)
  simpa using hle hz

theorem conj_inv_mem {Z : Subgroup G} {g z : G} (hg : g ∈ normalizer (Z : Set G)) (hz : z ∈ Z) :
    g⁻¹ * z * g ∈ Z := by
  have := (mem_normalizer_iff.mp (inv_mem hg) z).mp hz
  rwa [inv_inv] at this

end General

section Elementary

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
theorem mem_zpowers_t (h : FCHyp L K n φ t) {b : G} (hb : b ∈ zpowers t) : b = 1 ∨ b = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [← zpow_mod_orderOf, h.setup.order_t, Nat.cast_ofNat, hk, zpow_zero]
  · right
    rw [← zpow_mod_orderOf, h.setup.order_t, Nat.cast_ofNat, hk, zpow_one]

theorem X_le_normalizer_Bstar (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐗[i.swap] ≤ normalizer (𝐁⋆[i] : Set G) := fun x hx =>
  mem_normalizer_of_conj_le fun _ hb => conj_mem_of_sup
    (fun m hm => by
      have h1 := comm_mem_swap (comm_P₂_X h i hne hbot (SixF.M_le_P₂ h i hm) hx)
      have h2 : x * m * x⁻¹ * m⁻¹ * m ∈ 𝐁⋆[i] :=
        mul_mem (K_le_Bstar h i h1) (mem_sup_left hm)
      rwa [inv_mul_cancel_right] at h2)
    (fun k hk => mem_sup_right (conj_R_mem_Ks h _ (X_le_R h _ hx) hk)) hb

theorem T₂_le_normalizer_Bstar (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐓₂[i.swap] ≤ normalizer (𝐁⋆[i] : Set G) := by
  rw [← (Astar_sup_t h i hne hbot).1, Astar_eq h i]
  exact sup_le (sup_le le_normalizer (X_le_normalizer_Bstar h i hne hbot))
    (zpowers_le.mpr (t_mem_normalizer_Bstar h i hne hbot))

theorem t_mem_normalizer_K (h : FCHyp L K n φ t) (k : Axis) :
    t ∈ normalizer (𝐊[k] : Set G) :=
  T₂_le_normalizer_K h k (H_le_T₂ h k t_mem_H)

theorem comm_t_Astar_mem_Bstar (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {a : G}
    (ha : a ∈ 𝐀⋆[i]) : t * a * t⁻¹ * a⁻¹ ∈ 𝐁⋆[i] := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (SixF.t_mul_t h)
  have hBX : 𝐁⋆[i] ⊔ 𝐗[i.swap] ≤ normalizer (𝐁⋆[i] : Set G) :=
    (Astar_eq h i).ge.trans ((Astar_le_T₂ h i hne hbot).trans (T₂_le_normalizer_Bstar h i hne hbot))
  refine comm_mem_sup hBX
    (fun b hb => comm_mem_of_mem_right (t_mem_normalizer_Bstar h i hne hbot) hb)
    (fun z hz => ?_) a ((Astar_eq h i).le ha)
  have h1 := kappa_E_mem_A h _ (X_le_E h _ (inv_mem hz))
  have e : t * z * t⁻¹ * z⁻¹ = t⁻¹ * (z⁻¹⁻¹ * t * z⁻¹) := by
    rw [inv_inv, hti]
    group
  rw [e]
  exact K_le_Bstar h i ((le_sup_left : 𝐀[i.swap] ≤ 𝐊[i.swap]) h1)

theorem comm_Astar_mem_Bstar (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {a b : G} (ha : a ∈ 𝐀⋆[i]) (hb : b ∈ 𝐀⋆[i]) :
    a * b * a⁻¹ * b⁻¹ ∈ 𝐁⋆[i] := by
  have hBX : 𝐁⋆[i] ⊔ 𝐗[i.swap] ≤ normalizer (𝐁⋆[i] : Set G) :=
    (Astar_eq h i).ge.trans ((Astar_le_T₂ h i hne hbot).trans (T₂_le_normalizer_Bstar h i hne hbot))
  refine comm_sup_of_comm hBX
    (fun c hc d hd => K_le_Bstar h i (ZP_le_K _ (comm_Bstar h i hne hbot hM2 hc hd)))
    (fun c hc d hd => ?_) (fun c hc d hd => K_le_Bstar h i
      (comm_P₂_X h i hne hbot (X_le_P₂ h i hne hbot hc) hd))
    ((Astar_eq h i).le ha) ((Astar_eq h i).le hb)
  have h1 := mul_mem hc ((mem_normalizer_iff.mp (X_le_normalizer_Bstar h i hne hbot hd) _).mp
    (inv_mem hc))
  have e : c * d * c⁻¹ * d⁻¹ = c * (d * c⁻¹ * d⁻¹) := by group
  rw [e]
  exact h1

omit [Finite G] [Finite K] in
theorem comm_zpowers_mem (h : FCHyp L K n φ t) {Z : Subgroup G} {a b : G} (hb : b ∈ zpowers t)
    (ht : a * t * a⁻¹ * t⁻¹ ∈ Z) : a * b * a⁻¹ * b⁻¹ ∈ Z := by
  rcases mem_zpowers_t h hb with hb1 | hbt
  · rw [hb1, mul_one, inv_one, mul_one, mul_inv_cancel]
    exact one_mem _
  · rw [hbt]
    exact ht

theorem comm_T₂_mem_Bstar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {x y : G}
    (hx : x ∈ 𝐓₂[i.swap]) (hy : y ∈ 𝐓₂[i.swap]) : x * y * x⁻¹ * y⁻¹ ∈ 𝐁⋆[i] := by
  have hAt : 𝐀⋆[i] ⊔ zpowers t ≤ normalizer (𝐁⋆[i] : Set G) :=
    (Astar_sup_t h i hne hbot).1.le.trans (T₂_le_normalizer_Bstar h i hne hbot)
  have htt : t * t * t⁻¹ * t⁻¹ ∈ 𝐁⋆[i] := by
    rw [mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  refine comm_sup_of_comm hAt (fun a ha b hb => comm_Astar_mem_Bstar h i hne hbot hM2 ha hb)
    (fun a ha b hb => comm_zpowers_mem h hb
      (comm_mem_swap (comm_t_Astar_mem_Bstar h i hne hbot ha)))
    (fun a ha b hb => comm_mem_swap (comm_zpowers_mem h ha
      (comm_mem_swap (comm_zpowers_mem h hb htt))))
    ((Astar_sup_t h i hne hbot).1.ge hx) ((Astar_sup_t h i hne hbot).1.ge hy)

omit [Finite K] in
theorem relIndex_ne_zero_of_finite (H K' : Subgroup G) : H.relIndex K' ≠ 0 := fun h0 => by
  have := relIndex_mul_card H K'
  rw [h0, zero_mul] at this
  exact Nat.card_pos.ne this

omit [Finite G] [Finite K] in
theorem four_le_card_K (h : FCHyp L K n φ t) : 4 ≤ Nat.card K := by
  rw [h.setup.card_K]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.setup.two_le

omit [Finite G] in
theorem two_mul_lt (h : FCHyp L K n φ t) : 2 * Nat.card K ^ 6 < Nat.card K ^ 7 := by
  have hq := four_le_card_K h
  have hpos : 0 < Nat.card K ^ 6 := pow_pos Nat.card_pos 6
  calc 2 * Nat.card K ^ 6 < Nat.card K * Nat.card K ^ 6 := Nat.mul_lt_mul_of_pos_right
        (by omega) hpos
    _ = Nat.card K ^ 7 := by ring

theorem mem_L_of_mem_elem (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {e y : G} (hat : e * t ∈ 𝐀⋆[i])
    (hc : e * y * e⁻¹ * y⁻¹ ∈ 𝐊[i.swap]) (hyM : y ∈ 𝐌₀[i] ⊔ 𝐊[i.swap]) : y ∈ 𝐋[i.swap] := by
  have e1 : e = e * t * t := by rw [mul_assoc, SixF.t_mul_t h, mul_one]
  have hcen := (center_Astar h i hne hbot hM2 (M_sup_K_le_Astar h i hyM)).mpr hyM _ hat
  rw [e1, comm_mul_left_mem_iff (Astar_le_normalizer_K h i hne hbot hat)
    (comm_mem_swap hcen)] at hc
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _
    (M_le_normalizer_K_swap h i hne hbot), Set.mem_mul] at hyM
  obtain ⟨m, hm, k, hk, rfl⟩ := hyM
  rw [comm_mul_right_mem_iff' (M_le_normalizer_K_swap h i hne hbot hm)
    (comm_mem_of_mem_right (t_mem_normalizer_K h _) hk)] at hc
  exact mul_mem (F_le_L _ (mem_F_of_comm_t_mem_K h i hne hbot hm hc)) (K_le_L _ hk)

theorem relIndex_M_sup_K_le (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {X : Subgroup G}
    (hX : X ≤ 𝐁⋆[i] ∨ X ≤ 𝐂⋆[i]) : (𝐌₀[i] ⊔ 𝐊[i.swap]).relIndex X ≤ Nat.card K := by
  obtain ⟨Y, hXY, hZY, hY⟩ : ∃ Y : Subgroup G, X ≤ Y ∧
      𝐌₀[i] ⊔ 𝐊[i.swap] ≤ Y ∧ Nat.card Y = Nat.card K ^ 7 := by
    rcases hX with h1 | h1
    · exact ⟨_, h1, sup_le le_sup_left (K_le_Bstar h i), card_Bstar h i hne hbot⟩
    · exact ⟨_, h1, sup_le le_sup_left (K_le_Cstar h i hne hbot), card_Cstar h i hne hbot⟩
  have hidx : (𝐌₀[i] ⊔ 𝐊[i.swap]).relIndex Y = Nat.card K := by
    have := relIndex_mul_card (𝐌₀[i] ⊔ 𝐊[i.swap]) Y
    rw [inf_of_le_left hZY, card_M_sup_K h i hne hbot, hY] at this
    exact Nat.eq_of_mul_eq_mul_right (pow_pos Nat.card_pos 6) (this.trans (by ring))
  exact (relIndex_le_of_le_right (H := 𝐌₀[i] ⊔ 𝐊[i.swap]) hXY
    (relIndex_ne_zero_of_finite (𝐌₀[i] ⊔ 𝐊[i.swap]) Y)).trans hidx.le

theorem card_le_of_inf_le_L (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {X : Subgroup G}
    (hX : X ≤ 𝐁⋆[i] ∨ X ≤ 𝐂⋆[i]) (hL : (𝐌₀[i] ⊔ 𝐊[i.swap]) ⊓ X ≤ 𝐋[i.swap]) :
    Nat.card X ≤ Nat.card K ^ 6 := by
  have h2 := relIndex_mul_card (𝐌₀[i] ⊔ 𝐊[i.swap]) X
  have h4 : Nat.card ((𝐌₀[i] ⊔ 𝐊[i.swap]) ⊓ X : Subgroup G) ≤ Nat.card K ^ 5 :=
    (Subgroup.card_le_of_le hL).trans (card_L h i.swap).le
  rw [← h2]
  calc _ ≤ Nat.card K * Nat.card K ^ 5 :=
        Nat.mul_le_mul (relIndex_M_sup_K_le h i hne hbot hX) h4
    _ = Nat.card K ^ 6 := by ring

theorem relIndex_Astar_T₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐀⋆[i].relIndex 𝐓₂[i.swap] = 2 := by
  have := relIndex_mul_card 𝐀⋆[i] 𝐓₂[i.swap]
  rw [inf_of_le_left (Astar_le_T₂ h i hne hbot), card_Astar h i hne hbot,
    card_T₂ h i hne hbot] at this
  exact Nat.eq_of_mul_eq_mul_right (pow_pos Nat.card_pos 8) this

theorem relIndex_Astar_le (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {E : Subgroup G} (hET : E ≤ 𝐓₂[i.swap]) :
    𝐀⋆[i].relIndex E ≤ 2 :=
  (relIndex_le_of_le_right (H := 𝐀⋆[i]) hET
    (relIndex_ne_zero_of_finite 𝐀⋆[i] 𝐓₂[i.swap])).trans (relIndex_Astar_T₂ h i hne hbot).le

theorem card_le_two_mul (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {E : Subgroup G} (hET : E ≤ 𝐓₂[i.swap]) :
    Nat.card E ≤ 2 * Nat.card (E ⊓ 𝐀⋆[i] : Subgroup G) := by
  have h5 := relIndex_mul_card 𝐀⋆[i] E
  rw [← h5, inf_comm 𝐀⋆[i] E]
  exact Nat.mul_le_mul_right _ (relIndex_Astar_le h i hne hbot hET)

theorem mul_t_mem_Astar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {e : G} (heT : e ∈ 𝐓₂[i.swap]) (heA : e ∉ 𝐀⋆[i]) :
    e * t ∈ 𝐀⋆[i] :=
  (mem_or_mul_t_mem h (t_mem_normalizer_Astar h i hne hbot)
    ((Astar_sup_t h i hne hbot).1.ge heT)).resolve_left heA

theorem elem_inf_Astar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {E : Subgroup G}
    (helem : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ 𝐊[i.swap] ∧ x * x ∈ 𝐊[i.swap]) :
    E ⊓ 𝐀⋆[i] ≤ 𝐁⋆[i] ∨ E ⊓ 𝐀⋆[i] ≤ 𝐂⋆[i] :=
  elem_le_Bstar_or_Cstar h i hne hbot hM2 inf_le_right
    (fun x hx => (helem x (mem_inf.mp hx).1 x (mem_inf.mp hx).1).2)
    (fun x hx y hy => (helem x (mem_inf.mp hx).1 y (mem_inf.mp hy).1).1)

theorem inf_le_L_of_elem (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {E : Subgroup G}
    (helem : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ 𝐊[i.swap] ∧ x * x ∈ 𝐊[i.swap]) {e : G}
    (he : e ∈ E) (hat : e * t ∈ 𝐀⋆[i]) : (𝐌₀[i] ⊔ 𝐊[i.swap]) ⊓ (E ⊓ 𝐀⋆[i]) ≤ 𝐋[i.swap] :=
  fun y hy => mem_L_of_mem_elem h i hne hbot hM2 hat
    (helem e he y (mem_inf.mp (mem_inf.mp hy).2).1).1 (mem_inf.mp hy).1

theorem card_le_of_not_le_Astar (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {E : Subgroup G} (hET : E ≤ 𝐓₂[i.swap])
    (helem : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ 𝐊[i.swap] ∧ x * x ∈ 𝐊[i.swap])
    (hEA : ¬ E ≤ 𝐀⋆[i]) : Nat.card E ≤ 2 * Nat.card K ^ 6 := by
  obtain ⟨e, he, heA⟩ := IsConcreteLE.not_le_iff_exists.mp hEA
  exact (card_le_two_mul h i hne hbot hET).trans (Nat.mul_le_mul_left _
    (card_le_of_inf_le_L h i hne hbot (elem_inf_Astar h i hne hbot hM2 helem)
      (inf_le_L_of_elem h i hne hbot hM2 helem he
        (mul_t_mem_Astar h i hne hbot (hET he) heA))))

theorem card_le_of_elem (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {E : Subgroup G}
    (hET : E ≤ 𝐓₂[i.swap])
    (helem : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ 𝐊[i.swap] ∧ x * x ∈ 𝐊[i.swap]) :
    Nat.card E ≤ Nat.card K ^ 7 ∧
      (Nat.card E = Nat.card K ^ 7 → E = 𝐁⋆[i] ∨ E = 𝐂⋆[i]) := by
  by_cases hEA : E ≤ 𝐀⋆[i]
  · rcases elem_le_Bstar_or_Cstar h i hne hbot hM2 hEA (fun x hx => (helem x hx x hx).2)
      (fun x hx y hy => (helem x hx y hy).1) with h1 | h1
    · refine ⟨(Subgroup.card_le_of_le h1).trans (card_Bstar h i hne hbot).le, fun hc => ?_⟩
      exact Or.inl (Subgroup.eq_of_le_of_card_ge h1 (by rw [card_Bstar h i hne hbot, hc]))
    · refine ⟨(Subgroup.card_le_of_le h1).trans (card_Cstar h i hne hbot).le, fun hc => ?_⟩
      exact Or.inr (Subgroup.eq_of_le_of_card_ge h1 (by rw [card_Cstar h i hne hbot, hc]))
  · have h1 := card_le_of_not_le_Astar h i hne hbot hM2 hET helem hEA
    have h2 := two_mul_lt h
    exact ⟨h1.trans h2.le, fun hc => absurd (hc ▸ h1) (not_le.mpr h2)⟩

theorem mem_Ks_of_comm_t_mem_K (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {y : G}
    (hy : y ∈ 𝐁⋆[i]) (hc : t * y * t⁻¹ * y⁻¹ ∈ 𝐊[i.swap]) : y ∈ 𝐊⋆ := by
  obtain ⟨m, hm, k, hk, rfl⟩ := (mem_Bstar_iff h i hne hbot).mp hy
  have hctk : t * k * t⁻¹ * k⁻¹ ∈ 𝐊[i.swap] :=
    ZP_le_K _ (comm_mem_of_sq (fun _ ha => mul_self_mem_ZP h ha) t_mem_H (Ks_le_H h hk))
  rw [comm_mul_right_mem_iff' (M_le_normalizer_K_swap h i hne hbot hm) hctk] at hc
  exact mul_mem (F_le_Ks h (mem_F_of_comm_t_mem_K h i hne hbot hm hc)) hk

theorem mem_Ks_of_comm_mem_K (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {e y : G} (hb : e * t ∈ 𝐁⋆[i]) (hyB : y ∈ 𝐁⋆[i])
    (hc : e * y * e⁻¹ * y⁻¹ ∈ 𝐊[i.swap]) : y ∈ 𝐊⋆ := by
  have hBK : 𝐁⋆[i] ≤ normalizer (𝐊[i.swap] : Set G) :=
    (le_sup_left : 𝐁⋆[i] ≤ 𝐀⋆[i]).trans (Astar_le_normalizer_K h i hne hbot)
  have e1 : e = e * t * t := by rw [mul_assoc, SixF.t_mul_t h, mul_one]
  rw [e1, comm_mul_left_mem_iff (hBK hb) (elem_Bstar h i hne hbot hM2 hb hyB).1] at hc
  exact mem_Ks_of_comm_t_mem_K h i hne hbot hyB hc

theorem mem_H_of_sq_mem_K (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {e : G} (heT : e ∈ 𝐓₂[i.swap]) (hb : e * t ∈ 𝐁⋆[i])
    (hee : e * e ∈ 𝐊[i.swap]) : e ∈ 𝐇 := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (SixF.t_mul_t h)
  have heK := T₂_le_normalizer_K h _ heT
  have key : t * e * t⁻¹ * e⁻¹ = e⁻¹ * ((e * t) * (e * t)) * e * (e * e)⁻¹ := by
    rw [hti]
    group
  have h1 : t * e * t⁻¹ * e⁻¹ ∈ 𝐊[i.swap] := by
    rw [key]
    exact mul_mem (conj_inv_mem heK (elem_Bstar h i hne hbot hM2 hb hb).2) (inv_mem hee)
  have e2 : t * (e * t) * t⁻¹ * (e * t)⁻¹ = t * e * t⁻¹ * e⁻¹ := by group
  have hbK := mem_Ks_of_comm_t_mem_K h i hne hbot hb (e2 ▸ h1)
  have e3 : e = e * t * t⁻¹ := by group
  rw [e3]
  exact mul_mem (Ks_le_H h hbK) (inv_mem t_mem_H)

theorem le_Bstar_or_le_H (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {E : Subgroup G}
    (hET : E ≤ 𝐓₃[i])
    (helem : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ 𝐊[i.swap] ∧ x * x ∈ 𝐊[i.swap]) :
    E ≤ 𝐁⋆[i] ∨ E ≤ 𝐇 := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨e, he, heB⟩ := IsConcreteLE.not_le_iff_exists.mp hcon.1
  apply hcon.2
  have htB := t_mem_normalizer_Bstar h i hne hbot
  have hT : ∀ x ∈ E, x ∈ 𝐁⋆[i] ∨ x * t ∈ 𝐁⋆[i] := fun x hx =>
    mem_or_mul_t_mem h htB ((Bstar_sup_t h i hne hbot).1.ge (hET hx))
  have hb : e * t ∈ 𝐁⋆[i] := (hT e he).resolve_left heB
  have heH := mem_H_of_sq_mem_K h i hne hbot hM2 (mem_inf.mp (hET he)).2 hb (helem e he e he).2
  intro y hy
  rcases hT y hy with hyB | hyt
  · exact Ks_le_H h (mem_Ks_of_comm_mem_K h i hne hbot hM2 hb hyB (helem e he y hy).1)
  · have h1 : e⁻¹ * y ∈ 𝐁⋆[i] := by
      have e4 : e⁻¹ * y = t * ((e * t)⁻¹ * (y * t)) * t⁻¹ := by group
      rw [e4]
      exact (mem_normalizer_iff.mp htB _).mp (mul_mem (inv_mem hb) hyt)
    have h2 := mem_Ks_of_comm_mem_K h i hne hbot hM2 hb h1
      (helem e he _ (mul_mem (inv_mem he) hy)).1
    have e5 : y = e * (e⁻¹ * y) := by group
    rw [e5]
    exact mul_mem heH (Ks_le_H h h2)

theorem K_le_H (h : FCHyp L K n φ t) (k : Axis) : 𝐊[k] ≤ 𝐇 := (K_le_Ks h k).trans (Ks_le_H h)

theorem elem_H (h : FCHyp L K n φ t) (k : Axis) {x y : G} (hx : x ∈ 𝐇) (hy : y ∈ 𝐇) :
    x * y * x⁻¹ * y⁻¹ ∈ 𝐊[k] ∧ x * x ∈ 𝐊[k] :=
  ⟨ZP_le_K _ (comm_mem_of_sq (fun _ ha => mul_self_mem_ZP h ha) hx hy),
    ZP_le_K _ (mul_self_mem_ZP h hx)⟩

end Elementary

end SixG

end CFSG.LocalAnalysis.SymplecticFourStandard
