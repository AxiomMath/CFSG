module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixFBase
public import CFSG.LocalAnalysis.SteinbergSFSingleCommRootStandardTorus

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
local notation "𝐌ʷ[" i "," k "]" => (𝐌₀[i].map (MulAut.conj 𝐰[k]⁻¹).toMonoidHom : Subgroup G)

omit [Finite G] [Finite K] in
theorem t_mul_t (h : FCHyp L K n φ t) : t * t = 1 := by
  have := pow_orderOf_eq_one t
  rwa [h.setup.order_t, sq] at this

theorem U_comm_E (h : FCHyp L K n φ t) (i : Axis) {u : G} (hu : u ∈ 𝐔[i]) {e : G}
    (he : e ∈ 𝐄[i]) : u * e = e * u :=
  ((mem_center_map_iff.mp (U_le_center_E h i hu)).2 e he).symm

theorem sq_F_mem_U (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {f : G} (hf : f ∈ 𝐅) : f * f ∈ 𝐔[i] := by
  obtain ⟨-, lam, -, huniq, -, hlamne⟩ := square_map h i
  have hl : (1 : K) = lam := huniq 1 (W_sq_eq' h i hne hbot)
  obtain ⟨hclW, -, -, -⟩ := hlamne (hl ▸ one_ne_zero)
  rw [F_eq_W_sup_W h i] at hf
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_commute fun x hx y hy =>
    F_comm h (W_le_F _ hx) (W_le_F _ hy)).mp hf
  have hab : a * b = b * a := F_comm h (W_le_F _ ha) (W_le_F _ hb)
  have e : a * b * (a * b) = (a * a) * (b * b) := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
  rw [e, sq_W_swap h i hne hbot hb, mul_one, ← hclW]
  exact subset_closure ⟨a, ha, rfl⟩

theorem sq_L_mem_U (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {l : G} (hl : l ∈ 𝐋[i]) : l * l ∈ 𝐔[i] := by
  rw [← SetLike.mem_coe, ← L_mul h i] at hl
  obtain ⟨f, hf, a, ha, rfl⟩ := hl
  have hc : a * f * a⁻¹ * f⁻¹ ∈ 𝐔[i] := commutator_A_F h i (commutator_mem_commutator ha hf)
  have hcz := U_comm_E h i hc (F_le_E h i hf)
  have e : f * a * (f * a) = (a * f * a⁻¹ * f⁻¹) * (f * f) := by
    have h1 : f * a * (f * a) = f * (a * f * a⁻¹ * f⁻¹) * f * (a * a) := by group
    rw [h1, A_mul_self h i ha, mul_one, ← hcz]
    group
  rw [e]
  exact mul_mem hc (sq_F_mem_U h i hne hbot hf)

theorem mem_L_of_mem_X_of_mem_H (h : FCHyp L K n φ t) (i : Axis) {y : G} (hyX : y ∈ 𝐗[i])
    (hyH : y ∈ 𝐇) : y ∈ 𝐋[i] := by
  have hyE : y ∈ 𝐇 ⊓ 𝐄[i] := mem_inf.mpr ⟨hyH, X_le_E h i hyX⟩
  rw [← L_sup_t h i] at hyE
  have htL : t ∈ normalizer (𝐋[i] : Set G) :=
    R_le_normalizer_L h i (mem_sup_left (mem_sup_right (mem_zpowers t)))
  rcases mem_or_mul_mem (t_mul_t h) htL hyE with hy | hy
  · exact hy
  · exfalso
    apply t_not_mem_X h i
    have := mul_mem (L_le_X h i hy) (inv_mem hyX)
    rwa [mul_inv_cancel_right] at this

theorem sq_X_mem_U (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐗[i]) : x * x ∈ 𝐔[i] := by
  have hxE : x ∈ 𝐄[i] := X_le_E h i hx
  have ha := conj_t_mem_A h i (mem_sup_right hxE : x ∈ 𝐑[i])
  obtain ⟨M, hM⟩ : ∃ M : SL₂ K,
      ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ psiG φ i (t⁻¹ * (x * t * x⁻¹))) 1 = 0 := by
    by_cases hv : psiG φ i (t⁻¹ * (x * t * x⁻¹)) = 0
    · exact ⟨1, by rw [hv, Matrix.mulVec_zero]; rfl⟩
    · have h10 : (![1, 0] : Fin 2 → K) ≠ 0 := fun h0 => by simpa using congrFun h0 0
      obtain ⟨M, hM⟩ := exists_sl2_mulVec_eq hv h10
      exact ⟨M, by rw [hM]; simp⟩
  obtain ⟨hsC, hsA, hsU, hsN⟩ := h.symm_s_mem i M
  set s : G := ((φ.symm (sHom K i M) : L) : G) with hs
  have hx' : s * x * s⁻¹ ∈ 𝐄[i] := conj_mem_pCore_map hsN hxE
  have hsts : s * t * s⁻¹ = t := by
    rw [mem_centralizer_singleton_iff.mp hsC, mul_inv_cancel_right]
  have e1 : t⁻¹ * ((s * x * s⁻¹) * t * (s * x * s⁻¹)⁻¹) = s * (t⁻¹ * (x * t * x⁻¹)) * s⁻¹ := by
    calc t⁻¹ * ((s * x * s⁻¹) * t * (s * x * s⁻¹)⁻¹)
        = (s * t * s⁻¹)⁻¹ * ((s * x * s⁻¹) * (s * t * s⁻¹) * (s * x * s⁻¹)⁻¹) := by
          rw [hsts]
      _ = s * (t⁻¹ * (x * t * x⁻¹)) * s⁻¹ := by group
  have h1 : t⁻¹ * ((s * x * s⁻¹) * t * (s * x * s⁻¹)⁻¹) ∈ 𝐙 := by
    rw [e1, ← psiG_one_eq_zero_iff h i (psiG_conj_s h.twoCore φ i M ha).1,
      (psiG_conj_s h.twoCore φ i M ha).2]
    exact hM
  have h2 : s * x * s⁻¹ ∈ 𝐇 := (mem_H_iff_ZP h i (mem_sup_right hx')).mpr h1
  have hsX : s * x * s⁻¹ ∈ 𝐗[i] :=
    (mem_normalizer_iff.mp (normalizer_A_le h i ⟨(φ.symm _).2, hsA⟩) x).mp hx
  have h3 := sq_L_mem_U h i hne hbot (mem_L_of_mem_X_of_mem_H h i hsX h2)
  have h4 := (mem_normalizer_iff.mp (inv_mem hsU) _).mp h3
  rwa [show s⁻¹ * ((s * x * s⁻¹) * (s * x * s⁻¹)) * s⁻¹⁻¹ = x * x by group] at h4

theorem comm_X_mem_U (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x y : G} (hx : x ∈ 𝐗[i]) (hy : y ∈ 𝐗[i]) :
    x⁻¹ * y⁻¹ * x * y ∈ 𝐔[i] := by
  have hu₁ := sq_X_mem_U h i hne hbot (mul_mem hx hy)
  have hu₂ := sq_X_mem_U h i hne hbot hx
  have hu₃ := sq_X_mem_U h i hne hbot hy
  have hyE : y ∈ 𝐄[i] := X_le_E h i hy
  have e3 : y * x * (y * x) = x * y * (x * y) := by
    have h1 : y * x * (y * x) = y * (x * y * (x * y)) * y⁻¹ := by group
    rw [h1, ← U_comm_E h i hu₁ hyE, mul_inv_cancel_right]
  have e2 : (x * x) * y⁻¹ = y⁻¹ * (x * x) := U_comm_E h i hu₂ (inv_mem hyE)
  have e : x⁻¹ * y⁻¹ * x * y = (y * x * (y * x))⁻¹ * ((x * x) * (y * y)) := by
    have h1 : x⁻¹ * y⁻¹ * x * y = x⁻¹ * y⁻¹ * x⁻¹ * ((x * x) * y⁻¹) * (y * y) := by group
    rw [h1, e2]
    group
  rw [e, e3]
  exact mul_mem (inv_mem hu₁) (mul_mem hu₂ hu₃)

theorem conj_U_mem (h : FCHyp L K n φ t) (i : Axis) {g : G} (hg : g ∈ 𝐃𝐧[i]) {u : G}
    (hu : u ∈ 𝐔[i]) : g * u * g⁻¹ ∈ 𝐔[i] := by
  rw [← closure_sq_D h i] at hu ⊢
  have hle : (closure {x : G | ∃ y ∈ 𝐃[i], x = y * y}).map (MulAut.conj g).toMonoidHom ≤
      closure {x : G | ∃ y ∈ 𝐃[i], x = y * y} := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine subset_closure ⟨g * y * g⁻¹, (mem_normalizer_iff.mp hg y).mp hy, ?_⟩
    change g * (y * y) * g⁻¹ = _
    group
  exact hle ⟨u, hu, rfl⟩

theorem conj_E_mem_P₁ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {p : G} (hp : p ∈ 𝐏₁[i]) {e : G} (he : e ∈ 𝐄[i]) :
    p * e * p⁻¹ ∈ 𝐄[i] := by
  obtain ⟨hN, -, -⟩ := quotient_P₁ h i hne hbot
  have := hN.conj_mem ⟨e, E_le_P₁ h i hne hbot he⟩ (mem_subgroupOf.mpr he) ⟨p, hp⟩
  rw [mem_subgroupOf] at this
  exact this

theorem mem_X_or_of_mem_E (h : FCHyp L K n φ t) (i : Axis) {e : G} (he : e ∈ 𝐄[i]) :
    e ∈ 𝐗[i] ∨ t * e ∈ 𝐗[i] := by
  rw [← (X_sup_t h i).2] at he
  exact mem_or_mul_mem (t_mul_t h)
    (R_le_normalizer_X h i (mem_sup_left (mem_sup_right (mem_zpowers t)))) he

theorem conj_X_mem (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {p : G} (hp : p ∈ 𝐏₁[i]) {x : G} (hx : x ∈ 𝐗[i]) :
    p * x * p⁻¹ ∈ 𝐗[i] := by
  set Y := (𝐗[i]).map (MulAut.conj p).toMonoidHom with hY
  have hpD : p ∈ 𝐃𝐧[i] := P₁_le i hp
  by_cases hYX : Y ≤ 𝐗[i]
  · exact hYX ⟨x, hx, rfl⟩
  exfalso
  have hYE : Y ≤ 𝐄[i] := by
    rintro _ ⟨y, hy, rfl⟩
    exact conj_E_mem_P₁ h i hne hbot hp (X_le_E h i hy)
  have hYU : ∀ y ∈ Y, ∀ y' ∈ Y, y * y ∈ 𝐔[i] ∧ y⁻¹ * y'⁻¹ * y * y' ∈ 𝐔[i] := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    change (p * y * p⁻¹) * (p * y * p⁻¹) ∈ 𝐔[i] ∧
      (p * y * p⁻¹)⁻¹ * (p * y' * p⁻¹)⁻¹ * (p * y * p⁻¹) * (p * y' * p⁻¹) ∈ 𝐔[i]
    refine ⟨?_, ?_⟩
    · rw [show (p * y * p⁻¹) * (p * y * p⁻¹) = p * (y * y) * p⁻¹ by group]
      exact conj_U_mem h i hpD (sq_X_mem_U h i hne hbot hy)
    · rw [show (p * y * p⁻¹)⁻¹ * (p * y' * p⁻¹)⁻¹ * (p * y * p⁻¹) * (p * y' * p⁻¹) =
          p * (y⁻¹ * y'⁻¹ * y * y') * p⁻¹ by group]
      exact conj_U_mem h i hpD (comm_X_mem_U h i hne hbot hy hy')
  have hYD : Y ≤ 𝐃[i] := le_of_elementary_mod (t_mul_t h)
    (fun e he => mem_X_or_of_mem_E h i he) (X_le_E h i) (fun u hu e he => U_comm_E h i hu he)
    (fun x hx y hy => ⟨sq_X_mem_U h i hne hbot hx, comm_X_mem_U h i hne hbot hx hy⟩)
    (fun x hx hu => mem_D_of_kappa h i (X_le_E h i hx) (by
      rw [show t⁻¹ * (x⁻¹ * t * x) = (x⁻¹ * t⁻¹ * x * t)⁻¹ by group]
      exact inv_mem hu)) (t_mem_D h i) hYE hYU hYX
  have h1 := card_le_of_le hYD
  rw [hY, card_map_of_injective (MulAut.conj p).injective, card_X h i, h.card_D i] at h1
  have hq : 2 ≤ Nat.card K := by have := h.four_le_card; omega
  have h4 : 0 < Nat.card K ^ 4 := pow_pos (by omega) 4
  have h2 : 4 ≤ Nat.card K ^ 2 := by nlinarith
  have e : Nat.card K ^ 6 = Nat.card K ^ 4 * Nat.card K ^ 2 := by ring
  nlinarith

theorem P₁_le_normalizer_X (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐏₁[i] ≤ normalizer ((𝐗[i] : Subgroup G) : Set G) :=
  fun p hp => mem_normalizer_iff.mpr fun x => ⟨fun hx => conj_X_mem h i hne hbot hp hx,
    fun hx => by
      have := conj_X_mem h i hne hbot (inv_mem hp) hx
      rwa [show p⁻¹ * (p * x * p⁻¹) * p⁻¹⁻¹ = x by group] at this⟩

theorem relIndex_X_E (h : FCHyp L K n φ t) (i : Axis) : (𝐗[i]).relIndex 𝐄[i] = 2 := by
  have h1 := relIndex_mul_card (H := 𝐗[i]) (K := 𝐄[i])
  rw [inf_of_le_left (X_le_E h i), card_X h i, card_E h i] at h1
  have hq : 0 < Nat.card K ^ 6 := pow_pos Nat.card_pos 6
  have h2 : Nat.card K ^ 6 * (𝐗[i]).relIndex 𝐄[i] = Nat.card K ^ 6 * 2 := by rw [mul_comm, h1]; ring
  exact Nat.eq_of_mul_eq_mul_left hq h2

theorem conj_w_mem_X (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐏₁[i]) :
    x⁻¹ * 𝐰[i] * x * 𝐰[i]⁻¹ ∈ 𝐗[i] := by
  set s : SL₂ K →* G := L.subtype.comp (φ.symm.toMonoidHom.comp (sHom K i)) with hsdef
  have hK4 := h.four_le_card
  have : Group.IsPerfect (SL₂ K) := sl2_isPerfect hK4
  have : Group.IsPerfect ↥s.range :=
    Group.IsPerfect.ofSurjective (f := s.rangeRestrict) s.rangeRestrict_surjective
  obtain ⟨hN, e, he⟩ := quotient_P₁ h i hne hbot
  have hCY : s.range ≤ normalizer ((𝐗[i] : Subgroup G) : Set G) := by
    rintro _ ⟨M, rfl⟩
    exact normalizer_A_le h i ⟨(φ.symm _).2, (h.symm_s_mem i M).2.1⟩
  have hxE : ∀ c ∈ s.range, x⁻¹ * c * x * c⁻¹ ∈ 𝐄[i] := by
    rintro _ ⟨M, rfl⟩
    set c : G := ((φ.symm (sHom K i M) : L) : G) with hc
    have hcC : c ∈ 𝐂 := (h.symm_s_mem i M).1
    have hcM : c ∈ 𝐌[i] := h.symm_s_mem_M i M
    have hcD : c ∈ 𝐃𝐧[i] := mem_normalizer_iff.mpr fun d => ⟨fun hd =>
      conj_mem_pCore_map hcM hd, fun hd => by
        have := conj_mem_pCore_map (inv_mem hcM) hd
        rwa [show c⁻¹ * (c * d * c⁻¹) * c⁻¹⁻¹ = d by group] at this⟩
    have hcU : ∀ u ∈ 𝐔[i], u * c = c * u :=
      ((TwoCoreSetup.mem_pull_rootC_iff φ i).mp (symm_s_mem_rootC h.twoCore φ i M)).2
    have hy : c * x * c⁻¹ ∈ 𝐏₁[i] := conj_mem_P₁ i hcD hx
    have heq : e (⟨c * x * c⁻¹, hy⟩ : 𝐏₁[i]) = e (⟨x, hx⟩ : 𝐏₁[i]) := by
      apply Subtype.ext
      rw [he, he]
      change (t⁻¹ * ((c * x * c⁻¹)⁻¹ * t * (c * x * c⁻¹))) *
        (t⁻¹ * ((c * x * c⁻¹)⁻¹ * t * (c * x * c⁻¹))) = _
      rw [sq_kappa_conj_C hcC x]
      have hu : (t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x)) ∈ 𝐔[i] := by
        have := (e (⟨x, hx⟩ : 𝐏₁[i])).2
        rwa [he] at this
      rw [← hcU _ hu, mul_inv_cancel_right]
    have h1 := QuotientGroup.eq.mp (e.injective heq).symm
    rw [mem_subgroupOf] at h1
    change x⁻¹ * (c * x * c⁻¹) ∈ 𝐄[i] at h1
    rwa [show x⁻¹ * (c * x * c⁻¹) = x⁻¹ * c * x * c⁻¹ by group] at h1
  have hw : 𝐰[i] ∈ s.range := ⟨swapSL, by rw [w_eq]; rfl⟩
  exact mem_of_perfect_of_index_two (C := s.range) (relIndex_X_E h i) hCY hxE _ hw

theorem M_le_P₁ (h : FCHyp L K n φ t) (i : Axis) : 𝐌₀[i] ≤ 𝐏₁[i] :=
  (M_le_P₀ h i).trans inf_le_left

theorem X_le_P₁ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐗[i] ≤ 𝐏₁[i] :=
  (X_le_E h i).trans (E_le_P₁ h i hne hbot)

theorem M_mul_X (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    ((𝐌₀[i] : Subgroup G) : Set G) * ((𝐗[i] : Subgroup G) : Set G) =
      ((𝐌₀[i] ⊔ 𝐗[i] : Subgroup G) : Set G) :=
  (coe_mul_of_left_le_normalizer_right _ _
    ((M_le_P₁ h i).trans (P₁_le_normalizer_X h i hne hbot))).symm

theorem conj_w_mem_MX (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {y : G} (hy : y ∈ 𝐌₀[i] ⊔ 𝐗[i]) :
    𝐰[i] * y * 𝐰[i]⁻¹ ∈ 𝐌₀[i] ⊔ 𝐗[i] := by
  rw [← SetLike.mem_coe, ← M_mul_X h i hne hbot] at hy ⊢
  obtain ⟨m, hm, x, hx, rfl⟩ := hy
  have hwX : 𝐰[i] ∈ normalizer ((𝐗[i] : Subgroup G) : Set G) :=
    normalizer_A_le h i ⟨(φ.symm _).2, (w_facts h i).2.1⟩
  have h1 : m⁻¹ * 𝐰[i] * m * 𝐰[i]⁻¹ ∈ 𝐗[i] := conj_w_mem_X h i hne hbot (M_le_P₁ h i hm)
  have h2 : 𝐰[i] * x * 𝐰[i]⁻¹ ∈ 𝐗[i] := (mem_normalizer_iff.mp hwX x).mp hx
  refine ⟨m, hm, (m⁻¹ * 𝐰[i] * m * 𝐰[i]⁻¹) * (𝐰[i] * x * 𝐰[i]⁻¹), mul_mem h1 h2, ?_⟩
  group

theorem Mhat_eq (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐌₀[i] ⊔ 𝐌ʷ[i, i] = 𝐌₀[i] ⊔ 𝐗[i] := by
  apply le_antisymm
  · refine sup_le le_sup_left fun y hy => ?_
    rw [mem_map_conj_inv] at hy
    have h1 := conj_w_mem_MX h i hne hbot (mem_sup_left hy)
    have e : 𝐰[i] * (𝐰[i] * y * 𝐰[i]⁻¹) * 𝐰[i]⁻¹ = y := by
      rw [w_inv]
      calc 𝐰[i] * (𝐰[i] * y * 𝐰[i]) * 𝐰[i] = (𝐰[i] * 𝐰[i]) * y * (𝐰[i] * 𝐰[i]) := by group
        _ = y := by rw [w_mul_self, one_mul, mul_one]
    rwa [e] at h1
  · exact sup_le le_sup_left (sup_le ((F_le_M h i hne hbot).trans le_sup_left)
      ((map_mono (F_le_M h i hne hbot)).trans le_sup_right))

theorem M_mul_Mw (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    ((𝐌₀[i] : Subgroup G) : Set G) * ((𝐌ʷ[i, i] : Subgroup G) : Set G) =
      ((𝐌₀[i] ⊔ 𝐌ʷ[i, i] : Subgroup G) : Set G) := by
  apply le_antisymm
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)
  intro y hy
  rw [Mhat_eq h i hne hbot, ← M_mul_X h i hne hbot] at hy
  obtain ⟨m, hm, x, hx, rfl⟩ := hy
  rw [← F_mul_Fw' h i] at hx
  obtain ⟨f, hf, f', hf', rfl⟩ := hx
  exact ⟨m * f, mul_mem hm (F_le_M h i hne hbot hf), f', map_mono (F_le_M h i hne hbot) hf',
    mul_assoc m f f'⟩

theorem M_inf_X (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐌₀[i] ⊓ 𝐗[i] = 𝐅 :=
  le_antisymm (fun _ hx => (M_inf_E h i hne hbot).le ⟨hx.1, X_le_E h i hx.2⟩)
    (le_inf (F_le_M h i hne hbot) le_sup_left)

theorem card_Mhat (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    Nat.card (𝐌₀[i] ⊔ 𝐌ʷ[i, i] : Subgroup G) = Nat.card K ^ 7 := by
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := 𝐗[i]) (B := 𝐌₀[i]) ((M_le_P₁ h i).trans (P₁_le_normalizer_X h i hne hbot))
  rw [sup_comm 𝐗[i] 𝐌₀[i], inf_comm 𝐗[i] 𝐌₀[i], M_inf_X h i hne hbot, card_X h i,
    card_M h i hne hbot, card_F h, ← Mhat_eq h i hne hbot] at h1
  have hq : 0 < Nat.card K ^ 4 := pow_pos Nat.card_pos 4
  exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)

theorem Mhat_inf_E (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : (𝐌₀[i] ⊔ 𝐌ʷ[i, i]) ⊓ 𝐄[i] = 𝐗[i] := by
  rw [Mhat_eq h i hne hbot]
  refine le_antisymm (fun y hy => ?_) (le_inf le_sup_right (X_le_E h i))
  obtain ⟨hy1, hy2⟩ := mem_inf.mp hy
  rw [← SetLike.mem_coe, ← M_mul_X h i hne hbot] at hy1
  obtain ⟨m, hm, x, hx, rfl⟩ := hy1
  have hmE : m ∈ 𝐄[i] := by
    have := mul_mem hy2 (inv_mem (X_le_E h i hx))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (mem_sup_left ((M_inf_E h i hne hbot).le ⟨hm, hmE⟩)) hx

theorem Mhat_le_P₁ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐌₀[i] ⊔ 𝐌ʷ[i, i] ≤ 𝐏₁[i] := by
  rw [Mhat_eq h i hne hbot]
  exact sup_le (M_le_P₁ h i) (X_le_P₁ h i hne hbot)

theorem P₁_le_normalizer_E (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐏₁[i] ≤ normalizer ((𝐄[i] : Subgroup G) : Set G) :=
  fun p hp => mem_normalizer_iff.mpr fun e => ⟨fun he => conj_E_mem_P₁ h i hne hbot hp he,
    fun he => by
      have := conj_E_mem_P₁ h i hne hbot (inv_mem hp) he
      rwa [show p⁻¹ * (p * e * p⁻¹) * p⁻¹⁻¹ = e by group] at this⟩

theorem Mhat_mul_E (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    ((𝐌₀[i] ⊔ 𝐌ʷ[i, i] : Subgroup G) : Set G) * ((𝐄[i] : Subgroup G) : Set G) =
      ((𝐏₁[i] : Subgroup G) : Set G) := by
  have hle := (Mhat_le_P₁ h i hne hbot).trans (P₁_le_normalizer_E h i hne hbot)
  rw [← coe_mul_of_left_le_normalizer_right _ _ hle]
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := 𝐄[i]) (B := 𝐌₀[i] ⊔ 𝐌ʷ[i, i]) hle
  rw [sup_comm 𝐄[i] (𝐌₀[i] ⊔ 𝐌ʷ[i, i]), inf_comm 𝐄[i] (𝐌₀[i] ⊔ 𝐌ʷ[i, i]),
    Mhat_inf_E h i hne hbot, card_E h i, card_Mhat h i hne hbot, card_X h i] at h1
  have h2 : Nat.card (𝐌₀[i] ⊔ 𝐌ʷ[i, i] ⊔ 𝐄[i] : Subgroup G) = 2 * Nat.card K ^ 7 := by
    have hq : 0 < Nat.card K ^ 6 := pow_pos Nat.card_pos 6
    exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)
  rw [eq_of_le_of_card_ge (sup_le (Mhat_le_P₁ h i hne hbot) (E_le_P₁ h i hne hbot))
    (by rw [h2, card_P₁ h i hne hbot])]

theorem t_mem_normalizer_Mhat (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    t ∈ normalizer ((𝐌₀[i] ⊔ 𝐌ʷ[i, i] : Subgroup G) : Set G) := by
  rw [Mhat_eq h i hne hbot]
  exact mem_normalizer_of_conj_le fun _ hy => conj_mem_sup
    (fun m hm => (mem_normalizer_iff.mp (t_mem_normalizer_M h i hne hbot) m).mp hm)
    (fun x hx => conj_X_mem h i hne hbot (E_le_P₁ h i hne hbot (t_mem_E h i)) hx) hy

theorem J_le_normalizer_Mhat (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐉 ≤ normalizer ((𝐌₀[i] ⊔ 𝐌ʷ[i, i] : Subgroup G) : Set G) := by
  rw [Mhat_eq h i hne hbot]
  exact fun j hj => mem_normalizer_of_conj_le fun _ hy => conj_mem_sup
    (fun m hm => (mem_normalizer_iff.mp (J_le_normalizer_M h i hne hbot hj) m).mp hm)
    (fun x hx => (mem_normalizer_iff.mp (J_le_normalizer_X h i hj) x).mp hx) hy

theorem w_mem_normalizer_Mhat (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐰[i] ∈ normalizer ((𝐌₀[i] ⊔ 𝐌ʷ[i, i] : Subgroup G) : Set G) := by
  rw [Mhat_eq h i hne hbot]
  exact mem_normalizer_of_conj_le fun _ hy => conj_w_mem_MX h i hne hbot hy

theorem Mhat_sup_t (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : (𝐌₀[i] ⊔ 𝐌ʷ[i, i]) ⊔ zpowers t = 𝐏₁[i] := by
  refine le_antisymm (sup_le (Mhat_le_P₁ h i hne hbot)
    (zpowers_le.mpr (E_le_P₁ h i hne hbot (t_mem_E h i)))) fun p hp => ?_
  rw [← SetLike.mem_coe, ← Mhat_mul_E h i hne hbot] at hp
  obtain ⟨m, hm, e, he, rfl⟩ := hp
  refine mul_mem (mem_sup_left hm) ?_
  rcases mem_X_or_of_mem_E h i he with hx | hx
  · exact mem_sup_left ((Mhat_inf_E h i hne hbot).ge hx).1
  · rw [show e = t⁻¹ * (t * e) by group]
    exact mul_mem (mem_sup_right (inv_mem (mem_zpowers t)))
      (mem_sup_left ((Mhat_inf_E h i hne hbot).ge hx).1)

theorem Mhat_inf_t (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : (𝐌₀[i] ⊔ 𝐌ʷ[i, i]) ⊓ zpowers t = ⊥ := by
  have hle : (𝐌₀[i] ⊔ 𝐌ʷ[i, i]) ⊓ zpowers t ≤ 𝐗[i] ⊓ zpowers t := fun _ hy =>
    ⟨(Mhat_inf_E h i hne hbot).le ⟨hy.1, zpowers_le.mpr (t_mem_E h i) hy.2⟩, hy.2⟩
  exact le_bot_iff.mp (hle.trans (X_sup_t h i).1.le)

theorem P₁_inf_C (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐏₁[i] ⊓ 𝐂 = 𝐁[i] := by
  refine le_antisymm (fun c hc => ?_)
    ((E_inf_C h i).ge.trans (inf_le_inf_right _ (E_le_P₁ h i hne hbot)))
  obtain ⟨hcP, hcC⟩ := mem_inf.mp hc
  have hcD : c ∈ 𝐃𝐧[i] := P₁_le i hcP
  have hcN : c ∈ 𝐍[i] := by
    have h1 : c ∈ normalizer (((𝐃[i] ⊓ 𝐂 : Subgroup G) : Subgroup G) : Set G) :=
      mem_normalizer_of_conj_le fun y hy =>
        mem_inf.mpr ⟨(mem_normalizer_iff.mp hcD y).mp hy.1,
          mul_mem (mul_mem hcC hy.2) (inv_mem hcC)⟩
    rwa [h.D_inf_C i] at h1
  exact (E_inf_C h i).le ⟨(P₁_inf_N h i hne hbot).le ⟨hcP, hcN⟩, hcC⟩

theorem Mhat_inf_C (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : (𝐌₀[i] ⊔ 𝐌ʷ[i, i]) ⊓ 𝐂 = 𝐀[i] := by
  refine le_antisymm (fun c hc => ?_) (le_inf ?_ (A_le_C h i))
  · obtain ⟨hcM, hcC⟩ := mem_inf.mp hc
    have hcB : c ∈ 𝐁[i] := (P₁_inf_C h i hne hbot).le ⟨Mhat_le_P₁ h i hne hbot hcM, hcC⟩
    have hcX : c ∈ 𝐗[i] := (Mhat_inf_E h i hne hbot).le ⟨hcM, ((E_inf_C h i).ge hcB).1⟩
    have htA : t ∈ normalizer (𝐀[i] : Set G) := mem_normalizer_of_conj_le fun a ha => by
      rw [← mem_centralizer_singleton_iff.mp (A_le_C h i ha), mul_inv_cancel_right]
      exact ha
    rcases mem_or_mul_mem (t_mul_t h) htA ((sup_comm (zpowers t) 𝐀[i]).le hcB) with hA | hA
    · exact hA
    · exfalso
      apply t_not_mem_X h i
      have := mul_mem (L_le_X h i (mem_sup_right hA)) (inv_mem hcX)
      rwa [mul_inv_cancel_right] at this
  · rw [Mhat_eq h i hne hbot]
    exact fun a ha => mem_sup_right (L_le_X h i (mem_sup_right ha))

theorem X_inf_centralizer_le (h : FCHyp L K n φ t) (i : Axis) :
    𝐗[i] ⊓ centralizer (𝐉[i] : Set G) ≤ 𝐅 := by
  intro x hx
  obtain ⟨hxX, hxJ⟩ := mem_inf.mp hx
  rw [← SetLike.mem_coe, ← F_mul_Fw' h i] at hxX
  obtain ⟨f, hf, f', hf', rfl⟩ := hxX
  rw [SetLike.mem_coe, mem_map_conj_inv] at hf'
  have hfg : f' = 𝐰[i]⁻¹ * (𝐰[i] * f' * 𝐰[i]⁻¹) * 𝐰[i] := by group
  have hgW : 𝐰[i] * f' * 𝐰[i]⁻¹ ∈ 𝐖[i] ⊔ 𝐖[i.swap] := by
    rw [← F_eq_W_sup_W h i]
    exact hf'
  obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_of_commute fun x hx y hy =>
    F_comm h (W_le_F _ hx) (W_le_F _ hy)).mp hgW
  rw [← hab] at hfg hf'
  have hbJ : b ∈ centralizer (𝐉[i] : Set G) := by
    refine mem_centralizer_iff.mpr fun j' hj' => ?_
    have hj'0 : j' ∈ 𝐉 := axisTorus_le_J0 i hj'
    have hj : 𝐰[i]⁻¹ * j' * 𝐰[i] ∈ 𝐉[i] := by
      have := conj_w_mem_Ji i hj'
      rw [w_inv] at this ⊢
      exact this
    have hjx := mem_centralizer_iff.mp hxJ _ hj
    have e1 : f⁻¹ * ((𝐰[i]⁻¹ * j' * 𝐰[i]) * f * (𝐰[i]⁻¹ * j' * 𝐰[i])⁻¹) =
        𝐰[i]⁻¹ * ((a * b) * j' * (a * b)⁻¹ * j'⁻¹) * 𝐰[i] := by
      calc f⁻¹ * ((𝐰[i]⁻¹ * j' * 𝐰[i]) * f * (𝐰[i]⁻¹ * j' * 𝐰[i])⁻¹)
          = f⁻¹ * ((𝐰[i]⁻¹ * j' * 𝐰[i]) * (f * f')) * (𝐰[i]⁻¹ * j' * 𝐰[i])⁻¹ *
              ((𝐰[i]⁻¹ * j' * 𝐰[i]) * f'⁻¹ * (𝐰[i]⁻¹ * j' * 𝐰[i])⁻¹) := by group
        _ = f⁻¹ * ((f * f') * (𝐰[i]⁻¹ * j' * 𝐰[i])) * (𝐰[i]⁻¹ * j' * 𝐰[i])⁻¹ *
              ((𝐰[i]⁻¹ * j' * 𝐰[i]) * f'⁻¹ * (𝐰[i]⁻¹ * j' * 𝐰[i])⁻¹) := by rw [hjx]
        _ = 𝐰[i]⁻¹ * ((a * b) * j' * (a * b)⁻¹ * j'⁻¹) * 𝐰[i] := by rw [hfg]; group
    have hcF : (a * b) * j' * (a * b)⁻¹ * j'⁻¹ ∈ 𝐅 := by
      have h1 := conj_torus_mem_F h (inv_mem hj'0) (inv_mem hf')
      rw [inv_inv] at h1
      have h2 := mul_mem hf' h1
      rwa [show (a * b) * (j' * (a * b)⁻¹ * j'⁻¹) = (a * b) * j' * (a * b)⁻¹ * j'⁻¹ by group]
        at h2
    have hcw : (a * b) * j' * (a * b)⁻¹ * j'⁻¹ ∈ 𝐅ʷ[i] := by
      rw [mem_map_conj_inv]
      have h1 : 𝐰[i]⁻¹ * ((a * b) * j' * (a * b)⁻¹ * j'⁻¹) * 𝐰[i] ∈ 𝐅 := by
        rw [← e1]
        refine mul_mem (inv_mem hf) ?_
        simpa using conj_torus_mem_F h (inv_mem (axisTorus_le_J0 i hj)) hf
      rw [w_inv] at h1 ⊢
      exact h1
    have hcW : (a * b) * j' * (a * b)⁻¹ * j'⁻¹ ∈ 𝐖[i] := (F_inf_Fw h i).le ⟨hcF, hcw⟩
    have hdW : b * j' * b⁻¹ * j'⁻¹ ∈ 𝐖[i.swap] := by
      have h1 := conj_torus_mem_W h i.swap (inv_mem hj'0) (inv_mem hb)
      rw [inv_inv] at h1
      have h2 := mul_mem hb h1
      rwa [show b * (j' * b⁻¹ * j'⁻¹) = b * j' * b⁻¹ * j'⁻¹ by group] at h2
    have haj : j' * a = a * j' := mem_centralizer_iff.mp (mem_inf.mp ha).2 j' hj'
    have ea : j' * a⁻¹ * j'⁻¹ = a⁻¹ := by
      calc j' * a⁻¹ * j'⁻¹ = a⁻¹ * (a * j') * a⁻¹ * j'⁻¹ := by group
        _ = a⁻¹ * (j' * a) * a⁻¹ * j'⁻¹ := by rw [haj]
        _ = a⁻¹ := by group
    have had : a * (b * j' * b⁻¹ * j'⁻¹) = (b * j' * b⁻¹ * j'⁻¹) * a :=
      F_comm h (W_le_F _ ha) (W_le_F _ hdW)
    have hcd : (a * b) * j' * (a * b)⁻¹ * j'⁻¹ = b * j' * b⁻¹ * j'⁻¹ := by
      calc (a * b) * j' * (a * b)⁻¹ * j'⁻¹ =
          a * (b * j' * b⁻¹ * j'⁻¹) * (j' * a⁻¹ * j'⁻¹) := by group
        _ = b * j' * b⁻¹ * j'⁻¹ := by rw [ea, had, mul_inv_cancel_right]
    have hd1 : b * j' * b⁻¹ * j'⁻¹ = 1 := by
      have h1 : b * j' * b⁻¹ * j'⁻¹ ∈ 𝐖[i] ⊓ 𝐖[i.swap] := ⟨hcd ▸ hcW, hdW⟩
      rwa [W_inf_W_swap_eq h i, mem_bot] at h1
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hd1)).symm
  have hb1 : b = 1 := by
    have h1 : b ∈ 𝐖[i.swap] ⊓ centralizer (𝐉[i] : Set G) := ⟨hb, hbJ⟩
    rwa [W_swap_inf_centralizer h i, mem_bot] at h1
  rw [hb1, mul_one] at hfg
  have hf'W : f' ∈ 𝐖[i] := by
    have h1 := conj_w_mem_W h i ha
    rw [hfg]
    rw [w_inv] at h1 ⊢
    exact h1
  exact mul_mem hf (W_le_F i hf'W)

theorem Mhat_inf_centralizer_le (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    (𝐌₀[i] ⊔ 𝐌ʷ[i, i]) ⊓ centralizer (𝐉[i] : Set G) ≤ 𝐌₀[i] := by
  intro y hy
  obtain ⟨hyM, hyJ⟩ := mem_inf.mp hy
  rw [Mhat_eq h i hne hbot, ← SetLike.mem_coe, ← M_mul_X h i hne hbot] at hyM
  obtain ⟨m, hm, x, hx, rfl⟩ := hyM
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_V_mul_W h i hne hbot hm
  have hbx : b * x ∈ 𝐗[i] ⊓ centralizer (𝐉[i] : Set G) := by
    refine mem_inf.mpr ⟨mul_mem (mem_sup_left (W_le_F _ hb)) hx, ?_⟩
    have := mul_mem (inv_mem (mem_inf.mp ha).2) hyJ
    rwa [show a⁻¹ * (a * b * x) = b * x by group] at this
  have := mul_mem (mem_inf.mp ha).1 (F_le_M h i hne hbot (X_inf_centralizer_le h i hbx))
  rwa [← mul_assoc] at this

theorem V_le_Mw (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐕[i, i] ≤ 𝐌ʷ[i, i] := by
  intro v hv
  rw [mem_map_conj_inv]
  refine Mhat_inf_centralizer_le h i hne hbot (mem_inf.mpr
    ⟨(mem_normalizer_iff.mp (w_mem_normalizer_Mhat h i hne hbot) v).mp (mem_sup_left hv.1),
      mem_centralizer_iff.mpr fun j hj => ?_⟩)
  have hj' : 𝐰[i]⁻¹ * j * 𝐰[i] ∈ 𝐉[i] := by
    have := conj_w_mem_Ji i hj
    rw [w_inv] at this ⊢
    exact this
  have hc := mem_centralizer_iff.mp hv.2 _ hj'
  calc j * (𝐰[i] * v * 𝐰[i]⁻¹) = 𝐰[i] * ((𝐰[i]⁻¹ * j * 𝐰[i]) * v) * 𝐰[i]⁻¹ := by group
    _ = 𝐰[i] * (v * (𝐰[i]⁻¹ * j * 𝐰[i])) * 𝐰[i]⁻¹ := by rw [hc]
    _ = 𝐰[i] * v * 𝐰[i]⁻¹ * j := by group

omit [Finite G] [Finite K] in
theorem card_Mw (i k : Axis) : Nat.card 𝐌ʷ[i, k] = Nat.card 𝐌₀[i] :=
  card_map_of_injective (MulAut.conj 𝐰[k]⁻¹).injective

theorem card_M_mul_Mw (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    Nat.card ↥(((𝐌₀[i] : Subgroup G) : Set G) * ((𝐌ʷ[i, i] : Subgroup G) : Set G)) =
      Nat.card K ^ 7 := by
  rw [M_mul_Mw h i hne hbot, SetLike.coe_sort_coe]
  exact card_Mhat h i hne hbot

theorem card_M_inf_Mw (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    Nat.card (𝐌₀[i] ⊓ 𝐌ʷ[i, i] : Subgroup G) = Nat.card K ^ 3 := by
  have h1 := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf 𝐌₀[i] 𝐌ʷ[i, i]
  rw [card_M_mul_Mw h i hne hbot, card_Mw, card_M h i hne hbot] at h1
  have hq : 0 < Nat.card K ^ 7 := pow_pos Nat.card_pos 7
  exact Nat.eq_of_mul_eq_mul_left hq (by rw [h1]; ring)

theorem M_inf_Mw (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐌₀[i] ⊓ 𝐌ʷ[i, i] = 𝐕[i, i] :=
  (eq_of_le_of_card_ge (le_inf inf_le_left (V_le_Mw h i hne hbot))
    (by rw [card_M_inf_Mw h i hne hbot, card_V h i hne hbot])).symm

theorem P₁_le_normalizer_Mhat (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐏₁[i] ≤ normalizer ((𝐌₀[i] ⊔ 𝐌ʷ[i, i] : Subgroup G) : Set G) :=
  (Mhat_sup_t h i hne hbot).symm.le.trans
    (sup_le le_normalizer (zpowers_le.mpr (t_mem_normalizer_Mhat h i hne hbot)))

theorem weylProductConclusion_nontrivial (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    WeylProductConclusion 𝐌₀[i] 𝐌ʷ[i, i] 𝐏₁[i] 𝐄[i] 𝐗[i] 𝐀[i] 𝐕[i, i] 𝐂 𝐉 t 𝐰[i]
      (Nat.card K) 7 :=
  ⟨M_mul_Mw h i hne hbot, Mhat_le_P₁ h i hne hbot, M_inf_Mw h i hne hbot,
    Mhat_mul_E h i hne hbot, Mhat_inf_E h i hne hbot, card_Mhat h i hne hbot,
    ⟨P₁_le_normalizer_Mhat h i hne hbot, Mhat_sup_t h i hne hbot, Mhat_inf_t h i hne hbot⟩,
    Mhat_inf_C h i hne hbot, J_le_normalizer_Mhat h i hne hbot, t_mem_normalizer_Mhat h i hne hbot,
    w_mem_normalizer_Mhat h i hne hbot⟩

end SixF

end CFSG.LocalAnalysis.SymplecticFourStandard
