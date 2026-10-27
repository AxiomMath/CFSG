module

public import CFSG.LocalAnalysis.SteinbergSFOneAxisHeisenberg

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace OneAxisRadicalStructure

open Subgroup GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.LocalAnalysis.SteinbergCD
open scoped commutatorElement

section General

variable {G : Type*} [Group G]

theorem commutator_le_closure_sq (H : Subgroup G) :
    ⁅H, H⁆ ≤ closure {x : G | ∃ y ∈ H, x = y * y} := by
  rw [commutator_le]
  intro a ha b hb
  have e : ⁅a, b⁆ = (a * a) * ((a⁻¹ * b) * (a⁻¹ * b)) * (b⁻¹ * b⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (mul_mem (subset_closure ⟨a, ha, rfl⟩)
    (subset_closure ⟨a⁻¹ * b, mul_mem (inv_mem ha) hb, rfl⟩))
    (subset_closure ⟨b⁻¹, inv_mem hb, rfl⟩)

theorem mem_upperCentralSeries_two_iff {H : Subgroup G} {x : G} :
    x ∈ (Subgroup.upperCentralSeries H 2).map H.subtype ↔
      x ∈ H ∧ ∀ y ∈ H, x * y * x⁻¹ * y⁻¹ ∈ (center H).map H.subtype := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, fun y hy => ?_⟩
    have h1 := (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).mp hz ⟨y, hy⟩
    rw [Subgroup.upperCentralSeries_one] at h1
    exact ⟨_, h1, by simp [commutatorElement_def]⟩
  · rintro ⟨hx, h⟩
    refine ⟨⟨x, hx⟩, (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).mpr fun y => ?_, rfl⟩
    rw [Subgroup.upperCentralSeries_one]
    obtain ⟨z, hz, hzy⟩ := h y y.2
    have e : ⁅(⟨x, hx⟩ : H), y⁆ = z := Subtype.ext (by simp [commutatorElement_def, ← hzy])
    rw [e]
    exact hz

end General

section Coord

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {n : ℕ}
  {φ : L ≃* antiSp K} {t : G}

theorem coord_zero_eq (X Y Z : K) :
    coord φ t ((0, X, Y, Z) : QGSpace K) = ((φ.symm (uElt Y X (Z + X * Y) 0) : L) : G) := by
  simp [coord, aElt]

theorem coord_one_eq (X Y Z : K) :
    coord φ t ((1, X, Y, Z) : QGSpace K) = t * coord φ t ((0, X, Y, Z) : QGSpace K) := by
  simp [coord, ZMod.val_one]

theorem conj_coord_add (hS : TwoCoreSetup L K n t) {g : G} {e₁ e₂ f₁ f₂ : QGSpace K}
    (h₁ : g * coord φ t e₁ * g⁻¹ = coord φ t f₁) (h₂ : g * coord φ t e₂ * g⁻¹ = coord φ t f₂) :
    g * coord φ t (e₁ + e₂) * g⁻¹ = coord φ t (f₁ + f₂) := by
  have hc : ∀ x ∈ L, t * x = x * t := fun _ hx => hS.comm hx
  rw [coord_add φ hS.t_mul_t hc, coord_add φ hS.t_mul_t hc, ← h₁, ← h₂]
  group

theorem conj_coord_center (hS : TwoCoreSetup L K n t) {g : G} {x y d : K}
    (h : HAct φ t g x y d) (c : K) :
    g * coord φ t ((0, 0, 0, c) : QGSpace K) * g⁻¹ = coord φ t ((0, 0, 0, c) : QGSpace K) := by
  have e : ((0, 0, 0, c) : QGSpace K) =
      qgPoint ![0, c] + qgPoint ![1, c] + qgPoint 0 + qgPoint ![1, 0] := by
    simp only [qgPoint, Prod.mk_add_mk, Prod.mk.injEq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.zero_apply]
    refine ⟨by decide, by grind, by grind, by grind⟩
  rw [e, conj_coord_add hS (conj_coord_add hS (conj_coord_add hS (h _) (h _)) (h _)) (h _)]
  congr 1
  simp only [qgPoint, Prod.mk_add_mk, Prod.mk.injEq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.zero_apply]
  refine ⟨by decide, by grind, by grind, by grind⟩

theorem conj_coord_zero (hS : TwoCoreSetup L K n t) {g : G} {x y d : K}
    (h : HAct φ t g x y d) (X Y Z : K) :
    g * coord φ t ((0, X, Y, Z) : QGSpace K) * g⁻¹ =
      coord φ t ((0, X + d * Y, Y, Z + x * X + (y + d * x) * Y + d * Y ^ 2) : QGSpace K) := by
  have e : ((0, X, Y, Z) : QGSpace K) =
      qgPoint ![X, Y] + qgPoint 0 + ((0, 0, 0, Z + X * Y) : QGSpace K) := by
    simp only [qgPoint, Prod.mk_add_mk, Prod.mk.injEq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.zero_apply]
    refine ⟨by decide, by grind, by grind, by grind⟩
  rw [e, conj_coord_add hS (conj_coord_add hS (h _) (h _)) (conj_coord_center hS h _)]
  congr 1
  simp only [qgPoint, Prod.mk_add_mk, Prod.mk.injEq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.zero_apply]
  refine ⟨by decide, by grind, by grind, by grind⟩

theorem conj_coord_one (hS : TwoCoreSetup L K n t) {g : G} {x y d : K}
    (h : HAct φ t g x y d) (X Y Z : K) :
    g * coord φ t ((1, X, Y, Z) : QGSpace K) * g⁻¹ =
      coord φ t ((1, X + d * Y + y, Y + x, Z + x * X + (y + d * x) * Y + d * Y ^ 2 + x * y) :
        QGSpace K) := by
  have e : ((1, X, Y, Z) : QGSpace K) = qgPoint ![X, Y] + ((0, 0, 0, Z + X * Y) : QGSpace K) := by
    simp only [qgPoint, Prod.mk_add_mk, Prod.mk.injEq, Matrix.cons_val_zero, Matrix.cons_val_one]
    refine ⟨by decide, by grind, by grind, by grind⟩
  rw [e, conj_coord_add hS (h _) (conj_coord_center hS h _)]
  congr 1
  simp only [qgPoint, Prod.mk_add_mk, Prod.mk.injEq, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨by decide, by grind, by grind, by grind⟩

theorem coord_zero_mem_A (X Y Z : K) :
    coord φ t ((0, X, Y, Z) : QGSpace K) ∈ pull φ (rootA K Axis.two) := by
  rw [coord_zero_eq]
  exact symm_mem_pull.mpr ⟨Y, X, Z + X * Y, rfl⟩

theorem exists_coord_zero_eq {a : G} (ha : a ∈ pull φ (rootA K Axis.two)) :
    ∃ X Y Z : K, coord φ t ((0, X, Y, Z) : QGSpace K) = a := by
  obtain ⟨x, y, z, h⟩ := exists_symm_aElt_eq φ ha
  exact ⟨x, y, z, by rw [← h]; simp [coord]⟩

theorem coord_zero_mem_center_iff {X Y Z : K} :
    coord φ t ((0, X, Y, Z) : QGSpace K) ∈ pull φ (antiUnipotentCenter K) ↔ Y = 0 := by
  rw [coord_zero_eq, symm_mem_pull]
  constructor
  · rintro ⟨b, c, h⟩
    exact (uElt_inj h).1
  · rintro rfl
    exact ⟨X, Z + X * 0, rfl⟩

theorem coord_zero_mem_U₁_iff {X Y Z : K} :
    coord φ t ((0, X, Y, Z) : QGSpace K) ∈ pull φ (rootU K Axis.one) ↔ Y = 0 ∧ Z = 0 := by
  rw [coord_zero_eq, symm_mem_pull]
  constructor
  · rintro ⟨b, h⟩
    obtain ⟨hY, -, hZ, -⟩ := uElt_inj h
    refine ⟨hY, ?_⟩
    rw [hY, mul_zero, add_zero] at hZ
    exact hZ
  · rintro ⟨rfl, rfl⟩
    exact ⟨X, by rw [mul_zero, add_zero]⟩

theorem coord_zero_mem_U₂_iff {X Y Z : K} :
    coord φ t ((0, X, Y, Z) : QGSpace K) ∈ pull φ (rootU K Axis.two) ↔ X = 0 ∧ Y = 0 := by
  rw [coord_zero_eq, symm_mem_pull]
  constructor
  · rintro ⟨c, h⟩
    obtain ⟨hY, hX, -, -⟩ := uElt_inj h
    exact ⟨hX, hY⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨Z + 0 * 0, rfl⟩

theorem coord_mul_conj_inv (hS : TwoCoreSetup L K n t) {g : G} {e f : QGSpace K}
    (h : g * coord φ t e * g⁻¹ = coord φ t f) :
    coord φ t e * g * (coord φ t e)⁻¹ * g⁻¹ = coord φ t (e + f) := by
  have hc : ∀ x ∈ L, t * x = x * t := fun _ hx => hS.comm hx
  have hinv : (coord φ t f)⁻¹ = coord φ t f :=
    inv_eq_of_mul_eq_one_right (coord_mul_self φ hS.t_mul_t hc f)
  rw [coord_add φ hS.t_mul_t hc, ← hinv, ← h]
  group

theorem commutator_t_eq (hS : TwoCoreSetup L K n t) {g : G} {x y d : K}
    (h : HAct φ t g x y d) : g * t * g⁻¹ * t⁻¹ = ((φ.symm (uElt x y 0 0) : L) : G) := by
  have e := (hAct_iff.mp h) 0 0
  rw [uElt_zero_eq_one, map_one, OneMemClass.coe_one, mul_one, zero_add, mul_zero, add_zero,
    zero_add] at e
  rw [e, hS.comm (φ.symm _).2, mul_inv_cancel_right]

end Coord

section HActs

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {φ : L ≃* antiSp K} {t : G}

theorem hAct_one : HAct φ t (1 : G) 0 0 0 := by
  intro v
  rw [one_mul, inv_one, mul_one]
  congr 2
  ext i
  fin_cases i <;> simp

theorem hAct_inv {g : G} {x y d : K} (h : HAct φ t g x y d) :
    HAct φ t g⁻¹ x (y + d * x) d := by
  intro v
  have e := h ![v 0 + d * v 1 + (y + d * x), v 1 + x]
  have hv : (![(![v 0 + d * v 1 + (y + d * x), v 1 + x] : Fin 2 → K) 0 +
      d * (![v 0 + d * v 1 + (y + d * x), v 1 + x] : Fin 2 → K) 1 + y,
      (![v 0 + d * v 1 + (y + d * x), v 1 + x] : Fin 2 → K) 1 + x] : Fin 2 → K) = v := by
    ext i
    fin_cases i <;> simp <;> grind
  rw [hv] at e
  rw [inv_inv, ← e]
  group

theorem hAct_conj {g h : G} {x y d x' y' d' : K} (hg : HAct φ t g x y d)
    (hh : HAct φ t h x' y' d') : HAct φ t (g * h * g⁻¹) x' (y' + d * x' + d' * x) d' :=
  ((hg.mul hh).mul (hAct_inv hg)).congr (by grind) (by grind) (by grind)

theorem hAct_comm {g h : G} {x y d x' y' d' : K} (hg : HAct φ t g x y d)
    (hh : HAct φ t h x' y' d') : HAct φ t (g * h * g⁻¹ * h⁻¹) 0 (d * x' + d' * x) 0 :=
  (((hg.mul hh).mul (hAct_inv hg)).mul (hAct_inv hh)).congr (by grind) (by grind) (by grind)

end HActs

section Main

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {n : ℕ}
  {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)
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
local notation "𝐑" => (pull φ (antiUnipotent K) ⊔ TG ⊔ (CFSG.pCore 2 (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.one) : Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.one) : Subgroup G) : Set G)).subtype : Subgroup G)
set_option quotPrecheck false in
local notation "𝐒" => (pull φ (antiUnipotent K) ⊔ TG ⊔ (CFSG.pCore 2 (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.two) : Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.two) : Subgroup G) : Set G)).subtype : Subgroup G)

theorem t_mem_Q (hh : HeisHyp L K n φ TG t) : t ∈ 𝐐 :=
  hh.hyp.B_le_Q Axis.two (mem_sup_left (mem_zpowers t))

theorem B₁_le_D₁ (hh : HeisHyp L K n φ TG t) : 𝐁₁ ≤ 𝐃₁ := fun _ hb => (hh.inf₁.ge hb).1

theorem t_mem_D₁ (hh : HeisHyp L K n φ TG t) : t ∈ 𝐃₁ :=
  B₁_le_D₁ hh (mem_sup_left (mem_zpowers t))

theorem t_mem_D₂ [Finite K] (hh : HeisHyp L K n φ TG t) : t ∈ 𝐃₂ :=
  hh.sec.B_le_D SecondHyp.t_mem_B

theorem exists_D₁_not_comm (hh : HeisHyp L K n φ TG t) : ∃ d ∈ 𝐃₁, d * t ≠ t * d := by
  obtain ⟨d, hd, hdu⟩ := hh.surj₁ _ (coordG_mem φ Axis.one 1)
  refine ⟨d, hd, fun h => ?_⟩
  have h1 : d⁻¹ * t * d = t := by rw [mul_assoc, ← h, inv_mul_cancel_left]
  rw [h1, inv_mul_cancel] at hdu
  exact one_ne_zero (coordG_injective φ Axis.one (hdu.symm.trans (coordG_zero φ Axis.one).symm))

theorem mem_B₂_of_hAct [Finite K] (hh : HeisHyp L K n φ TG t) {g : G} (hg : g ∈ 𝐍₂)
    (h : HAct φ t g 0 0 0) : g ∈ 𝐁₂ := by
  simpa using inv_mul_mem_B hh.sec hg (one_mem _) h hAct_one

theorem mem_Q_of_comm [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {s : G} (hs : s ∈ 𝐒)
    (hst : s * t = t * s) : s ∈ 𝐐 := by
  obtain ⟨x, y, d, h⟩ := hh.exists_hAct_of_mem_S hs
  have e := h 0
  rw [qgPoint_zero, coord_qgT, hst, mul_inv_cancel_right] at e
  have e' : coord φ t (qgPoint ![(0 : Fin 2 → K) 0 + d * (0 : Fin 2 → K) 1 + y,
      (0 : Fin 2 → K) 1 + x]) = coord φ t (qgPoint 0) := by
    rw [qgPoint_zero, coord_qgT]
    exact e.symm
  have hw := coord_qgPoint_injective hh.sec.two e'
  have hy := congrFun hw 0
  have hx := congrFun hw 1
  simp at hx hy
  exact (hh.mem_Q_iff hs h).mpr ⟨hx, hy⟩

theorem comm_U₂ [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {s : G} (hs : s ∈ 𝐒) {u : G}
    (hu : u ∈ 𝐔₂) : s * u = u * s := by
  obtain ⟨x, y, d, h⟩ := hh.exists_hAct_of_mem_S hs
  obtain ⟨X, Y, Z, rfl⟩ := exists_coord_zero_eq (t := t) (pull_mono φ rootU₂_le_radA2 hu)
  obtain ⟨rfl, rfl⟩ := coord_zero_mem_U₂_iff.mp hu
  have e := conj_coord_center hh.sec.two h Z
  calc s * coord φ t ((0, 0, 0, Z) : QGSpace K)
      = (s * coord φ t ((0, 0, 0, Z) : QGSpace K) * s⁻¹) * s := by group
    _ = _ := by rw [e]

theorem comm_ZP [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {s : G} {y d : K}
    (h : HAct φ t s 0 y d) {z : G} (hz : z ∈ 𝐙) : s * z = z * s := by
  obtain ⟨X, Y, Z, rfl⟩ := exists_coord_zero_eq (t := t)
    (pull_mono φ (center_le_rootA Axis.two) hz)
  obtain rfl := coord_zero_mem_center_iff.mp hz
  have e := conj_coord_zero hh.sec.two h X 0 Z
  have e2 : ((0, X + d * 0, 0, Z + 0 * X + (y + d * 0) * 0 + d * 0 ^ 2) : QGSpace K) =
      (0, X, 0, Z) := by simp
  rw [e2] at e
  calc s * coord φ t ((0, X, 0, Z) : QGSpace K)
      = (s * coord φ t ((0, X, 0, Z) : QGSpace K) * s⁻¹) * s := by group
    _ = _ := by rw [e]

theorem comm_ZP_of_mem_R [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {r : G} (hr : r ∈ 𝐑)
    {z : G} (hz : z ∈ 𝐙) : r * z = z * r := by
  obtain ⟨x, y, d, h⟩ := hh.exists_hAct_of_mem_S (hh.R_le_S hr)
  obtain rfl := (hh.mem_R_iff (hh.R_le_S hr) h).mp hr
  exact comm_ZP hh h hz

theorem sq_mem_A₂ [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {s : G} (hs : s ∈ 𝐒)
    (hss : s * s ∈ 𝐁₂) : s * s ∈ 𝐀₂ := by
  have hS := hh.sec.two
  rcases (mem_zpowers_sup_iff hS.t_mul_t (TwoCoreSetup.comm_pull φ hS)).mp hss with h | h
  · exact h
  · exfalso
    obtain ⟨X, Y, Z, hXYZ⟩ := exists_coord_zero_eq (t := t) h
    have hsq : s * s = coord φ t ((1, X, Y, Z) : QGSpace K) := by
      rw [coord_one_eq, hXYZ, ← mul_assoc, hS.t_mul_t, one_mul]
    obtain ⟨g, hg, hgh⟩ := exists_D_hAct hh.sec Y X
    have hgS : g ∈ 𝐒 := mem_sup_right hg
    have hs'S : g * s * g⁻¹ ∈ 𝐒 := mul_mem (mul_mem hgS hs) (inv_mem hgS)
    set Z' := Z + Y * X + (X + 0 * Y) * Y + 0 * Y ^ 2 + Y * X
    have hu : coord φ t ((0, 0, 0, Z') : QGSpace K) ∈ 𝐔₂ := coord_zero_mem_U₂_iff.mpr ⟨rfl, rfl⟩
    have hsq' : (g * s * g⁻¹) * (g * s * g⁻¹) = t * coord φ t ((0, 0, 0, Z') : QGSpace K) := by
      have e1 : (g * s * g⁻¹) * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
      rw [e1, hsq, conj_coord_one hS hgh, coord_one_eq]
      congr 2
      simp only [Prod.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | grind
    have hcu := comm_U₂ hh hs'S hu
    have hct : (g * s * g⁻¹) * t = t * (g * s * g⁻¹) := by
      have e2 : (g * s * g⁻¹) * ((g * s * g⁻¹) * (g * s * g⁻¹)) =
          ((g * s * g⁻¹) * (g * s * g⁻¹)) * (g * s * g⁻¹) := by group
      rw [hsq'] at e2
      have e3 : (g * s * g⁻¹) * t * coord φ t ((0, 0, 0, Z') : QGSpace K) =
          t * (g * s * g⁻¹) * coord φ t ((0, 0, 0, Z') : QGSpace K) := by
        calc (g * s * g⁻¹) * t * coord φ t ((0, 0, 0, Z') : QGSpace K)
            = (g * s * g⁻¹) * (t * coord φ t ((0, 0, 0, Z') : QGSpace K)) := by group
          _ = t * coord φ t ((0, 0, 0, Z') : QGSpace K) * (g * s * g⁻¹) := e2
          _ = t * ((g * s * g⁻¹) * coord φ t ((0, 0, 0, Z') : QGSpace K)) := by
              rw [mul_assoc, ← hcu]
          _ = _ := by group
      exact mul_right_cancel e3
    have hs'Q := mem_Q_of_comm hh hs'S hct
    have hsqZ : (g * s * g⁻¹) * (g * s * g⁻¹) ∈ 𝐙 := by
      rw [← hh.hyp.setup.closure_sq_eq hh.hyp.T_eq]
      exact subset_closure ⟨_, hs'Q, rfl⟩
    rw [hsq'] at hsqZ
    have htL : t ∈ L := by
      have := mul_mem (pull_le φ _ hsqZ) (inv_mem (pull_le φ _ hu))
      rwa [mul_inv_cancel_right] at this
    exact hS.t_not_mem htL

theorem sq_mem_ZP_of_mem_R [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {r : G}
    (hr : r ∈ 𝐑) : r * r ∈ 𝐙 := by
  have hS := hh.sec.two
  have hrS := hh.R_le_S hr
  obtain ⟨x, y, d, h⟩ := hh.exists_hAct_of_mem_S hrS
  obtain rfl := (hh.mem_R_iff hrS h).mp hr
  have hrN := hh.S_le_N₂ hrS
  have hsqB : r * r ∈ 𝐁₂ := mem_B₂_of_hAct hh (mul_mem hrN hrN)
    ((h.mul h).congr (by grind) (by grind) (by grind))
  obtain ⟨X, Y, Z, hXYZ⟩ := exists_coord_zero_eq (t := t) (sq_mem_A₂ hh hrS hsqB)
  rw [← hXYZ, coord_zero_mem_center_iff]
  have hc : r * coord φ t ((0, X, Y, Z) : QGSpace K) * r⁻¹ = coord φ t ((0, X, Y, Z) : QGSpace K) :=
    by rw [hXYZ]; group
  rw [conj_coord_zero hS h] at hc
  have e := coord_injective φ hS.t_mul_t (fun _ hx => hS.comm hx) hS.t_not_mem hc
  simp only [Prod.mk.injEq] at e
  obtain ⟨-, h1, -, h2⟩ := e
  by_contra hY
  have hd : d = 0 := by
    have : d * Y = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_right hY
  subst hd
  have hy : y = 0 := by
    have : y * Y = 0 := by linear_combination h2
    exact (mul_eq_zero.mp this).resolve_right hY
  subst hy
  have h11 : r * r = 1 := hh.hyp.mul_self_of_mem_B Axis.two (mem_B₂_of_hAct hh hrN h)
  rw [h11] at hXYZ
  have := (coord_eq_one_iff φ hS.t_not_mem).mp hXYZ
  exact hY (congrArg (fun e : QGSpace K => e.2.2.1) this)

theorem two_lt_card (hh : HeisHyp L K n φ TG t) : 2 < Nat.card K := by
  rw [hh.sec.two.card_K]
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hh.sec.two.two_le

theorem commutator_P (hh : HeisHyp L K n φ TG t) : ⁅𝐏, 𝐏⁆ = 𝐙 := by
  rw [Setup.pull_eq_map, Setup.pull_eq_map, ← map_commutator,
    commutator_antiUnipotent_eq (two_lt_card hh)]

theorem center_R_le [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) :
    (center 𝐑).map 𝐑.subtype ≤ 𝐙 := by
  intro z hz
  obtain ⟨hzR, hzc⟩ := mem_center_map_iff.mp hz
  have htR : t ∈ 𝐑 := mem_sup_left (t_mem_Q hh)
  have hzQ := mem_Q_of_comm hh (hh.R_le_S hzR) (hzc t htR).symm
  have hzZQ : z ∈ (center 𝐐).map 𝐐.subtype :=
    mem_center_map_iff.mpr ⟨hzQ, fun y hy => hzc y (mem_sup_left hy)⟩
  obtain ⟨z₀, hz₀, c, hc, rfl⟩ := hh.hyp.setup.exists_of_mem_ZQ hzZQ
  rw [hh.hyp.T_eq] at hc
  have hc' : c = 1 ∨ c = t := by
    obtain ⟨j, rfl⟩ := hc
    exact zpow_eq_one_or_eq hh.sec.two.t_mul_t j
  rcases hc' with h1 | h1 <;> subst c
  · rw [mul_one]
    exact hz₀
  · exfalso
    obtain ⟨d, hd, hdt⟩ := exists_D₁_not_comm hh
    apply hdt
    have e1 := hzc d (mem_sup_right hd)
    have e2 := comm_ZP_of_mem_R hh (mem_sup_right hd) hz₀
    have e3 : z₀ * (d * t) = z₀ * (t * d) := by
      calc z₀ * (d * t) = d * (z₀ * t) := by rw [← mul_assoc, ← e2, mul_assoc]
        _ = z₀ * t * d := e1
        _ = z₀ * (t * d) := by group
    exact mul_left_cancel e3

theorem part_one [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) :
    ⁅𝐑, 𝐑⁆ = 𝐙 ∧ closure {x : G | ∃ y ∈ 𝐑, x = y * y} = 𝐙 ∧ (center 𝐑).map 𝐑.subtype = 𝐙 := by
  have hsq : closure {x : G | ∃ y ∈ 𝐑, x = y * y} ≤ 𝐙 :=
    (closure_le _).mpr (by rintro _ ⟨y, hy, rfl⟩; exact sq_mem_ZP_of_mem_R hh hy)
  have hPR : 𝐏 ≤ 𝐑 := le_sup_left.trans le_sup_left
  have hZ : 𝐙 ≤ ⁅𝐑, 𝐑⁆ := (commutator_P hh).ge.trans (commutator_mono hPR hPR)
  refine ⟨le_antisymm ((commutator_le_closure_sq _).trans hsq) hZ,
    le_antisymm hsq (hZ.trans (commutator_le_closure_sq _)), le_antisymm (center_R_le hh) ?_⟩
  intro z hz
  exact mem_center_map_iff.mpr ⟨hPR (Setup.ZP_le_PG hz), fun r hr => comm_ZP_of_mem_R hh hr hz⟩

theorem rootC_le_N₁ [Finite G] [Finite K] (hS : TwoCoreSetup L K n t) :
    pull φ (rootC K Axis.one) ≤ 𝐍₁ := by
  intro c hc
  rw [hS.mem_normalizer_zpowers_sup_iff (hS.L_le (pull_le φ _ hc)) (pull_le φ _)]
  obtain ⟨c', hc', rfl⟩ := exists_eq_symm_of_mem_pull hc
  have hst := hS.axisStr Axis.one
  have hN : c' ∈ normalizer (rootA K Axis.one : Set (antiSp K)) := by
    rw [← hst.N_eq]
    exact centralizer_le_normalizer _ hc'
  exact symm_mem_normalizer_pull hN

theorem pull_rootA_le_of_normal [Finite K] (hS : TwoCoreSetup L K n t) (i : Axis)
    {V : Subgroup G} (hVA : V ≤ pull φ (rootA K i))
    (hVn : ∀ c ∈ pull φ (rootC K i), ∀ v ∈ V, c * v * c⁻¹ ∈ V)
    (hVU : ¬ V ≤ pull φ (rootU K i)) : pull φ (rootA K i) ≤ V := by
  set W : Subgroup (antiSp K) := V.comap (L.subtype.comp φ.symm.toMonoidHom) with hW
  have hmem : ∀ w, w ∈ W ↔ ((φ.symm w : L) : G) ∈ V := fun w => Iff.rfl
  have hst := hS.axisStr i
  have hWA : W ≤ rootA K i := fun w hw => symm_mem_pull.mp (hVA ((hmem w).mp hw))
  have hWeq : W = rootA K i := by
    refine hst.normal_eq_A W (hWA.trans hst.A_le_C) (fun g hg w hw => ?_) hWA fun hle => ?_
    · rw [hmem, ← symm_conj_eq]
      exact hVn _ (symm_mem_pull.mpr hg) _ ((hmem w).mp hw)
    · refine hVU fun v hv => ?_
      obtain ⟨a, -, rfl⟩ := exists_eq_symm_of_mem_pull (hVA hv)
      exact symm_mem_pull.mpr (hle ((hmem a).mpr hv))
  intro a ha
  obtain ⟨a', ha', rfl⟩ := exists_eq_symm_of_mem_pull ha
  rw [← hWeq] at ha'
  exact (hmem a').mp ha'

theorem sq_D₁_le_U₁ [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) :
    closure {x : G | ∃ y ∈ 𝐃₁, x = y * y} ≤ 𝐔₁ := by
  have hS := hh.sec.two
  have hVZ : closure {x : G | ∃ y ∈ 𝐃₁, x = y * y} ≤ 𝐙 :=
    (closure_le _).mpr (by rintro _ ⟨y, hy, rfl⟩; exact sq_mem_ZP_of_mem_R hh (mem_sup_right hy))
  by_contra hVU
  have hle := pull_rootA_le_of_normal hS Axis.one
    (hVZ.trans (pull_mono φ (center_le_rootA Axis.one)))
    (fun c hc v hv => Setup.conj_mem_closure_sq (le_normalizer_pCore_map (rootC_le_N₁ hS hc)) hv)
    hVU
  have h1 : ((φ.symm (uElt 0 0 0 1) : L) : G) ∈ 𝐀₁ := symm_mem_pull.mpr ⟨0, 0, 1, rfl⟩
  obtain ⟨b, c, h⟩ := symm_mem_pull.mp (hVZ (hle h1))
  exact one_ne_zero (uElt_inj h).2.2.2

theorem U₁_le_commutator (hh : HeisHyp L K n φ TG t) : 𝐔₁ ≤ ⁅𝐃₁, 𝐃₁⁆ := by
  intro u hu
  obtain ⟨d, hd, rfl⟩ := hh.surj₁ u hu
  have e : t⁻¹ * (d⁻¹ * t * d) = ⁅t⁻¹, d⁻¹⁆ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact commutator_mem_commutator (inv_mem (t_mem_D₁ hh)) (inv_mem hd)

theorem center_D₁ [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) :
    (center 𝐃₁).map 𝐃₁.subtype = 𝐀₁ := by
  have hS := hh.sec.two
  have hA₁D : 𝐀₁ ≤ 𝐃₁ := le_sup_right.trans (B₁_le_D₁ hh)
  have hle : 𝐀₁ ≤ (center 𝐃₁).map 𝐃₁.subtype ⊓ 𝐀₁ := by
    refine pull_rootA_le_of_normal hS Axis.one inf_le_right (fun c hc v hv => ⟨?_, ?_⟩) ?_
    · exact Setup.conj_mem_center (le_normalizer_pCore_map (rootC_le_N₁ hS hc)) hv.1
    · refine hS.conj_mem_A φ Axis.one ?_ hv.2
      rw [hS.centralizer_eq φ Axis.one]
      exact mem_sup_right hc
    · intro hle'
      have hz : ((φ.symm (uElt 0 0 1 0) : L) : G) ∈ 𝐙 := symm_mem_pull.mpr ⟨0, 1, rfl⟩
      have hzA : ((φ.symm (uElt 0 0 1 0) : L) : G) ∈ 𝐀₁ :=
        pull_mono φ (center_le_rootA Axis.one) hz
      obtain ⟨b, h⟩ := symm_mem_pull.mp (hle' ⟨mem_center_map_iff.mpr ⟨hA₁D hzA,
        fun y hy => comm_ZP_of_mem_R hh (mem_sup_right hy) hz⟩, hzA⟩)
      exact one_ne_zero (uElt_inj h).2.2.1
  refine le_antisymm (fun z hz => ?_) (hle.trans inf_le_left)
  obtain ⟨hzD, hzc⟩ := mem_center_map_iff.mp hz
  have hzB := hh.mem_B₁ hzD (hzc t (t_mem_D₁ hh)).symm
  rcases (mem_zpowers_sup_iff hS.t_mul_t (TwoCoreSetup.comm_pull φ hS)).mp hzB with h | h
  · exact h
  · exfalso
    have h1 : t * z ∈ (center 𝐃₁).map 𝐃₁.subtype := (hle h).1
    have h2 : t ∈ (center 𝐃₁).map 𝐃₁.subtype := by
      have := mul_mem h1 (inv_mem hz)
      rwa [mul_inv_cancel_right] at this
    obtain ⟨d, hd, hdt⟩ := exists_D₁_not_comm hh
    exact hdt ((mem_center_map_iff.mp h2).2 d hd)

theorem part_two [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) :
    ⁅𝐃₁, 𝐃₁⁆ = 𝐔₁ ∧ closure {x : G | ∃ y ∈ 𝐃₁, x = y * y} = 𝐔₁ ∧
      (center 𝐃₁).map 𝐃₁.subtype = 𝐀₁ :=
  ⟨le_antisymm ((commutator_le_closure_sq _).trans (sq_D₁_le_U₁ hh)) (U₁_le_commutator hh),
    le_antisymm (sq_D₁_le_U₁ hh) ((U₁_le_commutator hh).trans (commutator_le_closure_sq _)),
    center_D₁ hh⟩

theorem sq_mem_A₂_of_mem_D₂ [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {d : G}
    (hd : d ∈ 𝐃₂) : d * d ∈ 𝐀₂ := by
  have hdS : d ∈ 𝐒 := mem_sup_right hd
  have hdN := hh.S_le_N₂ hdS
  obtain ⟨x, y, h⟩ := hAct_of_mem_D hh.sec hd
  exact sq_mem_A₂ hh hdS (mem_B₂_of_hAct hh (mul_mem hdN hdN)
    ((h.mul h).congr (by grind) (by grind) (by grind)))

theorem A₂_le_commutator [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) :
    𝐀₂ ≤ ⁅𝐃₂, 𝐃₂⁆ := by
  have hpair : ∀ a b : K, ((φ.symm (uElt a b 0 0) : L) : G) ∈ ⁅𝐃₂, 𝐃₂⁆ := by
    intro a b
    obtain ⟨d, hd, h⟩ := exists_D_hAct hh.sec a b
    rw [← commutator_t_eq hh.sec.two h, ← commutatorElement_def]
    exact commutator_mem_commutator hd (t_mem_D₂ hh)
  have hcen : ∀ c : K, ((φ.symm (uElt 0 0 c 0) : L) : G) ∈ ⁅𝐃₂, 𝐃₂⁆ := by
    intro c
    have e : uElt (0 : K) 0 c 0 = uElt c 0 0 0 * uElt 0 1 0 0 * uElt c 1 0 0 := by
      rw [uElt_mul, uElt_mul]
      congr 1 <;> grind
    rw [e, map_mul, map_mul, coe_mul, coe_mul]
    exact mul_mem (mul_mem (hpair _ _) (hpair _ _)) (hpair _ _)
  intro x hx
  obtain ⟨a', ha', rfl⟩ := exists_eq_symm_of_mem_pull hx
  change a' ∈ radA2 K at ha'
  obtain ⟨a, b, c, rfl⟩ := ha'
  have e : uElt a b c 0 = uElt a b 0 0 * uElt 0 0 c 0 := by
    rw [uElt_mul]
    congr 1 <;> ring
  rw [e, map_mul, coe_mul]
  exact mul_mem (hpair a b) (hcen c)

theorem mem_U₂_of_comm_D₂ [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {b : G}
    (hb : b ∈ 𝐁₂) (hc : ∀ d ∈ 𝐃₂, d * b = b * d) : b ∈ 𝐔₂ := by
  have hS := hh.sec.two
  have hinj := coord_injective φ hS.t_mul_t (fun _ hx => hS.comm hx) hS.t_not_mem
  obtain ⟨⟨ε, X, Y, Z⟩, rfl⟩ := exists_coord_eq φ hS.t_mul_t (fun _ hx => hS.comm hx) hb
  obtain ⟨d₁, hd₁, h₁⟩ := exists_D_hAct hh.sec 1 0
  obtain ⟨d₂, hd₂, h₂⟩ := exists_D_hAct hh.sec 0 1
  have hfix : ∀ d ∈ 𝐃₂, d * coord φ t (ε, X, Y, Z) * d⁻¹ = coord φ t (ε, X, Y, Z) :=
    fun d hd => by rw [hc d hd, mul_inv_cancel_right]
  rcases zmod_two_cases ε with rfl | rfl
  · have e1 := hinj ((conj_coord_zero hS h₁ X Y Z).symm.trans (hfix d₁ hd₁))
    have e2 := hinj ((conj_coord_zero hS h₂ X Y Z).symm.trans (hfix d₂ hd₂))
    simp only [Prod.mk.injEq] at e1 e2
    exact coord_zero_mem_U₂_iff.mpr ⟨by linear_combination e1.2.2.2, by
      linear_combination e2.2.2.2⟩
  · have e1 := hinj ((conj_coord_one hS h₁ X Y Z).symm.trans (hfix d₁ hd₁))
    simp only [Prod.mk.injEq] at e1
    exact absurd (by linear_combination e1.2.2.1 : (1 : K) = 0) one_ne_zero

theorem center_D₂ [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) :
    (center 𝐃₂).map 𝐃₂.subtype = 𝐔₂ := by
  have hUD : 𝐔₂ ≤ 𝐃₂ := ((pull_mono φ rootU₂_le_radA2).trans le_sup_right).trans hh.sec.B_le_D
  apply le_antisymm
  · intro z hz
    obtain ⟨hzD, hzc⟩ := mem_center_map_iff.mp hz
    have hzB : z ∈ 𝐁₂ := hh.sec.inf_eq.le
      ⟨hzD, mem_centralizer_singleton_iff.mpr (hzc t (t_mem_D₂ hh)).symm, SecondHyp.D_le_N hzD⟩
    exact mem_U₂_of_comm_D₂ hh hzB hzc
  · intro u hu
    exact mem_center_map_iff.mpr ⟨hUD hu, fun d hd => comm_U₂ hh (mem_sup_right hd) hu⟩

theorem hAct_of_commutator_t [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {x : G}
    (hx : x ∈ 𝐒) (hxt : x * t * x⁻¹ * t⁻¹ ∈ 𝐔₂) : ∃ d : K, HAct φ t x 0 0 d := by
  obtain ⟨a, b, d, h⟩ := hh.exists_hAct_of_mem_S hx
  rw [commutator_t_eq hh.sec.two h] at hxt
  obtain ⟨c, hc⟩ := symm_mem_pull.mp hxt
  obtain ⟨rfl, rfl, -, -⟩ := uElt_inj hc
  exact ⟨d, h⟩

theorem upper_D₂ [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) :
    (Subgroup.upperCentralSeries 𝐃₂ 2).map 𝐃₂.subtype = 𝐀₂ := by
  have hS := hh.sec.two
  have hAD : 𝐀₂ ≤ 𝐃₂ := le_sup_right.trans hh.sec.B_le_D
  have hA : ∀ a ∈ 𝐀₂, ∀ d ∈ 𝐃₂, a * d * a⁻¹ * d⁻¹ ∈ 𝐔₂ := by
    intro a ha d hd
    obtain ⟨x, y, h⟩ := hAct_of_mem_D hh.sec hd
    obtain ⟨X, Y, Z, rfl⟩ := exists_coord_zero_eq (t := t) ha
    rw [coord_mul_conj_inv hS (conj_coord_zero hS h X Y Z), coord_mem_U_iff φ hS.t_not_mem]
    refine ⟨rfl, ?_, ?_⟩ <;> simp <;> grind
  ext x
  rw [mem_upperCentralSeries_two_iff, center_D₂ hh]
  constructor
  · rintro ⟨hxD, hx⟩
    obtain ⟨d, h⟩ := hAct_of_commutator_t hh (mem_sup_right hxD) (hx t (t_mem_D₂ hh))
    obtain rfl : d = 0 := (hh.mem_D₂_iff (mem_sup_right hxD) h).mp hxD
    have hxB := mem_B₂_of_hAct hh (SecondHyp.D_le_N hxD) h
    rcases (mem_zpowers_sup_iff hS.t_mul_t (TwoCoreSetup.comm_pull φ hS)).mp hxB with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨X, Y, Z, hXYZ⟩ := exists_coord_zero_eq (t := t) h1
      have hxe : x = coord φ t ((1, X, Y, Z) : QGSpace K) := by
        rw [coord_one_eq, hXYZ, ← mul_assoc, hS.t_mul_t, one_mul]
      subst hxe
      obtain ⟨d₁, hd₁, h₁⟩ := exists_D_hAct hh.sec 1 0
      have h2 := hx d₁ hd₁
      rw [coord_mul_conj_inv hS (conj_coord_one hS h₁ X Y Z), coord_mem_U_iff φ hS.t_not_mem]
        at h2
      obtain ⟨-, -, h3⟩ := h2
      simp only [Prod.snd_add, Prod.fst_add] at h3
      exact one_ne_zero (by linear_combination h3 - Y * CharTwo.two_eq_zero (R := K) : (1 : K) = 0)
  · intro hx
    exact ⟨hAD hx, fun d hd => hA x hx d hd⟩

theorem part_three [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) :
    ⁅𝐃₂, 𝐃₂⁆ = 𝐀₂ ∧ closure {x : G | ∃ y ∈ 𝐃₂, x = y * y} = 𝐀₂ ∧
      (center 𝐃₂).map 𝐃₂.subtype = 𝐔₂ ∧
      (Subgroup.upperCentralSeries 𝐃₂ 2).map 𝐃₂.subtype = 𝐀₂ := by
  have hsq : closure {x : G | ∃ y ∈ 𝐃₂, x = y * y} ≤ 𝐀₂ :=
    (closure_le _).mpr (by rintro _ ⟨y, hy, rfl⟩; exact sq_mem_A₂_of_mem_D₂ hh hy)
  exact ⟨le_antisymm ((commutator_le_closure_sq _).trans hsq) (A₂_le_commutator hh),
    le_antisymm hsq ((A₂_le_commutator hh).trans (commutator_le_closure_sq _)), center_D₂ hh,
    upper_D₂ hh⟩

theorem U₂_le_S (hh : HeisHyp L K n φ TG t) : 𝐔₂ ≤ 𝐒 :=
  ((pull_mono φ rootU₂_le_radA2).trans le_sup_right).trans
    ((hh.hyp.B_le_Q Axis.two).trans le_sup_left)

theorem center_S [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) :
    (center 𝐒).map 𝐒.subtype = 𝐔₂ := by
  have hS := hh.sec.two
  apply le_antisymm
  · intro z hz
    obtain ⟨hzS, hzc⟩ := mem_center_map_iff.mp hz
    have hzQ := mem_Q_of_comm hh hzS (hzc t (mem_sup_left (t_mem_Q hh))).symm
    obtain ⟨δ, hδ⟩ := hh.hAct_of_mem_Q hzQ
    obtain ⟨s, hs, h1⟩ := hh.exists_mem_S_hAct 1 0 0
    have e1 := hδ.mul h1
    have e2 := h1.mul hδ
    rw [← hzc s hs] at e1
    have e3 := (HAct.unique hS e1 e2).2.1
    obtain rfl : δ = 0 := by linear_combination e3
    exact mem_U₂_of_comm_D₂ hh (mem_B₂_of_hAct hh (hh.S_le_N₂ hzS) hδ)
      fun d hd => hzc d (mem_sup_right hd)
  · intro u hu
    exact mem_center_map_iff.mpr ⟨U₂_le_S hh hu, fun s hs => comm_U₂ hh hs hu⟩

theorem upper_S [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) :
    (Subgroup.upperCentralSeries 𝐒 2).map 𝐒.subtype = 𝐙 := by
  have hS := hh.sec.two
  ext x
  rw [mem_upperCentralSeries_two_iff, center_S hh]
  constructor
  · rintro ⟨hxS, hx⟩
    obtain ⟨d, h⟩ := hAct_of_commutator_t hh hxS (hx t (mem_sup_left (t_mem_Q hh)))
    obtain ⟨s, hs, h1⟩ := hh.exists_mem_S_hAct 1 0 0
    have hxs := hx s hs
    have e1 := HAct.unique hS (hAct_comm h h1)
      (hAct_of_mem_B hh.sec (mem_sup_right (pull_mono φ rootU₂_le_radA2 hxs)))
    obtain rfl : d = 0 := by linear_combination e1.2.1
    have hxB := mem_B₂_of_hAct hh (hh.S_le_N₂ hxS) h
    rcases (mem_zpowers_sup_iff hS.t_mul_t (TwoCoreSetup.comm_pull φ hS)).mp hxB with h2 | h2
    · obtain ⟨X, Y, Z, rfl⟩ := exists_coord_zero_eq (t := t) h2
      obtain ⟨q, hq, hq1⟩ := hh.exists_mem_S_hAct 0 0 1
      have h3 := hx q hq
      rw [coord_mul_conj_inv hS (conj_coord_zero hS hq1 X Y Z), coord_mem_U_iff φ hS.t_not_mem]
        at h3
      obtain ⟨-, h4, -⟩ := h3
      simp only [Prod.snd_add, Prod.fst_add] at h4
      exact coord_zero_mem_center_iff.mpr
        (by linear_combination h4 - X * CharTwo.two_eq_zero (R := K))
    · exfalso
      obtain ⟨X, Y, Z, hXYZ⟩ := exists_coord_zero_eq (t := t) h2
      have hxe : x = coord φ t ((1, X, Y, Z) : QGSpace K) := by
        rw [coord_one_eq, hXYZ, ← mul_assoc, hS.t_mul_t, one_mul]
      subst hxe
      rw [coord_mul_conj_inv hS (conj_coord_one hS h1 X Y Z), coord_mem_U_iff φ hS.t_not_mem]
        at hxs
      obtain ⟨-, -, h3⟩ := hxs
      simp only [Prod.snd_add, Prod.fst_add] at h3
      exact one_ne_zero (by linear_combination h3 - Y * CharTwo.two_eq_zero (R := K) : (1 : K) = 0)
  · intro hz
    refine ⟨(le_sup_left.trans le_sup_left : 𝐏 ≤ 𝐒) (Setup.ZP_le_PG hz), fun s hs => ?_⟩
    obtain ⟨x', y', d', h⟩ := hh.exists_hAct_of_mem_S hs
    obtain ⟨X, Y, Z, rfl⟩ := exists_coord_zero_eq (t := t)
      (pull_mono φ (center_le_rootA Axis.two) hz)
    obtain rfl := coord_zero_mem_center_iff.mp hz
    rw [coord_mul_conj_inv hS (conj_coord_zero hS h X 0 Z), coord_mem_U_iff φ hS.t_not_mem]
    refine ⟨rfl, ?_, ?_⟩ <;> simp [CharTwo.add_self_eq_zero]

theorem conj_coord_U₁ (hS : TwoCoreSetup L K n t) {s : G} {x y d : K} (h : HAct φ t s x y d)
    (X : K) : s * coord φ t ((0, X, 0, 0) : QGSpace K) * s⁻¹ =
      coord φ t ((0, X, 0, x * X) : QGSpace K) := by
  rw [conj_coord_zero hS h]
  congr 1
  simp

theorem normalizer_le_U₁ [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {Y : Subgroup G}
    (hY : ⊥ < Y) (hYU : Y ≤ 𝐔₁) : 𝐒 ⊓ normalizer (Y : Set G) = 𝐑 := by
  have hS := hh.sec.two
  apply le_antisymm
  · rintro s ⟨hsS, hsN⟩
    obtain ⟨x, y, d, h⟩ := hh.exists_hAct_of_mem_S hsS
    obtain ⟨u, huY, hu1⟩ := IsConcreteLE.exists_of_lt hY
    obtain ⟨X, Y', Z, rfl⟩ := exists_coord_zero_eq (t := t)
      (pull_mono φ rootU_one_le_rootA_two (hYU huY))
    obtain ⟨rfl, rfl⟩ := coord_zero_mem_U₁_iff.mp (hYU huY)
    have hX : X ≠ 0 := by
      rintro rfl
      exact hu1 ((mem_bot).mpr (coord_zero φ))
    have h1 := hYU ((mem_normalizer_iff.mp hsN _).mp huY)
    rw [conj_coord_U₁ hS h, coord_zero_mem_U₁_iff] at h1
    exact (hh.mem_R_iff hsS h).mpr ((mul_eq_zero.mp h1.2).resolve_right hX)
  · intro r hr
    refine ⟨hh.R_le_S hr, mem_normalizer_of_conj_le fun u hu => ?_⟩
    obtain ⟨x, y, d, h⟩ := hh.exists_hAct_of_mem_S (hh.R_le_S hr)
    obtain rfl := (hh.mem_R_iff (hh.R_le_S hr) h).mp hr
    obtain ⟨X, Y', Z, rfl⟩ := exists_coord_zero_eq (t := t)
      (pull_mono φ rootU_one_le_rootA_two (hYU hu))
    obtain ⟨rfl, rfl⟩ := coord_zero_mem_U₁_iff.mp (hYU hu)
    rw [conj_coord_U₁ hS h, zero_mul]
    exact hu

theorem normalizer_le_A₁ [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {Y : Subgroup G}
    (hY : 𝐙 < Y) (hYA : Y ≤ 𝐀₁) : 𝐒 ⊓ normalizer (Y : Set G) = 𝐑 := by
  have hS := hh.sec.two
  have hA₁Q : 𝐀₁ ≤ 𝐐 := le_sup_right.trans (hh.hyp.B_le_Q Axis.one)
  apply le_antisymm
  · rintro s ⟨hsS, hsN⟩
    obtain ⟨x, y, d, h⟩ := hh.exists_hAct_of_mem_S hsS
    obtain ⟨a, haY, haZ⟩ := IsConcreteLE.exists_of_lt hY
    have haQ := hA₁Q (hYA haY)
    obtain ⟨δ, hδ⟩ := hh.hAct_of_mem_Q haQ
    have hδ0 : δ ≠ 0 := by
      rintro rfl
      have haB := mem_B₂_of_hAct hh (hh.Q_le_N haQ).2 hδ
      have haA₂ : a ∈ 𝐀₂ := by
        rw [← zpowers_sup_inf_eq hS.t_mul_t (pull_le φ _) hS.t_not_mem
          (TwoCoreSetup.comm_pull φ hS)]
        exact ⟨haB, pull_le φ _ (hYA haY)⟩
      apply haZ
      have h1 : a ∈ pull φ (rootA K Axis.one ⊓ rootA K Axis.two) := by
        rw [pull_inf]
        exact ⟨hYA haY, haA₂⟩
      rwa [show rootA K Axis.one ⊓ rootA K Axis.two = antiUnipotentCenter K from
        radA1_inf_radA2] at h1
    have hsa : s * a * s⁻¹ ∈ Y := (mem_normalizer_iff.mp hsN a).mp haY
    have hsaQ := hA₁Q (hYA hsa)
    have e := ((hh.mem_Q_iff (mem_sup_left hsaQ) (hAct_conj h hδ)).mp hsaQ).2
    have hx : δ * x = 0 := by linear_combination e
    exact (hh.mem_R_iff hsS h).mpr ((mul_eq_zero.mp hx).resolve_left hδ0)
  · intro r hr
    refine ⟨hh.R_le_S hr, (sup_le (fun q hq => ?_) (fun d hd => ?_) : 𝐑 ≤ _) hr⟩
    · refine mem_normalizer_of_conj_le fun a ha => ?_
      have hqa : q * a * q⁻¹ * a⁻¹ ∈ 𝐙 := by
        rw [← hh.hyp.setup.closure_sq_eq hh.hyp.T_eq, ← commutatorElement_def]
        exact commutator_le_closure_sq _ (commutator_mem_commutator hq (hA₁Q (hYA ha)))
      have e : q * a * q⁻¹ = (q * a * q⁻¹ * a⁻¹) * a := by group
      rw [e]
      exact mul_mem (hY.le hqa) ha
    · refine mem_normalizer_of_conj_le fun a ha => ?_
      have hac := (mem_center_map_iff.mp ((center_D₁ hh).ge (hYA ha))).2 d hd
      rw [hac, mul_inv_cancel_right]
      exact ha

theorem main [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) (Q ZP : Subgroup G)
    (hQ : Q = pull φ (antiUnipotent K) ⊔ TG) (hZP : ZP = pull φ (antiUnipotentCenter K)) :
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
    IsPGroup 2 R ∧ IsPGroup 2 S ∧
      (⁅R, R⁆ = ZP ∧ closure {x : G | ∃ y ∈ R, x = y * y} = ZP ∧
        (center R).map R.subtype = ZP) ∧
      (⁅D₁, D₁⁆ = U₁ ∧ closure {x : G | ∃ y ∈ D₁, x = y * y} = U₁ ∧
        (center D₁).map D₁.subtype = A₁) ∧
      (⁅D₂, D₂⁆ = A₂ ∧ closure {x : G | ∃ y ∈ D₂, x = y * y} = A₂ ∧
        (center D₂).map D₂.subtype = U₂ ∧
        (Subgroup.upperCentralSeries D₂ 2).map D₂.subtype = A₂) ∧
      ((center S).map S.subtype = U₂ ∧ (Subgroup.upperCentralSeries S 2).map S.subtype = ZP) ∧
      (∀ Y : Subgroup G, ⊥ < Y → Y ≤ U₁ → S ⊓ normalizer (Y : Set G) = R) ∧
      (∀ Y : Subgroup G, ZP < Y → Y ≤ A₁ → S ⊓ normalizer (Y : Set G) = R) := by
  subst hQ hZP
  intro U₁ U₂ A₁ A₂ B₁ B₂ N₁ N₂ D₁ D₂ R S
  obtain ⟨-, hR2, hS2, -⟩ := hh.main _ rfl
  exact ⟨hR2, hS2, part_one hh, part_two hh, part_three hh, ⟨center_S hh, upper_S hh⟩,
    fun Y hY hYU => normalizer_le_U₁ hh hY hYU, fun Y hY hYA => normalizer_le_A₁ hh hY hYA⟩

end Main

end OneAxisRadicalStructure

open Subgroup GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.PartOne.KCRootAxis

theorem standard_symplectic_four_one_axis_radical_structure
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
    {x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ u ∈ U₁, x = t * u} →
      IsPGroup 2 R ∧ IsPGroup 2 S ∧
      (⁅R, R⁆ = ZP ∧ closure {x : G | ∃ y ∈ R, x = y * y} = ZP ∧
        (center R).map R.subtype = ZP) ∧
      (⁅D₁, D₁⁆ = U₁ ∧ closure {x : G | ∃ y ∈ D₁, x = y * y} = U₁ ∧
        (center D₁).map D₁.subtype = A₁) ∧
      (⁅D₂, D₂⁆ = A₂ ∧ closure {x : G | ∃ y ∈ D₂, x = y * y} = A₂ ∧
        (center D₂).map D₂.subtype = U₂ ∧
        (Subgroup.upperCentralSeries D₂ 2).map D₂.subtype = A₂) ∧
      ((center S).map S.subtype = U₂ ∧ (Subgroup.upperCentralSeries S 2).map S.subtype = ZP) ∧
      (∀ Y : Subgroup G, ⊥ < Y → Y ≤ U₁ → S ⊓ normalizer (Y : Set G) = R) ∧
      (∀ Y : Subgroup G, ZP < Y → Y ≤ A₁ → S ⊓ normalizer (Y : Set G) = R) := by
  intro TG PG Q ZP U₁ U₂ A₁ A₂ B₁ B₂ N₁ N₂ D₁ D₂ R S hone
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
  exact OneAxisRadicalStructure.main hh Q ZP hQ hZP

end CFSG.LocalAnalysis.SymplecticFourStandard
