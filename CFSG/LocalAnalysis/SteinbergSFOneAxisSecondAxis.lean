module

public import CFSG.LocalAnalysis.SteinbergSFOneAxisRadicalStructure

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace OneAxisSecondAxis

open Subgroup GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
  OneAxisRadicalStructure
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.LocalAnalysis.SteinbergCD
open scoped Matrix commutatorElement Pointwise

section General

variable {G : Type*} [Group G]

theorem mem_map_conj_inv_iff {H : Subgroup G} {g x : G} :
    x ∈ H.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    refine ⟨g * x * g⁻¹, h, ?_⟩
    simp [mul_assoc]

theorem card_sup_mul_card_inf {A B : Subgroup G} (hAB : A ≤ normalizer (B : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  have : (B.subgroupOf (A ⊔ B)).Normal := normal_subgroupOf_sup_of_le_normalizer hAB
  have : (B.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hAB
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A B hAB
  have h1 := card_eq_card_quotient_mul_card_subgroup (B.subgroupOf A)
  have h2 := card_eq_card_quotient_mul_card_subgroup (B.subgroupOf (A ⊔ B))
  have h3 : Nat.card (B.subgroupOf A) = Nat.card (A ⊓ B : Subgroup G) := by
    rw [← card_map_of_injective A.subtype_injective, subgroupOf_map_subtype, inf_comm]
  have h4 : Nat.card (B.subgroupOf (A ⊔ B)) = Nat.card B :=
    Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem comm_mod_sup {H Z A B : Subgroup G} (hZ : ∀ z ∈ Z, ∀ h ∈ H, z * h = h * z) {x : G}
    (hx : x ∈ H) (hA : A ≤ H) (hB : B ≤ H) (h₁ : ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ Z)
    (h₂ : ∀ b ∈ B, x * b * x⁻¹ * b⁻¹ ∈ Z) : ∀ y ∈ A ⊔ B, x * y * x⁻¹ * y⁻¹ ∈ Z := by
  let C : Subgroup G :=
    { carrier := {y | y ∈ H ∧ x * y * x⁻¹ * y⁻¹ ∈ Z}
      mul_mem' := by
        rintro y y' ⟨hy, hyz⟩ ⟨hy', hyz'⟩
        refine ⟨mul_mem hy hy', ?_⟩
        have hxy : x * y * x⁻¹ ∈ H := mul_mem (mul_mem hx hy) (inv_mem hx)
        have e : x * (y * y') * x⁻¹ * (y * y')⁻¹ =
            (x * y * x⁻¹) * (x * y' * x⁻¹ * y'⁻¹) * y⁻¹ := by group
        rw [e, ← hZ _ hyz' _ hxy, mul_assoc]
        exact mul_mem hyz' hyz
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := by
        rintro y ⟨hy, hyz⟩
        refine ⟨inv_mem hy, ?_⟩
        have e : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y := by group
        rw [e, ← hZ _ (inv_mem hyz) _ (inv_mem hy), inv_mul_cancel_right]
        exact inv_mem hyz }
  have hle : A ⊔ B ≤ C := sup_le (fun a ha => ⟨hA ha, h₁ a ha⟩) fun b hb => ⟨hB hb, h₂ b hb⟩
  exact fun y hy => (hle hy).2

theorem comm_mod_of_sup {H Z A B : Subgroup G} (hZ : ∀ z ∈ Z, ∀ h ∈ H, z * h = h * z)
    (hA : A ≤ H) (hB : B ≤ H) (hAA : ∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ Z)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hBB : ∀ b ∈ B, ∀ b' ∈ B, b * b' * b⁻¹ * b'⁻¹ ∈ Z) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y * x⁻¹ * y⁻¹ ∈ Z := by
  have hsym : ∀ {x y : G}, x * y * x⁻¹ * y⁻¹ ∈ Z → y * x * y⁻¹ * x⁻¹ ∈ Z := fun {x y} h => by
    have e : (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ := by group
    rw [← e]
    exact inv_mem h
  have hAB' : A ⊔ B ≤ H := sup_le hA hB
  have hfirst : ∀ y ∈ A ⊔ B, ∀ a ∈ A ⊔ B, (a ∈ A ∨ a ∈ B) → a * y * a⁻¹ * y⁻¹ ∈ Z := by
    rintro y hy a - (ha | ha)
    · exact comm_mod_sup hZ (hA ha) hA hB (hAA a ha) (hAB a ha) y hy
    · exact comm_mod_sup hZ (hB ha) hA hB (fun a' ha' => hsym (hAB a' ha' a ha)) (hBB a ha) y hy
  intro x hx y hy
  exact hsym (comm_mod_sup hZ (hAB' hy) hA hB
    (fun a ha => hsym (hfirst y hy a (mem_sup_left ha) (Or.inl ha)))
    (fun b hb => hsym (hfirst y hy b (mem_sup_right hb) (Or.inr hb))) x hx)

end General

section Model

variable {K : Type} [Field K] [CharP K 2]

@[expose] def swapSL : SL₂ K := ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two_of, CharTwo.neg_eq]⟩

theorem swapSL_mulVec (v : Fin 2 → K) :
    ((swapSL : SL₂ K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![v 1, v 0] := by
  ext i
  fin_cases i <;> simp [swapSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem sElt_swap_mul_self : sElt (swapSL : SL₂ K) * sElt swapSL = 1 := by
  apply mat_ext
  rw [mat_mul, mat_sElt, sMat_mul, mat_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sMat, swapSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem sElt_swap_inv : (sElt (swapSL : SL₂ K))⁻¹ = sElt swapSL :=
  inv_eq_of_mul_eq_one_right sElt_swap_mul_self

theorem glMat_sElt_swap : glMat (sElt (swapSL : SL₂ K) : GL (Fin 4) K) =
    !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1] := by
  rw [glMat_sElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sMat, swapSL]

theorem sElt_swap_conj_uElt (a b c : K) :
    sElt (swapSL : SL₂ K) * uElt a b c 0 * (sElt swapSL)⁻¹ = uElt b a c 0 := by
  have e1 : uElt a b c 0 = aElt ![b, a] c := by simp [aElt]
  have e2 : uElt b a c 0 = aElt ![a, b] c := by simp [aElt]
  rw [e1, e2, sElt_mul_aElt, mul_inv_cancel_right, swapSL_mulVec]
  simp

theorem sElt_swap_conj_aElt (v : Fin 2 → K) (c : K) :
    sElt (swapSL : SL₂ K) * aElt v c * (sElt swapSL)⁻¹ = aElt ![v 1, v 0] c := by
  rw [sElt_mul_aElt, mul_inv_cancel_right, swapSL_mulVec]

theorem sElt_swap_conj_diagTorus {δ : antiSp K} (hδ : δ ∈ diagTorus K) :
    sElt (swapSL : SL₂ K) * δ * (sElt swapSL)⁻¹ ∈ diagTorus K := by
  obtain ⟨r, s, hr, hs, hδm⟩ := hδ
  refine ⟨r, s⁻¹, hr, inv_ne_zero hs, ?_⟩
  rw [sElt_swap_inv]
  change mat (sElt swapSL * δ * sElt swapSL) = _
  rw [mat_mul, mat_mul, mat_sElt]
  change sMat _ * glMat (δ : GL (Fin 4) K) * sMat _ = _
  rw [hδm, diagMat, diagMat, inv_inv]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp [sMat, swapSL]

theorem diagTorus_conj' {δ : antiSp K} (hδ : δ ∈ diagTorus K) (a b c d : K) :
    ∃ a' b' c' d' : K, δ * uElt a b c d * δ⁻¹ = uElt a' b' c' d' ∧ (a = 0 → a' = 0) ∧
      (d = 0 → d' = 0) := by
  obtain ⟨r, s, hr, hs, hδm⟩ := inv_mem hδ
  have h := diagTorus_conj hr hs hδm a b c d
  rw [inv_inv] at h
  refine ⟨_, _, _, _, h, fun ha => by rw [ha, mul_zero], fun hd => by rw [hd, mul_zero]⟩

theorem diagTorus_conj_radA1 {δ : antiSp K} (hδ : δ ∈ diagTorus K) {x : antiSp K}
    (hx : x ∈ radA1 K) : δ * x * δ⁻¹ ∈ radA1 K := by
  obtain ⟨b, c, d, rfl⟩ := hx
  obtain ⟨a', b', c', d', h, ha, -⟩ := diagTorus_conj' hδ 0 b c d
  rw [h, ha rfl]
  exact ⟨b', c', d', rfl⟩

theorem diagTorus_conj_radA2 {δ : antiSp K} (hδ : δ ∈ diagTorus K) {x : antiSp K}
    (hx : x ∈ radA2 K) : δ * x * δ⁻¹ ∈ radA2 K := by
  obtain ⟨a, b, c, rfl⟩ := hx
  obtain ⟨a', b', c', d', h, -, hd⟩ := diagTorus_conj' hδ a b c 0
  rw [h, hd rfl]
  exact ⟨a', b', c', rfl⟩

theorem diagTorus_conj_antiUnipotent {δ : antiSp K} (hδ : δ ∈ diagTorus K) {x : antiSp K}
    (hx : x ∈ antiUnipotent K) : δ * x * δ⁻¹ ∈ antiUnipotent K := by
  obtain ⟨a, b, c, d, rfl⟩ := hx
  obtain ⟨a', b', c', d', h, -, -⟩ := diagTorus_conj' hδ a b c d
  rw [h]
  exact ⟨a', b', c', d', rfl⟩

theorem uElt_eq_mul (a b c d : K) : uElt a b c d = uElt 0 0 0 d * uElt a b c 0 := by
  rw [uElt_mul]
  congr 1 <;> ring

theorem uElt_eq_mul' (a b c : K) : uElt a b c 0 = uElt 0 b (c + a * b) 0 * uElt a 0 0 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [uElt_mul]
  congr 1 <;> first | ring1 | linear_combination (a * b) * h2 | linear_combination (-(a * b)) * h2

theorem eq_zero_of_comm_mod {a b c d : K}
    (h₁ : (uElt 1 0 0 0 * uElt a b c d)⁻¹ * (uElt a b c d * uElt 1 0 0 0) ∈ rootU₂ K)
    (h₂ : (uElt 0 0 0 1 * uElt a b c d)⁻¹ * (uElt a b c d * uElt 0 0 0 1) ∈ rootU₂ K) :
    a = 0 ∧ d = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨c₁, e₁⟩ := h₁
  obtain ⟨c₂, e₂⟩ := h₂
  rw [uElt_mul, uElt_mul, uElt_inv, uElt_mul] at e₁ e₂
  obtain ⟨-, e₁, -, -⟩ := uElt_inj e₁
  obtain ⟨-, e₂, -, -⟩ := uElt_inj e₂
  constructor
  · linear_combination e₂ - (b + a + a * d) * h2
  · linear_combination e₁ - (b + d + a * d) * h2

end Model

section Weyl

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {n : ℕ}
  {φ : L ≃* antiSp K} {t : G}

local notation "𝐰" => ((φ.symm (sElt swapSL) : L) : G)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐔₂" => pull φ (rootU K Axis.two)
local notation "𝐀₂" => pull φ (rootA K Axis.two)
local notation "𝐍₂" => normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐃₂" => (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G)).subtype

theorem w_mem_L : 𝐰 ∈ L := (φ.symm _).2

theorem w_mul_w : 𝐰 * 𝐰 = 1 := by
  rw [← coe_mul, ← map_mul, sElt_swap_mul_self, map_one, coe_one]

theorem w_inv : 𝐰⁻¹ = 𝐰 := inv_eq_of_mul_eq_one_right w_mul_w

theorem w_conj_conj (x : G) : 𝐰 * (𝐰 * x * 𝐰⁻¹) * 𝐰⁻¹ = x := by
  calc 𝐰 * (𝐰 * x * 𝐰⁻¹) * 𝐰⁻¹ = (𝐰 * 𝐰) * x * (𝐰 * 𝐰)⁻¹ := by group
    _ = x := by rw [w_mul_w]; group

theorem w_comm_t (hS : TwoCoreSetup L K n t) : 𝐰 * t = t * 𝐰 := (hS.comm w_mem_L).symm

theorem w_conj_uElt (a b c : K) :
    𝐰 * ((φ.symm (uElt a b c 0) : L) : G) * 𝐰⁻¹ = ((φ.symm (uElt b a c 0) : L) : G) := by
  rw [symm_conj_eq, sElt_swap_conj_uElt]

theorem w_conj_coord (hS : TwoCoreSetup L K n t) (v : Fin 2 → K) :
    𝐰 * coord φ t (qgPoint v) * 𝐰⁻¹ = coord φ t (qgPoint ![v 1, v 0]) := by
  rw [coord_qgPoint, coord_qgPoint, ← sElt_swap_conj_aElt, ← symm_conj_eq]
  calc 𝐰 * (t * ((φ.symm (aElt v 0) : L) : G)) * 𝐰⁻¹
      = (𝐰 * t) * ((φ.symm (aElt v 0) : L) : G) * 𝐰⁻¹ := by group
    _ = t * (𝐰 * ((φ.symm (aElt v 0) : L) : G) * 𝐰⁻¹) := by rw [w_comm_t hS]; group

theorem hAct_w_conj (hS : TwoCoreSetup L K n t) {g : G} {x y : K} (h : HAct φ t g x y 0) :
    HAct φ t (𝐰 * g * 𝐰⁻¹) y x 0 := by
  intro v
  have e1 : 𝐰⁻¹ * coord φ t (qgPoint v) * 𝐰⁻¹⁻¹ = coord φ t (qgPoint ![v 1, v 0]) := by
    rw [w_inv]
    exact w_conj_coord hS v
  have e2 := h ![v 1, v 0]
  calc 𝐰 * g * 𝐰⁻¹ * coord φ t (qgPoint v) * (𝐰 * g * 𝐰⁻¹)⁻¹
      = 𝐰 * (g * (𝐰⁻¹ * coord φ t (qgPoint v) * 𝐰⁻¹⁻¹) * g⁻¹) * 𝐰⁻¹ := by group
    _ = 𝐰 * coord φ t (qgPoint ![(![v 1, v 0] : Fin 2 → K) 0 + 0 * (![v 1, v 0] : Fin 2 → K) 1 +
          y, (![v 1, v 0] : Fin 2 → K) 1 + x]) * 𝐰⁻¹ := by rw [e1, e2]
    _ = _ := by
        rw [w_conj_coord hS]
        congr 2
        ext i
        fin_cases i <;> simp

theorem w_mem_N₂ [Finite G] (hS : TwoCoreSetup L K n t) : 𝐰 ∈ 𝐍₂ := by
  rw [hS.mem_normalizer_zpowers_sup_iff (hS.L_le w_mem_L) (pull_le φ _)]
  exact symm_mem_normalizer_pull (mem_normalizer_radA2_iff.mpr (firstCol_sElt _))

theorem w_conj_mem_D₂ [Finite G] (hS : TwoCoreSetup L K n t) {d : G} (hd : d ∈ 𝐃₂) :
    𝐰 * d * 𝐰⁻¹ ∈ 𝐃₂ :=
  conj_mem_pCore_map (w_mem_N₂ hS) hd

theorem w_conj_mem_A₂ {a : G} (ha : a ∈ 𝐀₂) : 𝐰 * a * 𝐰⁻¹ ∈ 𝐀₂ := by
  obtain ⟨a', ha', rfl⟩ := exists_eq_symm_of_mem_pull ha
  change a' ∈ radA2 K at ha'
  obtain ⟨x, y, z, rfl⟩ := ha'
  rw [w_conj_uElt]
  exact symm_mem_pull.mpr ⟨y, x, z, rfl⟩

theorem w_conj_U₂ {u : G} (hu : u ∈ 𝐔₂) : 𝐰 * u * 𝐰⁻¹ = u := by
  obtain ⟨a', ha', rfl⟩ := exists_eq_symm_of_mem_pull hu
  change a' ∈ rootU₂ K at ha'
  obtain ⟨c, rfl⟩ := ha'
  rw [w_conj_uElt]

theorem w_conj_J₀ {j : G} (hj : j ∈ pull φ (diagTorus K)) :
    𝐰 * j * 𝐰⁻¹ ∈ pull φ (diagTorus K) := by
  obtain ⟨δ, hδ, rfl⟩ := exists_eq_symm_of_mem_pull hj
  rw [symm_conj_eq]
  exact symm_mem_pull.mpr (sElt_swap_conj_diagTorus hδ)

theorem mem_U₂_of_mem_ZP {z : G} (hz : z ∈ 𝐙) (hz' : 𝐰 * z * 𝐰⁻¹ ∈ 𝐙) : z ∈ 𝐔₂ := by
  obtain ⟨a', ⟨b, c, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hz
  rw [w_conj_uElt] at hz'
  obtain ⟨b', c', h⟩ := symm_mem_pull.mp hz'
  obtain ⟨hb, -, -, -⟩ := uElt_inj h
  rw [hb]
  exact symm_mem_pull.mpr ⟨c, rfl⟩

theorem mem_A₂_of_conj_mem_ZP {z : G} (hz : 𝐰 * z * 𝐰⁻¹ ∈ 𝐙) : z ∈ 𝐀₂ := by
  have h := w_conj_mem_A₂ (pull_mono φ (center_le_rootA Axis.two) hz)
  rwa [w_conj_conj] at h

theorem exists_mul_of_mem_A₂ {a : G} (ha : a ∈ 𝐀₂) :
    ∃ z ∈ 𝐙, ∃ z', 𝐰 * z' * 𝐰⁻¹ ∈ 𝐙 ∧ z * z' = a := by
  obtain ⟨a', ha', rfl⟩ := exists_eq_symm_of_mem_pull ha
  change a' ∈ radA2 K at ha'
  obtain ⟨x, y, c, rfl⟩ := ha'
  refine ⟨_, symm_mem_pull.mpr ⟨y, c + x * y, rfl⟩, ((φ.symm (uElt x 0 0 0) : L) : G), ?_, ?_⟩
  · rw [w_conj_uElt]
    exact symm_mem_pull.mpr ⟨x, 0, rfl⟩
  · rw [← coe_mul, ← map_mul, ← uElt_eq_mul']

end Weyl

section Orders

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  (φ : L ≃* antiSp K)

theorem card_radA2 : Nat.card (radA2 K) = Nat.card K ^ 3 := by
  have hbij : Function.Bijective fun p : K × K × K =>
      (⟨uElt p.1 p.2.1 p.2.2 0, p.1, p.2.1, p.2.2, rfl⟩ : radA2 K) := by
    refine ⟨fun p p' h => ?_, fun g => ?_⟩
    · obtain ⟨h1, h2, h3, -⟩ := uElt_inj (congrArg Subtype.val h)
      exact Prod.ext h1 (Prod.ext h2 h3)
    · obtain ⟨a, b, c, h⟩ := g.2
      exact ⟨(a, b, c), Subtype.ext h.symm⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod, Nat.card_prod]
  ring

theorem card_pull_A₂ : Nat.card (pull φ (rootA K Axis.two)) = Nat.card K ^ 3 :=
  (card_pull φ _).trans card_radA2

theorem card_pull_ZP : Nat.card (pull φ (antiUnipotentCenter K)) = Nat.card K ^ 2 := by
  rw [card_pull, ← Nat.card_congr (centerEquiv (K := K)).toEquiv]
  change Nat.card (K × K) = _
  rw [Nat.card_prod, sq]

theorem card_pull_P : Nat.card (pull φ (antiUnipotent K)) = Nat.card K ^ 4 :=
  (card_pull φ _).trans (card_antiUnipotent rfl)

theorem pull_P_eq :
    pull φ (antiUnipotent K) = pull φ (rootA K Axis.one) ⊔ pull φ (rootA K Axis.two) := by
  rw [← pull_sup]
  exact congrArg (pull φ) antiUnipotent_eq_radA1_sup_radA2

theorem mem_ZP_of_mem_A₁_A₂ {y : G} (h₁ : y ∈ pull φ (rootA K Axis.one))
    (h₂ : y ∈ pull φ (rootA K Axis.two)) : y ∈ pull φ (antiUnipotentCenter K) := by
  have h : y ∈ pull φ (rootA K Axis.one ⊓ rootA K Axis.two) := by
    rw [pull_inf]
    exact ⟨h₁, h₂⟩
  rwa [show rootA K Axis.one ⊓ rootA K Axis.two = antiUnipotentCenter K from
    radA1_inf_radA2] at h

omit [CharP K 2] in
theorem symm_mul_symm (x y : antiSp K) :
    ((φ.symm x : L) : G) * ((φ.symm y : L) : G) = ((φ.symm (x * y) : L) : G) := by
  rw [map_mul, coe_mul]

omit [CharP K 2] in
theorem symm_inv' (x : antiSp K) : ((φ.symm x : L) : G)⁻¹ = ((φ.symm x⁻¹ : L) : G) := by
  rw [map_inv, coe_inv]

end Orders

theorem inf_zpowers_eq_bot {G : Type*} [Group G] {H : Subgroup G} {t : G} (htt : t * t = 1)
    (ht : t ∉ H) : H ⊓ zpowers t = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxH, j, rfl⟩
  rcases zpow_eq_one_or_eq htt j with h | h
  · exact (mem_bot).mpr h
  · exact absurd (h ▸ hxH) ht

theorem le_normalizer_sup {G : Type*} [Group G] [Finite G] {J H₁ H₂ : Subgroup G}
    (h₁ : J ≤ normalizer (H₁ : Set G)) (h₂ : J ≤ normalizer (H₂ : Set G)) :
    J ≤ normalizer ((H₁ ⊔ H₂ : Subgroup G) : Set G) := fun _ hj =>
  mem_normalizer_of_conj_le fun _ hx => conj_mem_sup
    (fun y hy => (mem_normalizer_iff.mp (h₁ hj) y).mp hy)
    (fun y hy => (mem_normalizer_iff.mp (h₂ hj) y).mp hy) hx

section Hyp

variable {G : Type} [Group G] (L : Subgroup G) (K : Type) [Field K] [CharP K 2] (n : ℕ)
  (φ : L ≃* antiSp K) (TG : Subgroup G) (t : G) (M : Subgroup G)

local notation "𝐰" => ((φ.symm (sElt swapSL) : L) : G)
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
local notation "𝐂" => centralizer ({t} : Set G)
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
local notation "𝐌₁" => (M ⊔ pull φ (rootA K Axis.one) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌w" => M.map (MulAut.conj ((φ.symm (sElt swapSL) : L) : G)⁻¹).toMonoidHom
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

structure AxisHyp : Prop where
  heis : HeisHyp L K n φ TG t
  le_D₁ : M ≤ 𝐃₁
  le_D₂ : M ≤ 𝐃₂
  comm : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x
  mul_self : ∀ x ∈ M, x * x = 1
  card : Nat.card M = (2 ^ n) ^ 3
  ZP_le : 𝐙 ≤ M
  card₁ : Nat.card 𝐌₁ = (2 ^ n) ^ 4
  conj₁ : ∀ s ∈ 𝐒, ∀ x ∈ 𝐌₁, s * x * s⁻¹ ∈ 𝐌₁
  t_not_mem₁ : t ∉ 𝐌₁

end Hyp

section Main

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {n : ℕ}
  {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G} {M : Subgroup G}

local notation "𝐰" => ((φ.symm (sElt swapSL) : L) : G)
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
local notation "𝐂" => centralizer ({t} : Set G)
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
local notation "𝐌₁" => (M ⊔ pull φ (rootA K Axis.one) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌w" => M.map (MulAut.conj ((φ.symm (sElt swapSL) : L) : G)⁻¹).toMonoidHom
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

namespace AxisHyp

theorem t_not_mem (ax : AxisHyp L K n φ TG t M) : t ∉ M := fun h =>
  ax.t_not_mem₁ (mem_sup_left h)

theorem A₁_le_D₁ (ax : AxisHyp L K n φ TG t M) : 𝐀₁ ≤ 𝐃₁ :=
  le_sup_right.trans (B₁_le_D₁ ax.heis)

theorem M₁_le_D₁ (ax : AxisHyp L K n φ TG t M) : 𝐌₁ ≤ 𝐃₁ := sup_le ax.le_D₁ ax.A₁_le_D₁

theorem B₂_le (ax : AxisHyp L K n φ TG t M) : 𝐁₂ ≤ 𝐂 ⊓ 𝐍₁ := fun _ hb =>
  ⟨ax.heis.sec.B_le_C hb, (ax.heis.Q_le_N (ax.heis.hyp.B_le_Q Axis.two hb)).1⟩

theorem mem_ZP_of_mem_B₁_B₂ (ax : AxisHyp L K n φ TG t M) {x : G} (h₁ : x ∈ 𝐁₁)
    (h₂ : x ∈ 𝐁₂) : x ∈ 𝐙 ∨ t * x ∈ 𝐙 := by
  have hS := ax.heis.sec.two
  rcases (mem_zpowers_sup_iff hS.t_mul_t (TwoCoreSetup.comm_pull φ hS)).mp h₁ with h | h <;>
    rcases (mem_zpowers_sup_iff hS.t_mul_t (TwoCoreSetup.comm_pull φ hS)).mp h₂ with h' | h'
  · exact Or.inl (mem_ZP_of_mem_A₁_A₂ φ h h')
  · exfalso
    apply hS.t_not_mem
    have := mul_mem (pull_le φ _ h') (inv_mem (pull_le φ _ h))
    rwa [mul_inv_cancel_right] at this
  · exfalso
    apply hS.t_not_mem
    have := mul_mem (pull_le φ _ h) (inv_mem (pull_le φ _ h'))
    rwa [mul_inv_cancel_right] at this
  · exact Or.inr (mem_ZP_of_mem_A₁_A₂ φ h h')

theorem M₁_inf_B₂ (ax : AxisHyp L K n φ TG t M) : 𝐌₁ ⊓ 𝐁₂ = 𝐙 := by
  refine le_antisymm (fun x ⟨hx₁, hx₂⟩ => ?_) (le_inf (ax.ZP_le.trans le_sup_left)
    ((pull_mono φ (center_le_rootA Axis.two)).trans le_sup_right))
  have hxB₁ : x ∈ 𝐁₁ := by
    rw [← ax.heis.inf₁]
    exact ⟨ax.M₁_le_D₁ hx₁, ax.B₂_le hx₂⟩
  rcases ax.mem_ZP_of_mem_B₁_B₂ hxB₁ hx₂ with h | h
  · exact h
  · exfalso
    apply ax.t_not_mem₁
    have := mul_mem ((ax.ZP_le.trans le_sup_left) h) (inv_mem hx₁)
    rwa [mul_inv_cancel_right] at this

theorem mem_ZP_of_mem_B₂ (ax : AxisHyp L K n φ TG t M) {m : G} (hm : m ∈ M) (hb : m ∈ 𝐁₂) :
    m ∈ 𝐙 := by
  rw [← ax.M₁_inf_B₂]
  exact ⟨mem_sup_left hm, hb⟩

theorem hAct_of_mem [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {m : G} (hm : m ∈ M) :
    ∃ y : K, HAct φ t m 0 y 0 := by
  obtain ⟨x, y, h⟩ := hAct_of_mem_D ax.heis.sec (ax.le_D₂ hm)
  have hmR : m ∈ 𝐑 := mem_sup_right (ax.le_D₁ hm)
  obtain rfl := (ax.heis.mem_R_iff (ax.heis.R_le_S hmR) h).mp hmR
  exact ⟨y, h⟩

theorem mem_ZP_of_hAct [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {m : G} (hm : m ∈ M)
    (h : HAct φ t m 0 0 0) : m ∈ 𝐙 :=
  ax.mem_ZP_of_mem_B₂ hm (mem_B₂_of_hAct ax.heis (SecondHyp.D_le_N (ax.le_D₂ hm)) h)

theorem le_S (ax : AxisHyp L K n φ TG t M) : M ≤ 𝐒 := fun _ hm => mem_sup_right (ax.le_D₂ hm)

theorem comm_mem_ZP [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {s m : G} (hs : s ∈ 𝐒)
    (hm : m ∈ M) : s * m * s⁻¹ * m⁻¹ ∈ 𝐙 := by
  have hh := ax.heis
  obtain ⟨x, y, d, h⟩ := hh.exists_hAct_of_mem_S hs
  obtain ⟨y', h'⟩ := ax.hAct_of_mem hm
  have hc : HAct φ t (s * m * s⁻¹ * m⁻¹) 0 0 0 := (hAct_comm h h').congr rfl (by ring) rfl
  rw [← ax.M₁_inf_B₂]
  have hm₁ : m ∈ 𝐌₁ := mem_sup_left hm
  refine mem_inf.mpr ⟨mul_mem (ax.conj₁ s hs m hm₁) (inv_mem hm₁), ?_⟩
  have hsN := hh.S_le_N₂ hs
  have hmN := hh.S_le_N₂ (ax.le_S hm)
  exact mem_B₂_of_hAct hh (mul_mem (mul_mem (mul_mem hsN hmN) (inv_mem hsN)) (inv_mem hmN)) hc

theorem conj_mem [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {s m : G} (hs : s ∈ 𝐒)
    (hm : m ∈ M) : s * m * s⁻¹ ∈ M := by
  have e : s * m * s⁻¹ = (s * m * s⁻¹ * m⁻¹) * m := by group
  rw [e]
  exact mul_mem (ax.ZP_le (ax.comm_mem_ZP hs hm)) hm

theorem S_le_normalizer [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    𝐒 ≤ normalizer (M : Set G) := fun _ hs =>
  mem_normalizer_of_conj_le fun _ hm => ax.conj_mem hs hm

theorem Mw_le_D₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : 𝐌w ≤ 𝐃₂ := fun x hx => by
  have h := w_conj_mem_D₂ ax.heis.sec.two (ax.le_D₂ (mem_map_conj_inv_iff.mp hx))
  rwa [w_conj_conj] at h

theorem Mw_le_S [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : 𝐌w ≤ 𝐒 := fun _ hx =>
  mem_sup_right (ax.Mw_le_D₂ hx)

theorem hAct_of_mem_Mw [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {x : G}
    (hx : x ∈ 𝐌w) : ∃ y : K, HAct φ t x y 0 0 := by
  obtain ⟨y, h⟩ := ax.hAct_of_mem (mem_map_conj_inv_iff.mp hx)
  refine ⟨y, ?_⟩
  have h' := hAct_w_conj ax.heis.sec.two h
  rwa [w_conj_conj] at h'

theorem Mw_comm (ax : AxisHyp L K n φ TG t M) {x y : G} (hx : x ∈ 𝐌w) (hy : y ∈ 𝐌w) :
    x * y = y * x := by
  have h := ax.comm _ (mem_map_conj_inv_iff.mp hx) _ (mem_map_conj_inv_iff.mp hy)
  have e : ∀ a b : G, (𝐰 * a * 𝐰⁻¹) * (𝐰 * b * 𝐰⁻¹) = 𝐰 * (a * b) * 𝐰⁻¹ := fun a b => by group
  rw [e, e] at h
  exact mul_left_cancel (mul_right_cancel h)

theorem Mw_mul_self (ax : AxisHyp L K n φ TG t M) {x : G} (hx : x ∈ 𝐌w) : x * x = 1 := by
  have h := ax.mul_self _ (mem_map_conj_inv_iff.mp hx)
  have e : (𝐰 * x * 𝐰⁻¹) * (𝐰 * x * 𝐰⁻¹) = 𝐰 * (x * x) * 𝐰⁻¹ := by group
  rw [e] at h
  have h' : 𝐰 * (x * x) * 𝐰⁻¹ = 𝐰 * 1 * 𝐰⁻¹ := by rw [h]; group
  exact mul_left_cancel (mul_right_cancel h')

theorem comm_mem_U₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {m x : G} (hm : m ∈ M)
    (hx : x ∈ 𝐌w) : m * x * m⁻¹ * x⁻¹ ∈ 𝐔₂ := by
  have h₁ : m * x * m⁻¹ * x⁻¹ ∈ 𝐙 := by
    have h := inv_mem (ax.comm_mem_ZP (ax.Mw_le_S hx) hm)
    rwa [show (x * m * x⁻¹ * m⁻¹)⁻¹ = m * x * m⁻¹ * x⁻¹ by group] at h
  refine mem_U₂_of_mem_ZP h₁ ?_
  have hm' : 𝐰 * m * 𝐰⁻¹ ∈ 𝐌w := mem_map_conj_inv_iff.mpr (by rwa [w_conj_conj])
  have e : 𝐰 * (m * x * m⁻¹ * x⁻¹) * 𝐰⁻¹ = (𝐰 * m * 𝐰⁻¹) * (𝐰 * x * 𝐰⁻¹) *
      (𝐰 * m * 𝐰⁻¹)⁻¹ * (𝐰 * x * 𝐰⁻¹)⁻¹ := by group
  rw [e]
  exact ax.comm_mem_ZP (ax.Mw_le_S hm') (mem_map_conj_inv_iff.mp hx)

theorem U₂_le (ax : AxisHyp L K n φ TG t M) : 𝐔₂ ≤ M :=
  (pull_mono φ (rootU_le_center Axis.two)).trans ax.ZP_le

theorem U₂_le_Mw (ax : AxisHyp L K n φ TG t M) : 𝐔₂ ≤ 𝐌w := fun u hu =>
  mem_map_conj_inv_iff.mpr (by rw [w_conj_U₂ hu]; exact ax.U₂_le hu)

theorem M_inf_Mw [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : M ⊓ 𝐌w = 𝐔₂ := by
  refine le_antisymm (fun x hx => ?_) (le_inf ax.U₂_le ax.U₂_le_Mw)
  obtain ⟨hxM, hxw⟩ := mem_inf.mp hx
  obtain ⟨y, h⟩ := ax.hAct_of_mem hxM
  obtain ⟨y', h'⟩ := ax.hAct_of_mem_Mw hxw
  obtain ⟨-, hy, -⟩ := HAct.unique ax.heis.sec.two h h'
  have h0 : HAct φ t x 0 0 0 := h.congr rfl hy rfl
  refine mem_U₂_of_mem_ZP (ax.mem_ZP_of_hAct hxM h0)
    (ax.mem_ZP_of_hAct (mem_map_conj_inv_iff.mp hxw) ?_)
  exact hAct_w_conj ax.heis.sec.two h0

theorem le_normalizer_Mw [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    M ≤ normalizer (𝐌w : Set G) := fun m hm =>
  mem_normalizer_of_conj_le fun x hx => by
    have e : m * x * m⁻¹ = (m * x * m⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact mul_mem (ax.U₂_le_Mw (ax.comm_mem_U₂ hm hx)) hx

theorem coe_M₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    (M : Set G) * (𝐌w : Set G) = 𝐌₂ :=
  (coe_mul_of_left_le_normalizer_right _ _ ax.le_normalizer_Mw).symm

theorem card_Mw (ax : AxisHyp L K n φ TG t M) : Nat.card 𝐌w = (2 ^ n) ^ 3 := by
  rw [card_map_of_injective (MulAut.conj _).injective, ax.card]

theorem card_U₂ (ax : AxisHyp L K n φ TG t M) : Nat.card 𝐔₂ = 2 ^ n :=
  (card_U φ Axis.two).trans ax.heis.sec.two.card_K

theorem card_ZP (ax : AxisHyp L K n φ TG t M) : Nat.card 𝐙 = (2 ^ n) ^ 2 := by
  rw [card_pull_ZP, ax.heis.sec.two.card_K]

theorem card_A₂ (ax : AxisHyp L K n φ TG t M) : Nat.card 𝐀₂ = (2 ^ n) ^ 3 := by
  rw [card_pull_A₂, ax.heis.sec.two.card_K]

theorem card_P (ax : AxisHyp L K n φ TG t M) : Nat.card 𝐏 = (2 ^ n) ^ 4 := by
  rw [card_pull_P, ax.heis.sec.two.card_K]

theorem card_M₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    Nat.card 𝐌₂ = (2 ^ n) ^ 5 := by
  have h := card_sup_mul_card_inf ax.le_normalizer_Mw
  rw [ax.M_inf_Mw, ax.card, ax.card_Mw, ax.card_U₂] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ n) (by rw [h]; ring)

theorem A₂_le_M₂ (ax : AxisHyp L K n φ TG t M) : 𝐀₂ ≤ 𝐌₂ := fun a ha => by
  obtain ⟨z, hz, z', hz', rfl⟩ := exists_mul_of_mem_A₂ ha
  exact mul_mem (mem_sup_left (ax.ZP_le hz))
    (mem_sup_right (mem_map_conj_inv_iff.mpr (ax.ZP_le hz')))

theorem M₂_le_D₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : 𝐌₂ ≤ 𝐃₂ :=
  sup_le ax.le_D₂ ax.Mw_le_D₂

theorem M₂_le_S [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : 𝐌₂ ≤ 𝐒 := fun _ hx =>
  mem_sup_right (ax.M₂_le_D₂ hx)

theorem exists_of_mem_M₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {x : G}
    (hx : x ∈ 𝐌₂) : ∃ m ∈ M, ∃ m' ∈ 𝐌w, ∃ a b : K, m * m' = x ∧ HAct φ t m 0 b 0 ∧
      HAct φ t m' a 0 0 ∧ HAct φ t x a b 0 := by
  rw [← SetLike.mem_coe, ← ax.coe_M₂] at hx
  obtain ⟨m, hm, m', hm', rfl⟩ := hx
  obtain ⟨b, hb⟩ := ax.hAct_of_mem hm
  obtain ⟨a, ha⟩ := ax.hAct_of_mem_Mw hm'
  exact ⟨m, hm, m', hm', a, b, rfl, hb, ha, (hb.mul ha).congr (by ring) (by ring) (by ring)⟩

theorem M₂_inf_B₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : 𝐌₂ ⊓ 𝐁₂ = 𝐀₂ := by
  refine le_antisymm (fun x hx => ?_) (le_inf ax.A₂_le_M₂ le_sup_right)
  obtain ⟨hx, hxB⟩ := mem_inf.mp hx
  obtain ⟨m, hm, m', hm', a, b, rfl, hb, ha, hx'⟩ := ax.exists_of_mem_M₂ hx
  obtain ⟨ha0, hb0, -⟩ := HAct.unique ax.heis.sec.two hx' (hAct_of_mem_B ax.heis.sec hxB)
  subst ha0 hb0
  have hmZ := ax.mem_ZP_of_hAct hm hb
  have hm'Z : 𝐰 * m' * 𝐰⁻¹ ∈ 𝐙 :=
    ax.mem_ZP_of_hAct (mem_map_conj_inv_iff.mp hm') (hAct_w_conj ax.heis.sec.two ha)
  exact mul_mem (pull_mono φ (center_le_rootA Axis.two) hmZ) (mem_A₂_of_conj_mem_ZP hm'Z)

theorem t_not_mem_M₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : t ∉ 𝐌₂ := fun h => by
  have ht : t ∈ 𝐀₂ := by
    rw [← ax.M₂_inf_B₂]
    exact mem_inf.mpr ⟨h, SecondHyp.t_mem_B⟩
  exact ax.heis.sec.two.t_not_mem (pull_le φ _ ht)

end AxisHyp

theorem D₂_le_normalizer [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {H : Subgroup G}
    (hA : 𝐀₂ ≤ H) (hHD : H ≤ 𝐃₂) : 𝐃₂ ≤ normalizer (H : Set G) := fun d hd =>
  mem_normalizer_of_conj_le fun h hH => by
    have hc : d * h * d⁻¹ * h⁻¹ ∈ 𝐀₂ := by
      rw [← (part_three hh).1, ← commutatorElement_def]
      exact commutator_mem_commutator hd (hHD hH)
    have e : d * h * d⁻¹ = (d * h * d⁻¹ * h⁻¹) * h := by group
    rw [e]
    exact mul_mem (hA hc) hH

theorem card_D₂ [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) :
    Nat.card 𝐃₂ = 2 * (2 ^ n) ^ 5 := by
  obtain ⟨_, _, e, -, -, hcard, -⟩ := hh.sec.exists_mulEquiv
  rw [card_eq_card_quotient_mul_card_subgroup (𝐁₂.subgroupOf 𝐃₂), hcard,
    Nat.card_congr (subgroupOfEquivOfLe hh.sec.B_le_D).toEquiv, card_B hh.sec.two,
    hh.sec.two.card_K]
  ring

theorem card_R [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) :
    Nat.card 𝐑 = 2 * (2 ^ n) ^ 5 := by
  obtain ⟨-, -, -, -, h, -⟩ := hh.main _ rfl
  exact h

theorem card_S [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) :
    Nat.card 𝐒 = 2 * (2 ^ n) ^ 6 := by
  obtain ⟨-, -, -, -, -, h, -⟩ := hh.main _ rfl
  exact h

theorem U₂_central [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) :
    ∀ z ∈ 𝐔₂, ∀ s ∈ 𝐒, z * s = s * z := fun _ hz _ hs => (comm_U₂ hh hs hz).symm

theorem t_mem_S (hh : HeisHyp L K n φ TG t) : t ∈ 𝐒 := mem_sup_left (t_mem_Q hh)

theorem comm_A₂ [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {a d : G} (ha : a ∈ 𝐀₂)
    (hd : d ∈ 𝐃₂) : a * d * a⁻¹ * d⁻¹ ∈ 𝐔₂ := by
  have h := (mem_upperCentralSeries_two_iff.mp ((upper_D₂ hh).ge ha)).2 d hd
  rwa [center_D₂ hh] at h

namespace AxisHyp

theorem D₂_semidirect [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    𝐌₂ ≤ 𝐃₂ ∧ (𝐌₂.subgroupOf 𝐃₂).Normal ∧ 𝐌₂ ⊓ zpowers t = ⊥ ∧ 𝐌₂ ⊔ zpowers t = 𝐃₂ := by
  have hN : 𝐃₂ ≤ normalizer (𝐌₂ : Set G) := D₂_le_normalizer ax.heis ax.A₂_le_M₂ ax.M₂_le_D₂
  have hinf : 𝐌₂ ⊓ zpowers t = ⊥ := inf_zpowers_eq_bot ax.heis.sec.two.t_mul_t ax.t_not_mem_M₂
  have ht : t ∈ 𝐃₂ := t_mem_D₂ ax.heis
  refine ⟨ax.M₂_le_D₂, (normal_subgroupOf_iff_le_normalizer ax.M₂_le_D₂).mpr hN, hinf, ?_⟩
  refine eq_of_le_of_card_ge (sup_le ax.M₂_le_D₂ (zpowers_le.mpr ht)) ?_
  have h := card_sup_mul_card_inf (A := zpowers t) (B := 𝐌₂) (zpowers_le.mpr (hN ht))
  rw [inf_comm (zpowers t) 𝐌₂, hinf, sup_comm (zpowers t) 𝐌₂, card_bot, mul_one,
    Nat.card_zpowers, ax.heis.hyp.setup.order_t, ax.card_M₂] at h
  exact ((card_D₂ ax.heis).trans h.symm).le

theorem comm_A₁ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {m a : G} (hm : m ∈ M)
    (ha : a ∈ 𝐀₁) : m * a = a * m :=
  (mem_center_map_iff.mp ((center_D₁ ax.heis).ge ha)).2 m (ax.le_D₁ hm)

theorem coe_M₁ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    (M : Set G) * (𝐀₁ : Set G) = 𝐌₁ :=
  (coe_mul_of_left_le_normalizer_right _ _ fun m hm => mem_normalizer_of_conj_le fun a ha => by
    rw [ax.comm_A₁ hm ha, mul_inv_cancel_right]
    exact ha).symm

theorem M₁_inf_D₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : 𝐌₁ ⊓ 𝐃₂ = M := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left ax.le_D₂)
  obtain ⟨hx, hxD⟩ := mem_inf.mp hx
  rw [← SetLike.mem_coe, ← ax.coe_M₁] at hx
  obtain ⟨m, hm, a, ha, rfl⟩ := hx
  have haD : a ∈ 𝐃₂ := by
    have := mul_mem (inv_mem (ax.le_D₂ hm)) hxD
    rwa [inv_mul_cancel_left] at this
  have haQ : a ∈ 𝐐 := (le_sup_right.trans (ax.heis.hyp.B_le_Q Axis.one)) ha
  have haB : a ∈ 𝐁₂ := by
    rw [← ax.heis.sec.inf_eq]
    exact mem_inf.mpr ⟨haD, mem_inf.mpr ⟨ax.heis.hyp.setup.Q_le_C haQ, (ax.heis.Q_le_N haQ).2⟩⟩
  have haA₂ : a ∈ 𝐀₂ := by
    rw [← zpowers_sup_inf_eq ax.heis.sec.two.t_mul_t (pull_le φ _) ax.heis.sec.two.t_not_mem
      (TwoCoreSetup.comm_pull φ ax.heis.sec.two)]
    exact mem_inf.mpr ⟨haB, pull_le φ _ ha⟩
  exact mul_mem hm (ax.ZP_le (mem_ZP_of_mem_A₁_A₂ φ ha haA₂))

theorem M₁_inf_M₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : 𝐌₁ ⊓ 𝐌₂ = M := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left le_sup_left)
  obtain ⟨h₁, h₂⟩ := mem_inf.mp hx
  rw [← ax.M₁_inf_D₂]
  exact mem_inf.mpr ⟨h₁, ax.M₂_le_D₂ h₂⟩

theorem M₂_comm [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    ∀ x ∈ 𝐌₂, ∀ y ∈ 𝐌₂, x * y * x⁻¹ * y⁻¹ ∈ 𝐔₂ :=
  comm_mod_of_sup (U₂_central ax.heis) ax.le_S ax.Mw_le_S
    (fun a ha a' ha' => by
      rw [ax.comm a ha a' ha', mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _)
    (fun _ ha _ hb => ax.comm_mem_U₂ ha hb)
    (fun b hb b' hb' => by
      rw [ax.Mw_comm hb hb', mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _)

theorem M₂_sq [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {x : G} (hx : x ∈ 𝐌₂) :
    x * x ∈ 𝐔₂ := by
  rw [← SetLike.mem_coe, ← ax.coe_M₂] at hx
  obtain ⟨m, hm, m', hm', rfl⟩ := hx
  have e : m * m' * (m * m') = (m * m' * m⁻¹ * m'⁻¹) * (m' * (m * m) * m') := by group
  rw [e, ax.mul_self m hm, mul_one, ax.Mw_mul_self hm', mul_one]
  exact ax.comm_mem_U₂ hm hm'

theorem four_le (ax : AxisHyp L K n φ TG t M) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) ax.heis.sec.two.two_le

theorem eq_M₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {X : Subgroup G}
    (hXD : X ≤ 𝐃₂) (hX : Nat.card X = (2 ^ n) ^ 5)
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ 𝐔₂) : X = 𝐌₂ := by
  by_contra hne
  have hh := ax.heis
  have hN : X ≤ normalizer (𝐌₂ : Set G) :=
    hXD.trans (D₂_le_normalizer hh ax.A₂_le_M₂ ax.M₂_le_D₂)
  have hprod := card_sup_mul_card_inf hN
  have hsupD : X ⊔ 𝐌₂ ≤ 𝐃₂ := sup_le hXD ax.M₂_le_D₂
  have hne' : ¬ X ⊔ 𝐌₂ ≤ 𝐌₂ := fun h =>
    hne (eq_of_le_of_card_ge (le_sup_left.trans h) (by rw [hX, ax.card_M₂]))
  have hcard : Nat.card (X ⊔ 𝐌₂ : Subgroup G) = 2 * (2 ^ n) ^ 5 := by
    obtain ⟨k, hk⟩ := card_dvd_of_le (le_sup_right : 𝐌₂ ≤ X ⊔ 𝐌₂)
    obtain ⟨j, hj⟩ := card_dvd_of_le hsupD
    rw [card_D₂ hh, hk, ax.card_M₂] at hj
    have hq : 0 < (2 ^ n) ^ 5 := by positivity
    have hkj : k * j = 2 := by
      have : (2 ^ n) ^ 5 * (k * j) = (2 ^ n) ^ 5 * 2 := by rw [← mul_assoc, ← hj]; ring
      exact Nat.eq_of_mul_eq_mul_left hq this
    have hk2 : k ∣ 2 := ⟨j, hkj.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with h1 | h2
    · exfalso
      apply hne'
      refine (eq_of_le_of_card_ge (le_sup_right : 𝐌₂ ≤ X ⊔ 𝐌₂) ?_).ge
      rw [hk, h1, mul_one]
    · rw [hk, h2, ax.card_M₂, mul_comm]
  have hsup : X ⊔ 𝐌₂ = 𝐃₂ :=
    eq_of_le_of_card_ge hsupD (by rw [hcard, card_D₂ hh])
  have hinfA : X ⊓ 𝐌₂ ≤ 𝐀₂ := by
    intro x hx
    obtain ⟨hxX, hxM⟩ := mem_inf.mp hx
    have hxD := hXD hxX
    have hc : ∀ y ∈ X ⊔ 𝐌₂, x * y * x⁻¹ * y⁻¹ ∈ 𝐔₂ :=
      comm_mod_sup (U₂_central hh) (mem_sup_right hxD) (fun _ hy => mem_sup_right (hXD hy))
        ax.M₂_le_S (hXc x hxX) (ax.M₂_comm x hxM)
    rw [hsup] at hc
    rw [← upper_D₂ hh, mem_upperCentralSeries_two_iff, center_D₂ hh]
    exact ⟨hxD, hc⟩
  have hle := card_le_of_le hinfA
  rw [ax.card_A₂] at hle
  rw [hcard, hX, ax.card_M₂] at hprod
  have h4 := ax.four_le
  have hq3 : 0 < (2 ^ n) ^ 3 := by positivity
  have key : (2 ^ n) ^ 5 * (2 ^ n) ^ 5 ≤ 2 * (2 ^ n) ^ 5 * (2 ^ n) ^ 3 := by
    rw [← hprod]
    exact Nat.mul_le_mul_left _ hle
  have key' : (2 ^ n) ^ 2 ≤ 2 := by
    have e1 : (2 ^ n) ^ 5 * (2 ^ n) ^ 5 = ((2 ^ n) ^ 2) * ((2 ^ n) ^ 5 * (2 ^ n) ^ 3) := by ring
    have e2 : 2 * (2 ^ n) ^ 5 * (2 ^ n) ^ 3 = 2 * ((2 ^ n) ^ 5 * (2 ^ n) ^ 3) := by ring
    rw [e1, e2] at key
    exact Nat.le_of_mul_le_mul_right key (by positivity)
  nlinarith

end AxisHyp

theorem conj_mem_U₂_of_normalizer [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {g : G}
    (hg : g ∈ normalizer (𝐃₂ : Set G)) {u : G} (hu : u ∈ 𝐔₂) : g * u * g⁻¹ ∈ 𝐔₂ := by
  rw [← center_D₂ hh] at hu ⊢
  obtain ⟨huD, huc⟩ := mem_center_map_iff.mp hu
  refine mem_center_map_iff.mpr ⟨(mem_normalizer_iff.mp hg u).mp huD, fun d hd => ?_⟩
  have hd' : g⁻¹ * d * g ∈ 𝐃₂ := (mem_normalizer_iff''.mp hg d).mp hd
  have h := huc _ hd'
  calc d * (g * u * g⁻¹) = g * ((g⁻¹ * d * g) * u) * g⁻¹ := by group
    _ = g * (u * (g⁻¹ * d * g)) * g⁻¹ := by rw [h]
    _ = g * u * g⁻¹ * d := by group

namespace AxisHyp

theorem normalizer_D₂_le [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    normalizer (𝐃₂ : Set G) ≤ normalizer (𝐌₂ : Set G) := by
  intro g hg
  have hX := ax.eq_M₂ (X := 𝐌₂.map (MulAut.conj g).toMonoidHom) ?_ ?_ ?_
  · refine mem_normalizer_of_conj_le fun x hx => ?_
    rw [← hX]
    exact ⟨x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp hg x).mp (ax.M₂_le_D₂ hx)
  · rw [card_map_of_injective (MulAut.conj g).injective, ax.card_M₂]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e : g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ =
        g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ := by group
    rw [e]
    exact conj_mem_U₂_of_normalizer ax.heis hg (ax.M₂_comm x hx y hy)

theorem conj_mem_M₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {s x : G}
    (hs : s ∈ 𝐒) (hx : x ∈ 𝐌₂) : s * x * s⁻¹ ∈ 𝐌₂ :=
  (mem_normalizer_iff.mp (ax.normalizer_D₂_le (le_normalizer_pCore_map (ax.heis.S_le_N₂ hs))) x).mp
    hx

theorem M₂_normal [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    𝐌₂ ≤ 𝐒 ∧ (𝐌₂.subgroupOf 𝐒).Normal :=
  ⟨ax.M₂_le_S, (normal_subgroupOf_iff_le_normalizer ax.M₂_le_S).mpr fun _ hs =>
    mem_normalizer_of_conj_le fun _ hx => ax.conj_mem_M₂ hs hx⟩

theorem characteristic [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    (𝐌₂.subgroupOf 𝐃₂).Characteristic := by
  rw [characteristic_iff_map_eq]
  intro α
  have hcen : ∀ u : 𝐃₂, (u : G) ∈ 𝐔₂ → ((α u : 𝐃₂) : G) ∈ 𝐔₂ := by
    intro u hu
    rw [← center_D₂ ax.heis] at hu ⊢
    obtain ⟨z, hz, hzu⟩ := hu
    obtain rfl : z = u := Subtype.ext hzu
    refine ⟨α z, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff] at hz ⊢
    intro y
    have h := hz (α.symm y)
    calc y * α z = α (α.symm y * z) := by rw [map_mul, MulEquiv.apply_symm_apply]
      _ = α (z * α.symm y) := by rw [h]
      _ = α z * y := by rw [map_mul, MulEquiv.apply_symm_apply]
  have hX := ax.eq_M₂ (X := ((𝐌₂.subgroupOf 𝐃₂).map α.toMonoidHom).map 𝐃₂.subtype)
    (map_subtype_le _) ?_ ?_
  · apply map_injective 𝐃₂.subtype_injective
    rw [hX, subgroupOf_map_subtype, inf_of_le_left ax.M₂_le_D₂]
  · rw [card_map_of_injective 𝐃₂.subtype_injective, card_map_of_injective α.injective,
      Nat.card_congr (subgroupOfEquivOfLe ax.M₂_le_D₂).toEquiv, ax.card_M₂]
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf] at ha hb
    have h := hcen (a * b * a⁻¹ * b⁻¹) (by simpa using ax.M₂_comm _ ha _ hb)
    simpa [map_mul, map_inv] using h

theorem t_le_normalizer_M₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    zpowers t ≤ normalizer (𝐌₂ : Set G) :=
  zpowers_le.mpr (mem_normalizer_of_conj_le fun _ hx => ax.conj_mem_M₂ (t_mem_S ax.heis) hx)

theorem mem_B₂_of_sq [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {x : G} (hx : x ∈ 𝐃₂)
    (hxM : x ∉ 𝐌₂) (hsq : x * x ∈ 𝐔₂) : x ∈ 𝐁₂ := by
  have hS := ax.heis.sec.two
  obtain ⟨-, -, -, hsup⟩ := ax.D₂_semidirect
  rw [← hsup, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ ax.t_le_normalizer_M₂]
    at hx
  obtain ⟨m, hm, c, hc, rfl⟩ := Set.mem_mul.mp hx
  have hc' : c = 1 ∨ c = t := by
    obtain ⟨j, rfl⟩ := hc
    exact zpow_eq_one_or_eq hS.t_mul_t j
  rcases hc' with hc1 | hct
  · rw [hc1, mul_one] at hxM
    exact absurd hm hxM
  · rw [hct] at hxM hsq ⊢
    obtain ⟨a, b, hab⟩ := hAct_of_mem_D ax.heis.sec (ax.M₂_le_D₂ hm)
    have hc := commutator_t_eq hS hab
    have hm2 := ax.M₂_sq hm
    have htm : t * (m * m) * t = m * m := by
      rw [comm_U₂ ax.heis (t_mem_S ax.heis) hm2, mul_assoc, hS.t_mul_t, mul_one]
    have hmt : m * t * (m * t) = ((φ.symm (uElt a b 0 0) : L) : G) * (t * (m * m) * t) := by
      rw [← hc]
      group
    rw [hmt, htm] at hsq
    have hu : ((φ.symm (uElt a b 0 0) : L) : G) ∈ 𝐔₂ := by
      have := mul_mem hsq (inv_mem hm2)
      rwa [mul_inv_cancel_right] at this
    obtain ⟨c', hc'⟩ := symm_mem_pull.mp hu
    obtain ⟨ha, hb, -, -⟩ := uElt_inj hc'
    subst ha hb
    exact mul_mem (mem_B₂_of_hAct ax.heis (SecondHyp.D_le_N (ax.M₂_le_D₂ hm)) hab)
      SecondHyp.t_mem_B

theorem le_B₂_or_le_M₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {F : Subgroup G}
    (hFD : F ≤ 𝐃₂) (hFc : ∀ x ∈ F, ∀ y ∈ F, x * y * x⁻¹ * y⁻¹ ∈ 𝐔₂)
    (hFs : ∀ x ∈ F, x * x ∈ 𝐔₂) : F ≤ 𝐁₂ ∨ F ≤ 𝐌₂ := by
  have hh := ax.heis
  have hS := hh.sec.two
  by_cases hF : F ≤ 𝐌₂
  · exact Or.inr hF
  left
  obtain ⟨f, hfF, hfM⟩ := IsConcreteLE.not_le_iff_exists.mp hF
  have hfB := ax.mem_B₂_of_sq (hFD hfF) hfM (hFs f hfF)
  have ha : t * f ∈ 𝐀₂ := by
    rcases (mem_zpowers_sup_iff hS.t_mul_t (TwoCoreSetup.comm_pull φ hS)).mp hfB with h | h
    · exact absurd (ax.A₂_le_M₂ h) hfM
    · exact h
  intro y hy
  by_cases hyM : y ∈ 𝐌₂
  · have hyD := hFD hy
    have hyS : y ∈ 𝐒 := mem_sup_right hyD
    obtain ⟨a, b, hab⟩ := hAct_of_mem_D hh.sec hyD
    have hfS : f ∈ 𝐒 := mem_sup_right (hFD hfF)
    have haS : t * f ∈ 𝐒 := mem_sup_right (hh.sec.B_le_D (mem_sup_right ha))
    have c₁ : y * (t * f) * y⁻¹ * (t * f)⁻¹ ∈ 𝐔₂ := by
      have := inv_mem (comm_A₂ hh ha hyD)
      rwa [show (t * f * y * (t * f)⁻¹ * y⁻¹)⁻¹ = y * (t * f) * y⁻¹ * (t * f)⁻¹ by group] at this
    have c₂ := hFc y hy f hfF
    have e : y * t * y⁻¹ * t⁻¹ = (y * (t * f) * y⁻¹ * (t * f)⁻¹) *
        ((t * f) * (f⁻¹ * (y * f * y⁻¹ * f⁻¹)⁻¹ * f) * (t * f)⁻¹) := by group
    have e₁ : f⁻¹ * (y * f * y⁻¹ * f⁻¹)⁻¹ * f = (y * f * y⁻¹ * f⁻¹)⁻¹ := by
      rw [mul_assoc, U₂_central hh _ (inv_mem c₂) f hfS, inv_mul_cancel_left]
    have e₂ : (t * f) * (y * f * y⁻¹ * f⁻¹)⁻¹ * (t * f)⁻¹ = (y * f * y⁻¹ * f⁻¹)⁻¹ := by
      rw [← U₂_central hh _ (inv_mem c₂) _ haS, mul_inv_cancel_right]
    rw [e₁, e₂] at e
    have hyt : y * t * y⁻¹ * t⁻¹ ∈ 𝐔₂ := by
      rw [e]
      exact mul_mem c₁ (inv_mem c₂)
    rw [commutator_t_eq hS hab] at hyt
    obtain ⟨c', hc'⟩ := symm_mem_pull.mp hyt
    obtain ⟨ha0, hb0, -, -⟩ := uElt_inj hc'
    subst ha0 hb0
    exact mem_B₂_of_hAct hh (SecondHyp.D_le_N hyD) hab
  · exact ax.mem_B₂_of_sq (hFD hy) hyM (hFs y hy)

theorem normalizer_B₂_eq [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    normalizer (𝐁₂ : Set G) = normalizer (𝐃₂ : Set G) := by
  refine le_antisymm (fun g hg => le_normalizer_pCore_map hg) fun g hg => ?_
  have hM := ax.normalizer_D₂_le hg
  have hX := ax.le_B₂_or_le_M₂ (F := 𝐁₂.map (MulAut.conj g).toMonoidHom) ?_ ?_ ?_
  · rcases hX with hX | hX
    · exact mem_normalizer_of_conj_le fun b hb => hX ⟨b, hb, rfl⟩
    · exfalso
      have h1 : g * t * g⁻¹ ∈ 𝐌₂ := hX ⟨t, SecondHyp.t_mem_B, rfl⟩
      have h2 := (mem_normalizer_iff''.mp hM (g * t * g⁻¹)).mp h1
      rw [show g⁻¹ * (g * t * g⁻¹) * g = t by group] at h2
      exact ax.t_not_mem_M₂ h2
  · rintro _ ⟨b, hb, rfl⟩
    exact (mem_normalizer_iff.mp hg b).mp (ax.heis.sec.B_le_D hb)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 : x * y * x⁻¹ * y⁻¹ = 1 := by
      rw [B_comm φ ax.heis.sec.two hx hy]
      group
    have e : g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ =
        g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ := by group
    rw [e, h1, mul_one, mul_inv_cancel]
    exact one_mem _
  · rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e : g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
    rw [e, ax.heis.hyp.mul_self_of_mem_B Axis.two hx, mul_one, mul_inv_cancel]
    exact one_mem _

theorem center_M₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    (center 𝐌₂).map 𝐌₂.subtype = 𝐔₂ := by
  have hh := ax.heis
  have hS := hh.sec.two
  have hinj := coord_injective φ hS.t_mul_t (fun _ hx => hS.comm hx) hS.t_not_mem
  apply le_antisymm
  · intro z hz
    obtain ⟨hzM, hzc⟩ := mem_center_map_iff.mp hz
    obtain ⟨x, y, h⟩ := hAct_of_mem_D hh.sec (ax.M₂_le_D₂ hzM)
    have hfix : ∀ X Y Z : K, coord φ t ((0, X, Y, Z) : QGSpace K) ∈ 𝐌₂ →
        coord φ t ((0, X + 0 * Y, Y, Z + x * X + (y + 0 * x) * Y + 0 * Y ^ 2) : QGSpace K) =
          coord φ t ((0, X, Y, Z) : QGSpace K) := by
      intro X Y Z hm
      rw [← conj_coord_zero hS h, ← hzc _ hm, mul_inv_cancel_right]
    have h1 : coord φ t ((0, 1, 0, 0) : QGSpace K) ∈ 𝐌₂ :=
      mem_sup_left (ax.ZP_le (coord_zero_mem_center_iff.mpr rfl))
    have h2 : coord φ t ((0, 0, 1, 0) : QGSpace K) ∈ 𝐌₂ := by
      refine mem_sup_right (mem_map_conj_inv_iff.mpr (ax.ZP_le ?_))
      rw [coord_zero_eq, w_conj_uElt]
      exact symm_mem_pull.mpr ⟨1, 0 + 0 * 1, rfl⟩
    have e1 := hinj (hfix 1 0 0 h1)
    have e2 := hinj (hfix 0 1 0 h2)
    simp only [Prod.mk.injEq] at e1 e2
    have hx : x = 0 := by linear_combination e1.2.2.2
    have hy : y = 0 := by linear_combination e2.2.2.2
    subst hx hy
    have hzA : z ∈ 𝐀₂ := by
      rw [← ax.M₂_inf_B₂]
      exact mem_inf.mpr ⟨hzM, mem_B₂_of_hAct hh (SecondHyp.D_le_N (ax.M₂_le_D₂ hzM)) h⟩
    rw [← center_D₂ hh]
    refine mem_center_map_iff.mpr ⟨ax.M₂_le_D₂ hzM, fun d hd => ?_⟩
    obtain ⟨-, -, -, hsup⟩ := ax.D₂_semidirect
    have hle : 𝐌₂ ⊔ zpowers t ≤ centralizer ({z} : Set G) :=
      sup_le (fun y hy => mem_centralizer_singleton_iff.mpr (hzc y hy))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hS.comm (pull_le φ _ hzA))))
    rw [hsup] at hle
    exact mem_centralizer_singleton_iff.mp (hle hd)
  · intro u hu
    exact mem_center_map_iff.mpr ⟨ax.A₂_le_M₂ (pull_mono φ rootU₂_le_radA2 hu),
      fun y hy => comm_U₂ hh (ax.M₂_le_S hy) hu⟩

theorem exists_not_mem_ZP [Finite G] (ax : AxisHyp L K n φ TG t M) : ∃ m ∈ M, m ∉ 𝐙 := by
  by_contra h
  have hMZ : M ≤ 𝐙 := fun m hm => by
    by_contra hz
    exact h ⟨m, hm, hz⟩
  have hle := card_le_of_le hMZ
  rw [ax.card, ax.card_ZP] at hle
  have h4 := ax.four_le
  have : (2 ^ n) ^ 2 * 1 < (2 ^ n) ^ 2 * 2 ^ n :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
  nlinarith

theorem commutator_M₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    ⁅𝐌₂, 𝐌₂⁆ = 𝐔₂ ∧ closure {x : G | ∃ y ∈ 𝐌₂, x = y * y} = 𝐔₂ := by
  have hh := ax.heis
  have hS := hh.sec.two
  have hsq : closure {x : G | ∃ y ∈ 𝐌₂, x = y * y} ≤ 𝐔₂ :=
    (closure_le _).mpr (by rintro _ ⟨y, hy, rfl⟩; exact ax.M₂_sq hy)
  have hcomm : ⁅𝐌₂, 𝐌₂⁆ ≤ 𝐔₂ := by
    rw [commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact ax.M₂_comm x hx y hy
  have hU : 𝐔₂ ≤ ⁅𝐌₂, 𝐌₂⁆ := by
    obtain ⟨m, hm, hmZ⟩ := ax.exists_not_mem_ZP
    obtain ⟨y, h⟩ := ax.hAct_of_mem hm
    have hy : y ≠ 0 := by
      rintro rfl
      exact hmZ (ax.mem_ZP_of_hAct hm h)
    intro u hu
    obtain ⟨a', ha', rfl⟩ := exists_eq_symm_of_mem_pull hu
    change a' ∈ rootU₂ K at ha'
    obtain ⟨c, rfl⟩ := ha'
    have hA : coord φ t ((0, 0, c / y, 0) : QGSpace K) ∈ 𝐌₂ := ax.A₂_le_M₂ (coord_zero_mem_A _ _ _)
    have e := coord_mul_conj_inv hS (conj_coord_zero hS h 0 (c / y) 0)
    have e' : ((0, 0, c / y, 0) : QGSpace K) +
        (0, 0 + 0 * (c / y), c / y, 0 + 0 * 0 + (y + 0 * 0) * (c / y) + 0 * (c / y) ^ 2) =
          (0, 0, 0, c) := by
      simp only [Prod.mk_add_mk, Prod.mk.injEq]
      refine ⟨by decide, by ring, CharTwo.add_self_eq_zero _, by field_simp; ring⟩
    have e'' : coord φ t ((0, 0, 0, c) : QGSpace K) = ((φ.symm (uElt 0 0 c 0) : L) : G) := by
      rw [coord_zero_eq, mul_zero, add_zero]
    rw [e', e''] at e
    rw [← e, ← commutatorElement_def]
    exact commutator_mem_commutator hA (mem_sup_left hm)
  exact ⟨le_antisymm hcomm hU, le_antisymm hsq (hU.trans (commutator_le_closure_sq _))⟩

theorem M₁_le_S [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : 𝐌₁ ≤ 𝐒 := fun _ hx =>
  ax.heis.R_le_S (mem_sup_right (ax.M₁_le_D₁ hx))

theorem S_le_normalizer₁ [Finite G] (ax : AxisHyp L K n φ TG t M) :
    𝐒 ≤ normalizer (𝐌₁ : Set G) := fun s hs =>
  mem_normalizer_of_conj_le fun x hx => ax.conj₁ s hs x hx

theorem coe_V [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    (𝐌₁ : Set G) * (𝐌₂ : Set G) = 𝐕 :=
  (coe_mul_of_right_le_normalizer_left _ _ (ax.M₂_le_S.trans ax.S_le_normalizer₁)).symm

theorem card_V [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : Nat.card 𝐕 = (2 ^ n) ^ 6 := by
  have h := card_sup_mul_card_inf (A := 𝐌₂) (B := 𝐌₁) (ax.M₂_le_S.trans ax.S_le_normalizer₁)
  rw [sup_comm 𝐌₂ 𝐌₁, inf_comm 𝐌₂ 𝐌₁, ax.M₁_inf_M₂, ax.card, ax.card_M₂, ax.card₁] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < (2 ^ n) ^ 3) (by rw [h]; ring)

theorem V_inf_D₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : 𝐕 ⊓ 𝐃₂ = 𝐌₂ := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right ax.M₂_le_D₂)
  obtain ⟨hx, hxD⟩ := mem_inf.mp hx
  rw [← SetLike.mem_coe, ← ax.coe_V] at hx
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Set.mem_mul.mp hx
  have h1 : m₁ ∈ 𝐃₂ := by
    have := mul_mem hxD (inv_mem (ax.M₂_le_D₂ hm₂))
    rwa [mul_inv_cancel_right] at this
  have h2 : m₁ ∈ M := by
    rw [← ax.M₁_inf_D₂]
    exact mem_inf.mpr ⟨hm₁, h1⟩
  exact mul_mem (mem_sup_left h2) hm₂

theorem t_not_mem_V [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : t ∉ 𝐕 := fun h => by
  apply ax.t_not_mem_M₂
  rw [← ax.V_inf_D₂]
  exact mem_inf.mpr ⟨h, t_mem_D₂ ax.heis⟩

theorem V_le_S [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : 𝐕 ≤ 𝐒 :=
  sup_le ax.M₁_le_S ax.M₂_le_S

theorem conj_mem_V [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {s x : G} (hs : s ∈ 𝐒)
    (hx : x ∈ 𝐕) : s * x * s⁻¹ ∈ 𝐕 :=
  conj_mem_sup (fun y hy => ax.conj₁ s hs y hy) (fun _ hy => ax.conj_mem_M₂ hs hy) hx

theorem S_semidirect [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    𝐕 ⊓ zpowers t = ⊥ ∧ 𝐕 ⊔ zpowers t = 𝐒 := by
  have hinf := inf_zpowers_eq_bot ax.heis.sec.two.t_mul_t ax.t_not_mem_V
  have htS := t_mem_S ax.heis
  refine ⟨hinf, eq_of_le_of_card_ge (sup_le ax.V_le_S (zpowers_le.mpr htS)) ?_⟩
  have h := card_sup_mul_card_inf (A := zpowers t) (B := 𝐕)
    (zpowers_le.mpr (mem_normalizer_of_conj_le fun _ hx => ax.conj_mem_V htS hx))
  rw [inf_comm (zpowers t) 𝐕, hinf, sup_comm (zpowers t) 𝐕, card_bot, mul_one,
    Nat.card_zpowers, ax.heis.hyp.setup.order_t, ax.card_V] at h
  exact ((card_S ax.heis).trans h.symm).le

theorem P_le_S : 𝐏 ≤ 𝐒 := le_sup_left.trans le_sup_left

theorem coe_E [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    (M : Set G) * (𝐏 : Set G) = 𝐄 :=
  (coe_mul_of_right_le_normalizer_left _ _ (P_le_S.trans ax.S_le_normalizer)).symm

theorem M_inf_P [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : M ⊓ 𝐏 = 𝐙 := by
  refine le_antisymm (fun x hx => ?_) (le_inf ax.ZP_le Setup.ZP_le_PG)
  obtain ⟨hxM, hxP⟩ := mem_inf.mp hx
  obtain ⟨y, h⟩ := ax.hAct_of_mem hxM
  obtain ⟨δ, hδ⟩ := ax.heis.hAct_of_mem_Q (mem_sup_left hxP : x ∈ 𝐐)
  obtain ⟨-, hy, -⟩ := HAct.unique ax.heis.sec.two h hδ
  exact ax.mem_ZP_of_hAct hxM (h.congr rfl hy rfl)

theorem card_E [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : Nat.card 𝐄 = (2 ^ n) ^ 5 := by
  have h := card_sup_mul_card_inf (A := 𝐏) (B := M) (P_le_S.trans ax.S_le_normalizer)
  rw [sup_comm 𝐏 M, inf_comm 𝐏 M, ax.M_inf_P, ax.card_P, ax.card_ZP, ax.card] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < (2 ^ n) ^ 2) (by rw [h]; ring)

theorem E_le_V [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : 𝐄 ≤ 𝐕 := by
  refine sup_le (le_sup_left.trans le_sup_left) ?_
  rw [pull_P_eq]
  exact sup_le (le_sup_right.trans le_sup_left) (ax.A₂_le_M₂.trans le_sup_right)

theorem E_le_R (ax : AxisHyp L K n φ TG t M) : 𝐄 ≤ 𝐑 :=
  sup_le (fun _ hm => mem_sup_right (ax.le_D₁ hm)) (le_sup_left.trans le_sup_left)

theorem t_le_normalizer_E [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    zpowers t ≤ normalizer (𝐄 : Set G) :=
  zpowers_le.mpr (mem_normalizer_of_conj_le fun _ hx => conj_mem_sup
    (fun _ hm => ax.conj_mem (t_mem_S ax.heis) hm)
    (fun p hp => by
      rw [ax.heis.sec.two.comm (pull_le φ _ hp), mul_inv_cancel_right]
      exact hp) hx)

theorem R_semidirect [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    𝐄 ⊓ zpowers t = ⊥ ∧ 𝐄 ⊔ zpowers t = 𝐑 := by
  have hinf := inf_zpowers_eq_bot ax.heis.sec.two.t_mul_t fun h => ax.t_not_mem_V (ax.E_le_V h)
  have htR : t ∈ 𝐑 := mem_sup_left (t_mem_Q ax.heis)
  refine ⟨hinf, eq_of_le_of_card_ge (sup_le ax.E_le_R (zpowers_le.mpr htR)) ?_⟩
  have h := card_sup_mul_card_inf (A := zpowers t) (B := 𝐄) ax.t_le_normalizer_E
  rw [inf_comm (zpowers t) 𝐄, hinf, sup_comm (zpowers t) 𝐄, card_bot, mul_one,
    Nat.card_zpowers, ax.heis.hyp.setup.order_t, ax.card_E] at h
  exact ((card_R ax.heis).trans h.symm).le

theorem V_inf_R [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) : 𝐕 ⊓ 𝐑 = 𝐄 := by
  refine le_antisymm (fun x hx => ?_) (le_inf ax.E_le_V ax.E_le_R)
  obtain ⟨hxV, hxR⟩ := mem_inf.mp hx
  rw [← ax.R_semidirect.2, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left _ _ ax.t_le_normalizer_E] at hxR
  obtain ⟨e, he, c, hc, rfl⟩ := Set.mem_mul.mp hxR
  have hc' : c = 1 ∨ c = t := by
    obtain ⟨j, rfl⟩ := hc
    exact zpow_eq_one_or_eq ax.heis.sec.two.t_mul_t j
  rcases hc' with hc1 | hct
  · rw [hc1, mul_one]
    exact he
  · exfalso
    rw [hct] at hxV
    apply ax.t_not_mem_V
    have := mul_mem (inv_mem (ax.E_le_V he)) hxV
    rwa [inv_mul_cancel_left] at this

end AxisHyp

theorem conj_mem_R [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {s r : G} (hs : s ∈ 𝐒)
    (hr : r ∈ 𝐑) : s * r * s⁻¹ ∈ 𝐑 := by
  obtain ⟨x, y, d, h⟩ := hh.exists_hAct_of_mem_S hs
  have hrS := hh.R_le_S hr
  obtain ⟨x', y', d', h'⟩ := hh.exists_hAct_of_mem_S hrS
  obtain rfl := (hh.mem_R_iff hrS h').mp hr
  exact (hh.mem_R_iff (mul_mem (mul_mem hs hrS) (inv_mem hs)) (hAct_conj h h')).mpr rfl

namespace AxisHyp

theorem E_normal [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    𝐄 ≤ 𝐒 ∧ (𝐄.subgroupOf 𝐒).Normal := by
  have hle : 𝐄 ≤ 𝐒 := ax.E_le_V.trans ax.V_le_S
  refine ⟨hle, (normal_subgroupOf_iff_le_normalizer hle).mpr fun s hs =>
    mem_normalizer_of_conj_le fun x hx => ?_⟩
  rw [← ax.V_inf_R] at hx ⊢
  obtain ⟨hxV, hxR⟩ := mem_inf.mp hx
  exact mem_inf.mpr ⟨ax.conj_mem_V hs hxV, conj_mem_R ax.heis hs hxR⟩

theorem le_normalizer_A₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    M ≤ normalizer (𝐀₂ : Set G) := fun _ hm =>
  mem_normalizer_of_conj_le fun _ ha =>
    ax.heis.sec.conj_mem_A (SecondHyp.D_le_N (ax.le_D₂ hm)) ha

theorem coe_M₀ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    (M : Set G) * (𝐀₂ : Set G) = 𝐌₀ :=
  (coe_mul_of_left_le_normalizer_right _ _ ax.le_normalizer_A₂).symm

theorem M_inf_A₂ (ax : AxisHyp L K n φ TG t M) : M ⊓ 𝐀₂ = 𝐙 :=
  le_antisymm (fun _ hx => ax.mem_ZP_of_mem_B₂ (mem_inf.mp hx).1 (mem_sup_right (mem_inf.mp hx).2))
    (le_inf ax.ZP_le (pull_mono φ (center_le_rootA Axis.two)))

theorem card_M₀ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    Nat.card 𝐌₀ = (2 ^ n) ^ 4 := by
  have h := card_sup_mul_card_inf ax.le_normalizer_A₂
  rw [ax.M_inf_A₂, ax.card, ax.card_A₂, ax.card_ZP] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < (2 ^ n) ^ 2) (by rw [h]; ring)

theorem exists_of_mem_M₀ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {x : G}
    (hx : x ∈ 𝐌₀) : ∃ m ∈ M, ∃ a ∈ 𝐀₂, ∃ y : K, m * a = x ∧ HAct φ t m 0 y 0 ∧
      HAct φ t x 0 y 0 := by
  rw [← SetLike.mem_coe, ← ax.coe_M₀] at hx
  obtain ⟨m, hm, a, ha, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨y, h⟩ := ax.hAct_of_mem hm
  exact ⟨m, hm, a, ha, y, rfl, h, (h.mul (hAct_of_mem_B ax.heis.sec (mem_sup_right ha))).congr
    (by ring) (by ring) (by ring)⟩

theorem M₀_inf [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    𝐌₀ ⊓ 𝐌₀.map (MulAut.conj 𝐰⁻¹).toMonoidHom = 𝐀₂ := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right fun a ha =>
    mem_map_conj_inv_iff.mpr (mem_sup_right (w_conj_mem_A₂ ha)))
  obtain ⟨hx, hxw⟩ := mem_inf.mp hx
  obtain ⟨m, hm, a, ha, y, rfl, hmy, hxy⟩ := ax.exists_of_mem_M₀ hx
  obtain ⟨_, _, _, _, y', _, _, hw⟩ := ax.exists_of_mem_M₀ (mem_map_conj_inv_iff.mp hxw)
  have hw' := hAct_w_conj ax.heis.sec.two hw
  rw [w_conj_conj] at hw'
  obtain ⟨-, hy, -⟩ := HAct.unique ax.heis.sec.two hxy hw'
  exact mul_mem
    (pull_mono φ (center_le_rootA Axis.two) (ax.mem_ZP_of_hAct hm (hmy.congr rfl hy rfl))) ha

theorem J₀_le_Mw [Finite G] (hJ : pull φ (diagTorus K) ≤ normalizer (M : Set G)) :
    pull φ (diagTorus K) ≤ normalizer (𝐌w : Set G) := fun j hj =>
  mem_normalizer_of_conj_le fun x hx => mem_map_conj_inv_iff.mpr (by
    have e : 𝐰 * (j * x * j⁻¹) * 𝐰⁻¹ =
        (𝐰 * j * 𝐰⁻¹) * (𝐰 * x * 𝐰⁻¹) * (𝐰 * j * 𝐰⁻¹)⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.mp (hJ (w_conj_J₀ hj)) _).mp (mem_map_conj_inv_iff.mp hx))

end AxisHyp

omit [CharP K 2] in
theorem J₀_le_normalizer_pull [Finite G] {S : Subgroup (antiSp K)}
    (hS : ∀ δ ∈ diagTorus K, ∀ a ∈ S, δ * a * δ⁻¹ ∈ S) :
    pull φ (diagTorus K) ≤ normalizer (pull φ S : Set G) := fun j hj =>
  mem_normalizer_of_conj_le fun x hx => by
    obtain ⟨δ, hδ, rfl⟩ := exists_eq_symm_of_mem_pull hj
    obtain ⟨a, ha, rfl⟩ := exists_eq_symm_of_mem_pull hx
    rw [symm_conj_eq]
    exact symm_mem_pull.mpr (hS δ hδ a ha)

theorem mem_ZP_of_comm_mod {p : G} (hp : p ∈ 𝐏)
    (h₁ : (((φ.symm (uElt 1 0 0 0) : L) : G) * p)⁻¹ * (p * ((φ.symm (uElt 1 0 0 0) : L) : G)) ∈
      𝐔₂)
    (h₂ : (((φ.symm (uElt 0 0 0 1) : L) : G) * p)⁻¹ * (p * ((φ.symm (uElt 0 0 0 1) : L) : G)) ∈
      𝐔₂) :
    p ∈ 𝐙 := by
  obtain ⟨u, ⟨a, b, c, d, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hp
  rw [symm_mul_symm, symm_mul_symm, symm_inv', symm_mul_symm, symm_mem_pull] at h₁ h₂
  obtain ⟨ha, hd⟩ := eq_zero_of_comm_mod h₁ h₂
  subst ha hd
  exact symm_mem_pull.mpr ⟨b, c, rfl⟩

namespace AxisHyp

theorem comm_M_P [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {m : G} (hm : m ∈ M) :
    ∀ p ∈ 𝐏, m * p * m⁻¹ * p⁻¹ ∈ 𝐔₂ := by
  rw [pull_P_eq]
  refine comm_mod_sup (U₂_central ax.heis) (ax.le_S hm)
    ((le_sup_right.trans (ax.heis.hyp.B_le_Q Axis.one)).trans le_sup_left)
    ((le_sup_right.trans (ax.heis.hyp.B_le_Q Axis.two)).trans le_sup_left) (fun a ha => ?_)
    (fun a ha => ?_)
  · rw [ax.comm_A₁ hm ha, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  · have h := inv_mem (comm_A₂ ax.heis ha (ax.le_D₂ hm))
    rwa [show (a * m * a⁻¹ * m⁻¹)⁻¹ = m * a * m⁻¹ * a⁻¹ by group] at h

theorem comm_M_E [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {m : G} (hm : m ∈ M) :
    ∀ e ∈ 𝐄, m * e * m⁻¹ * e⁻¹ ∈ 𝐔₂ :=
  comm_mod_sup (U₂_central ax.heis) (ax.le_S hm) ax.le_S P_le_S
    (fun m' hm' => by
      rw [ax.comm m hm m' hm', mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _)
    (ax.comm_M_P hm)

theorem center_quot_E [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    ∃ _ : (𝐔₂.subgroupOf 𝐄).Normal, center (↥𝐄 ⧸ 𝐔₂.subgroupOf 𝐄) =
      (M.subgroupOf 𝐄).map (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐄)) := by
  have hES := ax.E_normal.1
  have hn : (𝐔₂.subgroupOf 𝐄).Normal := ⟨fun u hu e => by
    rw [mem_subgroupOf] at hu ⊢
    rw [coe_mul, coe_mul, comm_U₂ ax.heis (hES e.2) hu, coe_inv, mul_inv_cancel_right]
    exact hu⟩
  refine ⟨hn, ?_⟩
  have hMc : ∀ m : 𝐄, (m : G) ∈ M →
      (m : ↥𝐄 ⧸ 𝐔₂.subgroupOf 𝐄) ∈ center (↥𝐄 ⧸ 𝐔₂.subgroupOf 𝐄) := by
    intro m hm
    rw [mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | H e =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
      have h := ax.comm_M_E (inv_mem hm) _ (inv_mem e.2)
      rw [inv_inv, inv_inv] at h
      convert h using 1
      simp only [coe_mul, coe_inv]
      group
  ext x
  constructor
  · intro hx
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective x
    have he : (e : G) ∈ (M : Set G) * (𝐏 : Set G) := by
      rw [ax.coe_E]
      exact e.2
    obtain ⟨m, hm, p, hp, hmp⟩ := Set.mem_mul.mp he
    have hep : e = (⟨m, mem_sup_left hm⟩ : 𝐄) * ⟨p, mem_sup_right hp⟩ := Subtype.ext hmp.symm
    have hpc : ((⟨p, mem_sup_right hp⟩ : 𝐄) : ↥𝐄 ⧸ 𝐔₂.subgroupOf 𝐄) ∈
        center (↥𝐄 ⧸ 𝐔₂.subgroupOf 𝐄) := by
      have e1 : ((⟨p, mem_sup_right hp⟩ : 𝐄) : ↥𝐄 ⧸ 𝐔₂.subgroupOf 𝐄) =
          ((⟨m, mem_sup_left hm⟩ : 𝐄) : ↥𝐄 ⧸ 𝐔₂.subgroupOf 𝐄)⁻¹ * (e : ↥𝐄 ⧸ 𝐔₂.subgroupOf 𝐄) := by
        rw [hep, QuotientGroup.mk_mul, inv_mul_cancel_left]
      rw [e1]
      exact mul_mem (inv_mem (hMc _ hm)) hx
    have hq : ∀ q ∈ 𝐏, (q * p)⁻¹ * (p * q) ∈ 𝐔₂ := by
      intro q hq
      have h := (mem_center_iff.mp hpc) ((⟨q, mem_sup_right hq⟩ : 𝐄) : ↥𝐄 ⧸ 𝐔₂.subgroupOf 𝐄)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf] at h
      exact h
    have hpZ := mem_ZP_of_comm_mod hp (hq _ (symm_mem_pull.mpr (uElt_mem_antiUnipotent 1 0 0 0)))
      (hq _ (symm_mem_pull.mpr (uElt_mem_antiUnipotent 0 0 0 1)))
    refine ⟨e, mem_subgroupOf.mpr ?_, rfl⟩
    rw [← hmp]
    exact mul_mem hm (ax.ZP_le hpZ)
  · rintro ⟨m, hm, rfl⟩
    exact hMc m (mem_subgroupOf.mp hm)

theorem quot_M₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    ∃ _ : (𝐔₂.subgroupOf 𝐌₂).Normal, IsElementaryAbelian 2 (↥𝐌₂ ⧸ 𝐔₂.subgroupOf 𝐌₂) ∧
      Nat.card (↥𝐌₂ ⧸ 𝐔₂.subgroupOf 𝐌₂) = (2 ^ n) ^ 4 := by
  have hU : 𝐔₂ ≤ 𝐌₂ := ax.U₂_le.trans le_sup_left
  have hn : (𝐔₂.subgroupOf 𝐌₂).Normal := ⟨fun u hu e => by
    rw [mem_subgroupOf] at hu ⊢
    rw [coe_mul, coe_mul, comm_U₂ ax.heis (ax.M₂_le_S e.2) hu, coe_inv, mul_inv_cancel_right]
    exact hu⟩
  have hcomm : ∀ a b : ↥𝐌₂ ⧸ 𝐔₂.subgroupOf 𝐌₂, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        have h := ax.M₂_comm _ (inv_mem y.2) _ (inv_mem x.2)
        rw [inv_inv, inv_inv] at h
        convert h using 1
        simp only [coe_mul, coe_inv]
        group
  have hexp : ∀ g : ↥𝐌₂ ⧸ 𝐔₂.subgroupOf 𝐌₂, g ^ 2 = 1 := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_one, QuotientGroup.eq, mem_subgroupOf]
      have h := inv_mem (ax.M₂_sq x.2)
      convert h using 1
      simp only [coe_mul, coe_inv, SubgroupClass.coe_pow, coe_one]
      group
  have hEA : IsElementaryAbelian 2 (↥𝐌₂ ⧸ 𝐔₂.subgroupOf 𝐌₂) :=
    { is_comm := ⟨hcomm⟩, exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp }
  refine ⟨hn, hEA, ?_⟩
  · have h := card_eq_card_quotient_mul_card_subgroup (𝐔₂.subgroupOf 𝐌₂)
    rw [Nat.card_congr (subgroupOfEquivOfLe hU).toEquiv, ax.card_M₂, ax.card_U₂] at h
    exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ n) (by rw [← h]; ring)

theorem quot_V [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    ∃ _ : (𝐌₁.subgroupOf 𝐕).Normal, IsElementaryAbelian 2 (↥𝐕 ⧸ 𝐌₁.subgroupOf 𝐕) ∧
      Nat.card (↥𝐕 ⧸ 𝐌₁.subgroupOf 𝐕) = (2 ^ n) ^ 2 := by
  have hn : (𝐌₁.subgroupOf 𝐕).Normal := ⟨fun u hu v => mem_subgroupOf.mpr
    (ax.conj₁ _ (ax.V_le_S v.2) _ (mem_subgroupOf.mp hu))⟩
  have hMwV : 𝐌w ≤ 𝐕 := (le_sup_right : 𝐌w ≤ 𝐌₂).trans le_sup_right
  have hrep : ∀ v : 𝐕, ∃ w : 𝐕, (w : G) ∈ 𝐌w ∧
      (v : ↥𝐕 ⧸ 𝐌₁.subgroupOf 𝐕) = (w : ↥𝐕 ⧸ 𝐌₁.subgroupOf 𝐕) := by
    intro v
    have hv : (v : G) ∈ (𝐌₁ : Set G) * (𝐌₂ : Set G) := by
      rw [ax.coe_V]
      exact v.2
    obtain ⟨m₁, hm₁, m₂, hm₂, hv'⟩ := Set.mem_mul.mp hv
    have hm₂' : m₂ ∈ (M : Set G) * (𝐌w : Set G) := by
      rw [ax.coe_M₂]
      exact hm₂
    obtain ⟨m, hm, m', hm', rfl⟩ := Set.mem_mul.mp hm₂'
    refine ⟨⟨m', hMwV hm'⟩, hm', ?_⟩
    rw [QuotientGroup.eq, mem_subgroupOf]
    have h := ax.conj₁ _ (inv_mem (ax.Mw_le_S hm')) _
      (inv_mem (mul_mem hm₁ (mem_sup_left hm) : m₁ * m ∈ 𝐌₁))
    convert h using 1
    simp only [coe_mul, coe_inv]
    rw [← hv']
    group
  have hcomm : ∀ a b : ↥𝐕 ⧸ 𝐌₁.subgroupOf 𝐕, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        obtain ⟨x', hx', hxx⟩ := hrep x
        obtain ⟨y', hy', hyy⟩ := hrep y
        rw [hxx, hyy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext (ax.Mw_comm hx' hy')
  have hexp : ∀ g : ↥𝐕 ⧸ 𝐌₁.subgroupOf 𝐕, g ^ 2 = 1 := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨x', hx', hxx⟩ := hrep x
      rw [hxx, ← QuotientGroup.mk_pow]
      have h1 : x' ^ 2 = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow, pow_two, coe_one]
        exact ax.Mw_mul_self hx')
      rw [h1, QuotientGroup.mk_one]
  have hEA : IsElementaryAbelian 2 (↥𝐕 ⧸ 𝐌₁.subgroupOf 𝐕) :=
    { is_comm := ⟨hcomm⟩, exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp }
  refine ⟨hn, hEA, ?_⟩
  · have h := card_eq_card_quotient_mul_card_subgroup (𝐌₁.subgroupOf 𝐕)
    rw [Nat.card_congr (subgroupOfEquivOfLe (le_sup_left : 𝐌₁ ≤ 𝐕)).toEquiv, ax.card_V,
      ax.card₁] at h
    exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < (2 ^ n) ^ 4) (by rw [← h]; ring)

theorem maximal_quot_D₂ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    ∃ _ : (𝐔₂.subgroupOf 𝐃₂).Normal, ∀ F : Subgroup (↥𝐃₂ ⧸ 𝐔₂.subgroupOf 𝐃₂),
      Maximal (fun F' : Subgroup (↥𝐃₂ ⧸ 𝐔₂.subgroupOf 𝐃₂) => IsElementaryAbelian 2 F') F ↔
        F = (𝐁₂.subgroupOf 𝐃₂).map (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐃₂)) ∨
        F = (𝐌₂.subgroupOf 𝐃₂).map (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐃₂)) := by
  have hDS : 𝐃₂ ≤ 𝐒 := fun _ hd => mem_sup_right hd
  have hn : (𝐔₂.subgroupOf 𝐃₂).Normal := ⟨fun u hu e => by
    rw [mem_subgroupOf] at hu ⊢
    rw [coe_mul, coe_mul, comm_U₂ ax.heis (hDS e.2) hu, coe_inv, mul_inv_cancel_right]
    exact hu⟩
  refine ⟨hn, ?_⟩
  have hEA : ∀ F : Subgroup (↥𝐃₂ ⧸ 𝐔₂.subgroupOf 𝐃₂), (∀ g ∈ F, ∀ h ∈ F, g * h = h * g) →
      (∀ g ∈ F, g ^ 2 = 1) → IsElementaryAbelian 2 F := fun F hc hs =>
    { is_comm := ⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa using hs g g.2) }
  have himg : ∀ H : Subgroup G, (∀ x ∈ H, ∀ y ∈ H, x * y * x⁻¹ * y⁻¹ ∈ 𝐔₂) →
      (∀ x ∈ H, x * x ∈ 𝐔₂) →
        IsElementaryAbelian 2 ((H.subgroupOf 𝐃₂).map (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐃₂))) := by
    intro H hc hs
    refine hEA _ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, mem_subgroupOf]
      have h := hc _ (inv_mem (mem_subgroupOf.mp hy)) _ (inv_mem (mem_subgroupOf.mp hx))
      rw [inv_inv, inv_inv] at h
      convert h using 1
      simp only [coe_mul, coe_inv]
      group
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, QuotientGroup.mk'_apply, ← QuotientGroup.mk_one, QuotientGroup.eq,
        mem_subgroupOf]
      have h := inv_mem (hs _ (mem_subgroupOf.mp hx))
      convert h using 1
      simp only [coe_mul, coe_inv, SubgroupClass.coe_pow, coe_one]
      group
  have hB := himg 𝐁₂ (fun x hx y hy => by
      rw [B_comm φ ax.heis.sec.two hx hy, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _)
    (fun x hx => by
      rw [ax.heis.hyp.mul_self_of_mem_B Axis.two hx]
      exact one_mem _)
  have hM := himg 𝐌₂ ax.M₂_comm fun x hx => ax.M₂_sq hx
  have hle : ∀ F : Subgroup (↥𝐃₂ ⧸ 𝐔₂.subgroupOf 𝐃₂), IsElementaryAbelian 2 F →
      F ≤ (𝐁₂.subgroupOf 𝐃₂).map (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐃₂)) ∨
        F ≤ (𝐌₂.subgroupOf 𝐃₂).map (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐃₂)) := by
    intro F hF
    have hcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hF.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hpow : ∀ a ∈ F, a ^ 2 = 1 := fun a ha => by
      have := hF
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := F) a ha
    have hc : ∀ x ∈ (F.comap (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐃₂))).map 𝐃₂.subtype,
        ∀ y ∈ (F.comap (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐃₂))).map 𝐃₂.subtype,
          x * y * x⁻¹ * y⁻¹ ∈ 𝐔₂ := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have h := hcomm _ (inv_mem hy) _ (inv_mem hx)
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf] at h
      convert h using 1
      simp only [Subgroup.coe_subtype, coe_mul, coe_inv]
      group
    have hs : ∀ x ∈ (F.comap (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐃₂))).map 𝐃₂.subtype,
        x * x ∈ 𝐔₂ := by
      rintro _ ⟨x, hx, rfl⟩
      have h := hpow _ hx
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h
      convert h using 1
      simp only [Subgroup.coe_subtype, pow_two, coe_mul]
    rcases ax.le_B₂_or_le_M₂ (map_subtype_le _) hc hs with h | h
    · left
      intro g hg
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
      exact ⟨x, mem_subgroupOf.mpr (h ⟨x, hg, rfl⟩), rfl⟩
    · right
      intro g hg
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
      exact ⟨x, mem_subgroupOf.mpr (h ⟨x, hg, rfl⟩), rfl⟩
  have hn12 : ¬ (𝐁₂.subgroupOf 𝐃₂).map (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐃₂)) ≤
      (𝐌₂.subgroupOf 𝐃₂).map (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐃₂)) := by
    intro h
    obtain ⟨m, hm, hmt⟩ := h ⟨⟨t, t_mem_D₂ ax.heis⟩, mem_subgroupOf.mpr SecondHyp.t_mem_B, rfl⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf] at hmt
    apply ax.t_not_mem_M₂
    have := mul_mem (mem_subgroupOf.mp hm) ((ax.U₂_le.trans le_sup_left) hmt)
    simpa using this
  have hn21 : ¬ (𝐌₂.subgroupOf 𝐃₂).map (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐃₂)) ≤
      (𝐁₂.subgroupOf 𝐃₂).map (QuotientGroup.mk' (𝐔₂.subgroupOf 𝐃₂)) := by
    intro h
    obtain ⟨m, hm, hmB⟩ : ∃ m ∈ 𝐌₂, m ∉ 𝐁₂ := by
      by_contra hc
      have hle' : 𝐌₂ ≤ 𝐁₂ := fun m hm => by
        by_contra hmB
        exact hc ⟨m, hm, hmB⟩
      have h1 := ax.M₂_inf_B₂
      rw [inf_of_le_left hle'] at h1
      have h2 := ax.card_M₂
      rw [h1, ax.card_A₂] at h2
      have h4 := ax.four_le
      have : (2 ^ n) ^ 3 < (2 ^ n) ^ 5 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      omega
    obtain ⟨b, hb, hbm⟩ := h ⟨⟨m, ax.M₂_le_D₂ hm⟩, mem_subgroupOf.mpr hm, rfl⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf] at hbm
    apply hmB
    have := mul_mem (mem_subgroupOf.mp hb)
      (((pull_mono φ rootU₂_le_radA2).trans le_sup_right) hbm : _ ∈ 𝐁₂)
    simpa using this
  intro F
  constructor
  · rintro ⟨hF, hmax⟩
    rcases hle F hF with h | h
    · exact Or.inl (le_antisymm h (hmax hB h))
    · exact Or.inr (le_antisymm h (hmax hM h))
  · rintro (rfl | rfl)
    · refine ⟨hB, fun F hF hEF => ?_⟩
      rcases hle F hF with h | h
      · exact h
      · exact absurd (hEF.trans h) hn12
    · refine ⟨hM, fun F hF hEF => ?_⟩
      rcases hle F hF with h | h
      · exact absurd (hEF.trans h) hn21
      · exact h


end AxisHyp

theorem main [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) (Q ZP PG : Subgroup G)
    (hPG : PG = pull φ (antiUnipotent K)) (hQ : Q = PG ⊔ TG)
    (hZP : ZP = pull φ (antiUnipotentCenter K)) (w : antiSp K)
    (hw : glMat (w : GL (Fin 4) K) = !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1])
    (M : Subgroup G) :
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
      ((M : Set G) * A₁ = M₁ ∧ (M : Set G) * A₂ = M₀ ∧ (M : Set G) * Mw = M₂ ∧
        (M : Set G) * PG = E ∧ (M₁ : Set G) * M₂ = V) ∧
      (J₀ ≤ normalizer (M₀ : Set G) ∧ J₀ ≤ normalizer (M₂ : Set G) ∧
        J₀ ≤ normalizer (E : Set G) ∧ J₀ ≤ normalizer (V : Set G)) ∧
      Nat.card M₀ = (2 ^ n) ^ 4 ∧ M₀ ⊓ M₀.map (MulAut.conj w₂⁻¹).toMonoidHom = A₂ ∧
      M ⊓ Mw = U₂ ∧ Nat.card M₂ = (2 ^ n) ^ 5 ∧ M₂ ⊓ B₂ = A₂ ∧ M₁ ⊓ M₂ = M ∧
      (M₂ ≤ D₂ ∧ (M₂.subgroupOf D₂).Normal ∧ M₂ ⊓ zpowers t = ⊥ ∧ M₂ ⊔ zpowers t = D₂) ∧
      Nat.card E = (2 ^ n) ^ 5 ∧ (E ≤ S ∧ (E.subgroupOf S).Normal) ∧
      (E ≤ R ∧ (E.subgroupOf R).Normal ∧ E ⊓ zpowers t = ⊥ ∧ E ⊔ zpowers t = R) ∧
      (∃ _ : (U₂.subgroupOf E).Normal, center (↥E ⧸ U₂.subgroupOf E) =
        (M.subgroupOf E).map (QuotientGroup.mk' (U₂.subgroupOf E))) ∧
      (∃ _ : (U₂.subgroupOf M₂).Normal, IsElementaryAbelian 2 (↥M₂ ⧸ U₂.subgroupOf M₂) ∧
        Nat.card (↥M₂ ⧸ U₂.subgroupOf M₂) = (2 ^ n) ^ 4) ∧
      (M₂.subgroupOf D₂).Characteristic ∧ (M₂ ≤ S ∧ (M₂.subgroupOf S).Normal) ∧
      (⁅M₂, M₂⁆ = U₂ ∧ closure {x : G | ∃ y ∈ M₂, x = y * y} = U₂ ∧
        (center M₂).map M₂.subtype = U₂) ∧
      (∃ _ : (U₂.subgroupOf D₂).Normal, ∀ F : Subgroup (↥D₂ ⧸ U₂.subgroupOf D₂),
        Maximal (fun F' : Subgroup (↥D₂ ⧸ U₂.subgroupOf D₂) => IsElementaryAbelian 2 F') F ↔
          F = (B₂.subgroupOf D₂).map (QuotientGroup.mk' (U₂.subgroupOf D₂)) ∨
          F = (M₂.subgroupOf D₂).map (QuotientGroup.mk' (U₂.subgroupOf D₂))) ∧
      (normalizer (B₂ : Set G) = normalizer (D₂ : Set G) ∧
        normalizer (D₂ : Set G) ≤ normalizer (M₂ : Set G)) ∧
      Nat.card V = (2 ^ n) ^ 6 ∧ (V ≤ S ∧ (V.subgroupOf S).Normal) ∧
      (V ⊓ zpowers t = ⊥ ∧ V ⊔ zpowers t = S) ∧ E ≤ V ∧ V ⊓ R = E ∧ V ⊓ D₂ = M₂ ∧
      (∃ _ : (M₁.subgroupOf V).Normal, IsElementaryAbelian 2 (↥V ⧸ M₁.subgroupOf V) ∧
        Nat.card (↥V ⧸ M₁.subgroupOf V) = (2 ^ n) ^ 2) := by
  subst hQ hPG hZP
  obtain rfl : w = sElt swapSL := antiSp_ext (hw.trans glMat_sElt_swap.symm)
  intro U₂ A₁ A₂ B₁ B₂ N₁ N₂ D₁ D₂ R S J₀ w₂ Mw M₁ M₀ M₂ E V hJ hMD hMab hMcard hZM _ hM₁card
    hM₁S hM₁D
  have hM₁n := (normal_subgroupOf_iff_le_normalizer hM₁S.1).mp hM₁S.2
  have ax : AxisHyp L K n φ TG t M :=
    { heis := hh
      le_D₁ := hMD.trans inf_le_left
      le_D₂ := hMD.trans inf_le_right
      comm := fun x hx y hy => congrArg Subtype.val (hMab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      mul_self := fun x hx => by
        have := hMab
        have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := M) x hx
        rwa [pow_two] at h
      card := hMcard
      ZP_le := hZM
      card₁ := hM₁card
      conj₁ := fun s hs x hx => (mem_normalizer_iff.mp (hM₁n hs) x).mp hx
      t_not_mem₁ := fun h => by
        have h1 : t ∈ M₁ ⊓ zpowers t := mem_inf.mpr ⟨h, mem_zpowers t⟩
        rw [hM₁D.2.2.1, mem_bot] at h1
        exact hh.hyp.setup.t_ne_one h1 }
  have hJA₁ : J₀ ≤ normalizer (A₁ : Set G) :=
    J₀_le_normalizer_pull (S := radA1 K) fun _ hδ _ ha => diagTorus_conj_radA1 hδ ha
  have hJA₂ : J₀ ≤ normalizer (A₂ : Set G) :=
    J₀_le_normalizer_pull (S := radA2 K) fun _ hδ _ ha => diagTorus_conj_radA2 hδ ha
  have hJP : J₀ ≤ normalizer (pull φ (antiUnipotent K) : Set G) :=
    J₀_le_normalizer_pull fun _ hδ _ ha => diagTorus_conj_antiUnipotent hδ ha
  have hJM₂ : J₀ ≤ normalizer (M₂ : Set G) := le_normalizer_sup hJ (AxisHyp.J₀_le_Mw hJ)
  have hES := ax.E_normal
  have hVS : (V.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer ax.V_le_S).mpr
    fun _ hs => mem_normalizer_of_conj_le fun _ hx => ax.conj_mem_V hs hx
  have hER : (E.subgroupOf R).Normal := (normal_subgroupOf_iff_le_normalizer ax.E_le_R).mpr
    fun _ hr => (normal_subgroupOf_iff_le_normalizer hES.1).mp hES.2 (hh.R_le_S hr)
  obtain ⟨hcomm, hsq⟩ := ax.commutator_M₂
  exact ⟨⟨ax.coe_M₁, ax.coe_M₀, ax.coe_M₂, ax.coe_E, ax.coe_V⟩,
    ⟨le_normalizer_sup hJ hJA₂, hJM₂, le_normalizer_sup hJ hJP,
      le_normalizer_sup (le_normalizer_sup hJ hJA₁) hJM₂⟩,
    ax.card_M₀, ax.M₀_inf, ax.M_inf_Mw, ax.card_M₂, ax.M₂_inf_B₂, ax.M₁_inf_M₂,
    ax.D₂_semidirect, ax.card_E, hES, ⟨ax.E_le_R, hER, ax.R_semidirect⟩, ax.center_quot_E,
    ax.quot_M₂, ax.characteristic, ax.M₂_normal, ⟨hcomm, hsq, ax.center_M₂⟩,
    ax.maximal_quot_D₂, ⟨ax.normalizer_B₂_eq, ax.normalizer_D₂_le⟩, ax.card_V,
    ⟨ax.V_le_S, hVS⟩, ax.S_semidirect, ax.E_le_V, ax.V_inf_R, ax.V_inf_D₂, ax.quot_V⟩

end Main

end OneAxisSecondAxis

open Subgroup GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.PartOne.KCRootAxis
open scoped Pointwise

theorem standard_symplectic_four_given_first_overgroup_second_axis_structure
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
    let R := Q ⊔ D₁
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
      ((M : Set G) * A₁ = M₁ ∧ (M : Set G) * A₂ = M₀ ∧ (M : Set G) * Mw = M₂ ∧
        (M : Set G) * PG = E ∧ (M₁ : Set G) * M₂ = V) ∧
      (J₀ ≤ normalizer (M₀ : Set G) ∧ J₀ ≤ normalizer (M₂ : Set G) ∧
        J₀ ≤ normalizer (E : Set G) ∧ J₀ ≤ normalizer (V : Set G)) ∧
      Nat.card M₀ = (2 ^ n) ^ 4 ∧ M₀ ⊓ M₀.map (MulAut.conj w₂⁻¹).toMonoidHom = A₂ ∧
      M ⊓ Mw = U₂ ∧ Nat.card M₂ = (2 ^ n) ^ 5 ∧ M₂ ⊓ B₂ = A₂ ∧ M₁ ⊓ M₂ = M ∧
      (M₂ ≤ D₂ ∧ (M₂.subgroupOf D₂).Normal ∧ M₂ ⊓ zpowers (t : G) = ⊥ ∧
        M₂ ⊔ zpowers (t : G) = D₂) ∧
      Nat.card E = (2 ^ n) ^ 5 ∧ (E ≤ S ∧ (E.subgroupOf S).Normal) ∧
      (E ≤ R ∧ (E.subgroupOf R).Normal ∧ E ⊓ zpowers (t : G) = ⊥ ∧ E ⊔ zpowers (t : G) = R) ∧
      (∃ _ : (U₂.subgroupOf E).Normal, center (↥E ⧸ U₂.subgroupOf E) =
        (M.subgroupOf E).map (QuotientGroup.mk' (U₂.subgroupOf E))) ∧
      (∃ _ : (U₂.subgroupOf M₂).Normal, IsElementaryAbelian 2 (↥M₂ ⧸ U₂.subgroupOf M₂) ∧
        Nat.card (↥M₂ ⧸ U₂.subgroupOf M₂) = (2 ^ n) ^ 4) ∧
      (M₂.subgroupOf D₂).Characteristic ∧ (M₂ ≤ S ∧ (M₂.subgroupOf S).Normal) ∧
      (⁅M₂, M₂⁆ = U₂ ∧ closure {x : G | ∃ y ∈ M₂, x = y * y} = U₂ ∧
        (center M₂).map M₂.subtype = U₂) ∧
      (∃ _ : (U₂.subgroupOf D₂).Normal, ∀ F : Subgroup (↥D₂ ⧸ U₂.subgroupOf D₂),
        Maximal (fun F' : Subgroup (↥D₂ ⧸ U₂.subgroupOf D₂) => IsElementaryAbelian 2 F') F ↔
          F = (B₂.subgroupOf D₂).map (QuotientGroup.mk' (U₂.subgroupOf D₂)) ∨
          F = (M₂.subgroupOf D₂).map (QuotientGroup.mk' (U₂.subgroupOf D₂))) ∧
      (normalizer (B₂ : Set G) = normalizer (D₂ : Set G) ∧
        normalizer (D₂ : Set G) ≤ normalizer (M₂ : Set G)) ∧
      Nat.card V = (2 ^ n) ^ 6 ∧ (V ≤ S ∧ (V.subgroupOf S).Normal) ∧
      (V ⊓ zpowers (t : G) = ⊥ ∧ V ⊔ zpowers (t : G) = S) ∧ E ≤ V ∧ V ⊓ R = E ∧ V ⊓ D₂ = M₂ ∧
      (∃ _ : (M₁.subgroupOf V).Normal, IsElementaryAbelian 2 (↥V ⧸ M₁.subgroupOf V) ∧
        Nat.card (↥V ⧸ M₁.subgroupOf V) = (2 ^ n) ^ 2) := by
  intro TG PG Q ZP U₁ U₂ A₁ A₂ B₁ B₂ N₁ N₂ D₁ D₂ R S J₀ w₂ Mw M₁ M₀ M₂ E V hone
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
  exact OneAxisSecondAxis.main hh Q ZP PG hPG rfl hZP w hw M

end CFSG.LocalAnalysis.SymplecticFourStandard
