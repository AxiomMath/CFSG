module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroCoordDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {m : ℕ}

private noncomputable def f4DualE (e : Fin 4 → V) : Fin 4 → V :=
  ![e 0 + e 1, e 0 - e 1, e 2 + e 3, e 2 - e 3]

private noncomputable def f4DualPhi (φ : Fin 4 → Module.Dual (ZMod p) V) :
    Fin 4 → Module.Dual (ZMod p) V :=
  ![(2 : ZMod p)⁻¹ • (φ 0 + φ 1), (2 : ZMod p)⁻¹ • (φ 0 - φ 1),
    (2 : ZMod p)⁻¹ • (φ 2 + φ 3), (2 : ZMod p)⁻¹ • (φ 2 - φ 3)]

section

variable {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}

private lemma f4DualPhi_zero (v : V) :
    f4DualPhi φ 0 v = (2 : ZMod p)⁻¹ * (φ 0 v + φ 1 v) := by
  simp [f4DualPhi]
  ring

private lemma f4DualPhi_one (v : V) :
    f4DualPhi φ 1 v = (2 : ZMod p)⁻¹ * (φ 0 v - φ 1 v) := by
  simp [f4DualPhi]

private lemma f4DualPhi_two (v : V) :
    f4DualPhi φ 2 v = (2 : ZMod p)⁻¹ * (φ 2 v + φ 3 v) := by
  simp [f4DualPhi]
  ring

private lemma f4DualPhi_three (v : V) :
    f4DualPhi φ 3 v = (2 : ZMod p)⁻¹ * (φ 2 v - φ 3 v) := by
  simp [f4DualPhi]

private lemma formula_of_formula {r : V ≃ₗ[ZMod p] V} {f g : V → ZMod p} {x y : V}
    (h : ∀ v, r v = v - f v • x) (hfg : ∀ v, f v • x = g v • y) :
    ∀ v, r v = v - g v • y := by
  intro v
  rw [h v, hfg v]

private lemma smul_sub_smul_swap {a b : ZMod p} {x y : V} {ε : ZMod p}
    (hε : ε = 1 ∨ ε = -1) :
    (a - ε * b) • (x - ε • y) = (b - ε * a) • (y - ε • x) := by
  rcases hε with rfl | rfl <;> module

private lemma formula_swap {r : V ≃ₗ[ZMod p] V} {f g : V → ZMod p} {x y : V} {ε : ZMod p}
    (hε : ε = 1 ∨ ε = -1) (h : ∀ v, r v = v - (f v - ε * g v) • (x - ε • y)) :
    ∀ v, r v = v - (g v - ε * f v) • (y - ε • x) := by
  intro v
  rw [h v, smul_sub_smul_swap hε]

private lemma ggCZRD_smul {c : ZMod p} (hc : c ≠ 0) :
    ggCZRD (fun k => c • e k) (fun k => c⁻¹ • φ k) = ggCZRD e φ := by
  ext r
  constructor
  · rintro ⟨i, j, hij, ε, hε, h⟩
    refine ⟨i, j, hij, ε, hε, formula_of_formula h ?_⟩
    intro v
    simp only [LinearMap.smul_apply, smul_eq_mul]
    have hcoef : c⁻¹ * φ i v - ε * (c⁻¹ * φ j v) = c⁻¹ * (φ i v - ε * φ j v) := by
      ring
    have hvec : c • e i - ε • c • e j = c • (e i - ε • e j) := by module
    rw [hcoef, hvec, smul_smul]
    have hcA : c⁻¹ * (φ i v - ε * φ j v) * c = φ i v - ε * φ j v := by
      rw [mul_assoc, mul_comm (φ i v - ε * φ j v) c, ← mul_assoc,
        inv_mul_cancel₀ hc, one_mul]
    rw [hcA]
  · rintro ⟨i, j, hij, ε, hε, h⟩
    refine ⟨i, j, hij, ε, hε, formula_of_formula h ?_⟩
    intro v
    simp only [LinearMap.smul_apply, smul_eq_mul]
    have hB : c⁻¹ * φ i v - ε * (c⁻¹ * φ j v) = c⁻¹ * (φ i v - ε * φ j v) := by
      ring
    have hY : c • e i - ε • c • e j = c • (e i - ε • e j) := by module
    rw [hB, hY, smul_smul]
    have hcA : c⁻¹ * (φ i v - ε * φ j v) * c = φ i v - ε * φ j v := by
      rw [mul_assoc, mul_comm (φ i v - ε * φ j v) c, ← mul_assoc,
        inv_mul_cancel₀ hc, one_mul]
    rw [hcA]

private lemma f4Dual_dual (hp2 : p ≠ 2) (hd : GGCZDual e φ) :
    GGCZDual (f4DualE e) (f4DualPhi φ) := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hd' : ∀ i j, φ i (e j) = if i = j then 1 else 0 := hd
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [f4DualE, f4DualPhi, hd'] <;>
    field_simp <;> ring

private lemma f4Dual_ker (hp2 : p ≠ 2) (v : V) :
    (∀ k, f4DualPhi φ k v = 0) ↔ ∀ k, φ k v = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  constructor
  · intro h k
    have h0 : φ 0 v + φ 1 v = 0 := by
      have := h 0
      rw [f4DualPhi_zero] at this
      exact (mul_eq_zero.mp this).resolve_left (inv_ne_zero h2)
    have h1 : φ 0 v - φ 1 v = 0 := by
      have := h 1
      rw [f4DualPhi_one] at this
      exact (mul_eq_zero.mp this).resolve_left (inv_ne_zero h2)
    have h2' : φ 2 v + φ 3 v = 0 := by
      have := h 2
      rw [f4DualPhi_two] at this
      exact (mul_eq_zero.mp this).resolve_left (inv_ne_zero h2)
    have h3 : φ 2 v - φ 3 v = 0 := by
      have := h 3
      rw [f4DualPhi_three] at this
      exact (mul_eq_zero.mp this).resolve_left (inv_ne_zero h2)
    fin_cases k
    · have : (2 : ZMod p) * φ 0 v = 0 := by linear_combination h0 + h1
      exact (mul_eq_zero.mp this).resolve_left h2
    · have : (2 : ZMod p) * φ 1 v = 0 := by linear_combination h0 - h1
      exact (mul_eq_zero.mp this).resolve_left h2
    · have : (2 : ZMod p) * φ 2 v = 0 := by linear_combination h2' + h3
      exact (mul_eq_zero.mp this).resolve_left h2
    · have : (2 : ZMod p) * φ 3 v = 0 := by linear_combination h2' - h3
      exact (mul_eq_zero.mp this).resolve_left h2
  · intro h k
    fin_cases k <;> simp [f4DualPhi, h]

private lemma f4DualE_f4DualE : f4DualE (f4DualE e) = fun k => (2 : ZMod p) • e k := by
  funext k
  fin_cases k <;> simp [f4DualE] <;> module

private lemma f4DualPhi_f4DualPhi (hp2 : p ≠ 2) :
    f4DualPhi (f4DualPhi φ) = fun k => (2 : ZMod p)⁻¹ • φ k := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  funext k
  fin_cases k <;>
    refine LinearMap.ext fun v => ?_ <;>
    simp [f4DualPhi, h2] <;>
    field_simp <;> ring

private lemma f4_formula_01_one (hp2 : p ≠ 2) {r : V ≃ₗ[ZMod p] V} :
    (∀ v, r v = v - (f4DualPhi φ 0 v - 1 * f4DualPhi φ 1 v) •
      (f4DualE e 0 - (1 : ZMod p) • f4DualE e 1)) ↔
    (∀ v, r v = v - (2 * φ 1 v) • e 1) := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hfg : ∀ v, (f4DualPhi φ 0 v - 1 * f4DualPhi φ 1 v) •
      (f4DualE e 0 - (1 : ZMod p) • f4DualE e 1) = (2 * φ 1 v) • e 1 := by
    intro v
    rw [f4DualPhi_zero, f4DualPhi_one]
    have hvec : f4DualE e 0 - (1 : ZMod p) • f4DualE e 1 = 2 • e 1 := by
      simp [f4DualE]
      module
    rw [hvec]
    rw [show (2 : ZMod p)⁻¹ * (φ 0 v + φ 1 v) -
        1 * (2⁻¹ * (φ 0 v - φ 1 v)) = φ 1 v by field_simp; ring]
    module
  exact ⟨fun h => formula_of_formula h hfg,
    fun h => formula_of_formula h fun v => (hfg v).symm⟩

private lemma f4_formula_01_neg (hp2 : p ≠ 2) {r : V ≃ₗ[ZMod p] V} :
    (∀ v, r v = v - (f4DualPhi φ 0 v - (-1) * f4DualPhi φ 1 v) •
      (f4DualE e 0 - (-1 : ZMod p) • f4DualE e 1)) ↔
    (∀ v, r v = v - (2 * φ 0 v) • e 0) := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hfg : ∀ v, (f4DualPhi φ 0 v - (-1) * f4DualPhi φ 1 v) •
      (f4DualE e 0 - (-1 : ZMod p) • f4DualE e 1) = (2 * φ 0 v) • e 0 := by
    intro v
    rw [f4DualPhi_zero, f4DualPhi_one]
    have hvec : f4DualE e 0 - (-1 : ZMod p) • f4DualE e 1 = 2 • e 0 := by
      simp [f4DualE]
      module
    rw [hvec]
    rw [show (2 : ZMod p)⁻¹ * (φ 0 v + φ 1 v) -
        (-1) * (2⁻¹ * (φ 0 v - φ 1 v)) = φ 0 v by field_simp; ring]
    module
  exact ⟨fun h => formula_of_formula h hfg,
    fun h => formula_of_formula h fun v => (hfg v).symm⟩

private lemma f4_formula_23_one (hp2 : p ≠ 2) {r : V ≃ₗ[ZMod p] V} :
    (∀ v, r v = v - (f4DualPhi φ 2 v - 1 * f4DualPhi φ 3 v) •
      (f4DualE e 2 - (1 : ZMod p) • f4DualE e 3)) ↔
    (∀ v, r v = v - (2 * φ 3 v) • e 3) := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hfg : ∀ v, (f4DualPhi φ 2 v - 1 * f4DualPhi φ 3 v) •
      (f4DualE e 2 - (1 : ZMod p) • f4DualE e 3) = (2 * φ 3 v) • e 3 := by
    intro v
    rw [f4DualPhi_two, f4DualPhi_three]
    have hvec : f4DualE e 2 - (1 : ZMod p) • f4DualE e 3 = 2 • e 3 := by
      simp [f4DualE]
      module
    rw [hvec]
    rw [show (2 : ZMod p)⁻¹ * (φ 2 v + φ 3 v) -
        1 * (2⁻¹ * (φ 2 v - φ 3 v)) = φ 3 v by field_simp; ring]
    module
  exact ⟨fun h => formula_of_formula h hfg,
    fun h => formula_of_formula h fun v => (hfg v).symm⟩

private lemma f4_formula_23_neg (hp2 : p ≠ 2) {r : V ≃ₗ[ZMod p] V} :
    (∀ v, r v = v - (f4DualPhi φ 2 v - (-1) * f4DualPhi φ 3 v) •
      (f4DualE e 2 - (-1 : ZMod p) • f4DualE e 3)) ↔
    (∀ v, r v = v - (2 * φ 2 v) • e 2) := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hfg : ∀ v, (f4DualPhi φ 2 v - (-1) * f4DualPhi φ 3 v) •
      (f4DualE e 2 - (-1 : ZMod p) • f4DualE e 3) = (2 * φ 2 v) • e 2 := by
    intro v
    rw [f4DualPhi_two, f4DualPhi_three]
    have hvec : f4DualE e 2 - (-1 : ZMod p) • f4DualE e 3 = 2 • e 2 := by
      simp [f4DualE]
      module
    rw [hvec]
    rw [show (2 : ZMod p)⁻¹ * (φ 2 v + φ 3 v) -
        (-1) * (2⁻¹ * (φ 2 v - φ 3 v)) = φ 2 v by field_simp; ring]
    module
  exact ⟨fun h => formula_of_formula h hfg,
    fun h => formula_of_formula h fun v => (hfg v).symm⟩

private lemma f4_formula_02_one (hp2 : p ≠ 2) {r : V ≃ₗ[ZMod p] V} :
    (∀ v, r v = v - (f4DualPhi φ 0 v - 1 * f4DualPhi φ 2 v) •
      (f4DualE e 0 - (1 : ZMod p) • f4DualE e 2)) ↔
    (∀ v, r v = v - ((2 : ZMod p)⁻¹ * ∑ k,
      (![1, 1, -1, -1] : Fin 4 → ZMod p) k * φ k v) •
      ∑ k, (![1, 1, -1, -1] : Fin 4 → ZMod p) k • e k) := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hfg : ∀ v, (f4DualPhi φ 0 v - 1 * f4DualPhi φ 2 v) •
      (f4DualE e 0 - (1 : ZMod p) • f4DualE e 2) =
      ((2 : ZMod p)⁻¹ * ∑ k, (![1, 1, -1, -1] : Fin 4 → ZMod p) k * φ k v) •
        ∑ k, (![1, 1, -1, -1] : Fin 4 → ZMod p) k • e k := by
    intro v
    simp only [f4DualE, f4DualPhi, Fin.sum_univ_four]
    norm_num
    module
  exact ⟨fun h => formula_of_formula h hfg,
    fun h => formula_of_formula h fun v => (hfg v).symm⟩

private lemma f4_formula_02_neg (hp2 : p ≠ 2) {r : V ≃ₗ[ZMod p] V} :
    (∀ v, r v = v - (f4DualPhi φ 0 v - (-1) * f4DualPhi φ 2 v) •
      (f4DualE e 0 - (-1 : ZMod p) • f4DualE e 2)) ↔
    (∀ v, r v = v - ((2 : ZMod p)⁻¹ * ∑ k,
      (![1, 1, 1, 1] : Fin 4 → ZMod p) k * φ k v) •
      ∑ k, (![1, 1, 1, 1] : Fin 4 → ZMod p) k • e k) := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hfg : ∀ v, (f4DualPhi φ 0 v - (-1) * f4DualPhi φ 2 v) •
      (f4DualE e 0 - (-1 : ZMod p) • f4DualE e 2) =
      ((2 : ZMod p)⁻¹ * ∑ k, (![1, 1, 1, 1] : Fin 4 → ZMod p) k * φ k v) •
        ∑ k, (![1, 1, 1, 1] : Fin 4 → ZMod p) k • e k := by
    intro v
    simp only [f4DualE, f4DualPhi, Fin.sum_univ_four]
    norm_num
    module
  exact ⟨fun h => formula_of_formula h hfg,
    fun h => formula_of_formula h fun v => (hfg v).symm⟩

private lemma f4_formula_03_one (hp2 : p ≠ 2) {r : V ≃ₗ[ZMod p] V} :
    (∀ v, r v = v - (f4DualPhi φ 0 v - 1 * f4DualPhi φ 3 v) •
      (f4DualE e 0 - (1 : ZMod p) • f4DualE e 3)) ↔
    (∀ v, r v = v - ((2 : ZMod p)⁻¹ * ∑ k,
      (![1, 1, -1, 1] : Fin 4 → ZMod p) k * φ k v) •
      ∑ k, (![1, 1, -1, 1] : Fin 4 → ZMod p) k • e k) := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hfg : ∀ v, (f4DualPhi φ 0 v - 1 * f4DualPhi φ 3 v) •
      (f4DualE e 0 - (1 : ZMod p) • f4DualE e 3) =
      ((2 : ZMod p)⁻¹ * ∑ k, (![1, 1, -1, 1] : Fin 4 → ZMod p) k * φ k v) •
        ∑ k, (![1, 1, -1, 1] : Fin 4 → ZMod p) k • e k := by
    intro v
    simp only [f4DualE, f4DualPhi, Fin.sum_univ_four]
    norm_num
    module
  exact ⟨fun h => formula_of_formula h hfg,
    fun h => formula_of_formula h fun v => (hfg v).symm⟩

private lemma f4_formula_03_neg (hp2 : p ≠ 2) {r : V ≃ₗ[ZMod p] V} :
    (∀ v, r v = v - (f4DualPhi φ 0 v - (-1) * f4DualPhi φ 3 v) •
      (f4DualE e 0 - (-1 : ZMod p) • f4DualE e 3)) ↔
    (∀ v, r v = v - ((2 : ZMod p)⁻¹ * ∑ k,
      (![1, 1, 1, -1] : Fin 4 → ZMod p) k * φ k v) •
      ∑ k, (![1, 1, 1, -1] : Fin 4 → ZMod p) k • e k) := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hfg : ∀ v, (f4DualPhi φ 0 v - (-1) * f4DualPhi φ 3 v) •
      (f4DualE e 0 - (-1 : ZMod p) • f4DualE e 3) =
      ((2 : ZMod p)⁻¹ * ∑ k, (![1, 1, 1, -1] : Fin 4 → ZMod p) k * φ k v) •
        ∑ k, (![1, 1, 1, -1] : Fin 4 → ZMod p) k • e k := by
    intro v
    simp only [f4DualE, f4DualPhi, Fin.sum_univ_four]
    norm_num
    module
  exact ⟨fun h => formula_of_formula h hfg,
    fun h => formula_of_formula h fun v => (hfg v).symm⟩

private lemma f4_formula_12_one (hp2 : p ≠ 2) {r : V ≃ₗ[ZMod p] V} :
    (∀ v, r v = v - (f4DualPhi φ 1 v - 1 * f4DualPhi φ 2 v) •
      (f4DualE e 1 - (1 : ZMod p) • f4DualE e 2)) ↔
    (∀ v, r v = v - ((2 : ZMod p)⁻¹ * ∑ k,
      (![1, -1, -1, -1] : Fin 4 → ZMod p) k * φ k v) •
      ∑ k, (![1, -1, -1, -1] : Fin 4 → ZMod p) k • e k) := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hfg : ∀ v, (f4DualPhi φ 1 v - 1 * f4DualPhi φ 2 v) •
      (f4DualE e 1 - (1 : ZMod p) • f4DualE e 2) =
      ((2 : ZMod p)⁻¹ * ∑ k, (![1, -1, -1, -1] : Fin 4 → ZMod p) k * φ k v) •
        ∑ k, (![1, -1, -1, -1] : Fin 4 → ZMod p) k • e k := by
    intro v
    simp only [f4DualE, f4DualPhi, Fin.sum_univ_four]
    norm_num
    module
  exact ⟨fun h => formula_of_formula h hfg,
    fun h => formula_of_formula h fun v => (hfg v).symm⟩

private lemma f4_formula_12_neg (hp2 : p ≠ 2) {r : V ≃ₗ[ZMod p] V} :
    (∀ v, r v = v - (f4DualPhi φ 1 v - (-1) * f4DualPhi φ 2 v) •
      (f4DualE e 1 - (-1 : ZMod p) • f4DualE e 2)) ↔
    (∀ v, r v = v - ((2 : ZMod p)⁻¹ * ∑ k,
      (![1, -1, 1, 1] : Fin 4 → ZMod p) k * φ k v) •
      ∑ k, (![1, -1, 1, 1] : Fin 4 → ZMod p) k • e k) := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hfg : ∀ v, (f4DualPhi φ 1 v - (-1) * f4DualPhi φ 2 v) •
      (f4DualE e 1 - (-1 : ZMod p) • f4DualE e 2) =
      ((2 : ZMod p)⁻¹ * ∑ k, (![1, -1, 1, 1] : Fin 4 → ZMod p) k * φ k v) •
        ∑ k, (![1, -1, 1, 1] : Fin 4 → ZMod p) k • e k := by
    intro v
    simp only [f4DualE, f4DualPhi, Fin.sum_univ_four]
    norm_num
    module
  exact ⟨fun h => formula_of_formula h hfg,
    fun h => formula_of_formula h fun v => (hfg v).symm⟩

private lemma f4_formula_13_one (hp2 : p ≠ 2) {r : V ≃ₗ[ZMod p] V} :
    (∀ v, r v = v - (f4DualPhi φ 1 v - 1 * f4DualPhi φ 3 v) •
      (f4DualE e 1 - (1 : ZMod p) • f4DualE e 3)) ↔
    (∀ v, r v = v - ((2 : ZMod p)⁻¹ * ∑ k,
      (![1, -1, -1, 1] : Fin 4 → ZMod p) k * φ k v) •
      ∑ k, (![1, -1, -1, 1] : Fin 4 → ZMod p) k • e k) := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hfg : ∀ v, (f4DualPhi φ 1 v - 1 * f4DualPhi φ 3 v) •
      (f4DualE e 1 - (1 : ZMod p) • f4DualE e 3) =
      ((2 : ZMod p)⁻¹ * ∑ k, (![1, -1, -1, 1] : Fin 4 → ZMod p) k * φ k v) •
        ∑ k, (![1, -1, -1, 1] : Fin 4 → ZMod p) k • e k := by
    intro v
    simp only [f4DualE, f4DualPhi, Fin.sum_univ_four]
    norm_num
    module
  exact ⟨fun h => formula_of_formula h hfg,
    fun h => formula_of_formula h fun v => (hfg v).symm⟩

private lemma f4_formula_13_neg (hp2 : p ≠ 2) {r : V ≃ₗ[ZMod p] V} :
    (∀ v, r v = v - (f4DualPhi φ 1 v - (-1) * f4DualPhi φ 3 v) •
      (f4DualE e 1 - (-1 : ZMod p) • f4DualE e 3)) ↔
    (∀ v, r v = v - ((2 : ZMod p)⁻¹ * ∑ k,
      (![1, -1, 1, -1] : Fin 4 → ZMod p) k * φ k v) •
      ∑ k, (![1, -1, 1, -1] : Fin 4 → ZMod p) k • e k) := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hfg : ∀ v, (f4DualPhi φ 1 v - (-1) * f4DualPhi φ 3 v) •
      (f4DualE e 1 - (-1 : ZMod p) • f4DualE e 3) =
      ((2 : ZMod p)⁻¹ * ∑ k, (![1, -1, 1, -1] : Fin 4 → ZMod p) k * φ k v) •
        ∑ k, (![1, -1, 1, -1] : Fin 4 → ZMod p) k • e k := by
    intro v
    simp only [f4DualE, f4DualPhi, Fin.sum_univ_four]
    norm_num
    module
  exact ⟨fun h => formula_of_formula h hfg,
    fun h => formula_of_formula h fun v => (hfg v).symm⟩

private lemma f4w_11mm : ∀ k, (![1, 1, -1, -1] : Fin 4 → ZMod p) k = 1 ∨
    (![1, 1, -1, -1] : Fin 4 → ZMod p) k = -1 := by
  intro k
  fin_cases k <;> first | left; rfl | right; rfl

private lemma f4w_1111 : ∀ k, (![1, 1, 1, 1] : Fin 4 → ZMod p) k = 1 ∨
    (![1, 1, 1, 1] : Fin 4 → ZMod p) k = -1 := by
  intro k
  fin_cases k <;> exact Or.inl rfl

private lemma f4w_11m1 : ∀ k, (![1, 1, -1, 1] : Fin 4 → ZMod p) k = 1 ∨
    (![1, 1, -1, 1] : Fin 4 → ZMod p) k = -1 := by
  intro k
  fin_cases k <;> first | left; rfl | right; rfl

private lemma f4w_111m : ∀ k, (![1, 1, 1, -1] : Fin 4 → ZMod p) k = 1 ∨
    (![1, 1, 1, -1] : Fin 4 → ZMod p) k = -1 := by
  intro k
  fin_cases k <;> first | left; rfl | right; rfl

private lemma f4w_1mmm : ∀ k, (![1, -1, -1, -1] : Fin 4 → ZMod p) k = 1 ∨
    (![1, -1, -1, -1] : Fin 4 → ZMod p) k = -1 := by
  intro k
  fin_cases k <;> first | left; rfl | right; rfl

private lemma f4w_1m11 : ∀ k, (![1, -1, 1, 1] : Fin 4 → ZMod p) k = 1 ∨
    (![1, -1, 1, 1] : Fin 4 → ZMod p) k = -1 := by
  intro k
  fin_cases k <;> first | left; rfl | right; rfl

private lemma f4w_1mm1 : ∀ k, (![1, -1, -1, 1] : Fin 4 → ZMod p) k = 1 ∨
    (![1, -1, -1, 1] : Fin 4 → ZMod p) k = -1 := by
  intro k
  fin_cases k <;> first | left; rfl | right; rfl

private lemma f4w_1m1m : ∀ k, (![1, -1, 1, -1] : Fin 4 → ZMod p) k = 1 ∨
    (![1, -1, 1, -1] : Fin 4 → ZMod p) k = -1 := by
  intro k
  fin_cases k <;> first | left; rfl | right; rfl



private lemma f4_mem_S {r : V ≃ₗ[ZMod p] V} {i : Fin 4}
    (h : ∀ v, r v = v - (2 * φ i v) • e i) : r ∈ ggCZS e φ := ⟨i, h⟩

private lemma f4_mem_H {r : V ≃ₗ[ZMod p] V} {w : Fin 4 → ZMod p}
    (hw : ∀ k, w k = 1 ∨ w k = -1)
    (h : ∀ v, r v = v - ((2 : ZMod p)⁻¹ * ∑ k, w k * φ k v) • ∑ k, w k • e k) :
    r ∈ ggCZH e φ := ⟨w, hw, h⟩

private lemma f4_mem_D {r : V ≃ₗ[ZMod p] V} {i j : Fin 4} {ε : ZMod p}
    (hij : i ≠ j) (hε : ε = 1 ∨ ε = -1)
    (h : ∀ v, r v = v - (f4DualPhi φ i v - ε * f4DualPhi φ j v) •
      (f4DualE e i - ε • f4DualE e j)) :
    r ∈ ggCZRD (f4DualE e) (f4DualPhi φ) := ⟨i, j, hij, ε, hε, h⟩

private lemma f4_D_subset (hp2 : p ≠ 2) :
    ggCZRD (f4DualE e) (f4DualPhi φ) ⊆ ggCZS e φ ∪ ggCZH e φ := by
  rintro r ⟨i, j, hij, ε, hε, h⟩
  rcases hε with rfl | rfl
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Or.inl (f4_mem_S ((f4_formula_01_one hp2).mp h))
    · exact Or.inr (f4_mem_H f4w_11mm ((f4_formula_02_one hp2).mp h))
    · exact Or.inr (f4_mem_H f4w_11m1 ((f4_formula_03_one hp2).mp h))
    · exact Or.inl (f4_mem_S ((f4_formula_01_one hp2).mp
        (formula_swap (Or.inl rfl) h)))
    · exact absurd rfl hij
    · exact Or.inr (f4_mem_H f4w_1mmm ((f4_formula_12_one hp2).mp h))
    · exact Or.inr (f4_mem_H f4w_1mm1 ((f4_formula_13_one hp2).mp h))
    · exact Or.inr (f4_mem_H f4w_11mm ((f4_formula_02_one hp2).mp
        (formula_swap (Or.inl rfl) h)))
    · exact Or.inr (f4_mem_H f4w_1mmm ((f4_formula_12_one hp2).mp
        (formula_swap (Or.inl rfl) h)))
    · exact absurd rfl hij
    · exact Or.inl (f4_mem_S ((f4_formula_23_one hp2).mp h))
    · exact Or.inr (f4_mem_H f4w_11m1 ((f4_formula_03_one hp2).mp
        (formula_swap (Or.inl rfl) h)))
    · exact Or.inr (f4_mem_H f4w_1mm1 ((f4_formula_13_one hp2).mp
        (formula_swap (Or.inl rfl) h)))
    · exact Or.inl (f4_mem_S ((f4_formula_23_one hp2).mp
        (formula_swap (Or.inl rfl) h)))
    · exact absurd rfl hij
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Or.inl (f4_mem_S ((f4_formula_01_neg hp2).mp h))
    · exact Or.inr (f4_mem_H f4w_1111 ((f4_formula_02_neg hp2).mp h))
    · exact Or.inr (f4_mem_H f4w_111m ((f4_formula_03_neg hp2).mp h))
    · exact Or.inl (f4_mem_S ((f4_formula_01_neg hp2).mp
        (formula_swap (Or.inr rfl) h)))
    · exact absurd rfl hij
    · exact Or.inr (f4_mem_H f4w_1m11 ((f4_formula_12_neg hp2).mp h))
    · exact Or.inr (f4_mem_H f4w_1m1m ((f4_formula_13_neg hp2).mp h))
    · exact Or.inr (f4_mem_H f4w_1111 ((f4_formula_02_neg hp2).mp
        (formula_swap (Or.inr rfl) h)))
    · exact Or.inr (f4_mem_H f4w_1m11 ((f4_formula_12_neg hp2).mp
        (formula_swap (Or.inr rfl) h)))
    · exact absurd rfl hij
    · exact Or.inl (f4_mem_S ((f4_formula_23_neg hp2).mp h))
    · exact Or.inr (f4_mem_H f4w_111m ((f4_formula_03_neg hp2).mp
        (formula_swap (Or.inr rfl) h)))
    · exact Or.inr (f4_mem_H f4w_1m1m ((f4_formula_13_neg hp2).mp
        (formula_swap (Or.inr rfl) h)))
    · exact Or.inl (f4_mem_S ((f4_formula_23_neg hp2).mp
        (formula_swap (Or.inr rfl) h)))
    · exact absurd rfl hij

private lemma f4_S_to_D (hp2 : p ≠ 2) {r : V ≃ₗ[ZMod p] V} {i : Fin 4}
    (h : ∀ v, r v = v - (2 * φ i v) • e i) :
    r ∈ ggCZRD (f4DualE e) (f4DualPhi φ) := by
  fin_cases i
  · exact f4_mem_D (by decide) (Or.inr rfl) ((f4_formula_01_neg hp2).mpr h)
  · exact f4_mem_D (by decide) (Or.inl rfl) ((f4_formula_01_one hp2).mpr h)
  · exact f4_mem_D (by decide) (Or.inr rfl) ((f4_formula_23_neg hp2).mpr h)
  · exact f4_mem_D (by decide) (Or.inl rfl) ((f4_formula_23_one hp2).mpr h)

private lemma f4_H_to_D (hp2 : p ≠ 2) {w : Fin 4 → ZMod p}
    (hw : ∀ k, w k = 1 ∨ w k = -1) {r : V ≃ₗ[ZMod p] V}
    (h : ∀ v, r v = v - ((2 : ZMod p)⁻¹ * ∑ k, w k * φ k v) • ∑ k, w k • e k) :
    r ∈ ggCZRD (f4DualE e) (f4DualPhi φ) := by
  rcases hw 0 with h0 | h0 <;> rcases hw 1 with h1 | h1 <;>
    rcases hw 2 with h2 | h2 <;> rcases hw 3 with h3 | h3
  · refine f4_mem_D (by decide) (Or.inr rfl) ((f4_formula_02_neg hp2).mpr ?_)
    intro v
    rw [h v]
    simp only [Fin.sum_univ_four, h0, h1, h2, h3]
    norm_num
  · refine f4_mem_D (by decide) (Or.inr rfl) ((f4_formula_03_neg hp2).mpr ?_)
    intro v
    rw [h v]
    simp only [Fin.sum_univ_four, h0, h1, h2, h3]
    norm_num
  · refine f4_mem_D (by decide) (Or.inl rfl) ((f4_formula_03_one hp2).mpr ?_)
    intro v
    rw [h v]
    simp only [Fin.sum_univ_four, h0, h1, h2, h3]
    norm_num
  · refine f4_mem_D (by decide) (Or.inl rfl) ((f4_formula_02_one hp2).mpr ?_)
    intro v
    rw [h v]
    simp only [Fin.sum_univ_four, h0, h1, h2, h3]
    norm_num
  · refine f4_mem_D (by decide) (Or.inr rfl) ((f4_formula_12_neg hp2).mpr ?_)
    intro v
    rw [h v]
    simp only [Fin.sum_univ_four, h0, h1, h2, h3]
    norm_num
  · refine f4_mem_D (by decide) (Or.inr rfl) ((f4_formula_13_neg hp2).mpr ?_)
    intro v
    rw [h v]
    simp only [Fin.sum_univ_four, h0, h1, h2, h3]
    norm_num
  · refine f4_mem_D (by decide) (Or.inl rfl) ((f4_formula_13_one hp2).mpr ?_)
    intro v
    rw [h v]
    simp only [Fin.sum_univ_four, h0, h1, h2, h3]
    norm_num
  · refine f4_mem_D (by decide) (Or.inl rfl) ((f4_formula_12_one hp2).mpr ?_)
    intro v
    rw [h v]
    simp only [Fin.sum_univ_four, h0, h1, h2, h3]
    norm_num
  · refine f4_mem_D (by decide) (Or.inl rfl) ((f4_formula_12_one hp2).mpr ?_)
    intro v
    rw [h v]
    simp only [Fin.sum_univ_four, h0, h1, h2, h3]
    norm_num
    module
  · refine f4_mem_D (by decide) (Or.inl rfl) ((f4_formula_13_one hp2).mpr ?_)
    intro v
    rw [h v]
    simp only [Fin.sum_univ_four, h0, h1, h2, h3]
    norm_num
    module
  · refine f4_mem_D (by decide) (Or.inr rfl) ((f4_formula_13_neg hp2).mpr ?_)
    intro v
    rw [h v]
    simp only [Fin.sum_univ_four, h0, h1, h2, h3]
    norm_num
    module
  · refine f4_mem_D (by decide) (Or.inr rfl) ((f4_formula_12_neg hp2).mpr ?_)
    intro v
    rw [h v]
    simp only [Fin.sum_univ_four, h0, h1, h2, h3]
    norm_num
    module
  · refine f4_mem_D (by decide) (Or.inl rfl) ((f4_formula_02_one hp2).mpr ?_)
    intro v
    rw [h v]
    simp only [Fin.sum_univ_four, h0, h1, h2, h3]
    norm_num
    module
  · refine f4_mem_D (by decide) (Or.inl rfl) ((f4_formula_03_one hp2).mpr ?_)
    intro v
    rw [h v]
    simp only [Fin.sum_univ_four, h0, h1, h2, h3]
    norm_num
    module
  · refine f4_mem_D (by decide) (Or.inr rfl) ((f4_formula_03_neg hp2).mpr ?_)
    intro v
    rw [h v]
    simp only [Fin.sum_univ_four, h0, h1, h2, h3]
    norm_num
    module
  · refine f4_mem_D (by decide) (Or.inr rfl) ((f4_formula_02_neg hp2).mpr ?_)
    intro v
    rw [h v]
    simp only [Fin.sum_univ_four, h0, h1, h2, h3]
    norm_num
    module

private lemma f4_S_H_subset (hp2 : p ≠ 2) :
    ggCZS e φ ∪ ggCZH e φ ⊆ ggCZRD (f4DualE e) (f4DualPhi φ) := by
  rintro r (hr | hr)
  · obtain ⟨i, hi⟩ := hr
    exact f4_S_to_D hp2 hi
  · obtain ⟨w, hw, h⟩ := hr
    exact f4_H_to_D hp2 hw h

private lemma f4_RD_eq (hp2 : p ≠ 2) :
    ggCZRD (f4DualE e) (f4DualPhi φ) = ggCZS e φ ∪ ggCZH e φ :=
  Set.Subset.antisymm (f4_D_subset hp2) (f4_S_H_subset hp2)


end

theorem ggCZ_F4_dual (hp2 : p ≠ 2) {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) :
    ∃ (e' : Fin 4 → V) (φ' : Fin 4 → Module.Dual (ZMod p) V), GGCZDual e' φ' ∧
      (∀ v, (∀ k, φ' k v = 0) ↔ ∀ k, φ k v = 0) ∧
      ggCZRD e' φ' = ggCZS e φ ∪ ggCZH e φ ∧ ggCZS e' φ' ∪ ggCZH e' φ' = ggCZRD e φ := by
  refine ⟨f4DualE e, f4DualPhi φ, f4Dual_dual hp2 hd, ?_, f4_RD_eq hp2, ?_⟩
  · intro v
    exact f4Dual_ker hp2 v
  · have hdual := f4Dual_dual hp2 hd
    have hscale : ggCZRD (f4DualE (f4DualE e)) (f4DualPhi (f4DualPhi φ)) =
        ggCZRD e φ := by
      rw [f4DualE_f4DualE (p := p) (e := e), f4DualPhi_f4DualPhi (p := p) (φ := φ) hp2]
      exact ggCZRD_smul (p := p) (e := e) (φ := φ) (c := 2) (zmod_two_ne_zero hp2)
    have hdouble := f4_RD_eq (p := p) (e := f4DualE e) (φ := f4DualPhi φ) hp2
    rw [hscale] at hdouble
    exact hdouble.symm

end

end CFSG.StandardType

end
