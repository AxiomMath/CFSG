module

public import CFSG.LocalAnalysis.StandardType.GGF4Rk2Core
import CFSG.LocalAnalysis.StandardType.GGF4ReflData
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.F4Model

@[expose] def axB : ℕ := 12

@[expose] def axC : ℕ := 0

@[expose] def wordB : List (ℕ × List (Fin 3) × Fin 3) :=
  [(1, [0, 1], 2), (3, [], 0), (5, [0], 1), (6, [2, 0], 1), (9, [1, 2, 0], 1), (14, [], 2),
   (16, [], 1), (17, [2], 1), (19, [1], 2)]

@[expose] def wordC : List (ℕ × List (Fin 3) × Fin 3) :=
  [(13, [], 0), (14, [], 1), (15, [0], 1), (16, [], 2), (17, [1], 2), (18, [0, 1], 2), (19, [2], 1),
   (20, [2, 0], 1), (21, [1, 2, 0], 1)]

abbrev CommM (x y : ℕ) : Prop := (Rm x).mul (Rm y) = (Rm y).mul (Rm x)

abbrev WordOK (σ : Fin 3 → Fin 4) (refl : List ℕ) (words : List (ℕ × List (Fin 3) × Fin 3)) :
    Prop :=
  ∀ x ∈ refl, ∃ e ∈ words, e.1 = x ∧ conjW (e.2.1.map σ) (Sm (σ e.2.2)) = Rm x

theorem axB_spec : ∀ y, y < 24 → y ≠ axB → CommM y axB → y ∈ reflB := by decide +kernel

theorem axC_spec : ∀ y, y < 24 → y ≠ axC → CommM y axC → y ∈ reflC := by decide +kernel

theorem sharedB : ∀ z, z < 24 → ∃ y ∈ reflB, y ≠ z ∧ CommM y z := by decide +kernel

theorem sharedC : ∀ z, z < 24 → ∃ y ∈ reflC, y ≠ z ∧ CommM y z := by decide +kernel

theorem wordB_spec : WordOK posB reflB wordB := by decide +kernel

theorem wordC_spec : WordOK posC reflC wordC := by decide +kernel

private theorem sharedB_first_two : ∀ z, z < 24 →
    ∃ y ∈ reflB, y ≠ z ∧ CommM y z ∧ ∃ e ∈ wordB,
      e.1 = y ∧ conjW (e.2.1.map posB) (Sm (posB e.2.2)) = Rm y ∧
        e.2.2 ≠ (2 : Fin 3) := by decide +kernel

private theorem sharedC_first_two : ∀ z, z < 24 →
    ∃ y ∈ reflC, y ≠ z ∧ CommM y z ∧ ∃ e ∈ wordC,
      e.1 = y ∧ conjW (e.2.1.map posC) (Sm (posC e.2.2)) = Rm y ∧
        e.2.2 ≠ (2 : Fin 3) := by decide +kernel

namespace F4Rep

variable {W : Type} [Group W] (R : F4Rep W)

private theorem exists_pos {a : Fin 3 → W} (ha : ∀ k, R.IsRefl (a k))
    (ha01 : orderOf (a 0 * a 1) = 3) (ha12 : orderOf (a 1 * a 2) = 4)
    (ha02 : orderOf (a 0 * a 2) = 2) :
    ∃ (g : W) (σ : Fin 3 → Fin 4) (ax : ℕ) (refl : List ℕ)
      (words : List (ℕ × List (Fin 3) × Fin 3)),
      (∀ k, g * a k * g⁻¹ = R.s (σ k)) ∧ ax < 24 ∧
      (∀ y, y < 24 → y ≠ ax → CommM y ax → y ∈ refl) ∧
      (∀ z, z < 24 → ∃ y ∈ refl, y ≠ z ∧ CommM y z) ∧ WordOK σ refl words ∧
      (∀ y ∈ refl, y < 24) ∧ ∀ z, z < 24 →
        ∃ y ∈ refl, y ≠ z ∧ CommM y z ∧ ∃ e ∈ words,
          e.1 = y ∧ conjW (e.2.1.map σ) (Sm (σ e.2.2)) = Rm y ∧
            e.2.2 ≠ (2 : Fin 3) := by
  obtain ⟨g, hg⟩ := R.classify (ha 0) (ha 1) (ha 2) ha01 ha12 ha02
  have hk : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  rcases hg with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · refine ⟨g, posB, axB, reflB, wordB, ?_, by decide, axB_spec, sharedB, wordB_spec,
      by decide, sharedB_first_two⟩
    intro k
    rcases hk k with rfl | rfl | rfl
    exacts [h0, h1, h2]
  · refine ⟨g, posC, axC, reflC, wordC, ?_, by decide, axC_spec, sharedC, wordC_spec,
      by decide, sharedC_first_two⟩
    intro k
    rcases hk k with rfl | rfl | rfl
    exacts [h0, h1, h2]

private theorem wd_map_eq {a : Fin 3 → W} {g : W} {σ : Fin 3 → Fin 4}
    (hσ : ∀ k, g * a k * g⁻¹ = R.s (σ k)) (v : List (Fin 3)) :
    R.wd (v.map σ) = g * (v.map a).prod * g⁻¹ := by
  induction v with
  | nil => simp [wd]
  | cons k v ih =>
    have hw : R.wd ((k :: v).map σ) = R.s (σ k) * R.wd (v.map σ) := by simp [wd]
    rw [hw, ih, ← hσ k, List.map_cons, List.prod_cons]
    group

private abbrev cj (k : W) (A : Matrix (Fin 4) (Fin 4) ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  R.ρ k * A * R.ρ k⁻¹

private theorem cj_mul (k : W) (A B : Matrix (Fin 4) (Fin 4) ℤ) :
    R.cj k (A * B) = R.cj k A * R.cj k B := by
  simp only [cj, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (R.ρ k⁻¹) (R.ρ k), ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]

private theorem cj_cj (k l : W) (A : Matrix (Fin 4) (Fin 4) ℤ) :
    R.cj k (R.cj l A) = R.cj (k * l) A := by
  simp only [cj, mul_inv_rev, map_mul, Matrix.mul_assoc]

private theorem cj_one (A : Matrix (Fin 4) (Fin 4) ℤ) : R.cj 1 A = A := by
  simp [cj]

private theorem rho_entry {a : Fin 3 → W} {g : W} {σ : Fin 3 → Fin 4}
    (hσ : ∀ k, g * a k * g⁻¹ = R.s (σ k)) {x : ℕ} {e : ℕ × List (Fin 3) × Fin 3}
    (he : conjW (e.2.1.map σ) (Sm (σ e.2.2)) = Rm x) :
    R.ρ ((e.2.1.map a).prod * a e.2.2 * ((e.2.1.map a).prod)⁻¹) = R.cj g⁻¹ (Rm x).toMat := by
  have h1 := R.rho_conj_wd (e.2.1.map σ) (R.hs (σ e.2.2))
  rw [he, wd_map_eq R hσ, ← hσ e.2.2] at h1
  have e1 : g * (e.2.1.map a).prod * g⁻¹ * (g * a e.2.2 * g⁻¹) *
      (g * (e.2.1.map a).prod * g⁻¹)⁻¹ =
      g * ((e.2.1.map a).prod * a e.2.2 * ((e.2.1.map a).prod)⁻¹) * g⁻¹ := by group
  rw [e1, map_mul, map_mul] at h1
  rw [← h1, cj, inv_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  group

private theorem exists_shared_refl_ne_two_left {a b : Fin 3 → W} (ha : ∀ k, R.IsRefl (a k))
    (ha01 : orderOf (a 0 * a 1) = 3) (ha12 : orderOf (a 1 * a 2) = 4)
    (ha02 : orderOf (a 0 * a 2) = 2) (hb : ∀ k, R.IsRefl (b k))
    (hb01 : orderOf (b 0 * b 1) = 3) (hb12 : orderOf (b 1 * b 2) = 4)
    (hb02 : orderOf (b 0 * b 2) = 2) :
    ∃ (u v : List (Fin 3)) (c d : Fin 3),
      (u.map a).prod * a c * ((u.map a).prod)⁻¹ =
        (v.map b).prod * b d * ((v.map b).prod)⁻¹ ∧ c ≠ 2 := by
  obtain ⟨g, σ, -, refla, wordsa, hσ, -, -, -, -, hra, hsha⟩ :=
    R.exists_pos ha ha01 ha12 ha02
  obtain ⟨h, τ, ax, reflb, wordsb, hτ, hax, haxb, -, hwb, -, -⟩ :=
    R.exists_pos hb hb01 hb12 hb02
  obtain ⟨z, hz, ehz⟩ := (R.conjR2 (g * h⁻¹)).1 ax hax
  obtain ⟨y, hyr, hyz, hcomm, ea, -, -, hea, hc⟩ := hsha z hz
  have hy : y < 24 := hra y hyr
  obtain ⟨x, hx, ehx⟩ := (R.conjR2 (g * h⁻¹)).2 y hy
  have ehx' : R.cj (g * h⁻¹)⁻¹ (Rm y).toMat = (Rm x).toMat := ehx
  have eax : (Rm ax).toMat = R.cj (g * h⁻¹)⁻¹ (Rm z).toMat := by
    rw [← ehz, show R.ρ (g * h⁻¹) * (Rm ax).toMat * R.ρ (g * h⁻¹)⁻¹ =
      R.cj (g * h⁻¹) (Rm ax).toMat from rfl, cj_cj, inv_mul_cancel, cj_one]
  have hcx : CommM x ax := by
    apply M4.toMat_injective
    have hc := congrArg M4.toMat hcomm
    rw [M4.toMat_mul, M4.toMat_mul] at hc ⊢
    rw [← ehx', eax, ← cj_mul, ← cj_mul, hc]
  have hxax : x ≠ ax := by
    rintro rfl
    apply hyz
    apply Rm_inj y hy z hz
    apply M4.toMat_injective
    rw [← ehz, show R.ρ (g * h⁻¹) * (Rm x).toMat * R.ρ (g * h⁻¹)⁻¹ =
      R.cj (g * h⁻¹) (Rm x).toMat from rfl, ← ehx', cj_cj, mul_inv_cancel, cj_one]
  have hxr : x ∈ reflb := haxb x hx hxax hcx
  obtain ⟨eb, -, heb1, heb⟩ := hwb x hxr
  refine ⟨ea.2.1, eb.2.1, ea.2.2, eb.2.2, R.inj ?_, hc⟩
  rw [R.rho_entry hσ hea, R.rho_entry hτ heb, ← ehx', cj_cj]
  congr 1
  group

theorem exists_shared_refl_ne_two {a b : Fin 3 → W} (ha : ∀ k, R.IsRefl (a k))
    (ha01 : orderOf (a 0 * a 1) = 3) (ha12 : orderOf (a 1 * a 2) = 4)
    (ha02 : orderOf (a 0 * a 2) = 2) (hb : ∀ k, R.IsRefl (b k))
    (hb01 : orderOf (b 0 * b 1) = 3) (hb12 : orderOf (b 1 * b 2) = 4)
    (hb02 : orderOf (b 0 * b 2) = 2) :
    ∃ (u v : List (Fin 3)) (c d : Fin 3),
      (u.map a).prod * a c * ((u.map a).prod)⁻¹ =
        (v.map b).prod * b d * ((v.map b).prod)⁻¹ ∧ d ≠ 2 := by
  obtain ⟨v, u, d, c, h, hd⟩ :=
    R.exists_shared_refl_ne_two_left hb hb01 hb12 hb02 ha ha01 ha12 ha02
  exact ⟨u, v, c, d, h.symm, hd⟩

theorem exists_shared_refl {a b : Fin 3 → W} (ha : ∀ k, R.IsRefl (a k))
    (ha01 : orderOf (a 0 * a 1) = 3) (ha12 : orderOf (a 1 * a 2) = 4)
    (ha02 : orderOf (a 0 * a 2) = 2) (hb : ∀ k, R.IsRefl (b k))
    (hb01 : orderOf (b 0 * b 1) = 3) (hb12 : orderOf (b 1 * b 2) = 4)
    (hb02 : orderOf (b 0 * b 2) = 2) :
    ∃ (u v : List (Fin 3)) (c d : Fin 3),
      (u.map a).prod * a c * ((u.map a).prod)⁻¹ = (v.map b).prod * b d * ((v.map b).prod)⁻¹ := by
  obtain ⟨u, v, c, d, h, -⟩ :=
    R.exists_shared_refl_ne_two ha ha01 ha12 ha02 hb hb01 hb12 hb02
  exact ⟨u, v, c, d, h⟩

end F4Rep

end CFSG.StandardType.F4Model

end
