module

public import CFSG.Quasithin.Background.SmithCurtisMain
public import CFSG.LieType.Universal.Spin.Chevalley.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin

private theorem c2slomqi2_sl2_gauss {F : Type*} [Field F] {s t : F} (hd : 1 + s * t ≠ 0) :
    upperSL2 s * lowerSL2 t =
      lowerSL2 (t / (1 + s * t)) * diagSL2 (Units.mk0 (1 + s * t) hd) *
        upperSL2 (s / (1 + s * t)) := by
  have hd' : 1 + t * s ≠ 0 := by rwa [mul_comm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp
  · field_simp
  · field_simp
    ring

private theorem c2slomqi2_sl2_singular {F : Type*} [Field F] {s t : F} (hd : 1 + s * t = 0)
    (hs : s ≠ 0) :
    upperSL2 s * lowerSL2 t = diagSL2 (Units.mk0 s hs) * weylSL2 1 * upperSL2 (-s) := by
  have ht : t = -s⁻¹ := by
    field_simp
    linear_combination hd
  subst ht
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [mul_inv_cancel₀ hs]; ring
  · rw [inv_mul_cancel₀ hs]

theorem omq_curtis_hcoeff_of_bruhat {G : Type*} [Group G] [Finite G] {B : Type*}
    {M : CoxeterMatrix B} {W : Type*} [Group W] {cs : CoxeterSystem M W} {p : ℕ} [Fact p.Prime]
    (D : CurtisDatum G cs p) {F k V : Type*} [Field F] [Field k] [CharP k p]
    [AddCommGroup V] [Module k V] (ι : F →+* k) {σ : Representation k G V}
    (hσ : IsSimpleRep σ) {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType σ y χ μ)
    (X Y : F → G) (T : Fˣ → G) (N : G)
    (hX : ∀ a, X a ∈ D.U) (hY : ∀ a, Y a ∈ D.L) (hT : ∀ a, T a ∈ D.H)
    {c : ℕ} (hc : 1 ≤ c) (hχ : ∀ a : Fˣ, χ (T a) = ι (a : F) ^ c)
    (hgauss : ∀ (s t : F) (hd : 1 + s * t ≠ 0),
      X s * Y t = Y (t / (1 + s * t)) * T (Units.mk0 (1 + s * t) hd) * X (s / (1 + s * t)))
    (hsing : ∀ s t : F, 1 + s * t = 0 → ∃ (a : Fˣ) (u : F), X s * Y t = T a * N * X u)
    (hN : σ N y ∈ augSub σ D.L) :
    ∃ φ : Module.Dual k V, φ y = 1 ∧
      ∀ s t : F, φ (σ (X s * Y t) y) = (1 + ι s * ι t) ^ c := by
  obtain ⟨φ, hφ, hφy⟩ := D.exists_form hσ ht.1 ht.2.1
  refine ⟨φ, hφy, fun s t => ?_⟩
  have hιd : ι (1 + s * t) = 1 + ι s * ι t := by rw [map_add, map_mul, map_one]
  by_cases hd : 1 + s * t = 0
  · obtain ⟨a, u, he⟩ := hsing s t hd
    have hmem : σ (X s * Y t) y ∈ augSub σ D.L := by
      rw [he, ← act_mul, ← act_mul, (D.mem_fixU σ).mp ht.1 _ (hX u)]
      exact act_mem_augSub σ (fun l hl => D.H_normL _ (hT a) l hl) hN
    rw [hφ _ hmem, ← hιd, hd, map_zero, zero_pow (by omega)]
  · have h1 : σ (Y (t / (1 + s * t))) y - y ∈ augSub σ D.L := sub_mem_augSub σ (hY _) y
    have h2 : φ (σ (Y (t / (1 + s * t))) y) = 1 := by
      have := hφ _ h1
      rw [map_sub, hφy, sub_eq_zero] at this
      exact this
    rw [hgauss s t hd, ← act_mul, ← act_mul, (D.mem_fixU σ).mp ht.1 _ (hX _),
      ht.2.2.1 _ (hT _), map_smul, map_smul, h2, hχ, smul_eq_mul, mul_one, Units.val_mk0, hιd]

theorem omq_curtis_hcoeff_of_sl2 {G : Type*} [Group G] [Finite G] {B : Type*}
    {M : CoxeterMatrix B} {W : Type*} [Group W] {cs : CoxeterSystem M W} {p : ℕ} [Fact p.Prime]
    (D : CurtisDatum G cs p) {F k V : Type*} [Field F] [Field k] [CharP k p]
    [AddCommGroup V] [Module k V] (ι : F →+* k) {σ : Representation k G V}
    (hσ : IsSimpleRep σ) {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType σ y χ μ)
    (Φ : Matrix.SpecialLinearGroup (Fin 2) F →* G)
    (hX : ∀ a, Φ (upperSL2 a) ∈ D.U) (hY : ∀ a, Φ (lowerSL2 a) ∈ D.L)
    (hT : ∀ a : Fˣ, Φ (diagSL2 a) ∈ D.H) {c : ℕ} (hc : 1 ≤ c)
    (hχ : ∀ a : Fˣ, χ (Φ (diagSL2 a)) = ι (a : F) ^ c)
    (hN : σ (Φ (weylSL2 1)) y ∈ augSub σ D.L) :
    ∃ φ : Module.Dual k V, φ y = 1 ∧
      ∀ s t : F, φ (σ (Φ (upperSL2 s) * Φ (lowerSL2 t)) y) = (1 + ι s * ι t) ^ c := by
  refine omq_curtis_hcoeff_of_bruhat D ι hσ ht (fun a => Φ (upperSL2 a))
    (fun a => Φ (lowerSL2 a)) (fun a => Φ (diagSL2 a)) (Φ (weylSL2 1)) hX hY hT hc hχ ?_ ?_ hN
  · intro s t hd
    rw [← map_mul, ← map_mul, ← map_mul, c2slomqi2_sl2_gauss hd]
  · intro s t hd
    have hs : s ≠ 0 := by
      rintro rfl
      simp at hd
    exact ⟨Units.mk0 s hs, -s, by
      rw [← map_mul, ← map_mul, ← map_mul, c2slomqi2_sl2_singular hd hs]⟩

end CFSG.LocalAnalysis.WeakClosure81
