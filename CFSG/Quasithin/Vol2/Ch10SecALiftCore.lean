module

public import CFSG.Quasithin.Vol2.Ch10SecALift

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

variable {F : Type} [Field F] [CharP F 2] {M : Type} [CommGroup M]

theorem fix_of_natural (hM : ∀ m : M, m ^ 2 = 1)
    (ρ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut M) {Z : Subgroup M}
    (hZ : ∀ γ, ∀ z ∈ Z, ρ γ z = z) (β : M →* Multiplicative (Fin 2 → F))
    (hβs : Function.Surjective β) (hβk : ∀ w, β w = 1 ↔ w ∈ Z)
    (hβe : ∀ γ w, β (ρ γ w) = Multiplicative.ofAdd
      ((γ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β w))))
    {w : M} (hw : Multiplicative.toAdd (β w) 1 = 0) (b : F) : ρ (unipSL b) w = w := by
  set E : M → F → M := fun w b => ρ (unipSL b) w * w⁻¹ with hEdef
  have hβu : ∀ (a : F) (w : M), Multiplicative.toAdd (β (ρ (unipSL a) w)) =
      ![Multiplicative.toAdd (β w) 0 + a * Multiplicative.toAdd (β w) 1,
        Multiplicative.toAdd (β w) 1] := by
    intro a w
    rw [hβe, toAdd_ofAdd, coe_unipSL, unipSL_mulVec]
  have hβh : ∀ {μ : F} (hμ : μ ≠ 0) (w : M), Multiplicative.toAdd (β (ρ (diagSL hμ) w)) =
      ![μ * Multiplicative.toAdd (β w) 0, μ⁻¹ * Multiplicative.toAdd (β w) 1] := by
    intro μ hμ w
    rw [hβe, toAdd_ofAdd, coe_diagSL, diagSL_mulVec]
  have hEZ : ∀ w : M, Multiplicative.toAdd (β w) 1 = 0 → ∀ b, E w b ∈ Z := by
    intro w hw b
    rw [← hβk]
    apply Multiplicative.toAdd.injective
    rw [hEdef]
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv, toAdd_one, hβu b w, hw, mul_zero,
      add_zero]
    ext i
    fin_cases i <;> simp [hw]
  have hEβ : ∀ w w' : M, β w = β w' → ∀ b, E w b = E w' b := by
    intro w w' h b
    have hc : w⁻¹ * w' ∈ Z := by rw [← hβk, map_mul, map_inv, h, inv_mul_cancel]
    have hw' : w' = w * (w⁻¹ * w') := by group
    rw [hEdef]
    dsimp only
    rw [hw', map_mul, hZ _ _ hc]
    group
  have hEtor : ∀ {μ : F} (hμ : μ ≠ 0) (w : M), Multiplicative.toAdd (β w) 1 = 0 →
      ∀ b, E (ρ (diagSL hμ) w) (μ ^ 2 * b) = E w b := by
    intro μ hμ w hw b
    have hconj : ρ (unipSL (μ ^ 2 * b)) = ρ (diagSL hμ) * ρ (unipSL b) * (ρ (diagSL hμ))⁻¹ := by
      rw [← diagSL_conj hμ b, map_mul, map_mul, map_inv]
    have h1 : E (ρ (diagSL hμ) w) (μ ^ 2 * b) = ρ (diagSL hμ) (E w b) := by
      rw [hEdef]
      dsimp only
      rw [hconj, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, map_mul, map_inv]
    rw [h1, hZ _ _ (hEZ w hw b)]
  have hEdiag : ∀ a : F, ∃ x : M, β x = Multiplicative.ofAdd ![a, 0] ∧ E x a = 1 := by
    intro a
    obtain ⟨y, hy⟩ := hβs (Multiplicative.ofAdd ![0, 1])
    refine ⟨ρ (unipSL a) y * y⁻¹, ?_, ?_⟩
    · apply Multiplicative.toAdd.injective
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hβu, hy, toAdd_ofAdd]
      ext i
      fin_cases i <;> simp
    · rw [hEdef]
      dsimp only
      have h2 : ρ (unipSL a) (ρ (unipSL a) y) = y := by
        rw [← MulAut.mul_apply, ← map_mul, unipSL_mul_self, map_one, MulAut.one_apply]
      rw [map_mul, map_inv, h2]
      have hsq := hM (ρ (unipSL a) y * y⁻¹)
      calc y * (ρ (unipSL a) y)⁻¹ * (ρ (unipSL a) y * y⁻¹)⁻¹
          = ((ρ (unipSL a) y * y⁻¹)⁻¹) ^ 2 := by rw [sq]; group
        _ = 1 := by rw [inv_pow, hsq, inv_one]
  obtain ⟨w₁, hw₁⟩ := hβs (Multiplicative.ofAdd ![1, 0])
  have hw₁' : Multiplicative.toAdd (β w₁) 1 = 0 := by rw [hw₁, toAdd_ofAdd]; rfl
  have hE₁ : ∀ d : F, E w₁ d = 1 := by
    intro d
    by_cases hd : d = 0
    · rw [hEdef]
      dsimp only
      rw [hd, unipSL_zero, map_one, MulAut.one_apply, mul_inv_cancel]
    · obtain ⟨x, hx, hxE⟩ := hEdiag d⁻¹
      have hx1 : Multiplicative.toAdd (β x) 1 = 0 := by rw [hx, toAdd_ofAdd]; rfl
      have h1 := hEtor hd x hx1 d⁻¹
      rw [hxE, show d ^ 2 * d⁻¹ = d by field_simp] at h1
      rw [← h1]
      refine hEβ _ _ ?_ d
      apply Multiplicative.toAdd.injective
      rw [hβh hd, hx, hw₁, toAdd_ofAdd, toAdd_ofAdd]
      ext i
      fin_cases i <;> simp [hd]
  set c := Multiplicative.toAdd (β w) 0 with hc
  have hfin : E w b = 1 := by
    by_cases hc0 : c = 0
    · have hwZ : w ∈ Z := by
        rw [← hβk]
        apply Multiplicative.toAdd.injective
        ext i
        fin_cases i
        · simpa [hc] using hc0
        · simpa using hw
      rw [hEdef]
      dsimp only
      rw [hZ _ _ hwZ, mul_inv_cancel]
    · have h1 := hEtor hc0 w₁ hw₁' (c⁻¹ ^ 2 * b)
      rw [show c ^ 2 * (c⁻¹ ^ 2 * b) = b by field_simp, hE₁] at h1
      rw [← hEβ (ρ (diagSL hc0) w₁) w ?_ b, h1]
      apply Multiplicative.toAdd.injective
      rw [hβh hc0, hw₁, toAdd_ofAdd]
      ext i
      fin_cases i
      · simp [hc]
      · simpa using hw.symm
  have := hfin
  rw [hEdef] at this
  exact mul_inv_eq_one.mp this

end CFSG.Quasithin.Vol2.Ch10.SecA
