module

public import CFSG.Quasithin.Vol2.Ch10SecQ6O4d
public import CFSG.Quasithin.Vol2.Ch10SecQ6Rk
public import CFSG.Quasithin.Vol2.Ch10SecQ6O4b

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Matrix

variable {W : Type*} [CommGroup W] {F : Type} [Field F]

theorem eq_one_of_centralizes_herm [CharP F 2] [Finite F] {n : ℕ} (hF : Nat.card F = 4 ^ n)
    (hn : 1 ≤ n) {Λ : Subgroup (MulAut W)} {π : SpecialLinearGroup (Fin 2) F →* Λ}
    {Ψ : W → Matrix (Fin 2) (Fin 2) F} (hc : IsO4Coord n Λ π Ψ) {e : MulAut W}
    (he2 : e * e = 1) (hec : ∀ l ∈ Λ, e * l = l * e) : e = 1 := by
  obtain ⟨-, hmul, hinj, hherm, honto, heq⟩ := hc
  have hcomm : ∀ γ w, e ((π γ : MulAut W) w) = (π γ : MulAut W) (e w) := fun γ w => by
    rw [← MulAut.mul_apply, hec _ (π γ).2, MulAut.mul_apply]
  have hee : ∀ w, e (e w) = w := fun w => by
    rw [← MulAut.mul_apply, he2]
    rfl
  have hΨ1 : Ψ 1 = 0 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact add_eq_left.mp h.symm
  have hE : IsHerm n (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) :=
    isHerm_iff.mpr ⟨by simp [sig_one], by simp [sig_zero], by simp [sig_zero], by simp [sig_zero]⟩
  obtain ⟨w₁, hw₁⟩ := honto _ hE
  have hX : ∀ t : F, ((ut t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      Ψ (e w₁) * (frobPow n ((ut t : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F))ᵀ = Ψ (e w₁) := fun t => by
    have h1 : (π (ut t) : MulAut W) w₁ = w₁ := hinj (by rw [heq, hw₁, conj_ut_E11])
    rw [← heq, ← hcomm, h1]
  have hμ := eq_E11_of_ut_fix hF hn (hherm (e w₁)) hX
  set μ := Ψ (e w₁) 0 0 with hμdef
  have hσμ : sig n μ = μ := (isHerm_iff.mp (hherm (e w₁))).1
  have hμ0 : μ ≠ 0 := by
    intro h0
    have h1 : e w₁ = 1 := hinj (by
      rw [hμ, h0, hΨ1]
      ext i j
      fin_cases i <;> fin_cases j <;> rfl)
    have h2 : w₁ = 1 := by rw [← hee w₁, h1, map_one]
    have h3 := congrFun (congrFun hw₁ 0) 0
    rw [h2, hΨ1] at h3
    simp at h3
  obtain ⟨l, hl⟩ := exists_norm_eq hF hn hσμ hμ0
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hl
    exact hμ0 hl.symm
  have hew : e w₁ = (π (dg l hl0) : MulAut W) w₁ := hinj (by
    rw [heq, hw₁, conj_dg, mul_one, hl]
    exact hμ)
  have h2 : Ψ w₁ = !![l * sig n l * μ, 0; 0, 0] :=
    calc Ψ w₁ = Ψ (e (e w₁)) := by rw [hee]
      _ = Ψ (e ((π (dg l hl0) : MulAut W) w₁)) := by rw [← hew]
      _ = Ψ ((π (dg l hl0) : MulAut W) (e w₁)) := by rw [hcomm]
      _ = _ := heq _ _
      _ = _ := by rw [hμ]
      _ = _ := conj_dg n hl0 μ
  have hμ1 : μ = 1 := by
    have h3 : (1 : F) = l * sig n l * μ := by
      have := congrFun (congrFun (hw₁.symm.trans h2) 0) 0
      simpa using this
    rw [hl] at h3
    exact eq_one_of_sq_eq_one_char_two (by rw [sq]; exact h3.symm)
  have hew1 : e w₁ = w₁ := hinj (by rw [hμ, hμ1, hw₁])
  have hfixc : ∀ c, sig n c = c → ∃ w, Ψ w = !![c, 0; 0, 0] ∧ e w = w := by
    intro c hc
    by_cases hc0 : c = 0
    · refine ⟨1, ?_, map_one e⟩
      rw [hΨ1, hc0]
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · obtain ⟨l', hl'⟩ := exists_norm_eq hF hn hc hc0
      have hl'0 : l' ≠ 0 := by
        rintro rfl
        rw [zero_mul] at hl'
        exact hc0 hl'.symm
      exact ⟨(π (dg l' hl'0) : MulAut W) w₁, by rw [heq, hw₁, conj_dg, mul_one, hl'],
        by rw [hcomm, hew1]⟩
  have hall : ∀ X, IsHerm n X → ∃ w, Ψ w = X ∧ e w = w := fun X hX =>
    herm_induction hF (P := fun X => ∃ w, Ψ w = X ∧ e w = w)
      (fun X Y ⟨w, hw, hew⟩ ⟨w', hw', hew'⟩ =>
        ⟨w * w', by rw [hmul, hw, hw'], by rw [map_mul, hew, hew']⟩)
      (fun g c hc => by
        obtain ⟨w, hw, hew⟩ := hfixc c hc
        exact ⟨(π g : MulAut W) w, by rw [heq, hw]; rfl, by rw [hcomm, hew]⟩) hX
  ext w
  obtain ⟨w', hw', hew'⟩ := hall (Ψ w) (hherm w)
  rw [← hinj hw']
  exact hew'

end C10P06

open C10P06 in
theorem fact12O4 : Fact12O4 := by
  intro W _ _ _ Λ n hn _ _ hO
  obtain ⟨F, _, _, _, hF, hreal⟩ := hO
  have hF4 : Nat.card F = 4 ^ n := by
    rw [hF, pow_mul]
    norm_num
  have hn1 : 1 ≤ n := by omega
  obtain ⟨π, Ψ, hc⟩ := exists_isO4Coord hreal
  refine ⟨?_, fun E hEN hEab => ?_⟩
  · rw [← card_herm hF4 hn1]
    exact Nat.card_congr (Equiv.ofBijective (fun w => ⟨Ψ w, hc.2.2.2.1 w⟩)
      ⟨fun w w' h => hc.2.2.1 (congrArg Subtype.val h), fun X => by
        obtain ⟨w, hw⟩ := hc.2.2.2.2.1 X.1 X.2
        exact ⟨w, Subtype.ext hw⟩⟩)
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro γ hγ
    rw [MonoidHom.mem_ker] at hγ
    rw [Subgroup.mem_bot]
    refine eq_one_of_herm_fix hF4 fun X hX => ?_
    obtain ⟨w, rfl⟩ := hc.2.2.2.2.1 X hX
    rw [← hc.2.2.2.2.2 γ w, hγ]
    rfl
  obtain ⟨A, hAc, hA2, hEA⟩ := exists_elem_aut (MulEquiv.ofBijective π ⟨hπinj, hc.1⟩)
    (fun x hx2 hxc => eq_one_of_centralizes_herm hF4 hn1 hc hx2 hxc) hEN hEab
  calc Nat.card E ≤ Nat.card A := hEA
    _ ≤ Nat.card F := card_le_of_elem_aut hF (by omega) hAc hA2
    _ = 2 ^ (2 * n) := hF

end CFSG.Quasithin.Vol2.Ch10.SecD
