module

public import CFSG.Quasithin.Background.SzG11NCNatural
public import CFSG.Quasithin.Background.SzG11NCKLin
public import CFSG.Quasithin.Background.SzG11NCCore

public section

namespace CFSG.Quasithin.SzG11NC

open CFSG.Quasithin CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem endCommutant_eq_commutantOf (H : Subgroup (GLV V)) :
    endCommutant H = commutantOf H := rfl

theorem false_of_commutant_four [Finite V] {B : LinearMap.BilinForm (ZMod 2) V}
    {Γ X X₀ : Subgroup (GLV V)} {v₁ : V} {W : Submodule (ZMod 2) V}
    (hyp : G111Hyp B Γ v₁ W X X₀) {H : Subgroup (GLV V)} (hirr : IsIrr H ⊤)
    (hnorm : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (hE4 : 4 ≤ Nat.card (CommF H hirr)) (hd : 8 ≤ Module.finrank (ZMod 2) V)
    (hlin : ∀ x ∈ X, ∀ f ∈ endCommutant H, ∀ v, x (f v) = f (x v)) : False := by
  have hVne : Nontrivial V := nontrivial_of_isIrr_top hirr
  have hchar : CharP (CommF H hirr) 2 := by
    refine CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero ?_
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply smul_left_inj_of_ne_zero hv
    rw [two_smul, zmod_two_add_self, zero_smul]
  have hsl : ∀ x ∈ X, ∃ σ : CommF H hirr ≃+* CommF H hirr,
      ∀ (e : CommF H hirr) (v : V), x (e • v) = σ e • x v :=
    fun x hx => CommF.exists_semilinear Γ hnorm (hyp.X_le hx)
  have : Fintype (CommF H hirr) := Fintype.ofFinite _
  obtain ⟨m, -, hm⟩ := FiniteField.card (CommF H hirr) 2
  have hm' : Nat.card (CommF H hirr) = 2 ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hm
  by_cases h8 : 8 ≤ Nat.card (CommF H hirr)
  · exact not_three_of_field (CommF H hirr) h8 (by omega) X hyp.X_sq hsl v₁ hyp.point hyp.three
  · have hE : Nat.card (CommF H hirr) = 4 := by
      generalize (m : ℕ) = n at hm'
      have hn3 : n < 3 := by
        by_contra hcon
        push Not at hcon
        have : 8 ≤ 2 ^ n := by
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hcon
        omega
      have hn2 : 2 ≤ n := by
        by_contra hcon
        push Not at hcon
        have : 2 ^ n ≤ 2 := by
          calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ = 2 := by norm_num
        omega
      have : n = 2 := by omega
      subst this
      exact hm'.trans (by norm_num)
    have hlinE : ∀ x ∈ X, ∀ (κ : CommF H hirr) (v : V), x (κ • v) = κ • x v := by
      intro x hx κ v
      rw [CommF.smul_def, CommF.smul_def]
      exact hlin x hx κ.val (by rw [endCommutant_eq_commutantOf]; exact CommF.val_mem κ) v
    have h6 := klin_dim_le_six (CommF H hirr) hE hyp.toG101Hyp hlinE
    omega

theorem card_galoisField_two_two : Nat.card (GaloisField 2 2) = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem four_le_card_galoisField_two : 4 ≤ Nat.card (GaloisField 2 2) :=
  card_galoisField_two_two.ge

theorem eight_le_finrank_of_natural_two {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : 4 ≤ Fintype.card ι) {H : Subgroup (GLV V)}
    {Γ₀ : Subgroup (Matrix.GeneralLinearGroup ι (GaloisField 2 2))}
    (hnat : IsNaturalMatrixModule H Γ₀) : 8 ≤ Module.finrank (ZMod 2) V := by
  rw [finrank_of_natural hnat, GaloisField.finrank 2 (n := 2) (by norm_num)]
  omega

end CFSG.Quasithin.SzG11NC

