module

public import CFSG.Quasithin.Background.F918Z3Cg2H4
public import CFSG.Quasithin.Background.F918Z3CaRank

public section

namespace CFSG.Quasithin

open scoped Matrix

namespace Z3Cg2

section Bounds

variable {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)} {s : MulAut V}
  {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
  {β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) F)}
  {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F}
  {σ : ↥X →* Matrix.GeneralLinearGroup (Fin d) F}

theorem three_le_rkIdx_of_model (hZ : Z37 D X G T' s) (hM : IsMatModel D X β ρ σ) (hd4 : d = 4)
    {a : ℕ} (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ a) {b : MulAut V} (hb1 : b ≠ 1)
    (hbb : b * b = 1) (hbD : D.map (MulAut.conj b).toMonoidHom = D)
    (hbX : X.map (MulAut.conj b).toMonoidHom = X) : 3 ≤ rkIdx (fixV (Subgroup.zpowers b)) := by
  have hd : 0 < d := by omega
  rcases normalizer_dichotomy hM hd hbb hbD hbX with h | ⟨P, Q, hP, hQ, hb⟩
  · have h8 := eight_a_le_rkIdx hZ.exp _ (card_V_orth β hd4 hF) h
    omega
  · have hPQ : P ≠ 1 ∨ Q ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hb1
      ext v
      apply β.injective
      apply Multiplicative.toAdd.injective
      rw [hb v, hcon.1, hcon.2]
      simp
    have hle := card_fixV_mul_le hb (card_range_ge_of_ne_one hP hQ hPQ)
    rw [hF, ← pow_mul] at hle
    have h4 := le_rkIdx_of_card_mul_le hZ.exp _ hle
    subst hd4
    omega

theorem five_le_rkIdx_of_model (hZ : Z37 D X G T' s) (hM : IsMatModel D X β ρ σ) (hd4 : d = 4)
    {a : ℕ} (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ a) {b : MulAut V} (hbb : b * b = 1)
    (hbD : D.map (MulAut.conj b).toMonoidHom = D) (hbX : X.map (MulAut.conj b).toMonoidHom = X)
    (hoD : ¬ ∃ g ∈ D, ∀ y ∈ D, b * y * b⁻¹ = g * y * g⁻¹)
    (hoX : ¬ ∃ g ∈ X, ∀ x ∈ X, b * x * b⁻¹ = g * x * g⁻¹) :
    5 ≤ rkIdx (fixV (Subgroup.zpowers b)) := by
  have hd : 0 < d := by omega
  rcases normalizer_dichotomy hM hd hbb hbD hbX with h | ⟨P, Q, hP, hQ, hb⟩
  · have h8 := eight_a_le_rkIdx hZ.exp _ (card_V_orth β hd4 hF) h
    omega
  · have hP1 : P ≠ 1 := by
      intro hP1
      apply hoD
      refine ⟨1, D.one_mem, fun y hy => ?_⟩
      have hcomm : b * y = y * b := by
        ext v
        apply β.injective
        apply Multiplicative.toAdd.injective
        change Multiplicative.toAdd (β (b (y v))) = Multiplicative.toAdd (β (y (b v)))
        rw [hb, toAdd_left_apply hM hy, toAdd_left_apply hM hy, hb, hP1]
        simp [Matrix.mul_assoc]
      rw [hcomm]
      simp
    have hQ1 : Q ≠ 1 := by
      intro hQ1
      apply hoX
      refine ⟨1, X.one_mem, fun x hx => ?_⟩
      have hcomm : b * x = x * b := by
        ext v
        apply β.injective
        apply Multiplicative.toAdd.injective
        change Multiplicative.toAdd (β (b (x v))) = Multiplicative.toAdd (β (x (b v)))
        rw [hb, toAdd_right_apply hM hx, toAdd_right_apply hM hx, hb, hQ1]
        simp [Matrix.mul_assoc]
      rw [hcomm]
      simp
    have hle := card_fixV_mul_le hb (card_range_ge_of_ne_one_both hP hQ hP1 hQ1)
    rw [hF, ← pow_mul] at hle
    have h4 := le_rkIdx_of_card_mul_le hZ.exp _ hle
    subst hd4
    norm_num at h4
    omega

end Bounds

end Z3Cg2

end CFSG.Quasithin
