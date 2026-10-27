module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xi
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Open.StatedAPI Matrix
open scoped Matrix

namespace P22x

section F2b

variable {F : Type} [Field F] [Finite F]

theorem two_eq_zero_of_card {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) : (2 : F) = 0 := by
  haveI := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  haveI : CharP F 2 := charP_of_card_eq_prime_pow h
  exact CharP.cast_eq_zero F 2

theorem sl2_stab_mul_self {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (g : ↥(StatedSL 2 F))
    {w : Fin 2 → F} (hw : w ≠ 0)
    (hg : (((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ w = w) :
    (((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *
      (((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) = 1 := by
  have h2 : (2 : F) = 0 := two_eq_zero_of_card hF hn
  have hdet := det_of_mem_statedSL g.2
  set M : Matrix (Fin 2) (Fin 2) F := (((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) with hM
  rw [Matrix.det_fin_two] at hdet
  have hw0 := congrFun hg 0
  have hw1 := congrFun hg 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hw0 hw1
  have e1 : (M 0 0 - 1) * w 0 + M 0 1 * w 1 = 0 := by linear_combination hw0
  have e2 : M 1 0 * w 0 + (M 1 1 - 1) * w 1 = 0 := by linear_combination hw1
  have k0 : ((M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0) * w 0 = 0 := by
    linear_combination (M 1 1 - 1) * e1 - M 0 1 * e2
  have k1 : ((M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0) * w 1 = 0 := by
    linear_combination (M 0 0 - 1) * e2 - M 1 0 * e1
  have hk : (M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0 = 0 := by
    by_contra hne
    apply hw
    funext i
    fin_cases i
    · exact (mul_eq_zero.1 k0).resolve_left hne
    · exact (mul_eq_zero.1 k1).resolve_left hne
  have htr : M 0 0 + M 1 1 = 0 := by linear_combination (-1 : F) * hk + hdet + h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Fin.zero_eta, Fin.isValue,
      Fin.mk_one, if_true, if_false, one_ne_zero, zero_ne_one]
  · linear_combination (-1 : F) * hdet + M 0 0 * htr - h2
  · linear_combination M 0 1 * htr
  · linear_combination M 1 0 * htr
  · linear_combination (-1 : F) * hdet + M 1 1 * htr - h2

@[expose] def sl2Stab (w : Fin 2 → F) : Subgroup ↥(StatedSL 2 F) where
  carrier := {g | (((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ w = w}
  mul_mem' {a b} ha hb := by
    change (((a * b : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w = w
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [← Matrix.mulVec_mulVec]
    exact (congrArg _ hb).trans ha
  one_mem' := by
    change (((1 : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w = w
    simp
  inv_mem' {a} ha := by
    change (((a⁻¹ : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w = w
    have ha' : (((a : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w = w := ha
    conv_lhs => rw [← ha']
    rw [Matrix.mulVec_mulVec]
    simp only [Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem sl2Stab_isPGroup {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) {w : Fin 2 → F}
    (hw : w ≠ 0) : IsPGroup 2 (sl2Stab w) := by
  rintro ⟨g, hg⟩
  refine ⟨1, ?_⟩
  have h := sl2_stab_mul_self hF hn g hw hg
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  simpa [pow_two] using h

theorem sl2_eq_stab_of_card {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) {w : Fin 2 → F}
    (hw : w ≠ 0) (Q' : Subgroup ↥(StatedSL 2 F)) (hQ' : Nat.card Q' = Nat.card F)
    (hQw : w ∈ sl2Fix Q') : Q' = sl2Stab w :=
  Subgroup.eq_of_le_of_card_ge (fun g hg => hQw g hg)
    (by rw [hQ']; exact (sl2_card_le hF _ (sl2Stab_isPGroup hF hn hw)).1)

theorem odd_card_sub_one {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) : Odd (Nat.card F - 1) := by
  have hev : Even (Nat.card F) := by
    rw [hF]
    exact Nat.even_pow.2 ⟨even_two, by omega⟩
  have hpos : 1 ≤ Nat.card F := Nat.card_pos
  exact Nat.Even.sub_odd hpos hev odd_one

theorem sl2_theta_mem {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (Q' : Subgroup ↥(StatedSL 2 F)) (hQ' : Nat.card Q' = Nat.card F)
    {w₀ : Fin 2 → F} (hw₀ : w₀ ≠ 0) (hQw : w₀ ∈ sl2Fix Q')
    (Θ : (Fin 2 → F) ≃+ (Fin 2 → F))
    (hΘ : ∀ g : ↥(StatedSL 2 F), ∃ g' : ↥(StatedSL 2 F), ∀ v,
      Θ ((((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        (((g' : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ Θ v)
    (hfix : ∀ c : F, Θ (c • w₀) = c • w₀) {k : ℕ} (hord : ∀ v, (⇑Θ)^[2 ^ k] v = v) :
    ∃ g ∈ Q', ∀ v, Θ v = (((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v := by
  have hlin := sl2_linear_of_fixed_line Θ hΘ hw₀ hfix
  let Θl : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) := Θ.toLinearEquiv hlin
  have hpow : Θl ^ (2 ^ k) = 1 := by
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.pow_apply]
    exact hord v
  let eGL : GL (Fin 2) F ≃* ((Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) :=
    Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 2 → F))
  obtain ⟨γ, hγ⟩ : ∃ γ : GL (Fin 2) F, eGL γ = Θl := ⟨eGL.symm Θl, eGL.apply_symm_apply Θl⟩
  have hγv : ∀ v, (γ : Matrix (Fin 2) (Fin 2) F) *ᵥ v = Θ v := by
    intro v
    have := congrArg (fun e : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) => e v) hγ
    exact this
  have hγpow : γ ^ (2 ^ k) = 1 := by
    apply eGL.injective
    rw [map_pow, hγ, hpow, map_one]
  have hdet : (γ : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    set δ : Fˣ := Matrix.GeneralLinearGroup.det γ with hδ
    have h1 : δ ^ (2 ^ k) = 1 := by
      rw [hδ, ← map_pow, hγpow, map_one]
    have h2 : orderOf δ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf δ ∣ Nat.card F - 1 := by
      rw [← Nat.card_units F]
      exact orderOf_dvd_natCard δ
    have hcop : Nat.Coprime (2 ^ k) (Nat.card F - 1) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 (odd_card_sub_one hF hn))
    have h4 : orderOf δ = 1 := Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h2 h3)
    have h5 : δ = 1 := orderOf_eq_one_iff.1 h4
    have h6 := Matrix.GeneralLinearGroup.val_det_apply γ
    rw [← h6, ← hδ, h5]
    rfl
  have hγSL : γ ∈ StatedSL 2 F := mem_statedSL_of_det hdet
  have hgw : (((⟨γ, hγSL⟩ : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w₀ =
      w₀ := by
    show (γ : Matrix (Fin 2) (Fin 2) F) *ᵥ w₀ = w₀
    rw [hγv]
    simpa using hfix 1
  have hQeq := sl2_eq_stab_of_card hF hn hw₀ Q' hQ' hQw
  refine ⟨⟨γ, hγSL⟩, ?_, fun v => (hγv v).symm⟩
  rw [hQeq]
  exact hgw

end F2b

end P22x

end CFSG.LocalAnalysis.UniquenessCase.UC22
