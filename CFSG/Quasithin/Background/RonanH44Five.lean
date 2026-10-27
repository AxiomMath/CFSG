module

public import CFSG.Quasithin.Background.HFL3PRank

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem part5_pow_eq_one (β γ u u' : K) (hβ : β * bar n β = 1) (hdet : β * β * γ = 1)
    (g : SpecialLinearGroup (Fin 3) K)
    (hg : (g : Matrix (Fin 3) (Fin 3) K) = !![β, 0, u; 0, β, u'; 0, 0, γ]) :
    g ^ (2 * (2 ^ n + 1)) = 1 := by
  obtain ⟨s, hs⟩ := exists_blk_pow β u u' γ (2 ^ n + 1)
  have hβq : β ^ (2 ^ n + 1) = 1 := by
    rw [pow_succ, ← bar_apply, mul_comm, hβ]
  have hγq : γ ^ (2 ^ n + 1) = 1 := by
    have h1 : (β * β * γ) ^ (2 ^ n + 1) = 1 := by rw [hdet, one_pow]
    rw [mul_pow, mul_pow, hβq, one_mul, one_mul] at h1
    exact h1
  have hmat : ((g ^ (2 ^ n + 1) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![(1 : K), 0, u * s; 0, 1, u' * s; 0, 0, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_pow, hg, hs, hβq, hγq]
  have hN : !![(1 : K), 0, u * s; 0, 1, u' * s; 0, 0, 1] *
      !![(1 : K), 0, u * s; 0, 1, u' * s; 0, 0, 1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]
  rw [pow_mul']
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hmat, sq, hN, Matrix.SpecialLinearGroup.coe_one]

theorem part5_sub_one_eq_one (hn : 1 ≤ n) (h : 2 ^ n - 1 ∣ 2 * (2 ^ n + 1)) :
    2 ^ n - 1 = 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have hodd : ¬ 2 ∣ 2 ^ n - 1 := by omega
  have hcop : Nat.Coprime (2 ^ n - 1) 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd).symm
  have h3 : 2 ^ n - 1 ∣ 2 ^ n + 1 := Nat.Coprime.dvd_of_dvd_mul_left hcop h
  have h4 : 2 ^ n - 1 ∣ 2 := by
    have h5 := Nat.dvd_sub h3 (dvd_refl (2 ^ n - 1))
    have h6 : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by omega
    rwa [h6] at h5
  rcases (Nat.dvd_prime Nat.prime_two).1 h4 with h7 | h7
  · exact h7
  · omega

theorem part5 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {M : Subgroup (MulAut (HMod n K))} (hMN : M ≤ norm hK) :
    ∀ A : Subgroup (MulAut (HMod n K)), IsA2 M A → rk ↥A = 4 * n → rkIdx (fixV A) = 5 * n →
      ¬ ∃ x ∈ img hK, x ≠ 1 ∧ orderOf x = 2 ^ n - 1 ∧ ∀ v ∈ fixV A, x v = v := by
  intro A hA hrkA hidx
  rintro ⟨x, hxL, hx1, hord, hxfix⟩
  have hAN : A ≤ norm hK := hA.1.trans hMN
  have hAe : IsElemAbelian2 A := hA.2.2
  haveI : Finite (MulAut (HMod n K)) := MulEquiv.finite_left
  have hV : rk (HMod n K) = 9 * n := by
    unfold rk
    rw [card_HMod hn hK, padicValNat.prime_pow]
  have hfixrk : rk ↥(fixV A) = 4 * n := by
    have := rk_add_rkIdx (fixV A)
    omega
  have hfixcard : Nat.card ↥(fixV A) = 2 ^ (4 * n) := by
    rw [card_eq_two_pow (sq_eq_one_HMod (n := n) (K := K)) (fixV A), hfixrk]
  have hAcard : Nat.card ↥A = 2 ^ (4 * n) := by
    rw [card_eq_two_pow_of_isPGroup (E3.isPGroup_of_isElemAbelian2 hAe), hrkA]
  have hK4 : Nat.card K ^ 2 = 2 ^ (4 * n) := by
    rw [hK, ← pow_mul, ← pow_mul]
    ring_nf
  have hcard : Nat.card K ^ 2 ≤ Nat.card ↥A := (hK4.trans hAcard.symm).le
  have hfix : 2 ^ n < Nat.card ↥(fixV A) := by
    rw [hfixcard]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨g, hg⟩ := exists_conj_eq_Q2 hn hK hAN hAe hcard hfix
  have hblk : blkW n K = (fixV A).map (rho hK g).toMonoidHom := by
    rw [← fixV_rhoQ2 hn hK, ← hg, conj_eq_congrHom, fixV_map_congrHom]
  have he_img : rho hK g ∈ img hK := MonoidHom.mem_range.2 ⟨g, rfl⟩
  have hx'L : MulAut.conj (rho hK g) x ∈ img hK := by
    rw [MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ he_img hxL) (Subgroup.inv_mem _ he_img)
  have hord': orderOf (MulAut.conj (rho hK g) x) = orderOf x :=
    orderOf_injective (MulAut.conj (rho hK g)).toMonoidHom (MulAut.conj (rho hK g)).injective x
  have hx'fix : ∀ v ∈ blkW n K, MulAut.conj (rho hK g) x v = v := by
    intro v hv
    rw [hblk] at hv
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hv
    simp only [MulEquiv.coe_toMonoidHom]
    rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self,
      hxfix w hw]
  obtain ⟨g', hg'⟩ := hx'L
  have hfixD : ∀ X ∈ blkW n K, rhoT hK (SpecialLinearGroup.toGL g') X = X := by
    intro X hX
    have h := hx'fix X hX
    rw [← hg'] at h
    exact h
  obtain ⟨d10, d20, d01, d21, d11, dbb⟩ := entries_of_fix_blkW hK hfixD
  have e10 : (g' : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := d10
  have e20 : (g' : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := d20
  have e01 : (g' : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := d01
  have e21 : (g' : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := d21
  have e11 : (g' : Matrix (Fin 3) (Fin 3) K) 1 1 = (g' : Matrix (Fin 3) (Fin 3) K) 0 0 := d11
  have hbb : (g' : Matrix (Fin 3) (Fin 3) K) 0 0 *
      bar n ((g' : Matrix (Fin 3) (Fin 3) K) 0 0) = 1 := dbb
  have hshape : (g' : Matrix (Fin 3) (Fin 3) K) =
      !![(g' : Matrix (Fin 3) (Fin 3) K) 0 0, 0, (g' : Matrix (Fin 3) (Fin 3) K) 0 2;
        0, (g' : Matrix (Fin 3) (Fin 3) K) 0 0, (g' : Matrix (Fin 3) (Fin 3) K) 1 2;
        0, 0, (g' : Matrix (Fin 3) (Fin 3) K) 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e10, e20, e01, e21, e11]
  have hdet : (g' : Matrix (Fin 3) (Fin 3) K) 0 0 * (g' : Matrix (Fin 3) (Fin 3) K) 0 0 *
      (g' : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    have h := g'.2
    rw [Matrix.det_fin_three] at h
    simp only [e10, e20, e01, e21, e11, mul_zero, zero_mul, sub_zero, add_zero, zero_add] at h
    linear_combination h
  have hsl : g' ^ (2 * (2 ^ n + 1)) = 1 :=
    part5_pow_eq_one _ _ ((g' : Matrix (Fin 3) (Fin 3) K) 0 2) ((g' : Matrix (Fin 3) (Fin 3) K) 1 2)
      hbb hdet g' hshape
  have hpow : MulAut.conj (rho hK g) x ^ (2 * (2 ^ n + 1)) = 1 := by
    rw [← hg', ← map_pow, hsl, map_one]
  have hdvd : orderOf (MulAut.conj (rho hK g) x) ∣ 2 * (2 ^ n + 1) :=
    orderOf_dvd_of_pow_eq_one hpow
  rw [hord', hord] at hdvd
  apply hx1
  exact orderOf_eq_one_iff.mp (hord.trans (part5_sub_one_eq_one hn hdvd))

end CFSG.Quasithin.RonanH44
