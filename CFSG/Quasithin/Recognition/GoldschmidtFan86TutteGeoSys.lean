module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteGeoCycle
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteGeoChain

public section

namespace CFSG.Quasithin.Fan86.Tutte.Geo

open CFSG.Quasithin.F6.GoldAmL3T CFSG.Quasithin.Fan86.Tutte.Red

variable {W : Type} {Γ : SimpleGraph W} {H : Type} [Group H] [MulAction H W] {s : ℕ}

namespace RegData

variable (R : RegData Γ H s) {a : Arc Γ s} {r l ξ : H}

include R

theorem xs_sq_not_mem (hs : 2 ≤ s) (C : Config a r l ξ) :
    tx r l (s : ℤ) ^ 2 ∉ chain a H (s - 1) := by
  intro h
  obtain ⟨c1, c2, -⟩ := R.tx_s_cycle hs C
  have h1 := (mem_chain.1 h) 1 (by omega)
  rw [pow_two, mul_smul, c1, c2] at h1
  exact (R.nbrs_a0 hs C).2.1 h1

theorem xs_cube_mem (hs : 2 ≤ s) (C : Config a r l ξ) :
    tx r l (s : ℤ) ^ 3 ∈ chain a H (s - 1) := by
  obtain ⟨c1, c2, c3⟩ := R.tx_s_cycle hs C
  refine mem_chain.2 fun j hj => ?_
  have hfix : tx r l (s : ℤ) • a.vert 0 = a.vert 0 := tx_smul_vert C le_rfl (by omega)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega : j ≤ 1) with rfl | rfl
  · rw [pow_succ, pow_two, mul_smul, mul_smul, hfix, hfix, hfix]
  · rw [pow_succ, pow_two, mul_smul, mul_smul, c1, c2, c3]

omit R in
theorem xi_inv (C : Config a r l ξ) : ξ⁻¹ = ξ := inv_eq_of_mul_eq_one_right C.xi_sq

omit R in
theorem xi_conj_shift (C : Config a r l ξ) {g : H}
    (hg : ∀ j, j < s → g • a.vert j = a.vert (j + 1)) :
    ξ * g * ξ = r⁻¹ ∨ ξ * g * ξ = l⁻¹ := by
  have hshift : ∀ j, j < s → (ξ * g⁻¹ * ξ) • a.vert j = a.vert (j + 1) := by
    intro j hj
    rw [mul_smul, mul_smul, C.xi_vert j hj.le, shift_inv_vert hg (by omega) (by omega),
      C.xi_vert _ (by omega)]
    congr 1
    omega
  have hinv : ξ * g * ξ = (ξ * g⁻¹ * ξ)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, xi_inv C]
    simp [mul_assoc]
  rcases C.cases _ hshift with h | h
  · left
    rw [hinv, h]
  · right
    rw [hinv, h]

omit R in
theorem xi_case (C : Config a r l ξ) :
    (ξ * r * ξ = r⁻¹ ∧ ξ * l * ξ = l⁻¹) ∨ (ξ * r * ξ = l⁻¹ ∧ ξ * l * ξ = r⁻¹) := by
  have hne : ξ * r * ξ ≠ ξ * l * ξ := by
    intro h
    exact C.ne (mul_left_cancel (mul_right_cancel h))
  rcases xi_conj_shift C C.r_shift with hr | hr <;> rcases xi_conj_shift C C.l_shift with hl | hl
  · exact absurd (hr.trans hl.symm) (by simpa using hne)
  · exact Or.inl ⟨hr, hl⟩
  · exact Or.inr ⟨hr, hl⟩
  · exact absurd (hr.trans hl.symm) (by simpa using hne)

theorem rel (hs : 2 ≤ s) (C : Config a r l ξ) :
    ξ * r ^ s * tx r l (s : ℤ) ∈ chain a H (s - 1) := by
  obtain ⟨c1, -, -⟩ := R.tx_s_cycle hs C
  have hfix : tx r l (s : ℤ) • a.vert 0 = a.vert 0 := tx_smul_vert C le_rfl (by omega)
  refine mem_chain.2 fun j hj => ?_
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega : j ≤ 1) with rfl | rfl
  · have := pow_smul_vert C.r_shift s 0 (by omega)
    rw [mul_smul, mul_smul, hfix, this, zero_add, C.xi_vert s le_rfl, Nat.sub_self]
  · rw [mul_smul, mul_smul, c1, rpow_s_b (by omega) C, C.xi_vert _ (by omega)]
    congr 1
    omega

theorem inter (C : Config a r l ξ) {i : ℕ} (hi : i ≤ s) :
    chain a H (s - i) ⊓ (chain a H i).map (MulAut.conj ξ).toMonoidHom = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨hg1, k, hk, rfl⟩ := Subgroup.mem_inf.1 hg |>.imp_right fun h => Subgroup.mem_map.1 h
  refine R.faith a _ fun m hm => ?_
  rcases Nat.lt_or_ge i m with him | him
  · show (ξ * k * ξ⁻¹) • a.vert m = a.vert m
    rw [xi_inv C, mul_smul, mul_smul, C.xi_vert m hm,
      (mem_chain.1 hk) (s - m) (by omega), C.xi_vert _ (by omega)]
    congr 1
    omega
  · exact (mem_chain.1 hg1) m (by omega)

end RegData

end CFSG.Quasithin.Fan86.Tutte.Geo
