module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bBase

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Quasithin

section Witt

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem exists_sing_of_B_eq_one (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w) {v w : W} (hqv : q v = 0) (hqw : q w = 0)
    (hvw : B v w = 1) : ∃ γ ∈ orthogonalSubgroupOf q, γ v = w := by
  have hu : q (v + w) = 1 := by
    simp [hq, hqv, hqw, hvw]
  refine ⟨trEquiv q B hq (v + w), trEquiv_mem q B hq hu, ?_⟩
  rw [trEquiv_apply, map_add, B_self q B hq v, hvw, zero_add, one_smul, ← add_assoc,
    add_self_eq_zero', zero_add]

theorem exists_hyp_partner (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w)
    (hB : ∀ v : W, (∀ w, B v w = 0) → v = 0) {v : W} (hv : v ≠ 0) (hqv : q v = 0) :
    ∃ v' : W, B v v' = 1 ∧ q v' = 0 := by
  obtain ⟨x, hx⟩ := exists_B_eq_one B hB q hq hv
  have hxv : B v x = 1 := by
    rw [B_symm q B hq]
    exact hx
  rcases zmod2_cases (q x) with h | h
  · exact ⟨x, hxv, h⟩
  · refine ⟨x + v, ?_, ?_⟩
    · rw [map_add, hxv, B_self q B hq v, add_zero]
    · rw [hq, h, hqv, hx]
      decide

theorem q_hyp_add (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w) {v v' r : W} (hqv : q v = 0) (hqv' : q v' = 0)
    (hvv' : B v v' = 1) (hrv : B v r = 0) (hrv' : B v' r = 0) (c : ZMod 2) :
    q (c • v + v' + r) = c + q r := by
  have h1 : q (c • v + v') = c := by
    rw [hq, q_smul q B hq, hqv, hqv', map_smul, LinearMap.smul_apply, hvv', smul_eq_mul]
    ring
  have h2 : B (c • v + v') r = 0 := by
    rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hrv, hrv', smul_eq_mul,
      mul_zero, add_zero]
  rw [hq, h1, h2, add_zero]

theorem exists_common_perp (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w)
    (hB : ∀ v : W, (∀ w, B v w = 0) → v = 0) {v w : W} (hv : v ≠ 0) (hw : w ≠ 0)
    (hqv : q v = 0) (hqw : q w = 0) (hBvw : B v w = 0) (hvw : v ≠ w) :
    ∃ z : W, B v z = 1 ∧ B w z = 1 ∧ q z = 0 := by
  obtain ⟨v', hvv', hqv'⟩ := exists_hyp_partner q B hq hB hv hqv
  have hv'v : B v' v = 1 := by
    rw [B_symm q B hq]
    exact hvv'
  have hBvv : B v v = 0 := B_self q B hq v
  obtain ⟨a, ha⟩ : ∃ a : ZMod 2, a = B w v' := ⟨_, rfl⟩
  rcases zmod2_cases a with ha1 | ha1
  ·
    have hwv' : B w v' = 0 := by
      rw [← ha]
      exact ha1
    obtain ⟨x, hx⟩ := exists_B_eq_one B hB q hq hw
    have hwx : B w x = 1 := by
      rw [B_symm q B hq]
      exact hx
    have hBwv : B w v = 0 := by
      rw [B_symm q B hq]
      exact hBvw
    set r : W := x + B x v' • v + B x v • v' with hr
    have hrv : B r v = 0 := by
      rw [hr]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hBvv, hvv', hv'v, mul_zero, zero_add, mul_one, add_zero]
      exact zmod2_add_self _
    have hrv' : B r v' = 0 := by
      rw [hr]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hBvv, hvv', hv'v, mul_zero, zero_add, mul_one, B_self q B hq v', add_zero]
      exact zmod2_add_self _
    have hwr : B w r = 1 := by
      rw [hr]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hBwv, hwv', mul_zero, zero_add, add_zero, hwx]
    have hrv_symm : B v r = 0 := by
      rw [B_symm q B hq]
      exact hrv
    have hrv'_symm : B v' r = 0 := by
      rw [B_symm q B hq]
      exact hrv'
    refine ⟨q r • v + v' + r, ?_, ?_, ?_⟩
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hBvv, hvv', hrv_symm, mul_zero, zero_add, add_zero]
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hBwv, hwv', hwr, mul_zero, zero_add, add_zero]
    · rw [q_hyp_add q B hq hqv hqv' hvv' hrv_symm hrv'_symm (q r)]
      exact zmod2_add_self _
  ·
    have ha1' : B w v' = 1 := by
      rw [← ha]
      exact ha1
    exact ⟨v', hvv', ha1', hqv'⟩

theorem singular_transitive (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w)
    (hB : ∀ v : W, (∀ w, B v w = 0) → v = 0) {v w : W} (hv : v ≠ 0) (hw : w ≠ 0)
    (hqv : q v = 0) (hqw : q w = 0) : ∃ γ ∈ orthogonalSubgroupOf q, γ v = w := by
  by_cases hvw : v = w
  · exact ⟨1, Subgroup.one_mem _, by rw [hvw]; rfl⟩
  · rcases zmod2_cases (B v w) with h | h
    · obtain ⟨z, hvz, hwz, hqz⟩ := exists_common_perp q B hq hB hv hw hqv hqw h hvw
      obtain ⟨γ1, hγ1, h1⟩ := exists_sing_of_B_eq_one q B hq hqv hqz hvz
      have hzw : B z w = 1 := by
        rw [B_symm q B hq]
        exact hwz
      obtain ⟨γ2, hγ2, h2⟩ := exists_sing_of_B_eq_one q B hq hqz hqw hzw
      exact ⟨γ2 * γ1, Subgroup.mul_mem _ hγ2 hγ1, by
        show γ2 (γ1 v) = w
        rw [h1, h2]⟩
    · exact exists_sing_of_B_eq_one q B hq hqv hqw h

end Witt

end CFSG.Quasithin.H13.C1294
