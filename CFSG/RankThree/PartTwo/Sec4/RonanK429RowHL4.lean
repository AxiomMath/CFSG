module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHL4Diag
import CFSG.RankThree.PartTwo.Sec4.RonanK432DiagThree
import CFSG.RankThree.PartTwo.Sec4.Item426A6Field

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSL projImage)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Matrix

section SL4

variable {K : Type} [Field K]

theorem l4_det_of_mem_ker {n : ℕ} {g : GL (Fin n) K}
    (hg : g ∈ (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker) :
    (g : Matrix (Fin n) (Fin n) K).det = 1 := by
  have h := congrArg Units.val (MonoidHom.mem_ker.mp hg)
  rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at h

theorem l4_mem_ker_det {n : ℕ} {g : GL (Fin n) K}
    (hg : (g : Matrix (Fin n) (Fin n) K).det = 1) :
    g ∈ (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, Units.val_one]
  exact hg

theorem l4_pow_four_of_scalar_mem_ker {u : Kˣ}
    (hu : GeneralLinearGroup.scalar (Fin 4) u ∈
      (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker) : u ^ 4 = 1 := by
  have h := l4_det_of_mem_ker hu
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at h
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h)


theorem l4_good429_SL4 [Finite K] {ω : K} (hω2 : ω ^ 2 + ω + 1 = 0) (h3 : (3 : K) ≠ 0)
    (A : (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker) (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) :
    Good429 (Subgroup.centralizer ({(A : GL (Fin 4) K)} : Set (GL (Fin 4) K)) ⊓
      (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker) := by
  have hω := RonanK432.isPrimitiveRoot_three_of_sq_add_add_one hω2 h3
  have hA3' : (A : GL (Fin 4) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hA3, Subgroup.coe_one]
  have hA1' : (A : GL (Fin 4) K) ≠ 1 := fun h => hA1 (Subtype.ext h)
  obtain ⟨g, a, hD⟩ := RonanK432.exists_conj_diagonal_of_pow_three hω2 h3 hA3'
  have hQ : IsQuasisimple (GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker :=
    IsQuasisimple.of_mulEquiv SpecialLinearGroup.toGLKerEquiv.symm
      (Item426.isQuasisimple_SL_three K).1
  refine l4_good429_of_conj h3 hω hQ (fun g hg => l4_det_of_mem_ker hg) ?_ ?_ ?_ ?_ A.2 hA3'
    hA1' ?_ hD
  · intro σ g
    have e : ((Sec21.Tables.reindexGL σ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det =
        (g : Matrix (Fin 4) (Fin 4) K).det := by
      rw [Sec21.Tables.coe_reindexGL, det_submatrix_equiv_self]
    exact ⟨fun hg => l4_mem_ker_det (e.trans (l4_det_of_mem_ker hg)),
      fun hg => l4_mem_ker_det (e.symm.trans (l4_det_of_mem_ker hg))⟩
  · intro B hB
    exact l4_mem_ker_det (by rw [coe_l4BlkGL3, det_l4Blk3]; exact l4_det_of_mem_ker hB)
  · intro M _ B _ _ hdet
    exact l4_mem_ker_det hdet
  · intro u hu hu3
    calc u = u ^ 4 * (u ^ 3)⁻¹ := by group
      _ = 1 := by rw [l4_pow_four_of_scalar_mem_ker hu, hu3, inv_one, one_mul]
  · intro h
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, map_mul, map_mul, map_inv,
      mul_comm (GeneralLinearGroup.det g), mul_inv_cancel_right]

theorem l4_good429_projSL [Finite K] {ω : K} (hω2 : ω ^ 2 + ω + 1 = 0) (h3 : (3 : K) ≠ 0)
    (y : projSL 4 K) (hy : orderOf y = 3) :
    Good429 (Subgroup.centralizer ({y} : Set (projSL 4 K))) :=
  l4_good429_proj (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker
    (fun _ hu => l4_pow_four_of_scalar_mem_ker hu)
    (fun A hA3 hA1 => l4_good429_SL4 hω2 h3 A hA3 hA1) y hy

end SL4

theorem l4_not_three_dvd_outer (p : ℕ) [Fact p.Prime] :
    ¬ 3 ∣ Nat.card (Outer (projSL 4 (GaloisField p 1))) := by
  have hp : p.Prime := Fact.out
  have hadm : CFSG.Open.StatedLieAdmissible .PSL 4 p 1 := by
    unfold CFSG.Open.StatedLieAdmissible
    refine ⟨hp, le_refl 1, ?_⟩
    simp
  have hT := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm
    (MulEquiv.refl (projSL 4 (GaloisField p 1)))
  have hdvd : Nat.card (Outer (projSL 4 (GaloisField p 1))) ∣ 2 * 1 * Nat.gcd 4 (p ^ 1 - 1) :=
    (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inl rfl) (by norm_num) hp (le_refl 1) hT).1
  rw [pow_one] at hdvd
  intro h3
  have h3' : 3 ∣ 2 * 1 * Nat.gcd 4 (p - 1) := h3.trans hdvd
  have h4 : 3 ∣ Nat.gcd 4 (p - 1) := by omega
  have h5 : 3 ∣ 4 := h4.trans (Nat.gcd_dvd_left 4 (p - 1))
  omega

theorem l4_exists_cube_root (p : ℕ) [Fact p.Prime] (hp1 : p % 3 = 1) :
    ∃ ω : GaloisField p 1, ω ^ 2 + ω + 1 = 0 := by
  have hcardK : Nat.card (GaloisField p 1) = p := by
    rw [GaloisField.card p 1 one_ne_zero, pow_one]
  have hdvdU : 3 ∣ Nat.card (GaloisField p 1)ˣ := by
    rw [Nat.card_units, hcardK]
    omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g3, hg3⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField p 1)ˣ) 3 hdvdU
  have hω3 : (g3 : GaloisField p 1) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hg3, pow_orderOf_eq_one, Units.val_one]
  have hω1 : (g3 : GaloisField p 1) ≠ 1 := by
    intro h1
    have hg1 : g3 = 1 := Units.ext h1
    rw [hg1, orderOf_one] at hg3
    exact absurd hg3 (by norm_num)
  refine ⟨g3, ?_⟩
  have h1 : ((g3 : GaloisField p 1) - 1) *
      ((g3 : GaloisField p 1) ^ 2 + (g3 : GaloisField p 1) + 1) = 0 := by
    linear_combination hω3
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd (sub_eq_zero.mp h2) hω1
  · exact h2

theorem l4_three_ne_zero (p : ℕ) [Fact p.Prime] (hp : 3 < p) : (3 : GaloisField p 1) ≠ 0 := by
  intro h0
  have h0' : ((3 : ℕ) : GaloisField p 1) = 0 := by exact_mod_cast h0
  have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff (GaloisField p 1) p 3).mp h0'
  have := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp hdvd
  omega


theorem rowSOf429_four_SL_mod_one : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 1 →
    RowSOf429 (projSL 4 (GaloisField p 1)) := by
  intro p _ hp hp1
  obtain ⟨ω, hω2⟩ := l4_exists_cube_root p hp1
  refine rowSOf429_of_noCfg fun S _ _ _ hna ⟨e⟩ => ?_
  exact noCfgS429_of_model e (center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e (l4_not_three_dvd_outer p))
    (fun x hx => l4_good429_projSL hω2 (l4_three_ne_zero p hp) x hx)

end CFSG.RankThree.PartTwo.Sec4.RonanK429H
