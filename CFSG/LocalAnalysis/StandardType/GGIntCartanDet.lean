module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

public section

namespace CFSG.StandardType

private theorem intCast_ne_zero_of_not_dvd {p : ℕ} {d : ℤ}
    (h : ¬ (p : ℤ) ∣ d) : (d : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact h

private theorem intCast_one_ne_zero {p : ℕ} [Fact p.Prime] :
    ((1 : ℤ) : ZMod p) ≠ 0 := by
  refine intCast_ne_zero_of_not_dvd fun h => ?_
  have hnat : p ∣ 1 := by
    have := Int.natAbs_dvd_natAbs.mpr h
    simpa using this
  have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) hnat
  have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
  omega

private theorem intCast_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ((2 : ℤ) : ZMod p) ≠ 0 := by
  refine intCast_ne_zero_of_not_dvd fun h => ?_
  have hnat : p ∣ 2 := by
    have := Int.natAbs_dvd_natAbs.mpr h
    simpa using this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by norm_num)).mp hnat)

private theorem intCast_three_ne_zero {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) :
    ((3 : ℤ) : ZMod p) ≠ 0 := by
  refine intCast_ne_zero_of_not_dvd fun h => ?_
  have hnat : p ∣ 3 := by
    have := Int.natAbs_dvd_natAbs.mpr h
    simpa using this
  exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by norm_num)).mp hnat)

private theorem intCast_four_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ((4 : ℤ) : ZMod p) ≠ 0 := by
  refine intCast_ne_zero_of_not_dvd fun h => ?_
  have hnat : p ∣ 4 := by
    have := Int.natAbs_dvd_natAbs.mpr h
    simpa using this
  have hp : p.Prime := Fact.out
  rcases (hp.dvd_mul (m := 2) (n := 2)).mp (by simpa using hnat) with h2 | h2
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h2)
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h2)

private theorem det_map_ne_zero_of_reindex {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {p n : ℕ} {C₀ : Matrix (Fin n) (Fin n) ℤ} {C : Matrix Λ Λ ℤ} (e : Fin n ≃ Λ)
    (h : C = Matrix.reindex e e C₀ ∨ C = (Matrix.reindex e e C₀).transpose)
    (hd : ((C₀.det : ℤ) : ZMod p) ≠ 0) :
    (C.map (Int.cast : ℤ → ZMod p)).det ≠ 0 := by
  rcases h with rfl | rfl
  · rw [← Int.cast_det, Matrix.det_reindex_self]
    exact hd
  · rw [← Int.cast_det, Matrix.det_transpose, Matrix.det_reindex_self]
    exact hd

theorem GGIntCartan.det_map_ne_zero_of_not_A {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C) (hW : GGIsWeylMatrix M)
    (hA : ¬ ∃ (n : ℕ) (e : Fin n ≃ Λ), M = (CoxeterMatrix.A n).reindex e)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hE6 : p = 3 → ¬ ∃ e : Fin 6 ≃ Λ, M = CoxeterMatrix.E₆.reindex e) :
    (C.map (Int.cast : ℤ → ZMod p)).det ≠ 0 := by
  rcases hW with hABD | hE6' | hE7 | hE8 | hF4 | hG2
  · rcases hABD with ⟨n, e, -, hA' | ⟨hnB, hB⟩ | ⟨hnD, hD⟩⟩
    · exact absurd ⟨n, e, hA'⟩ hA
    · have hC' : GGIntCartan ((CoxeterMatrix.B n).reindex e) C := hB ▸ hC
      exact det_map_ne_zero_of_reindex e
        (hC'.eq_or_eq_transpose ((ggIntCartan_B n).reindex e)
          ((ggAtMostOneMultipleEdge_B n).reindex e))
        (by rw [CartanMatrix.B_det (by omega)]; exact intCast_two_ne_zero hp2)
    · have hC' : GGIntCartan ((ggCoxeterMatrixD n).reindex e) C := hD ▸ hC
      exact det_map_ne_zero_of_reindex e
        (hC'.eq_or_eq_transpose ((ggIntCartan_D n).reindex e)
          ((ggAtMostOneMultipleEdge_D n).reindex e))
        (by rw [CartanMatrix.D_det (by omega)]; exact intCast_four_ne_zero hp2)
  · rcases hE6' with ⟨e, hMe⟩
    have hp3 : p ≠ 3 := fun hp => hE6 hp ⟨e, hMe⟩
    have hC' : GGIntCartan (CoxeterMatrix.E₆.reindex e) C := hMe ▸ hC
    exact det_map_ne_zero_of_reindex e
      (hC'.eq_or_eq_transpose (ggIntCartan_E₆.reindex e)
        (ggAtMostOneMultipleEdge_E₆.reindex e))
      (by
        rw [CartanMatrix.E_det (by norm_num : 3 ≤ 6)]
        rw [show (9 : ℤ) - ((6 : ℕ) : ℤ) = 3 by norm_num]
        exact intCast_three_ne_zero hp3)
  · rcases hE7 with ⟨e, hMe⟩
    have hC' : GGIntCartan (CoxeterMatrix.E₇.reindex e) C := hMe ▸ hC
    exact det_map_ne_zero_of_reindex e
      (hC'.eq_or_eq_transpose (ggIntCartan_E₇.reindex e)
        (ggAtMostOneMultipleEdge_E₇.reindex e))
      (by
        rw [CartanMatrix.E_det (by norm_num : 3 ≤ 7)]
        rw [show (9 : ℤ) - ((7 : ℕ) : ℤ) = 2 by norm_num]
        exact intCast_two_ne_zero hp2)
  · rcases hE8 with ⟨e, hMe⟩
    have hC' : GGIntCartan (CoxeterMatrix.E₈.reindex e) C := hMe ▸ hC
    exact det_map_ne_zero_of_reindex e
      (hC'.eq_or_eq_transpose (ggIntCartan_E₈.reindex e)
        (ggAtMostOneMultipleEdge_E₈.reindex e))
      (by
        rw [CartanMatrix.E_det (by norm_num : 3 ≤ 8)]
        rw [show (9 : ℤ) - ((8 : ℕ) : ℤ) = 1 by norm_num]
        exact intCast_one_ne_zero)
  · rcases hF4 with ⟨e, hMe⟩
    have hC' : GGIntCartan (CoxeterMatrix.F₄.reindex e) C := hMe ▸ hC
    exact det_map_ne_zero_of_reindex e
      (hC'.eq_or_eq_transpose (ggIntCartan_F₄.reindex e)
        (ggAtMostOneMultipleEdge_F₄.reindex e))
      (by rw [CartanMatrix.F₄_det]; exact intCast_one_ne_zero)
  · rcases hG2 with ⟨e, hMe⟩
    have hC' : GGIntCartan (CoxeterMatrix.G₂.reindex e) C := hMe ▸ hC
    exact det_map_ne_zero_of_reindex e
      (hC'.eq_or_eq_transpose (ggIntCartan_G₂.reindex e)
        (ggAtMostOneMultipleEdge_G₂.reindex e))
      (by rw [CartanMatrix.G₂_det]; exact intCast_one_ne_zero)

end CFSG.StandardType

end
