module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoStd
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.StandardType.LevTwo

open LevTwoType

theorem levTwoS4c_rank_of_det_ne_zero {p : ℕ} (hp : p.Prime) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (h : ¬ (p : ℤ) ∣ A.det) :
    (A.map (Int.castRingHom (ZMod p))).rank = n := by
  have : Fact p.Prime := ⟨hp⟩
  have hdet : (A.map (Int.castRingHom (ZMod p))).det ≠ 0 := by
    rw [show A.map (Int.castRingHom (ZMod p)) = A.map (fun x : ℤ => (x : ZMod p)) from rfl]
    rw [← Int.cast_det]
    exact fun h0 => h ((ZMod.intCast_zmod_eq_zero_iff_dvd A.det p).mp h0)
  simpa using Matrix.rank_of_det_ne_zero hdet

theorem levTwoS4c_le_rank_of_minor {p : ℕ} (hp : p.Prime) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (e : Fin m → Fin n)
    (h : ¬ (p : ℤ) ∣ (A.submatrix e e).det) :
    m ≤ (A.map (Int.castRingHom (ZMod p))).rank := by
  have : Fact p.Prime := ⟨hp⟩
  have hdet : ((A.map (Int.castRingHom (ZMod p))).submatrix e e).det ≠ 0 := by
    rw [Matrix.submatrix_map,
      show (A.submatrix e e).map (Int.castRingHom (ZMod p)) =
        (A.submatrix e e).map (fun x : ℤ => (x : ZMod p)) from rfl]
    rw [← Int.cast_det]
    exact fun h0 => h ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0)
  have h2 : ((A.map (Int.castRingHom (ZMod p))).submatrix e e).rank = m := by
    simpa using Matrix.rank_of_det_ne_zero hdet
  calc m = _ := h2.symm
    _ ≤ _ := Matrix.rank_submatrix_le _ e e

private theorem levTwoS4c_not_dvd_one_two_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c : ℤ}
    (hc : c = 1 ∨ c = 2 ∨ c = 4) : ¬ (p : ℤ) ∣ c := by
  rintro h
  rcases hc with rfl | rfl | rfl
  · exact hp.ne_one (Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 h))
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (Int.natCast_dvd_natCast.1 h))
  · have h2 : p ∣ 2 := by
      apply hp.dvd_of_dvd_pow (n := 2)
      simpa using Int.natCast_dvd_natCast.1 h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

theorem levTwoS4c_det_A (n : ℕ) : (CartanMatrix.A n).det = (n : ℤ) + 1 :=
  CartanMatrix.A_det n

theorem levTwoS4c_det_B {n : ℕ} (hn : 0 < n) : (CartanMatrix.B n).det = 2 :=
  CartanMatrix.B_det hn

theorem levTwoS4c_det_D {n : ℕ} (hn : 2 ≤ n) : (CartanMatrix.D n).det = 4 :=
  CartanMatrix.D_det hn

theorem levTwoS4c_det_E6 : (CartanMatrix.E 6).det = 3 := by
  rw [← CFSG.LieType.Chevalley.laplaceDet_eq_det]; decide +kernel

theorem levTwoS4c_det_E7 : (CartanMatrix.E 7).det = 2 := by
  rw [← CFSG.LieType.Chevalley.laplaceDet_eq_det]; decide +kernel

theorem levTwoS4c_det_E8 : (CartanMatrix.E 8).det = 1 := by
  rw [← CFSG.LieType.Chevalley.laplaceDet_eq_det]; decide +kernel

theorem levTwoS4c_det_F4 : (CartanMatrix.F₄).det = 1 := by
  rw [← CFSG.LieType.Chevalley.laplaceDet_eq_det]; decide +kernel

def levTwoS4c_embA (n : ℕ) : Fin (n - 1) → Fin n := fun i => ⟨i.1, by omega⟩

theorem levTwoS4c_det_A_minor {n : ℕ} (hn : 1 ≤ n) :
    ((CartanMatrix.A n).submatrix (levTwoS4c_embA n) (levTwoS4c_embA n)).det = (n : ℤ) := by
  have hsub : (CartanMatrix.A n).submatrix (levTwoS4c_embA n) (levTwoS4c_embA n) =
      CartanMatrix.A (n - 1) := by
    ext i j
    simp only [Matrix.submatrix_apply, CartanMatrix.A, Matrix.of_apply]
    split_ifs with h1 h2 h3 <;> simp_all [Fin.ext_iff, levTwoS4c_embA]
  rw [hsub, CartanMatrix.A_det]
  have h3 : (n - 1 : ℕ) + 1 = n := by omega
  exact_mod_cast h3

def levTwoS4c_embE6 : Fin 5 → Fin 6 := fun i => ⟨i.1, by omega⟩

theorem levTwoS4c_det_E6_minor :
    ((CartanMatrix.E 6).submatrix levTwoS4c_embE6 levTwoS4c_embE6).det = 4 := by
  rw [← CFSG.LieType.Chevalley.laplaceDet_eq_det]; decide +kernel

theorem levTwoS4c_rankPair (T : LevTwoType) (hT : T.Valid) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    T.n ≤ (T.pair.map (Int.castRingHom (ZMod p))).rank + 1 ∧
      (¬ (p : ℤ) ∣ T.pair.det → (T.pair.map (Int.castRingHom (ZMod p))).rank = T.n) := by
  constructor
  · cases T with
    | A n =>
        change n ≤ Matrix.rank ((CartanMatrix.A n).map (Int.castRingHom (ZMod p))) + 1
        have hn : 1 ≤ n := hT
        by_cases hpdiv : (p : ℤ) ∣ (CartanMatrix.A n).det
        · have hpn1 : (p : ℤ) ∣ (n : ℤ) + 1 := by rwa [levTwoS4c_det_A n] at hpdiv
          have hpndvd : ¬ (p : ℤ) ∣ (n : ℤ) := by
            intro hpn
            have h1 : (p : ℤ) ∣ (1 : ℤ) := by
              have := dvd_sub hpn1 hpn
              simpa using this
            exact hp.ne_one (Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 h1))
          have hminor : ¬ (p : ℤ) ∣
              ((CartanMatrix.A n).submatrix (levTwoS4c_embA n) (levTwoS4c_embA n)).det := by
            rw [levTwoS4c_det_A_minor hn]
            exact hpndvd
          have := levTwoS4c_le_rank_of_minor hp (CartanMatrix.A n) (levTwoS4c_embA n) hminor
          omega
        · have := levTwoS4c_rank_of_det_ne_zero hp (CartanMatrix.A n) hpdiv
          omega
    | B n =>
        change n ≤ Matrix.rank ((CartanMatrix.B n).map (Int.castRingHom (ZMod p))) + 1
        have h2n : 2 ≤ n := hT
        have hn : 0 < n := by omega
        have hndvd : ¬ (p : ℤ) ∣ (CartanMatrix.B n).det := by
          rw [levTwoS4c_det_B hn]
          exact levTwoS4c_not_dvd_one_two_four hp hp2 (Or.inr (Or.inl rfl))
        have := levTwoS4c_rank_of_det_ne_zero hp (CartanMatrix.B n) hndvd
        omega
    | D n =>
        change n ≤ Matrix.rank ((CartanMatrix.D n).map (Int.castRingHom (ZMod p))) + 1
        have hn4 : 4 ≤ n := hT
        have hn : 2 ≤ n := by omega
        have hndvd : ¬ (p : ℤ) ∣ (CartanMatrix.D n).det := by
          rw [levTwoS4c_det_D hn]
          exact levTwoS4c_not_dvd_one_two_four hp hp2 (Or.inr (Or.inr rfl))
        have := levTwoS4c_rank_of_det_ne_zero hp (CartanMatrix.D n) hndvd
        omega
    | E6 =>
        change 6 ≤ Matrix.rank ((CartanMatrix.E 6).map (Int.castRingHom (ZMod p))) + 1
        have hminor : ¬ (p : ℤ) ∣
            ((CartanMatrix.E 6).submatrix levTwoS4c_embE6 levTwoS4c_embE6).det := by
          rw [levTwoS4c_det_E6_minor]
          exact levTwoS4c_not_dvd_one_two_four hp hp2 (Or.inr (Or.inr rfl))
        have := levTwoS4c_le_rank_of_minor hp (CartanMatrix.E 6) levTwoS4c_embE6 hminor
        omega
    | E7 =>
        change 7 ≤ Matrix.rank ((CartanMatrix.E 7).map (Int.castRingHom (ZMod p))) + 1
        have hndvd : ¬ (p : ℤ) ∣ (CartanMatrix.E 7).det := by
          rw [levTwoS4c_det_E7]
          exact levTwoS4c_not_dvd_one_two_four hp hp2 (Or.inr (Or.inl rfl))
        have := levTwoS4c_rank_of_det_ne_zero hp (CartanMatrix.E 7) hndvd
        omega
    | E8 =>
        change 8 ≤ Matrix.rank ((CartanMatrix.E 8).map (Int.castRingHom (ZMod p))) + 1
        have hndvd : ¬ (p : ℤ) ∣ (CartanMatrix.E 8).det := by
          rw [levTwoS4c_det_E8]
          exact levTwoS4c_not_dvd_one_two_four hp hp2 (Or.inl rfl)
        have := levTwoS4c_rank_of_det_ne_zero hp (CartanMatrix.E 8) hndvd
        omega
    | F4 =>
        change 4 ≤ Matrix.rank ((CartanMatrix.F₄).map (Int.castRingHom (ZMod p))) + 1
        have hndvd : ¬ (p : ℤ) ∣ (CartanMatrix.F₄).det := by
          rw [levTwoS4c_det_F4]
          exact levTwoS4c_not_dvd_one_two_four hp hp2 (Or.inl rfl)
        have := levTwoS4c_rank_of_det_ne_zero hp (CartanMatrix.F₄) hndvd
        omega
  · intro h
    exact levTwoS4c_rank_of_det_ne_zero hp T.pair h

end CFSG.StandardType.LevTwo
