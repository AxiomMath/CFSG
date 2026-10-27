module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Data
public import CFSG.Quasithin.EmptyFaithful.S1421Elim

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.S1421Elim
open scoped MatrixGroups

section SmallGroups

private noncomputable def szRoot (a : ℕ) (x y : GaloisField 2 (2 * a + 1)) :
    Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1)) :=
  !![1, x, y, x ^ (2 + 2 ^ (a + 1)) + x * y + y ^ (2 ^ (a + 1));
    0, 1, x ^ (2 ^ (a + 1)), x ^ (1 + 2 ^ (a + 1)) + y;
    0, 0, 1, x;
    0, 0, 0, 1]

private theorem det_szRoot (a : ℕ) (x y : GaloisField 2 (2 * a + 1)) :
    (szRoot a x y).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [szRoot, Fin.prod_univ_four]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [szRoot]

theorem sixtyFour_le_card_sz {a : ℕ} (ha : 1 ≤ a) : 64 ≤ Nat.card ↥(Sz a) := by
  let K := GaloisField 2 (2 * a + 1)
  have hunit : ∀ x y : K, IsUnit (szRoot a x y).det := fun x y => by
    rw [det_szRoot]
    exact isUnit_one
  let u : K × K → GL (Fin 4) K := fun p => Matrix.nonsingInvUnit (szRoot a p.1 p.2) (hunit _ _)
  have hu : ∀ p, u p ∈ Sz a := fun p => Subgroup.subset_closure (Or.inl ⟨p.1, p.2, rfl⟩)
  let φ : K × K → ↥(Sz a) := fun p => ⟨u p, hu p⟩
  have hφ : Function.Injective φ := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    have h' : szRoot a x y = szRoot a x' y' :=
      congrArg (fun v : ↥(Sz a) => ((v : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) h
    have h1 := congrFun (congrFun h' 0) 1
    have h2 := congrFun (congrFun h' 0) 2
    simp only [szRoot] at h1 h2
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons] at h1 h2
    rw [h1, h2]
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  have hle := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, hK] at hle
  calc 64 = 2 ^ 3 * 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega))
          (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ ≤ Nat.card ↥(Sz a) := hle

end SmallGroups

end CFSG.Quasithin.H13
