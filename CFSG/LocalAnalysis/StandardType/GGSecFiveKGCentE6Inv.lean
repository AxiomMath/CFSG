module

public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LieType.Chevalley.ExactNormalFormE
public import CFSG.LieType.Steinberg.Adjoint.Pairs

public section

namespace CFSG.StandardType.KGCentE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

theorem cartan_symmetric_E6 (i j : Fin Tag.E6.rank) :
    Tag.cartan Tag.E6 i j = Tag.cartan Tag.E6 j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem cartan_diag_E6 (i : Fin Tag.E6.rank) : Tag.cartan Tag.E6 i i = 2 := by
  revert i
  decide

theorem iform_eq_E6 (x y : Fin Tag.E6.rank → ℤ) :
    iform x y = x ⬝ᵥ (Tag.cartan Tag.E6 *ᵥ y) := by
  simp only [iform, Tag.symmetrizedCartan, Tag.symmetrizer, Matrix.one_mul, dotProduct, mulVec,
    Finset.mul_sum, mul_assoc]

theorem dotProduct_cartan_single (x : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank) :
    x ⬝ᵥ (Tag.cartan Tag.E6 *ᵥ Pi.single i 1) = (Tag.cartan Tag.E6 *ᵥ x) i := by
  simp only [dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun k _ => by rw [cartan_symmetric_E6, mul_comm]

theorem reflect_eq_E6 (i : Fin Tag.E6.rank) (v : Fin Tag.E6.rank → ℤ) :
    reflect Tag.E6 i v = v - (Tag.cartan Tag.E6 *ᵥ v) i • Pi.single i 1 :=
  rfl

theorem iform_reflect_E6 (i : Fin Tag.E6.rank) (x y : Fin Tag.E6.rank → ℤ) :
    iform (reflect Tag.E6 i x) (reflect Tag.E6 i y) = iform x y := by
  have h1 : (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ⬝ᵥ (Tag.cartan Tag.E6 *ᵥ y) =
      (Tag.cartan Tag.E6 *ᵥ y) i := by
    simp [single_dotProduct]
  have h2 : (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ⬝ᵥ (Tag.cartan Tag.E6 *ᵥ Pi.single i 1) = 2 := by
    rw [dotProduct_cartan_single]
    simp [mulVec, dotProduct, Pi.single_apply, cartan_diag_E6]
  simp only [reflect_eq_E6, iform_eq_E6, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, dotProduct_cartan_single, h1, h2, smul_eq_mul]
  ring

theorem iform_smul_E6 (w : WeylGroup Tag.E6) (x y : Fin Tag.E6.rank → ℤ) :
    iform (w • x) (w • y) = iform x y := by
  induction w using (coxeterSystem Tag.E6).simple_induction_left generalizing x y with
  | one => simp
  | mul_simple_left w i ih =>
    rw [mul_smul, mul_smul, simple_smul, simple_smul, iform_reflect_E6, ih]

abbrev diagPermE6 : Equiv.Perm (Fin Tag.E6.rank) := TwistTag.E6.perm

theorem cartan_diagPermE6 (i j : Fin Tag.E6.rank) :
    Tag.cartan Tag.E6 (diagPermE6 i) (diagPermE6 j) = Tag.cartan Tag.E6 i j :=
  TwistTag.cartan_perm TwistTag.E6 i j

theorem iform_permLattice_diagPermE6 (x y : Fin Tag.E6.rank → ℤ) :
    iform (permLattice diagPermE6 x) (permLattice diagPermE6 y) = iform x y := by
  simp only [iform_eq_E6, dotProduct, mulVec, permLattice, Function.comp_apply]
  rw [← Equiv.sum_comp diagPermE6]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Equiv.symm_apply_apply]
  congr 1
  rw [← Equiv.sum_comp diagPermE6]
  exact Finset.sum_congr rfl fun j _ => by rw [Equiv.symm_apply_apply, cartan_diagPermE6]

theorem exactPerm_E6_of_odd {ε : ℕ} (hε : ε % 2 = 1) : exactPerm .E6 ε = diagPermE6 := by
  have h2 : (diagPermE6 : Equiv.Perm (Fin Tag.E6.rank)) ^ 2 = 1 := by
    ext i
    fin_cases i <;> rfl
  obtain ⟨k, rfl⟩ : ∃ k, ε = 2 * k + 1 := ⟨ε / 2, by omega⟩
  show (diagPermE6 : Equiv.Perm (Fin Tag.E6.rank)) ^ (2 * k + 1) = _
  rw [pow_succ, pow_mul, h2, one_pow, one_mul]

theorem three_dvd_smul_sub (u : Fin Tag.E6.rank → ℤ)
    (hu : ∀ i, (3 : ℤ) ∣ (Tag.cartan Tag.E6 *ᵥ u) i) (w : WeylGroup Tag.E6) :
    ∀ k, (3 : ℤ) ∣ (w • u - u) k := by
  induction w using (coxeterSystem Tag.E6).simple_induction_left with
  | one => intro k; simp
  | mul_simple_left w i ih =>
    intro k
    have ht : (3 : ℤ) ∣ (Tag.cartan Tag.E6 *ᵥ (w • u)) i := by
      have e : (Tag.cartan Tag.E6 *ᵥ (w • u)) i = (Tag.cartan Tag.E6 *ᵥ u) i +
          ∑ j, Tag.cartan Tag.E6 i j * (w • u - u) j := by
        simp only [mulVec, dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
        ring
      rw [e]
      exact dvd_add (hu i) (Finset.dvd_sum fun j _ => Dvd.dvd.mul_left (ih j) _)
    rw [mul_smul, simple_smul, reflect_eq_E6]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    have h := ih k
    simp only [Pi.sub_apply] at h
    split_ifs
    · rw [mul_one]
      have : (w • u) k - (Tag.cartan Tag.E6 *ᵥ (w • u)) i - u k =
          ((w • u) k - u k) - (Tag.cartan Tag.E6 *ᵥ (w • u)) i := by ring
      rw [this]
      exact dvd_sub h ht
    · rw [mul_zero, sub_zero]
      exact h

end CFSG.StandardType.KGCentE6
