module

public import CFSG.Quasithin.Vol2.Ch3E213MOLA5
public import CFSG.ClassicalInvolution.AschTight.S19KUniStd

public section

namespace CFSG.Quasithin.Ch3E213M.OLA

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalInvolution.Disconnected.AschTight.S19K CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  {E : Type} [Group E]

theorem center_pow_three_su3 (hF : Nat.card F = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    ∀ c ∈ Subgroup.center (Phan.Su F p f 3), c ^ 3 = 1 := by
  intro c hc
  obtain ⟨r, hr⟩ := exists_scalar_of_mem_center_su hF hq (le_refl 3) hc
  have hr' : (((c : Phan.Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.scalar (Fin 3) r := hr
  have hdet := (mem_SUid.mp c.2).1
  rw [hr', Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_const] at hdet
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hr', ← map_pow, hdet, map_one,
    Subgroup.coe_one, Units.val_one]

theorem uni_centralizer_two (hF : Nat.card F = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hq4 : p ^ f % 4 = 1) (θ : Phan.Su F p f 3 →* E) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Phan.Su F p f 3)) :
    ∀ c ∈ Subgroup.centralizer (((rootU F p f).map θ : Subgroup E) : Set E), ∀ k : ℕ,
      c ^ 2 ^ k = 1 → c ∈ Subgroup.zpowers (θ (Models.rootInvSU F p f (n := 3) (by norm_num))) := by
  intro c hc k hk
  have hcl2 := Models.isClassicalSL2_rootSU2 (K := F) (p := p) (f := f) hF hp
    (by norm_num : 2 ≤ 3)
  have h4 : 4 ≤ Nat.card (fixedSubfield F p f) := by rw [card_fixedSubfield hF]; omega
  have : Group.IsPerfect (rootU F p f) := hcl2.isPerfect h4
  obtain ⟨x, rfl⟩ := hθ c
  have hx := mem_centralizer_of_map hker Subgroup.commutator_eq_self hc
  obtain ⟨h01, h02, h10, h12, h20, h21, h0011⟩ :=
    isBlockScalar_of_mem_centralizerU hF hp (by omega) hx
  set X := (((x : Phan.Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hX
  have hXd : X = Matrix.diagonal ![X 0 0, X 0 0, X 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21, ← h0011]
  have hpow : ∀ n : ℕ, (((x ^ n : Phan.Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![X 0 0 ^ n, X 0 0 ^ n, X 2 2 ^ n] := by
    intro n
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ← hX, hXd, Matrix.diagonal_pow]
    congr 1
    ext i
    fin_cases i <;> rfl
  have hmem := mem_SUid.mp x.2
  have hdet : X 0 0 * X 0 0 * X 2 2 = 1 := by
    have h1 := hmem.1
    rw [← hX, hXd, Matrix.det_diagonal, Fin.prod_univ_three] at h1
    simpa [mul_assoc] using h1
  have hlq : X 0 0 ^ (p ^ f + 1) = 1 := by
    have h1 := congrFun (congrFun hmem.2 0) 0
    simp [conjTr, Matrix.mul_apply, Fin.sum_univ_three, ← hX, h10, h20] at h1
    rw [pow_succ]
    exact h1
  have hk' : x ^ 2 ^ k ∈ θ.ker := by rw [MonoidHom.mem_ker, map_pow, hk]
  obtain ⟨r, hr⟩ := exists_scalar_of_mem_center_su hF hq (le_refl 3) (hker hk')
  have hr' : (((x ^ 2 ^ k : Phan.Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.scalar (Fin 3) r := hr
  have hlk : X 0 0 ^ 2 ^ k = r := by
    have h1 := congrFun (congrFun (hpow (2 ^ k)) 0) 0
    rw [hr'] at h1
    simpa [Matrix.scalar_apply] using h1.symm
  have hmk : X 2 2 ^ 2 ^ k = r := by
    have h1 := congrFun (congrFun (hpow (2 ^ k)) 2) 2
    rw [hr'] at h1
    simpa [Matrix.scalar_apply] using h1.symm
  have hr3 : r ^ 3 = 1 := by
    calc r ^ 3 = (X 0 0 ^ 2 ^ k) ^ 2 * X 2 2 ^ 2 ^ k := by rw [hlk, hmk]; ring
      _ = (X 0 0 * X 0 0 * X 2 2) ^ 2 ^ k := by ring
      _ = 1 := by rw [hdet, one_pow]
  have hνk : (X 0 0 ^ 3) ^ 2 ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, hlk, hr3]
  have hνq : (X 0 0 ^ 3) ^ (2 * ((p ^ f + 1) / 2)) = 1 := by
    rw [show 2 * ((p ^ f + 1) / 2) = p ^ f + 1 by omega, ← pow_mul, mul_comm, pow_mul, hlq,
      one_pow]
  have hν2 := sq_eq_one_of_pow hνk hνq (Nat.odd_iff.mpr (by omega))
  have hμ3 : X 2 2 ^ 3 = 1 := by
    have h1 : (X 0 0 * X 0 0 * X 2 2) ^ 3 = (X 0 0 ^ 3) ^ 2 * X 2 2 ^ 3 := by ring
    rw [hdet, one_pow, hν2, one_mul] at h1
    exact h1.symm
  have h3 : θ x ^ 3 ∈ Subgroup.zpowers (θ (Models.rootInvSU F p f (n := 3) (by norm_num))) := by
    have h1 : (X 0 0 ^ 3 - 1) * (X 0 0 ^ 3 + 1) = 0 := by linear_combination hν2
    rw [← map_pow]
    rcases mul_eq_zero.mp h1 with h | h
    · have hx3 : x ^ 3 = 1 := by
        apply Subtype.ext
        apply Units.ext
        rw [hpow, sub_eq_zero.mp h, hμ3, Subgroup.coe_one, Units.val_one]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      rw [hx3, map_one]
      exact Subgroup.one_mem _
    · have hx3 : x ^ 3 = Models.rootInvSU F p f (n := 3) (by norm_num) := by
        apply Subtype.ext
        apply Units.ext
        rw [hpow, eq_neg_of_add_eq_zero_left h, hμ3, coe_rootInvSU_three]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      rw [hx3]
      exact Subgroup.mem_zpowers _
  exact mem_of_pow_three_mem hk h3

end CFSG.Quasithin.Ch3E213M.OLA
