module

public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open Polynomial Matrix

section Four

variable {F : Type*} [Field F] [Fintype F]

theorem cube_eq_zero_or_one (hF : Fintype.card F = 4) (x : F) : x ^ 3 = 0 ∨ x ^ 3 = 1 := by
  by_cases hx : x = 0
  · left
    simp [hx]
  · right
    have := FiniteField.pow_card_sub_one_eq_one x hx
    rwa [hF] at this

theorem exists_omega (hF : Fintype.card F = 4) :
    ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0 := by
  classical
  obtain ⟨ω, hω⟩ : ∃ ω : F, ω ∉ ({0, 1} : Finset F) := by
    by_contra h
    push Not at h
    have h1 := Finset.card_le_card (fun x (_ : x ∈ (Finset.univ : Finset F)) => h x)
    rw [Finset.card_univ, hF] at h1
    have h2 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  have h3 : ω ^ 3 = 1 := (cube_eq_zero_or_one hF ω).resolve_left (pow_ne_zero 3 hω.1)
  have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
  exact ⟨ω, hω.1, hω.2, (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω.2)⟩

theorem isCoprime_charpoly (hF : Fintype.card F = 4) {ζ : F} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    {M : Matrix (Fin 3) (Fin 3) F} (hdet : M.det = 1) :
    IsCoprime (X ^ 3 - C ζ) M.charpoly := by
  have hdeg : (X ^ 3 - C ζ : F[X]).natDegree = 3 := by
    rw [natDegree_sub_C, natDegree_X_pow]
  have hirr : Irreducible (X ^ 3 - C ζ : F[X]) := by
    refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) fun x hx => ?_
    rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hx
    rcases cube_eq_zero_or_one hF x with h | h
    · exact hζ0 (hx.symm.trans h)
    · exact hζ1 (hx.symm.trans h)
  refine (Irreducible.coprime_iff_not_dvd hirr).mpr fun hdvd => ?_
  have hmon : (X ^ 3 - C ζ : F[X]).Monic := monic_X_pow_sub_C ζ (by norm_num)
  have heq : M.charpoly = X ^ 3 - C ζ :=
    eq_of_monic_of_dvd_of_natDegree_le hmon (charpoly_monic M) hdvd
      (by rw [charpoly_natDegree_eq_dim, Fintype.card_fin, hdeg])
  have h0 := det_eq_sign_charpoly_coeff M
  rw [heq, hdet, Fintype.card_fin, coeff_sub, coeff_X_pow, coeff_C_zero] at h0
  norm_num at h0
  exact hζ1 (by linear_combination -h0)

theorem pow_three_eq_one_of_pow_nine (hF : Fintype.card F = 4) {M : Matrix (Fin 3) (Fin 3) F}
    (hdet : M.det = 1) (h9 : M ^ 9 = 1) : M ^ 3 = 1 := by
  obtain ⟨ω, hω0, hω1, hω⟩ := exists_omega hF
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω20 : ω ^ 2 ≠ 0 := pow_ne_zero 2 hω0
  have hω21 : ω ^ 2 ≠ 1 := by
    intro h
    apply hω1
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by field_simp
      _ = 1 := by rw [hω3, h, inv_one, one_mul]
  have hcop := (isCoprime_charpoly hF hω0 hω1 hdet).mul_left
    (isCoprime_charpoly hF hω20 hω21 hdet)
  obtain ⟨u, v, huv⟩ := hcop
  have hC1 : C ω + C (ω ^ 2) = (-1 : F[X]) := by
    rw [← C_add, show ω + ω ^ 2 = -1 by linear_combination hω, C_neg, C_1]
  have hC2 : C ω * C (ω ^ 2) = (1 : F[X]) := by
    rw [← C_mul, show ω * ω ^ 2 = 1 by linear_combination hω3, C_1]
  have hq : (X ^ 3 - 1 : F[X]) * ((X ^ 3 - C ω) * (X ^ 3 - C (ω ^ 2))) = X ^ 9 - 1 := by
    linear_combination (X ^ 3 - 1 : F[X]) * ((-(X : F[X]) ^ 3) * hC1 + hC2)
  have hkey : (X ^ 3 - 1 : F[X]) = u * (X ^ 9 - 1) + v * (X ^ 3 - 1) * M.charpoly := by
    calc (X ^ 3 - 1 : F[X]) = (X ^ 3 - 1) * (u * ((X ^ 3 - C ω) * (X ^ 3 - C (ω ^ 2))) +
          v * M.charpoly) := by rw [huv, mul_one]
      _ = u * ((X ^ 3 - 1) * ((X ^ 3 - C ω) * (X ^ 3 - C (ω ^ 2)))) +
          v * (X ^ 3 - 1) * M.charpoly := by ring
      _ = u * (X ^ 9 - 1) + v * (X ^ 3 - 1) * M.charpoly := by rw [hq]
  have h := congrArg (aeval M) hkey
  simp only [map_sub, map_add, map_mul, map_pow, aeval_X, map_one, aeval_self_charpoly,
    mul_zero, add_zero, h9, sub_self] at h
  exact sub_eq_zero.mp h

end Four

section Two

variable {F : Type*} [Field F]

theorem mul_self_eq_two (X : Matrix (Fin 2) (Fin 2) F) :
    X * X = (X 0 0 + X 1 1) • X - X.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem exists_eq_of_commute {X Y : Matrix (Fin 2) (Fin 2) F}
    (hX : ¬ (X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 0 0 = X 1 1)) (hXY : Y * X = X * Y) :
    ∃ α β : F, Y = α • (1 : Matrix (Fin 2) (Fin 2) F) + β • X := by
  have e := fun i j => congrFun (congrFun hXY i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  by_cases hb : X 0 1 = 0
  · by_cases hc : X 1 0 = 0
    · have had : X 0 0 - X 1 1 ≠ 0 := fun h => hX ⟨hb, hc, sub_eq_zero.mp h⟩
      refine ⟨Y 0 0 - (Y 0 0 - Y 1 1) / (X 0 0 - X 1 1) * X 0 0,
        (Y 0 0 - Y 1 1) / (X 0 0 - X 1 1), ?_⟩
      have hf : Y 0 1 = 0 := by
        have : Y 0 1 * (X 0 0 - X 1 1) = 0 := by rw [hb] at e01; linear_combination -e01
        exact (mul_eq_zero.mp this).resolve_right had
      have hg : Y 1 0 = 0 := by
        have : Y 1 0 * (X 0 0 - X 1 1) = 0 := by rw [hc] at e10; linear_combination e10
        exact (mul_eq_zero.mp this).resolve_right had
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, hf, hg]
      field_simp
      ring
    · refine ⟨Y 0 0 - Y 1 0 / X 1 0 * X 0 0, Y 1 0 / X 1 0, ?_⟩
      have hf : Y 0 1 = 0 := by
        have : Y 0 1 * X 1 0 = 0 := by rw [hb] at e00; linear_combination e00
        exact (mul_eq_zero.mp this).resolve_right hc
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hf] <;> field_simp
      linear_combination e10
  · refine ⟨Y 0 0 - Y 0 1 / X 0 1 * X 0 0, Y 0 1 / X 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;>
      first | ring1 | linear_combination e00 | linear_combination -e00 |
        linear_combination -e01 - e00 | linear_combination e01 + e00 |
        linear_combination e01 | linear_combination -e01

theorem trace_eq_neg_one {X : Matrix (Fin 2) (Fin 2) F} (hdet : X.det = 1) (h3 : X ^ 3 = 1)
    (h1 : X ≠ 1) :
    ¬ (X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 0 0 = X 1 1) ∧ X 0 0 + X 1 1 = -1 := by
  have hCH := mul_self_eq_two X
  rw [hdet, one_smul] at hCH
  set t := X 0 0 + X 1 1 with ht
  have hX3 : X ^ 3 = (t ^ 2 - 1) • X - t • (1 : Matrix (Fin 2) (Fin 2) F) := by
    calc X ^ 3 = X * (X * X) := pow_three X
      _ = X * (t • X - 1) := by rw [hCH]
      _ = t • (X * X) - X := by rw [mul_sub, mul_smul_comm, mul_one]
      _ = t • (t • X - 1) - X := by rw [hCH]
      _ = (t ^ 2 - 1) • X - t • (1 : Matrix (Fin 2) (Fin 2) F) := by
        rw [smul_sub, smul_smul, sub_smul, one_smul, sq]
        abel
  rw [h3] at hX3
  have e := fun i j => congrFun (congrFun hX3 i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp at e00 e01 e10 e11
  have hns : ¬ (X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 0 0 = X 1 1) := by
    rintro ⟨hb, hc, had⟩
    apply h1
    have hd := hdet
    rw [Matrix.det_fin_two, hb, hc, had] at hd
    rw [ht, had] at e00
    have hl : X 1 1 = 1 := by linear_combination (-1 : F) * e00 - 4 * X 1 1 * hd
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, had, hl]
  refine ⟨hns, ?_⟩
  have ht2 : t ^ 2 - 1 = 0 := by
    by_contra hne
    apply hns
    refine ⟨?_, ?_, ?_⟩
    · exact e01.resolve_left hne
    · exact e10.resolve_left hne
    · have : (t ^ 2 - 1) * (X 0 0 - X 1 1) = 0 := by linear_combination e11 - e00
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hne)
  linear_combination e00 + X 0 0 * ht2

theorem eq_one_or_of_commute (h3F : (3 : F) ≠ 0) {X Y : Matrix (Fin 2) (Fin 2) F}
    (hXd : X.det = 1) (hYd : Y.det = 1) (hX3 : X ^ 3 = 1) (hY3 : Y ^ 3 = 1) (hX1 : X ≠ 1)
    (hXY : Y * X = X * Y) : Y = 1 ∨ Y = X ∨ Y = X * X := by
  by_cases hY1 : Y = 1
  · exact Or.inl hY1
  right
  obtain ⟨hXns, htX⟩ := trace_eq_neg_one hXd hX3 hX1
  obtain ⟨-, htY⟩ := trace_eq_neg_one hYd hY3 hY1
  have hCH := mul_self_eq_two X
  rw [hXd, one_smul, htX] at hCH
  obtain ⟨α, β, rfl⟩ := exists_eq_of_commute hXns hXY
  have hXd' := hXd
  rw [Matrix.det_fin_two] at hXd' hYd
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hYd htY
  norm_num at hYd htY
  have h1 : 2 * α - β = -1 := by linear_combination htY - β * htX
  have h2 : α ^ 2 - α * β + β ^ 2 = 1 := by
    linear_combination hYd - α * β * htX - β ^ 2 * hXd'
  have h3 : 3 * (α * (α + 1)) = 0 := by
    linear_combination h2 + (3 * α + 2 + (β - 2 * α - 1)) * h1
  rcases mul_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left h3F) with ha | ha
  · left
    have hb : β = 1 := by linear_combination -h1 + 2 * ha
    rw [ha, hb, zero_smul, one_smul, zero_add]
  · right
    have ha' : α = -1 := by linear_combination ha
    have hb : β = -1 := by linear_combination -h1 + 2 * ha
    rw [hCH, ha', hb, neg_one_smul, neg_one_smul]
    abel

end Two

section GL2

theorem card_le_three_of_exponent_three {p : ℕ} [hp : Fact p.Prime]
    (Q : Subgroup (GL (Fin 2) (ZMod p)))
    (hdet : ∀ q ∈ Q, (q : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1) (h3 : ∀ q ∈ Q, q ^ 3 = 1) :
    Nat.card Q ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ3 : IsPGroup 3 ↥Q := fun q => ⟨1, Subtype.ext (by simpa using h3 q q.2)⟩
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨k, hk⟩ := hQ3.exists_card_eq
    have hdvd : Nat.card Q ∣ 48 := by
      have h := Subgroup.card_subgroup_dvd_card Q
      rwa [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two] at h
    rw [hk] at hdvd ⊢
    have hk1 : k ≤ 1 := by
      by_contra hk1
      have : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
      have := this.trans hdvd
      norm_num at this
    calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 3 := by norm_num
  have h3F : (3 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 3 := by exact_mod_cast (ZMod.natCast_eq_zero_iff 3 p).mp (by exact_mod_cast h)
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp this)
  rcases subsingleton_or_nontrivial ↥Q with hs | hnt
  · rw [Nat.card_unique (α := ↥Q)]
    norm_num
  have := hQ3.center_nontrivial
  obtain ⟨⟨z, hzc⟩, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥Q))
  have hz1' : (z : GL (Fin 2) (ZMod p)) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  have hsub : (Q : Set (GL (Fin 2) (ZMod p))) ⊆
      {1, (z : GL (Fin 2) (ZMod p)), (z : GL (Fin 2) (ZMod p)) * z} := by
    intro y hy
    have hyz := Subgroup.mem_center_iff.mp hzc ⟨y, hy⟩
    have hyz' : (y : Matrix (Fin 2) (Fin 2) (ZMod p)) * (z : GL (Fin 2) (ZMod p)) =
        ((z : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) * y := by
      have := congrArg (fun u : ↥Q => ((u : GL (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p))) hyz
      simpa using this
    have hz3 : ((z : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, h3 _ z.2, Units.val_one]
    have hy3 : (y : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, h3 y hy, Units.val_one]
    have hzM1 : ((z : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) ≠ 1 :=
      fun h => hz1' (Units.ext h)
    rcases eq_one_or_of_commute h3F (hdet _ z.2) (hdet y hy) hz3 hy3 hzM1 hyz' with h | h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Or.inl (Units.ext h))
    · exact Or.inr (Or.inr (Units.ext (by rw [h, Units.val_mul])))
  calc Nat.card Q = (Q : Set (GL (Fin 2) (ZMod p))).ncard := rfl
    _ ≤ ({1, (z : GL (Fin 2) (ZMod p)), (z : GL (Fin 2) (ZMod p)) * z} :
        Set (GL (Fin 2) (ZMod p))).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 3 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      have := Set.ncard_insert_le (z : GL (Fin 2) (ZMod p))
        {(z : GL (Fin 2) (ZMod p)) * z}
      rw [Set.ncard_singleton] at this
      omega

end GL2

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
