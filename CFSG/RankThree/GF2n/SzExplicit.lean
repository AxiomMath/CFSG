module

public import CFSG.Open.Catalog

public section

namespace CFSG.RankThree.GF2n.SzExplicit

open Matrix CFSG.Open

variable (n : ℕ)

abbrev F := GaloisField 2 (2 * n + 1)

@[expose] noncomputable def rootMat (a b : F n) : Matrix (Fin 4) (Fin 4) (F n) :=
  !![1, a, b, a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1));
     0, 1, a ^ (2 ^ (n + 1)), a ^ (1 + 2 ^ (n + 1)) + b;
     0, 0, 1, a;
     0, 0, 0, 1]

@[expose] noncomputable def wMat : Matrix (Fin 4) (Fin 4) (F n) :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

theorem rootMat_mem (a b : F n) : rootMat n a b ∈ SzGenerators n := Or.inl ⟨a, b, rfl⟩

theorem wMat_mem : wMat n ∈ SzGenerators n := Or.inr (Or.inr rfl)

theorem det_rootMat (a b : F n) : (rootMat n a b).det = 1 := by
  rw [det_of_isUpperTriangular]
  · simp [rootMat, Fin.prod_univ_four]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [rootMat]

theorem wMat_mul_self : wMat n * wMat n = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] noncomputable def rootGL (a b : F n) : GL (Fin 4) (F n) :=
  GeneralLinearGroup.mkOfDetNeZero (rootMat n a b) (by rw [det_rootMat]; exact one_ne_zero)

@[expose] noncomputable def wGL : GL (Fin 4) (F n) :=
  ⟨wMat n, wMat n, wMat_mul_self n, wMat_mul_self n⟩

@[simp] theorem coe_rootGL (a b : F n) :
    ((rootGL n a b : GL (Fin 4) (F n)) : Matrix (Fin 4) (Fin 4) (F n)) = rootMat n a b := rfl

@[simp] theorem coe_wGL : ((wGL n : GL (Fin 4) (F n)) : Matrix (Fin 4) (Fin 4) (F n)) = wMat n :=
  rfl

theorem rootGL_mem (a b : F n) : rootGL n a b ∈ Sz n :=
  Subgroup.subset_closure (show _ ∈ SzGenerators n by rw [coe_rootGL]; exact rootMat_mem n a b)

theorem wGL_mem : wGL n ∈ Sz n :=
  Subgroup.subset_closure (show _ ∈ SzGenerators n by rw [coe_wGL]; exact wMat_mem n)

theorem rootMat_zero_one : rootMat n 0 1 = !![1, 0, 1, 1; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMat]

theorem rootMat_one_zero : rootMat n 1 0 = !![1, 1, 0, 1; 0, 1, 1, 1; 0, 0, 1, 1; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMat]

theorem add_self' (x : F n) : x + x = 0 := CharTwo.add_self_eq_zero x

theorem rootMat_zero_one_mul_self : rootMat n 0 1 * rootMat n 0 1 = 1 := by
  rw [rootMat_zero_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, add_self']

theorem wMat_mul_rootMat : wMat n * rootMat n 0 1 =
    !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 1] := by
  rw [rootMat_zero_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem P_sq : (!![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 1] :
      Matrix (Fin 4) (Fin 4) (F n)) * !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 1] =
    !![1, 0, 1, 1; 0, 1, 0, 1; 1, 0, 0, 1; 1, 1, 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, add_self']

theorem P_four : (!![1, 0, 1, 1; 0, 1, 0, 1; 1, 0, 0, 1; 1, 1, 1, 1] :
      Matrix (Fin 4) (Fin 4) (F n)) * !![1, 0, 1, 1; 0, 1, 0, 1; 1, 0, 0, 1; 1, 1, 1, 1] =
    !![1, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, add_self']

theorem P_five : (!![1, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] :
      Matrix (Fin 4) (Fin 4) (F n)) * !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, add_self']

theorem wMat_mul_rootMat_pow_five : (wMat n * rootMat n 0 1) ^ 5 = 1 := by
  rw [wMat_mul_rootMat]
  set P : Matrix (Fin 4) (Fin 4) (F n) := !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 1]
    with hP
  have h2 : P ^ 2 = !![1, 0, 1, 1; 0, 1, 0, 1; 1, 0, 0, 1; 1, 1, 1, 1] := by
    rw [sq, hP]
    exact P_sq n
  have h4 : P ^ 4 = !![1, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
    rw [show P ^ 4 = (P ^ 2) ^ 2 by rw [← pow_mul], h2, sq]
    exact P_four n
  rw [pow_succ, h4, hP]
  exact P_five n

theorem wMat_mul_rootMat_ne_one : wMat n * rootMat n 0 1 ≠ 1 := by
  rw [wMat_mul_rootMat]
  intro h
  have := congrFun (congrFun h 0) 0
  simp at this

@[expose] noncomputable def u : ↥(Sz n) := ⟨rootGL n 0 1, rootGL_mem n 0 1⟩

@[expose] noncomputable def w : ↥(Sz n) := ⟨wGL n, wGL_mem n⟩

theorem w_mul_self : w n * w n = 1 :=
  Subtype.ext (Units.ext (wMat_mul_self n))

theorem u_mul_self : u n * u n = 1 :=
  Subtype.ext (Units.ext (rootMat_zero_one_mul_self n))

theorem orderOf_w_mul_u : orderOf (w n * u n) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime (Subtype.ext (Units.ext ?_)) fun h => wMat_mul_rootMat_ne_one n ?_
  · simpa [w, u] using wMat_mul_rootMat_pow_five n
  · have := congrArg (fun g : ↥(Sz n) => ((g : GL (Fin 4) (F n)) : Matrix (Fin 4) (Fin 4) (F n))) h
    simpa [w, u] using this

theorem rootMat_mulVec (a b : F n) (x : Fin 4 → F n) : rootMat n a b *ᵥ x =
    ![x 0 + a * x 1 + b * x 2 + (a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1))) * x 3,
      x 1 + a ^ (2 ^ (n + 1)) * x 2 + (a ^ (1 + 2 ^ (n + 1)) + b) * x 3, x 2 + a * x 3, x 3] := by
  ext i
  fin_cases i <;> simp [rootMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem wMat_mulVec (x : Fin 4 → F n) : wMat n *ᵥ x = ![x 3, x 2, x 1, x 0] := by
  ext i
  fin_cases i <;> simp [wMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem vec_eq (x : Fin 4 → F n) : x = ![x 0, x 1, x 2, x 3] := by
  ext i
  fin_cases i <;> rfl

theorem eq_bot_or_eq_top_of_sz {U : AddSubgroup (Fin 4 → F n)}
    (hU : ∀ g ∈ Sz n, ∀ x ∈ U, ((g : GL (Fin 4) (F n)) : Matrix (Fin 4) (Fin 4) (F n)) *ᵥ x ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  have hS : ∀ (a b : F n), ∀ x ∈ U, rootMat n a b *ᵥ x - x ∈ U := fun a b x hx =>
    U.sub_mem (by simpa using hU _ (rootGL_mem n a b) x hx) hx
  have hw : ∀ x ∈ U, wMat n *ᵥ x ∈ U := fun x hx => by simpa using hU _ (wGL_mem n) x hx
  by_cases hU0 : U = ⊥
  · exact Or.inl hU0
  right
  have h01 : ∀ x ∈ U, rootMat n 0 1 *ᵥ x - x = ![x 2 + x 3, x 3, 0, 0] := fun x _ => by
    rw [rootMat_mulVec]
    ext i
    fin_cases i <;> simp
    ring
  have h10 : ∀ x ∈ U, x 3 = 0 → rootMat n 1 0 *ᵥ x - x = ![x 1, x 2, 0, 0] := fun x _ hx3 => by
    rw [rootMat_mulVec]
    ext i
    fin_cases i <;> simp [hx3]
  obtain ⟨y₀, y₁, hy, hy₁⟩ : ∃ y₀ y₁ : F n, ![y₀, y₁, 0, 0] ∈ U ∧ y₁ ≠ 0 := by
    obtain ⟨⟨x, hxU⟩, hx0'⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hU0
    have hx0 : x ≠ 0 := fun h => hx0' (Subtype.ext h)
    by_cases h3 : x 3 = 0
    · by_cases h2 : x 2 = 0
      · by_cases h1 : x 1 = 0
        · have h0 : x 0 ≠ 0 := fun h0 => hx0 (by
            rw [vec_eq n x, h0, h1, h2, h3]
            ext i
            fin_cases i <;> rfl)
          have hwx := hw x hxU
          rw [wMat_mulVec, h1, h2, h3] at hwx
          refine ⟨0 + x 0, x 0, ?_, h0⟩
          have := hS 0 1 _ hwx
          rwa [h01 _ hwx] at this
        · refine ⟨x 0, x 1, ?_, h1⟩
          rw [vec_eq n x, h2, h3] at hxU
          exact hxU
      · refine ⟨x 1, x 2, ?_, h2⟩
        have := hS 1 0 x hxU
        rwa [h10 x hxU h3] at this
    · refine ⟨x 2 + x 3, x 3, ?_, h3⟩
      have := hS 0 1 x hxU
      rwa [h01 x hxU] at this
  have he₁ : ∀ c : F n, ![c, 0, 0, 0] ∈ U := by
    intro c
    have := hS (c / y₁) 0 _ hy
    rw [rootMat_mulVec] at this
    convert this using 1
    ext i
    fin_cases i <;> simp [hy₁]
  have he₄ : ∀ c : F n, ![0, 0, 0, c] ∈ U := fun c => by
    have := hw _ (he₁ c)
    rwa [wMat_mulVec] at this
  have hall : ∀ c : F n, ![c, c, c, c] ∈ U := fun c => by
    have := U.add_mem (hS 1 0 _ (he₄ c)) (he₄ c)
    rw [sub_add_cancel, rootMat_mulVec] at this
    convert this using 1
    ext i
    fin_cases i <;> simp
  have hpart : ∀ c : F n, ![c, c, 0, c] ∈ U := fun c => by
    have := U.add_mem (hS 0 1 _ (he₄ c)) (he₄ c)
    rw [sub_add_cancel, rootMat_mulVec] at this
    convert this using 1
    ext i
    fin_cases i <;> simp
  rw [eq_top_iff]
  intro x _
  have hx : x = ![x 2, x 2, x 2, x 2] + ![x 1 - x 2, x 1 - x 2, 0, x 1 - x 2] +
      ![x 0 - x 1, 0, 0, 0] + ![0, 0, 0, x 3 - x 1] := by
    ext i
    fin_cases i <;> simp
  rw [hx]
  exact U.add_mem (U.add_mem (U.add_mem (hall _) (hpart _)) (he₁ _)) (he₄ _)

end CFSG.RankThree.GF2n.SzExplicit
