module

public import CFSG.YGroups.Y433.Relabel

public section

namespace CFSG.YGroups

open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

abbrev U433 : Type := YGroup 4 3 3

namespace U433

@[expose] def armStart : ℕ → ℕ
  | 1 => 1
  | 2 => 5
  | 3 => 8
  | _ => 0

@[expose] noncomputable def A : U433 := yGen 4 3 3 0

@[expose] noncomputable def B (i : ℕ) : U433 := yGen 4 3 3 (armStart i)

@[expose] noncomputable def C (i : ℕ) : U433 := yGen 4 3 3 (armStart i + 1)

@[expose] noncomputable def D (i : ℕ) : U433 := yGen 4 3 3 (armStart i + 2)

@[expose] noncomputable def E₁ : U433 := yGen 4 3 3 (armStart 1 + 3)

theorem yEdges_433 : yEdges 4 3 3 =
    [(0, armStart 1), (0, armStart 2), (0, armStart 3),
      (armStart 1, armStart 1 + 1), (armStart 1 + 1, armStart 1 + 2),
      (armStart 1 + 2, armStart 1 + 3),
      (armStart 2, armStart 2 + 1), (armStart 2 + 1, armStart 2 + 2),
      (armStart 3, armStart 3 + 1), (armStart 3 + 1, armStart 3 + 2)] := by
  decide

theorem spiderWord_433 : spiderWord 4 3 =
    [0, armStart 1, armStart 1 + 1, 0, armStart 2, armStart 2 + 1, 0, armStart 3,
      armStart 3 + 1] := by
  decide

theorem A_mul_self : A * A = 1 := yGen_mul_self 4 3 3 0

theorem B_mul_self (i : ℕ) : B i * B i = 1 := yGen_mul_self 4 3 3 _

theorem C_mul_self (i : ℕ) : C i * C i = 1 := yGen_mul_self 4 3 3 _

theorem D_mul_self (i : ℕ) : D i * D i = 1 := yGen_mul_self 4 3 3 _

theorem E₁_mul_self : E₁ * E₁ = 1 := yGen_mul_self 4 3 3 _

@[expose] noncomputable def T (i : ℕ) : U433 := A * B i * C i

theorem spider : (T 1 * T 2 * T 3) ^ 10 = 1 := by
  have h := evalWord_yGen_of_mem (p := 4) (q := 3) (r := 3)
    (w := (List.replicate 10 (spiderWord 4 3)).flatten) (by
      simp only [yRels, List.mem_append]
      refine Or.inr ?_
      simp)
  rw [Y443.evalWord_replicate_flatten] at h
  rw [← h, Relabel.evalWord_spiderWord]
  rfl

end U433

@[expose] noncomputable def F433 (i j k : ℕ) : U433 :=
  (U433.A * U433.B i * U433.C i * U433.D i * U433.B j * U433.C j * U433.B k) ^ 9

theorem F433_eq_evalWord (i j k : ℕ) :
    F433 i j k = evalWord (yGen 4 3 3) [0, U433.armStart i, U433.armStart i + 1,
      U433.armStart i + 2, U433.armStart j, U433.armStart j + 1, U433.armStart k] ^ 9 := by
  simp only [F433, U433.A, U433.B, U433.C, U433.D, evalWord_cons, evalWord_nil, mul_one,
    mul_assoc]

abbrev R433 : Type := U433 ⧸ Subgroup.normalClosure {F433 2 1 3}

namespace R433

@[expose] noncomputable def π : U433 →* R433 :=
  QuotientGroup.mk' (Subgroup.normalClosure {F433 2 1 3})

@[expose] noncomputable def A : R433 := π U433.A

@[expose] noncomputable def B (i : ℕ) : R433 := π (U433.B i)

@[expose] noncomputable def C (i : ℕ) : R433 := π (U433.C i)

@[expose] noncomputable def D (i : ℕ) : R433 := π (U433.D i)

@[expose] noncomputable def E₁ : R433 := π U433.E₁

theorem π_surjective : Function.Surjective π := QuotientGroup.mk'_surjective _

theorem π_F433_213 : π (F433 2 1 3) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure rfl)

theorem ker_π : π.ker = Subgroup.normalClosure {F433 2 1 3} := QuotientGroup.ker_mk' _

end R433

end CFSG.YGroups
