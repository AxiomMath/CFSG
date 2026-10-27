module

public import CFSG.Quasithin.Background.RonanE114SevenL35Defs

public section

namespace CFSG.Quasithin.RonanE114.Seven.L35

open scoped MatrixGroups

theorem cent_zmod5_key : ∀ a b x : ZMod 5, a ≠ b → x * b = a * x → x = 0 := by
  decide

theorem cent_entry_eq_zero {G : Matrix (Fin 3) (Fin 3) (ZMod 5)} {d : Fin 3 → ZMod 5}
    (h : G * Matrix.diagonal d = Matrix.diagonal d * G) {i j : Fin 3} (hij : d i ≠ d j) :
    G i j = 0 := by
  have e := congrFun (congrFun h i) j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at e
  exact cent_zmod5_key _ _ _ hij e

theorem cent_offdiag_zero {G : Matrix (Fin 3) (Fin 3) (ZMod 5)}
    (h1 : G * Matrix.diagonal ![2, 2, 4] = Matrix.diagonal ![2, 2, 4] * G)
    (h2 : G * Matrix.diagonal ![4, 1, 4] = Matrix.diagonal ![4, 1, 4] * G) :
    G 0 1 = 0 ∧ G 0 2 = 0 ∧ G 1 0 = 0 ∧ G 1 2 = 0 ∧ G 2 0 = 0 ∧ G 2 1 = 0 :=
  ⟨cent_entry_eq_zero h2 (by decide), cent_entry_eq_zero h1 (by decide),
    cent_entry_eq_zero h2 (by decide), cent_entry_eq_zero h1 (by decide),
    cent_entry_eq_zero h1 (by decide), cent_entry_eq_zero h1 (by decide)⟩

theorem cent_mul_comm {A B : Matrix (Fin 3) (Fin 3) (ZMod 5)}
    (hA : A 0 1 = 0 ∧ A 0 2 = 0 ∧ A 1 0 = 0 ∧ A 1 2 = 0 ∧ A 2 0 = 0 ∧ A 2 1 = 0)
    (hB : B 0 1 = 0 ∧ B 0 2 = 0 ∧ B 1 0 = 0 ∧ B 1 2 = 0 ∧ B 2 0 = 0 ∧ B 2 1 = 0) :
    A * B = B * A := by
  obtain ⟨hA01, hA02, hA10, hA12, hA20, hA21⟩ := hA
  obtain ⟨hB01, hB02, hB10, hB12, hB20, hB21⟩ := hB
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hA01, hA02, hA10, hA12, hA20, hA21,
      hB01, hB02, hB10, hB12, hB20, hB21] <;> ring

theorem cent_coe_uv35 :
    ((u35 * v35 : SL(3, ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) =
      Matrix.diagonal ![2, 2, 4] := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem cent_coe_uu35 :
    ((u35 * u35 : SL(3, ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) =
      Matrix.diagonal ![4, 1, 4] := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem cent_coe_comm {g x : SL(3, ZMod 5)} {D : Matrix (Fin 3) (Fin 3) (ZMod 5)}
    (hx : (x : Matrix (Fin 3) (Fin 3) (ZMod 5)) = D) (h : g * x = x * g) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) * D = D * g := by
  rw [← hx, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, h]

theorem comm_of_commutes_gens35 {g h : SL(3, ZMod 5)}
    (hg₁ : g * (u35 * v35) = (u35 * v35) * g) (hg₂ : g * u35 ^ 2 = u35 ^ 2 * g)
    (hh₁ : h * (u35 * v35) = (u35 * v35) * h) (hh₂ : h * u35 ^ 2 = u35 ^ 2 * h) :
    g * h = h * g := by
  rw [sq] at hg₂ hh₂
  have hG1 := cent_coe_comm cent_coe_uv35 hg₁
  have hG2 := cent_coe_comm cent_coe_uu35 hg₂
  have hH1 := cent_coe_comm cent_coe_uv35 hh₁
  have hH2 := cent_coe_comm cent_coe_uu35 hh₂
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact congrFun (congrFun (cent_mul_comm (cent_offdiag_zero hG1 hG2)
    (cent_offdiag_zero hH1 hH2)) i) j

end CFSG.Quasithin.RonanE114.Seven.L35
