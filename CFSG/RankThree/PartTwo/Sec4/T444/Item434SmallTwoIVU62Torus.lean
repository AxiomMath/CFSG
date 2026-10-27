module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU62Model
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverRanks

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

@[expose] def torusGL6 : (Fin 4 → F4ˣ) →* GL (Fin 6) F4 :=
  Census.diagHom.comp Census.torus6

theorem coe_torusGL6 (x : Fin 4 → F4ˣ) :
    (torusGL6 x : Matrix (Fin 6) (Fin 6) F4) = diagonal fun i => (Census.torus6 x i : F4) :=
  rfl

theorem torus6_pow_three (x : Fin 4 → F4ˣ) (i : Fin 6) : ((Census.torus6 x i : F4ˣ) : F4) ^ 3 = 1 :=
  pow_three_F4 (Census.torus6 x i).ne_zero

theorem torusGL6_mem (x : Fin 4 → F4ˣ) : torusGL6 x ∈ gramSU uData M6 := by
  refine ⟨?_, ?_⟩
  · rw [coe_torusGL6, Matrix.diagonal_map (map_zero _), diagonal_transpose, M6_eq_one,
      Matrix.mul_one, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [UnitaryFieldData.bar_apply]
    calc ((Census.torus6 x i : F4ˣ) : F4) ^ 2 ^ 1 * (Census.torus6 x i : F4ˣ) =
          ((Census.torus6 x i : F4ˣ) : F4) ^ 3 := by ring
      _ = 1 := torus6_pow_three x i
  · rw [coe_torusGL6, det_diagonal, Fin.prod_univ_six]
    simp only [Census.torus6, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
    simp

@[expose] def torusSU6 : (Fin 4 → F4ˣ) →* gramSU uData M6 :=
  torusGL6.codRestrict _ torusGL6_mem

theorem coe_torusSU6 (x : Fin 4 → F4ˣ) :
    ((torusSU6 x : gramSU uData M6) : GL (Fin 6) F4) = torusGL6 x :=
  rfl

@[expose] def torusP6 : (Fin 4 → F4ˣ) →* P6 :=
  (QuotientGroup.mk' (normOneScalars uData (gramSU uData M6) 6)).comp torusSU6

theorem torusP6_injective : Function.Injective torusP6 := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : torusSU6 x ∈ normOneScalars uData (gramSU uData M6) 6 :=
    (QuotientGroup.eq_one_iff _).1 hx
  obtain ⟨c, -, -, hc⟩ := h1
  have hc' : torusGL6 x = GeneralLinearGroup.scalar (Fin 6) c := hc
  have hent : ∀ j : Fin 6, ((Census.torus6 x j : F4ˣ) : F4) = c := fun j => by
    have := congrFun (congrFun (congrArg (fun g : GL (Fin 6) F4 => (g : Matrix (Fin 6) (Fin 6) F4))
      hc') j) j
    rw [coe_torusGL6, diagonal_apply_eq, GeneralLinearGroup.coe_scalar, scalar_apply,
      diagonal_apply_eq] at this
    exact this
  have hc1 : (c : F4) = 1 := by
    have := hent 5
    simp [Census.torus6] at this
    exact this.symm
  funext i
  apply Units.ext
  have := hent (Fin.castLE (by norm_num) i)
  fin_cases i <;> simpa [Census.torus6, hc1] using this

theorem card_range_torusP6 : Nat.card torusP6.range = 81 := by
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective torusP6_injective,
    Subgroup.card_top, Nat.card_fun, Nat.card_fin, card_units_F4]
  norm_num

theorem isElemAbelian_range_torusP6 : CFSG.Assembly.IsElemAbelian 3 torusP6.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨u, rfl⟩⟩ := a
    obtain ⟨_, ⟨v, rfl⟩⟩ := b
    apply Subtype.ext
    change torusP6 u * torusP6 v = torusP6 v * torusP6 u
    rw [← map_mul, ← map_mul]
    exact congrArg torusP6 (mul_comm u v)
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := funext fun i => Units.ext (by
      rw [Pi.pow_apply, Units.val_pow_eq_pow_val, pow_three_F4 (x i).ne_zero, Pi.one_apply,
        Units.val_one])
    rw [this, map_one]

theorem conj6_torusP6 {t : GU6} (ht : ((t : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).IsDiag)
    (x : Fin 4 → F4ˣ) : conj6 t (torusP6 x) = torusP6 x := by
  change conj6 t ((torusSU6 x : gramSU uData M6) : P6) = ((torusSU6 x : gramSU uData M6) : P6)
  rw [primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  change (t : GL (Fin 6) F4) * torusGL6 x * (t : GL (Fin 6) F4)⁻¹ = torusGL6 x
  have hcomm : (t : GL (Fin 6) F4) * torusGL6 x = torusGL6 x * (t : GL (Fin 6) F4) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_torusGL6, ← ht.diagonal_diag, diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  rw [hcomm, mul_inv_cancel_right]

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62
