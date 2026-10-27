module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H35

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {m k : ℕ}

@[expose] def a7 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 1, 0, 1; 0, 1, 0], by decide⟩

@[expose] def m7 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 1; 1, 1, 0; 1, 1, 1]

theorem one_add_a7_mul_m7 : (1 + (a7 : Matrix (Fin 3) (Fin 3) (ZMod 2))) * m7 = 1 := by decide

theorem m7_mul_one_add_a7 : m7 * (1 + (a7 : Matrix (Fin 3) (Fin 3) (ZMod 2))) = 1 := by decide

theorem append_add_zero (a b : Fin m → ZMod 2) :
    (Fin.append (a + b) 0 : Fin (m + k) → ZMod 2) = Fin.append a 0 + Fin.append b 0 := by
  funext i
  rcases fin_add_cases i with ⟨c, rfl⟩ | ⟨d, rfl⟩ <;> simp

theorem utSL_mul (B B' : Matrix (Fin m) (Fin k) (ZMod 2)) : utSL B * utSL B' = utSL (B + B') := by
  apply ext_mulVec
  intro v
  rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, ← smul_eq_mulVec', ← smul_eq_mulVec',
    ← smul_eq_mulVec', utSL_smul, utSL_smul, utSL_smul]
  have hb : (fun j => (v + Fin.append (B' *ᵥ fun j => v (Fin.natAdd m j)) 0 :
      Fin (m + k) → ZMod 2) (Fin.natAdd m j)) = fun j => v (Fin.natAdd m j) := by
    funext j
    simp
  rw [hb, add_mulVec, append_add_zero]
  abel

theorem utSL_inv (B : Matrix (Fin m) (Fin k) (ZMod 2)) : (utSL B)⁻¹ = utSL B :=
  inv_eq_of_mul_eq_one_right (utSL_mul_self B)

theorem comm_utSL_top {l : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)}
    (hl : PresStd (l : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)))
    (hb : botB (l : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) = 1)
    (B : Matrix (Fin m) (Fin k) (ZMod 2)) :
    l * utSL B * l⁻¹ * utSL B =
      utSL ((1 + topB (l : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2))) * B) := by
  have hli : PresStd ((l⁻¹ : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)) :
      Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) := (stabStd m k).inv_mem hl
  have htt : topB (l : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) *
      topB ((l⁻¹ : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)) :
        Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) = 1 := topB_inv_mul ⟨l, hl⟩
  have hbi : botB ((l⁻¹ : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)) :
      Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) = 1 := by
    have h := botB_inv_mul ⟨l, hl⟩
    simp only at h
    rw [hb, Matrix.one_mul] at h
    exact h
  apply ext_mulVec
  intro v
  rw [← smul_eq_mulVec', ← smul_eq_mulVec', mul_smul, mul_smul, mul_smul]
  have h1 := utSL_smul B v
  have h3 : (fun j => (l⁻¹ • v + Fin.append (topB ((l⁻¹ : Matrix.SpecialLinearGroup (Fin (m + k))
      (ZMod 2)) : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) *ᵥ
        (B *ᵥ fun j => v (Fin.natAdd m j))) 0 : Fin (m + k) → ZMod 2) (Fin.natAdd m j)) =
      fun j => v (Fin.natAdd m j) := by
    funext j
    rw [Pi.add_apply, Fin.append_right, Pi.zero_apply, add_zero, bot_smul hli, hbi, one_mulVec]
  rw [h1, smul_add, smul_append_zero hli, utSL_smul, h3, smul_add, smul_add, smul_inv_smul,
    smul_append_zero hl, smul_append_zero hl, mulVec_mulVec, htt, one_mulVec, utSL_smul,
    ← mulVec_mulVec, add_mulVec, one_mulVec, append_add_zero, add_assoc, add_comm
      (Fin.append (B *ᵥ fun j => v (Fin.natAdd m j)) 0 : Fin (m + k) → ZMod 2)]

theorem comm_utSL_bot {l : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)}
    (hl : PresStd (l : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)))
    (ht : topB (l : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) = 1)
    (B : Matrix (Fin m) (Fin k) (ZMod 2)) :
    l * utSL B * l⁻¹ * utSL B = utSL (B * (1 + botB ((l⁻¹ : Matrix.SpecialLinearGroup
      (Fin (m + k)) (ZMod 2)) : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)))) := by
  have hli : PresStd ((l⁻¹ : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)) :
      Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) := (stabStd m k).inv_mem hl
  have hti : topB ((l⁻¹ : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)) :
      Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) = 1 := by
    have h := topB_inv_mul ⟨l, hl⟩
    simp only at h
    rw [ht, Matrix.one_mul] at h
    exact h
  apply ext_mulVec
  intro v
  rw [← smul_eq_mulVec', ← smul_eq_mulVec', mul_smul, mul_smul, mul_smul]
  have h1 := utSL_smul B v
  have h3 : (fun j => (l⁻¹ • v + Fin.append (B *ᵥ fun j => v (Fin.natAdd m j)) 0 :
      Fin (m + k) → ZMod 2) (Fin.natAdd m j)) = botB ((l⁻¹ : Matrix.SpecialLinearGroup
        (Fin (m + k)) (ZMod 2)) : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) *ᵥ
          fun j => v (Fin.natAdd m j) := by
    funext j
    rw [Pi.add_apply, Fin.append_right, Pi.zero_apply, add_zero, bot_smul hli]
  rw [h1, smul_add, smul_append_zero hli, hti, one_mulVec, utSL_smul, h3, smul_add, smul_add,
    smul_inv_smul, smul_append_zero hl, smul_append_zero hl, ht, one_mulVec, one_mulVec,
    utSL_smul, ← mulVec_mulVec, add_mulVec, one_mulVec, mulVec_add, append_add_zero, add_assoc]

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
