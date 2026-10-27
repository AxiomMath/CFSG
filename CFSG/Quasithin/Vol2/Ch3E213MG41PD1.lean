module

public import CFSG.Quasithin.Vol2.Ch3E213MG41D2

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2]

@[expose] def eOne (k : Type) [Field k] : Fin 4 → k := Pi.single 1 1

omit [CharP k 2] in
theorem bil_eOne (x : Fin 4 → k) : spBil x (eOne k) = x 2 := by
  rw [eOne, bil_single]
  rfl

omit [CharP k 2] in
theorem bil_eOne_left (x : Fin 4 → k) : spBil (eOne k) x = x 2 := by
  rw [bil_symm, bil_eOne]

@[expose] def proj (x : Fin 4 → k) : Fin 4 → k := ![x 0, 0, 0, x 3]

omit [CharP k 2] in
theorem bil_proj (x y : Fin 4 → k) : spBil (proj x) (proj y) = x 0 * y 3 + x 3 * y 0 := by
  simp [proj, bil_apply]

@[expose] def stabE (k : Type) [Field k] [CharP k 2] : Subgroup (antiSp k) where
  carrier := {g | natAct g (eOne k) = eOne k}
  one_mem' := natAct_one _
  mul_mem' {g h} hg hh := by
    change natAct (g * h) (eOne k) = eOne k
    rw [natAct_mul, show natAct h (eOne k) = eOne k from hh,
      show natAct g (eOne k) = eOne k from hg]
  inv_mem' {g} hg := by
    change natAct g⁻¹ (eOne k) = eOne k
    have h := act_inv_act g (eOne k)
    rwa [show natAct g (eOne k) = eOne k from hg] at h

theorem mem_stabE {g : antiSp k} : g ∈ stabE k ↔ natAct g (eOne k) = eOne k :=
  Iff.rfl

variable {g : antiSp k}

theorem act_two (hg : g ∈ stabE k) (x : Fin 4 → k) : natAct g x 2 = x 2 := by
  have h := bil_act g x (eOne k)
  rw [mem_stabE.mp hg, bil_eOne, bil_eOne] at h
  exact h

theorem glMat_one_col (hg : g ∈ stabE k) (i : Fin 4) :
    glMat (g : GL (Fin 4) k) i 1 = eOne k i := by
  rw [← act_single_apply, ← eOne, mem_stabE.mp hg]

theorem glMat_two_row (hg : g ∈ stabE k) (j : Fin 4) :
    glMat (g : GL (Fin 4) k) 2 j = (Pi.single j 1 : Fin 4 → k) 2 := by
  rw [← act_single_apply, act_two hg]

theorem det_block (hg : g ∈ stabE k) :
    glMat (g : GL (Fin 4) k) 0 0 * glMat (g : GL (Fin 4) k) 3 3 +
      glMat (g : GL (Fin 4) k) 3 0 * glMat (g : GL (Fin 4) k) 0 3 = 1 := by
  have h := bil_act g (Pi.single 0 1) (Pi.single 3 1)
  have h20 := glMat_two_row hg 0
  have h23 := glMat_two_row hg 3
  simp only [bil_apply, act_single_apply] at h
  simp only [Pi.single_apply] at h20 h23 h
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte] at h20 h23 h
  rw [h20, h23] at h
  linear_combination h

@[expose] noncomputable def secCols (g : antiSp k) : Fin 4 → Fin 4 → k :=
  ![proj (natAct g (Pi.single 0 1)), eOne k, Pi.single 2 1, proj (natAct g (Pi.single 3 1))]

theorem secCols_gram (hg : g ∈ stabE k) (s t : Fin 4) :
    spBil (secCols g s) (secCols g t) = minorJ k s t := by
  have hd := det_block hg
  rw [minorJ_apply]
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  fin_cases s <;> fin_cases t <;>
    simp [secCols, proj, eOne, bil_apply, act_single_apply] <;>
    first
    | linear_combination hd
    | linear_combination (glMat (g : GL (Fin 4) k) 0 0 * glMat (g : GL (Fin 4) k) 3 0) * h2
    | linear_combination (glMat (g : GL (Fin 4) k) 0 3 * glMat (g : GL (Fin 4) k) 3 3) * h2

@[expose] noncomputable def sec (g : stabE k) : antiSp k :=
  ofBasis (secCols (g : antiSp k)) (secCols_gram g.2)

theorem act_sec (g : stabE k) (x : Fin 4 → k) :
    natAct (sec g) x = ![x 0 * glMat ((g : antiSp k) : GL (Fin 4) k) 0 0 +
        x 3 * glMat ((g : antiSp k) : GL (Fin 4) k) 0 3, x 1, x 2,
      x 0 * glMat ((g : antiSp k) : GL (Fin 4) k) 3 0 +
        x 3 * glMat ((g : antiSp k) : GL (Fin 4) k) 3 3] := by
  rw [sec, act_ofBasis]
  ext i
  fin_cases i <;>
    simp [Fin.sum_univ_four, secCols, proj, eOne, act_single_apply]

theorem glMat_mul_block (g h : stabE k) (a b : Fin 4) (ha : a = 0 ∨ a = 3) (hb : b = 0 ∨ b = 3) :
    glMat (((g * h : stabE k) : antiSp k) : GL (Fin 4) k) a b =
      glMat ((g : antiSp k) : GL (Fin 4) k) a 0 * glMat ((h : antiSp k) : GL (Fin 4) k) 0 b +
        glMat ((g : antiSp k) : GL (Fin 4) k) a 3 * glMat ((h : antiSp k) : GL (Fin 4) k) 3 b := by
  have hg1 := glMat_one_col g.2 a
  have hh2 := glMat_two_row h.2 b
  simp only [Subgroup.coe_mul, Units.val_mul, glMat, Matrix.mul_apply, Fin.sum_univ_four]
    at hg1 hh2 ⊢
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp_all [eOne]

@[expose] noncomputable def secHom : stabE k →* antiSp k where
  toFun := sec
  map_one' := by
    apply ext_act
    intro x
    rw [act_sec, natAct_one]
    ext i
    fin_cases i <;> simp [glMat]
  map_mul' g h := by
    apply ext_act
    intro x
    rw [natAct_mul, act_sec, act_sec, act_sec, glMat_mul_block g h 0 0 (.inl rfl) (.inl rfl),
      glMat_mul_block g h 0 3 (.inl rfl) (.inr rfl), glMat_mul_block g h 3 0 (.inr rfl) (.inl rfl),
      glMat_mul_block g h 3 3 (.inr rfl) (.inr rfl)]
    ext i
    fin_cases i <;> simp <;> ring

theorem act_secHom (g : stabE k) (x : Fin 4 → k) : natAct (secHom g) x = natAct (sec g) x :=
  rfl

theorem trv_mem_stabE {z : Fin 4 → k} (hz : z 2 = 0) (c : k) : trv z c ∈ stabE k := by
  rw [mem_stabE, act_trv, bil_eOne_left, hz, mul_zero, zero_smul, add_zero]

theorem secHom_trv {z : Fin 4 → k} (hz : z 2 = 0) (c : k) :
    secHom ⟨trv z c, trv_mem_stabE hz c⟩ = trv (proj z) c := by
  apply ext_act
  intro x
  rw [act_secHom, act_sec, act_trv]
  simp only [← act_single_apply, act_trv]
  ext i
  fin_cases i <;> simp [proj, bil_apply, hz] <;> ring

end CFSG.Quasithin.Ch3E213M.G41.Big
