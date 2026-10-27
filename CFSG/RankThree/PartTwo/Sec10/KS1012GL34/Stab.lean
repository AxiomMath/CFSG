module

public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012GL34

open CFSG.Fischer

theorem stabilizes_one (i : Fin 6) : stabilizes i 1 := by
  intro v hv
  exact ⟨v, hv, 1, one_ne_zero, by rw [Matrix.one_mulVec, one_smul]⟩

theorem stabilizes_mul {i : Fin 6} {M N : Matrix (Fin 3) (Fin 3) F4}
    (hM : stabilizes i M) (hN : stabilizes i N) : stabilizes i (M * N) := by
  intro v hv
  obtain ⟨w, hw, c, hc, hNv⟩ := hN v hv
  obtain ⟨u, hu, c', hc', hMw⟩ := hM w hw
  refine ⟨u, hu, c * c', mul_ne_zero hc hc', ?_⟩
  rw [← Matrix.mulVec_mulVec, hNv, Matrix.mulVec_smul, hMw, smul_smul]

theorem stabilizes_pow {i : Fin 6} {M : Matrix (Fin 3) (Fin 3) F4} (hM : stabilizes i M) :
    ∀ n : ℕ, stabilizes i (M ^ n)
  | 0 => by
    rw [pow_zero]
    exact stabilizes_one i
  | n + 1 => by
    rw [pow_succ]
    exact stabilizes_mul (stabilizes_pow hM n) hM

@[expose] def SLsub : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) F4).det = 1}
  mul_mem' {a b} ha hb := by
    have ha' : (a : Matrix (Fin 3) (Fin 3) F4).det = 1 := ha
    have hb' : (b : Matrix (Fin 3) (Fin 3) F4).det = 1 := hb
    show ((a * b : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).det = 1
    rw [Units.val_mul, Matrix.det_mul, ha', hb', one_mul]
  one_mem' := by
    show ((1 : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).det = 1
    rw [Units.val_one, Matrix.det_one]
  inv_mem' {a} ha := by
    have ha' : (a : Matrix (Fin 3) (Fin 3) F4).det = 1 := ha
    have h : ((a⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).det *
        (a : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    show ((a⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).det = 1
    rwa [ha', mul_one] at h

theorem mem_SLsub {g : Matrix.GeneralLinearGroup (Fin 3) F4} :
    g ∈ SLsub ↔ (g : Matrix (Fin 3) (Fin 3) F4).det = 1 :=
  Iff.rfl

theorem SLsub_eq_closure :
    SLsub = Subgroup.closure {A : Matrix.GeneralLinearGroup (Fin 3) F4 |
      (A : Matrix (Fin 3) (Fin 3) F4).det = 1} := by
  apply le_antisymm
  · intro g hg
    exact Subgroup.subset_closure hg
  · rw [Subgroup.closure_le]
    intro g hg
    exact hg

instance (g : Matrix.GeneralLinearGroup (Fin 3) F4) : Decidable (g ∈ SLsub) := by
  rw [mem_SLsub]
  infer_instance

theorem coe_inv_eq_pow (g : Matrix.GeneralLinearGroup (Fin 3) F4) :
    ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      (g : Matrix (Fin 3) (Fin 3) F4) ^ (orderOf g - 1) := by
  have hpos : 0 < orderOf g := orderOf_pos g
  have h : g * g ^ (orderOf g - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  have hinv : g ^ (orderOf g - 1) = g⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [← hinv, Units.val_pow_eq_pow_val]

@[expose] def P (i : Fin 6) : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) F4).det = 1 ∧
    stabilizes i (g : Matrix (Fin 3) (Fin 3) F4)}
  mul_mem' {a b} ha hb := by
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨?_, ?_⟩
    · show ((a * b : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).det = 1
      rw [Units.val_mul, Matrix.det_mul, ha1, hb1, one_mul]
    · show stabilizes i (((a * b : Matrix.GeneralLinearGroup (Fin 3) F4)) :
        Matrix (Fin 3) (Fin 3) F4)
      rw [Units.val_mul]
      exact stabilizes_mul ha2 hb2
  one_mem' := by
    refine ⟨?_, ?_⟩
    · show ((1 : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).det = 1
      rw [Units.val_one, Matrix.det_one]
    · show stabilizes i ((1 : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)
      rw [Units.val_one]
      exact stabilizes_one i
  inv_mem' {a} ha := by
    obtain ⟨ha1, ha2⟩ := ha
    refine ⟨?_, ?_⟩
    · show ((a⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).det = 1
      rw [coe_inv_eq_pow, Matrix.det_pow, ha1, one_pow]
    · show stabilizes i ((a⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)
      rw [coe_inv_eq_pow]
      exact stabilizes_pow ha2 _

theorem mem_P {i : Fin 6} {g : Matrix.GeneralLinearGroup (Fin 3) F4} :
    g ∈ P i ↔ (g : Matrix (Fin 3) (Fin 3) F4).det = 1 ∧
      stabilizes i (g : Matrix (Fin 3) (Fin 3) F4) :=
  Iff.rfl

instance (i : Fin 6) (g : Matrix.GeneralLinearGroup (Fin 3) F4) : Decidable (g ∈ P i) := by
  rw [mem_P]
  infer_instance

end CFSG.RankThree.PartTwo.Sec10.KS1012GL34

end
