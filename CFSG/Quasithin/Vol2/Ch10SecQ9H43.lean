module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H42

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {m k : ℕ}

theorem utSL_zero : utSL (0 : Matrix (Fin m) (Fin k) (ZMod 2)) = 1 := by
  apply ext_mulVec
  intro v
  rw [← smul_eq_mulVec', utSL_smul, zero_mulVec, Matrix.SpecialLinearGroup.coe_one, one_mulVec]
  have h0 : (Fin.append (0 : Fin m → ZMod 2) 0 : Fin (m + k) → ZMod 2) = 0 := by
    funext i
    rcases fin_add_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩ <;> simp
  rw [h0, add_zero]

@[expose] def rowE (b : Fin 4) : Matrix (Fin 1) (Fin 4) (ZMod 2) :=
  fun _ j => if j = b then 1 else 0

theorem rowE_mul_one_add_trvE :
    rowE 1 * (1 + ((trvE (1 : Fin (3 + 1)) 0 (by decide) : Matrix.SpecialLinearGroup
      (Fin (3 + 1)) (ZMod 2)) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2))) = rowE 0 ∧
    rowE 0 * (1 + ((trvE (0 : Fin (3 + 1)) 1 (by decide) : Matrix.SpecialLinearGroup
      (Fin (3 + 1)) (ZMod 2)) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2))) = rowE 1 ∧
    rowE 0 * (1 + ((trvE (0 : Fin (3 + 1)) 2 (by decide) : Matrix.SpecialLinearGroup
      (Fin (3 + 1)) (ZMod 2)) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2))) = rowE 2 ∧
    rowE 0 * (1 + ((trvE (0 : Fin (3 + 1)) 3 (by decide) : Matrix.SpecialLinearGroup
      (Fin (3 + 1)) (ZMod 2)) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2))) = rowE 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem eq_sum_rowE (B : Matrix (Fin 1) (Fin 4) (ZMod 2)) :
    B = B 0 0 • rowE 0 + B 0 1 • rowE 1 + B 0 2 • rowE 2 + B 0 3 • rowE 3 := by
  ext i j
  fin_cases i
  fin_cases j <;> simp [rowE]

theorem eq_X14_of_flag {X : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))}
    (h1 : InvStd X 1) (h4 : InvStd X 4) (hcard : Nat.card X = Nat.card (o2G X) * 168)
    (hU : uniSL 5 ≤ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))) :
    X = X14 := by
  have hX1 : X ≤ stabStd 1 4 := le_stabStd_of_invStd (m := 1) (k := 4) h1
  have hX4 : X ≤ stabStd 4 1 := le_stabStd_of_invStd (m := 4) (k := 1) h4
  have hrow : ∀ (a b : Fin (3 + 1)) (hab : a ≠ b), trvE a b hab ∈ stabStd 3 1 →
      ∀ B : Matrix (Fin 1) (Fin 4) (ZMod 2), utSL (m := 1) (k := 4) (B * (1 + ((trvE a b hab :
        Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :
          Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)))) ∈ X := by
    intro a b hab hmem B
    obtain ⟨y, hy⟩ := mem_range_actQ1 h1 h4 hcard hU hmem
    have hyX : (y.1)⁻¹ ∈ X := X.inv_mem y.2
    have hc := comm_utSL_mem (m := 1) (k := 4) hyX (hU (utSL_mem_uniSL (m := 1) (k := 4) B))
    rw [comm_utSL_bot (hX1 hyX) (topB_eq_one_of_one ⟨_, hX1 hyX⟩) B, inv_inv] at hc
    have hb : botB ((y.1 : Matrix.SpecialLinearGroup (Fin (1 + 4)) (ZMod 2)) :
        Matrix (Fin (1 + 4)) (Fin (1 + 4)) (ZMod 2)) = ((trvE a b hab :
          Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :
            Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) := by
      rw [actQ1_apply] at hy
      exact congrArg Subtype.val hy
    rwa [hb] at hc
  obtain ⟨e0, e1, e2, e3⟩ := rowE_mul_one_add_trvE
  have r0 : utSL (m := 1) (k := 4) (rowE 0) ∈ X := by
    have := hrow 1 0 (by decide) (by rw [mem_stabStd]; unfold PresStd; decide) (rowE 1)
    rwa [e0] at this
  have r1 : utSL (m := 1) (k := 4) (rowE 1) ∈ X := by
    have := hrow 0 1 (by decide) (by rw [mem_stabStd]; unfold PresStd; decide) (rowE 0)
    rwa [e1] at this
  have r2 : utSL (m := 1) (k := 4) (rowE 2) ∈ X := by
    have := hrow 0 2 (by decide) (by rw [mem_stabStd]; unfold PresStd; decide) (rowE 0)
    rwa [e2] at this
  have r3 : utSL (m := 1) (k := 4) (rowE 3) ∈ X := by
    have := hrow 0 3 (by decide) (by rw [mem_stabStd]; unfold PresStd; decide) (rowE 0)
    rwa [e3] at this
  have hall : ∀ B : Matrix (Fin 1) (Fin 4) (ZMod 2), utSL (m := 1) (k := 4) B ∈ X := by
    intro B
    have hs : ∀ (c : ZMod 2) (b : Fin 4), utSL (m := 1) (k := 4) (rowE b) ∈ X →
        utSL (m := 1) (k := 4) (c • rowE b) ∈ X := by
      intro c b hb
      rcases zmod2_cases c with h | h
      · rw [h, zero_smul, utSL_zero]
        exact X.one_mem
      · rw [h, one_smul]
        exact hb
    rw [eq_sum_rowE B, ← utSL_mul, ← utSL_mul, ← utSL_mul]
    exact X.mul_mem (X.mul_mem (X.mul_mem (hs _ _ r0) (hs _ _ r1)) (hs _ _ r2)) (hs _ _ r3)
  refine le_antisymm (fun x hx => ⟨hX1 hx, hX4 hx⟩) fun g hg => ?_
  have hg31 : botH 1 4 ⟨g, hg.1⟩ ∈ stabStd 3 1 := botH_mem_stabStd31 hg.1 fun v hv =>
    smul_mem_stdE_of_presStd (m := 4) (k := 1) hg.2 hv
  obtain ⟨x, hx⟩ := mem_range_actQ1 h1 h4 hcard hU hg31
  rw [actQ1_apply] at hx
  obtain ⟨s, hs⟩ : ∃ s : ↥(stabStd 1 4), s = ⟨g, hg.1⟩ * (⟨x.1, hX1 x.2⟩)⁻¹ := ⟨_, rfl⟩
  have hb : botH 1 4 s = 1 := by rw [hs, map_mul, map_inv, hx, mul_inv_cancel]
  have hsX : s.1 ∈ X := by
    rw [eq_utSL_of_blocks s.2 (topB_eq_one_of_one s) (congrArg Subtype.val hb)]
    exact hall _
  have hg' : g = s.1 * x.1 := by
    rw [hs, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
  rw [hg']
  exact X.mul_mem hsX x.2

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
