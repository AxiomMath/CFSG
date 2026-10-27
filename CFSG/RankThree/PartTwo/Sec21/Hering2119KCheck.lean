module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119KCore
import all CFSG.RankThree.PartTwo.Sec21.Hering2119SShareK

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open Matrix

theorem V4C.om_lt (x y : V4C) : x.om y < 3 := Nat.mod_lt _ (by norm_num)

theorem om_eq_iff (x y : V4C) {k : Nat} (hk : k < 3) :
    x.om y = k ↔ omega4 x.toV y.toV = (k : F3) := by
  rw [← V4C.om_spec]
  constructor
  · intro h; rw [h]
  · intro h; exact nat_eq_of_cast_eq (V4C.om_lt x y) hk h

@[expose] def ev (i : Fin 4) : V4 := fun j => if j = i then 1 else 0

theorem mulVec_ev (X : M4) (i : Fin 4) : X.mulVec (ev i) = fun r => X r i := by
  ext r
  simp [Matrix.mulVec, dotProduct, ev, Fin.sum_univ_four]

theorem omega4_ev : omega4 (ev 0) (ev 2) = 1 ∧ omega4 (ev 1) (ev 3) = 1 ∧
    omega4 (ev 0) (ev 1) = 0 ∧ omega4 (ev 0) (ev 3) = 0 ∧ omega4 (ev 1) (ev 2) = 0 ∧
    omega4 (ev 2) (ev 3) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [omega4, ev] <;> decide

theorem lineC_toV (L : Fin 4) : (lineC L.val).toV = lineVec L := by
  fin_cases L <;> (ext i; fin_cases i <;> simp [lineC, V4C.toV, lineVec])

theorem mv_eq_iff {A : M4C} {v : V4C} (hv : v.Valid) : A.mv v = v ↔ A.toM.mulVec v.toV = v.toV := by
  constructor
  · intro h
    have := M4C.toV_mv A v
    rw [h] at this
    exact this.symm
  · intro h
    exact V4C.toV_inj (M4C.valid_mv A v) hv (by rw [M4C.toV_mv]; exact h)

theorem toM_eq_one_iff {A : M4C} (hA : A.Valid) : A.toM = 1 ↔ A = M4C.one := by
  constructor
  · intro h
    exact M4C.toM_inj hA M4C.valid_one (by rw [h, M4C.toM_one])
  · rintro rfl; exact M4C.toM_one

theorem sameCyc_true {A B : M4} (h : sameCyc (toCM A) (toCM B) = true) : SameCyc A B := by
  simp only [sameCyc, Bool.or_eq_true, beq_iff_eq] at h
  unfold SameCyc
  rcases h with h | h
  · left
    have := congrArg M4C.toM h
    rwa [toM_toCM, toM_toCM] at this
  · right
    have := congrArg M4C.toM h
    rwa [toM_toCM, M4C.toM_mul, toM_toCM] at this

theorem sameCyc_false {A B : M4} (h : sameCyc (toCM A) (toCM B) = false) : ¬ SameCyc A B := by
  intro hS
  unfold SameCyc at hS
  simp only [sameCyc, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  rcases hS with hS | hS
  · exact h.1 (M4C.toM_inj (valid_toCM _) (valid_toCM _) (by rw [toM_toCM, toM_toCM]; exact hS))
  · exact h.2 (M4C.toM_inj (valid_toCM _) (M4C.valid_mul _ _)
      (by rw [M4C.toM_mul, toM_toCM, toM_toCM]; exact hS))

theorem conclC_sound {X : Fin 4 → M4}
    (h : conclC (toCM (X 0)) (toCM (X 1)) (toCM (X 2)) (toCM (X 3)) = true) : ConclK X := by
  simp only [conclC, Bool.and_eq_true] at h
  obtain ⟨hfix, hcyc⟩ := h
  have hf : ∀ (k : Fin 4) (v : V4), k ≠ 0 → (X k *ᵥ v = v ↔ X 0 *ᵥ v = v) := by
    intro k v hk
    have hv := (List.all_eq_true.mp hfix) (toCV v) (mem_allVecs_of_valid (valid_toCV v))
    simp only [Bool.and_eq_true, beq_iff_eq] at hv
    obtain ⟨⟨h1, h2⟩, h3⟩ := hv
    have conv : ∀ l : Fin 4, ((toCM (X l)).mv (toCV v) = toCV v ↔ X l *ᵥ v = v) := by
      intro l
      rw [mv_eq_iff (valid_toCV v), toM_toCM, toV_toCV]
    have d1 : ((toCM (X 1)).mv (toCV v) == toCV v) = ((toCM (X 0)).mv (toCV v) == toCV v) := h1
    have d2 : ((toCM (X 2)).mv (toCV v) == toCV v) = ((toCM (X 0)).mv (toCV v) == toCV v) := h2
    have d3 : ((toCM (X 3)).mv (toCV v) == toCV v) = ((toCM (X 0)).mv (toCV v) == toCV v) := h3
    have key : ∀ l : Fin 4, (((toCM (X l)).mv (toCV v) == toCV v) =
        ((toCM (X 0)).mv (toCV v) == toCV v)) → (X l *ᵥ v = v ↔ X 0 *ᵥ v = v) := by
      intro l hl
      rw [← conv l, ← conv 0]
      constructor
      · intro hh
        have : ((toCM (X l)).mv (toCV v) == toCV v) = true := beq_iff_eq.mpr hh
        rw [hl] at this
        exact beq_iff_eq.mp this
      · intro hh
        have : ((toCM (X 0)).mv (toCV v) == toCV v) = true := beq_iff_eq.mpr hh
        rw [← hl] at this
        exact beq_iff_eq.mp this
    fin_cases k
    · exact absurd rfl hk
    · exact key 1 d1
    · exact key 2 d2
    · exact key 3 d3
  refine ⟨?_, ?_⟩
  · intro i j v
    have hi : (X i *ᵥ v = v ↔ X 0 *ᵥ v = v) := by
      by_cases h0 : i = 0
      · subst h0; exact Iff.rfl
      · exact hf i v h0
    have hj : (X j *ᵥ v = v ↔ X 0 *ᵥ v = v) := by
      by_cases h0 : j = 0
      · subst h0; exact Iff.rfl
      · exact hf j v h0
    exact hi.trans hj.symm
  · simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hcyc
    rcases hcyc with (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩
    · refine ⟨1, ?_, ?_, ?_⟩
      · exact sameCyc_true h1
      · exact sameCyc_true h2
      · exact sameCyc_false h3
    · refine ⟨Equiv.swap 1 2, ?_, ?_, ?_⟩
      · have : (Equiv.swap (1 : Fin 4) 2) 0 = 0 := by decide
        have h' : (Equiv.swap (1 : Fin 4) 2) 1 = 2 := by decide
        rw [this, h']; exact sameCyc_true h1
      · have h' : (Equiv.swap (1 : Fin 4) 2) 2 = 1 := by decide
        have h'' : (Equiv.swap (1 : Fin 4) 2) 3 = 3 := by decide
        rw [h', h'']; exact sameCyc_true h2
      · have : (Equiv.swap (1 : Fin 4) 2) 0 = 0 := by decide
        have h' : (Equiv.swap (1 : Fin 4) 2) 2 = 1 := by decide
        rw [this, h']; exact sameCyc_false h3
    · let σ : Equiv.Perm (Fin 4) := Equiv.swap 1 3 * Equiv.swap 2 3
      have e0 : σ 0 = 0 := by decide
      have e1 : σ 1 = 3 := by decide
      have e2 : σ 2 = 1 := by decide
      have e3 : σ 3 = 2 := by decide
      refine ⟨σ, ?_, ?_, ?_⟩
      · rw [e0, e1]; exact sameCyc_true h1
      · rw [e2, e3]; exact sameCyc_true h2
      · rw [e0, e2]; exact sameCyc_false h3

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
