module

public import CFSG.Quasithin.H13.GoldschmidtU43EDat1

public section

namespace CFSG.Quasithin.H13.U43

namespace V4

@[expose] def Valid (v : V4) : Prop := v.v0 < 3 ∧ v.v1 < 3 ∧ v.v2 < 3 ∧ v.v3 < 3

instance (v : V4) : Decidable (Valid v) := by unfold Valid; infer_instance

theorem valid_of_mem_allV : ∀ w ∈ allV, Valid w := by decide

theorem valid_mulV (a : M16) (v : V4) : Valid (mulV a v) := by
  unfold Valid mulV
  exact ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
    Nat.mod_lt _ (by decide)⟩

theorem toVec_inj {v w : V4} (hv : Valid v) (hw : Valid w) (h : toVec v = toVec w) : v = w := by
  have key : ∀ x : ℕ, x < 3 → ∀ y : ℕ, y < 3 → ((x : ℕ) : ZMod 3) = ((y : ℕ) : ZMod 3) →
      x = y := by decide
  obtain ⟨hv0, hv1, hv2, hv3⟩ := hv
  obtain ⟨hw0, hw1, hw2, hw3⟩ := hw
  have e0 := key _ hv0 _ hw0 (by simpa [toVec] using congrFun h 0)
  have e1 := key _ hv1 _ hw1 (by simpa [toVec] using congrFun h 1)
  have e2 := key _ hv2 _ hw2 (by simpa [toVec] using congrFun h 2)
  have e3 := key _ hv3 _ hw3 (by simpa [toVec] using congrFun h 3)
  cases v
  cases w
  simp only at e0 e1 e2 e3
  subst e0 e1 e2 e3
  rfl

theorem card_le_length {p : (Fin 4 → ZMod 3) → Prop} (l : List V4)
    (h : ∀ v, p v → v ∈ l.map toVec) : Nat.card {v // p v} ≤ l.length := by
  classical
  calc Nat.card {v // p v} ≤ Nat.card ↥(l.map toVec).toFinset := by
        refine Nat.card_le_card_of_injective
          (fun v => ⟨v.1, List.mem_toFinset.mpr (h v.1 v.2)⟩) ?_
        intro a b hab
        exact Subtype.ext (by simpa using hab)
    _ = (l.map toVec).toFinset.card := Nat.card_eq_fintype_card.trans (Fintype.card_coe _)
    _ ≤ (l.map toVec).length := List.toFinset_card_le _
    _ = l.length := List.length_map _

@[expose] def fixCnt (a : M16) : ℕ := (allV.filter fun w => decide (mulV a w = w)).length

@[expose] def fixCnt2 (a b : M16) : ℕ :=
  (allV.filter fun w => decide (mulV a w = w ∧ mulV b w = w)).length

theorem card_fix_le (a : M16) :
    Nat.card {v : Fin 4 → ZMod 3 // (M16.toMat a).mulVec v = v} ≤ fixCnt a := by
  refine card_le_length _ fun v hv => ?_
  obtain ⟨w, hw, rfl⟩ := exists_toVec v
  refine List.mem_map.mpr ⟨w, List.mem_filter.mpr ⟨hw, ?_⟩, rfl⟩
  have h1 : toVec (mulV a w) = toVec w := by rw [toVec_mulV]; exact hv
  have := toVec_inj (valid_mulV a w) (valid_of_mem_allV w hw) h1
  simpa using this

theorem card_fix2_le (a b : M16) :
    Nat.card {v : Fin 4 → ZMod 3 //
      (M16.toMat a).mulVec v = v ∧ (M16.toMat b).mulVec v = v} ≤ fixCnt2 a b := by
  refine card_le_length _ fun v hv => ?_
  obtain ⟨w, hw, rfl⟩ := exists_toVec v
  refine List.mem_map.mpr ⟨w, List.mem_filter.mpr ⟨hw, ?_⟩, rfl⟩
  have h1 : toVec (mulV a w) = toVec w := by rw [toVec_mulV]; exact hv.1
  have h2 : toVec (mulV b w) = toVec w := by rw [toVec_mulV]; exact hv.2
  have e1 := toVec_inj (valid_mulV a w) (valid_of_mem_allV w hw) h1
  have e2 := toVec_inj (valid_mulV b w) (valid_of_mem_allV w hw) h2
  simpa using And.intro e1 e2

end V4

end CFSG.Quasithin.H13.U43
