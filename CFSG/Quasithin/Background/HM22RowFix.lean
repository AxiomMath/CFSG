module

public import CFSG.Quasithin.H13.L32NMatN
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.H.Mathieu.M22Row

open CFSG.Quasithin.H13.MatNCert Matrix

@[expose] def fixOK (A : List ℕ) (m : ℕ) : Bool :=
  (List.range 4096).all fun c => c &&& m != 0 || c == 0 || mvN A c != c

@[expose] def maskCard (m : ℕ) : ℕ := ((Finset.range 4096).filter fun d => d &&& m = d).card

theorem codeN_add (v w : Fin 12 → ZMod 2) : codeN (v + w) = codeN v ^^^ codeN w := by
  have h := vecN_xor (n := 12) (codeN v) (codeN w)
  rw [vecN_codeN, vecN_codeN] at h
  rw [← h, codeN_vecN (Nat.xor_lt_two_pow (codeN_lt v) (codeN_lt w))]

theorem eq_of_add_eq_zero {v w : Fin 12 → ZMod 2} (h : v + w = 0) : v = w := by
  funext i
  have h1 := congrFun h i
  simp only [Pi.add_apply, Pi.zero_apply] at h1
  revert h1
  generalize v i = a
  generalize w i = b
  revert a b
  decide

theorem card_fix_le {A : List ℕ} (hA : ValidN 12 A) {m : ℕ} (h : fixOK A m = true) :
    Nat.card {v : Fin 12 → ZMod 2 // decN 12 A *ᵥ v = v} ≤ maskCard m := by
  classical
  have key : ∀ v w : Fin 12 → ZMod 2, decN 12 A *ᵥ v = v → decN 12 A *ᵥ w = w →
      codeN v &&& m = codeN w &&& m → v = w := by
    intro v w hv hw hvw
    have hc : codeN (v + w) < 2 ^ 12 := codeN_lt _
    have hcm : codeN (v + w) &&& m = 0 := by
      rw [codeN_add, Nat.and_xor_distrib_right, hvw, Nat.xor_self]
    have hfix : mvN A (codeN (v + w)) = codeN (v + w) := by
      have h1 : decN 12 A *ᵥ (v + w) = v + w := by rw [Matrix.mulVec_add, hv, hw]
      rw [← vecN_codeN (v + w), decN_mulVec hA.1] at h1
      exact vecN_inj (mvN_lt hA.2 _) hc h1
    have h2 := List.all_eq_true.mp h _ (List.mem_range.mpr hc)
    simp only [hcm, hfix, bne_self_eq_false, Bool.or_false, Bool.false_or, beq_iff_eq] at h2
    apply eq_of_add_eq_zero
    rw [← vecN_codeN (v + w), h2, vecN_zero]
  have hS : Nat.card {v : Fin 12 → ZMod 2 // decN 12 A *ᵥ v = v} =
      (Finset.univ.filter fun v : Fin 12 → ZMod 2 => decN 12 A *ᵥ v = v).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hS, maskCard]
  refine Finset.card_le_card_of_injOn (fun v => codeN v &&& m) ?_ ?_
  · intro v _
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    exact ⟨lt_of_le_of_lt Nat.and_le_left (codeN_lt v), by rw [Nat.and_assoc, Nat.and_self]⟩
  · intro v hv w hw hvw
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv hw
    exact key v w hv hw hvw

theorem card_fix_conj (c g : GL (Fin 12) (ZMod 2)) :
    Nat.card {u : Fin 12 → ZMod 2 //
      ((c⁻¹ * g * c : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ u = u} =
      Nat.card {u : Fin 12 → ZMod 2 //
        ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ u = u} := by
  have hcc : ∀ u : Fin 12 → ZMod 2,
      ((c : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ
        (((c⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ u) = u := by
    intro u
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hcc' : ∀ u : Fin 12 → ZMod 2,
      ((c⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ
        (((c : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ u) = u := by
    intro u
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hconj : ∀ u : Fin 12 → ZMod 2,
      ((c⁻¹ * g * c : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ u =
        ((c⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ
          (((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ
            (((c : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ u)) := by
    intro u
    rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
  refine Nat.card_congr
    { toFun := fun u => ⟨((c : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ u.1,
        ?_⟩
      invFun := fun u =>
        ⟨((c⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ u.1, ?_⟩
      left_inv := fun u => Subtype.ext (hcc' u.1)
      right_inv := fun u => Subtype.ext (hcc u.1) }
  · have h1 := u.2
    rw [hconj] at h1
    have h2 := congrArg
      (fun t => ((c : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ t) h1
    simp only [hcc] at h2
    exact h2
  · rw [hconj, hcc, u.2]

end CFSG.Quasithin.H.Mathieu.M22Row
