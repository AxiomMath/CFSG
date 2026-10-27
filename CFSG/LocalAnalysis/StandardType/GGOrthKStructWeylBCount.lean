module

public import CFSG.LocalAnalysis.StandardType.GGOrthKStructDefs
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.GGHalf CFSG.StandardType.SpJoin
  CFSG.LieType.Universal.SpecialLinear Matrix

private theorem okCnt_inv_eq_self {x : Multiplicative (ZMod 3)} (h : x⁻¹ = x) : x = 1 := by
  revert x
  decide

private theorem okCnt_card_zmod3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

private theorem okCnt_card_pi (k : ℕ) :
    Nat.card (Fin k → Multiplicative (ZMod 3)) = 3 ^ k := by
  rw [Nat.card_fun, Nat.card_fin, okCnt_card_zmod3]

private theorem okCnt_coordInv_update_one {k : ℕ} (i : Fin k)
    (b : Fin k → Multiplicative (ZMod 3)) :
    coordInv k 3 i (Function.update b i 1) = Function.update b i 1 := by
  rw [coordInv_apply]
  funext t
  by_cases ht : t = i
  · rw [ht, Function.update_self, Function.update_self]
    exact inv_one
  · rw [Function.update_of_ne ht, Function.update_of_ne ht]

private noncomputable def okCnt_invEquiv {k : ℕ} (i : Fin k) :
    ({a : Fin k → Multiplicative (ZMod 3) // coordInv k 3 i a = a} ×
        Multiplicative (ZMod 3)) ≃ (Fin k → Multiplicative (ZMod 3)) where
  toFun p := Function.update p.1.1 i p.2
  invFun b := (⟨Function.update b i 1, okCnt_coordInv_update_one i b⟩, b i)
  left_inv := by
    rintro ⟨⟨a, ha⟩, s⟩
    have hai : a i = 1 := okCnt_inv_eq_self (by
      have h := congrFun ha i
      rwa [coordInv_apply, Function.update_apply, if_pos rfl] at h)
    have hfirst : Function.update (Function.update a i s) i 1 = a := by
      rw [Function.update_idem, ← hai, Function.update_eq_self]
    have hsecond : (Function.update a i s) i = s := Function.update_self i s a
    apply Prod.ext
    · apply Subtype.ext
      exact hfirst
    · exact hsecond
  right_inv := by
    intro b
    simp only [Function.update_idem, Function.update_eq_self]

private theorem okCnt_coordPerm_swap_update {k : ℕ} (i j : Fin k) (hij : i ≠ j)
    (b : Fin k → Multiplicative (ZMod 3)) :
    coordPerm k 3 (Equiv.swap i j) (Function.update b j (b i)) =
      Function.update b j (b i) := by
  funext t
  rw [coordPerm_apply, Equiv.symm_swap]
  by_cases hti : t = i
  · rw [hti, Equiv.swap_apply_left, Function.update_self, Function.update_of_ne hij]
  · by_cases htj : t = j
    · rw [htj, Equiv.swap_apply_right, Function.update_self, Function.update_of_ne hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hti htj]

private noncomputable def okCnt_swapEquiv {k : ℕ} (i j : Fin k) (hij : i ≠ j) :
    ({a : Fin k → Multiplicative (ZMod 3) // coordPerm k 3 (Equiv.swap i j) a = a} ×
        Multiplicative (ZMod 3)) ≃ (Fin k → Multiplicative (ZMod 3)) where
  toFun p := Function.update p.1.1 j p.2
  invFun b := (⟨Function.update b j (b i), okCnt_coordPerm_swap_update i j hij b⟩, b j)
  left_inv := by
    rintro ⟨⟨a, ha⟩, s⟩
    have hai : a i = a j := by
      have h := congrFun ha i
      rw [coordPerm_apply, Equiv.symm_swap, Equiv.swap_apply_left] at h
      exact h.symm
    have hfirst : Function.update (Function.update a j s) j ((Function.update a j s) i) = a := by
      rw [Function.update_of_ne hij, Function.update_idem, hai, Function.update_eq_self]
    have hsecond : (Function.update a j s) j = s := Function.update_self j s a
    apply Prod.ext
    · apply Subtype.ext
      exact hfirst
    · exact hsecond
  right_inv := by
    intro b
    simp only [Function.update_idem, Function.update_eq_self]

theorem ggOrthKStruct_refl_count {k : ℕ} (i : Fin k) :
    spReflPerm k 3 i * spReflPerm k 3 i = 1 ∧
      Nat.card {a : Fin k → Multiplicative (ZMod 3) // spReflPerm k 3 i a = a} * 3 = 3 ^ k := by
  constructor
  · apply Equiv.ext
    intro v
    rw [Equiv.Perm.mul_apply]
    exact spRefl_involutive k 3 i v
  · by_cases hlt : i.val + 1 < k
    · have hsp : spReflPerm k 3 i = coordPerm k 3 (Equiv.swap i ⟨i.val + 1, hlt⟩) :=
        spReflPerm_of_lt k 3 i hlt
      have hij : i ≠ (⟨i.val + 1, hlt⟩ : Fin k) := by
        intro h
        have h2 : i.val = i.val + 1 := by simpa using congrArg Fin.val h
        omega
      rw [hsp]
      have h1 : Nat.card ({a : Fin k → Multiplicative (ZMod 3) //
            coordPerm k 3 (Equiv.swap i ⟨i.val + 1, hlt⟩) a = a} ×
            Multiplicative (ZMod 3)) = Nat.card (Fin k → Multiplicative (ZMod 3)) :=
        Nat.card_congr (okCnt_swapEquiv i ⟨i.val + 1, hlt⟩ hij)
      rw [Nat.card_prod, okCnt_card_zmod3, okCnt_card_pi k] at h1
      exact h1
    · have hsp : spReflPerm k 3 i = coordInv k 3 i := spReflPerm_of_not_lt k 3 i hlt
      rw [hsp]
      have h1 : Nat.card ({a : Fin k → Multiplicative (ZMod 3) // coordInv k 3 i a = a} ×
            Multiplicative (ZMod 3)) = Nat.card (Fin k → Multiplicative (ZMod 3)) :=
        Nat.card_congr (okCnt_invEquiv i)
      rw [Nat.card_prod, okCnt_card_zmod3, okCnt_card_pi k] at h1
      exact h1

end CFSG.StandardType

end
