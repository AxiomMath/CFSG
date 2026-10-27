module

public import Certificates.Data.CFSGNative.MonsterAxis.Dense

public section

namespace CFSG.KC.KDense

open CFSG.Monster.AxisCount

@[expose] def letterOK : Native.Gen → Bool
  | .rho q => Nat.blt q.2.1 4096
  | .perm arr => Nat.beq arr.size 24
  | _ => true

@[expose] def pairsLetterOK (p : List (List Native.Gen × List Native.Gen)) : Bool :=
  p.all fun x => x.1.all letterOK && x.2.all letterOK

theorem letterOK_rho (s : Bool) {a : Nat} (d : Nat) (h : a < 4096) :
    letterOK (.rho (s, a, d)) = true := by
  change Nat.blt a 4096 = true
  rw [Nat.blt_eq]
  exact h

theorem letterOK_perm {arr : Array Nat} (h : arr.size = 24) : letterOK (.perm arr) = true := by
  change Nat.beq arr.size 24 = true
  rw [h]
  rfl

theorem pairsLetterOK_getD {p : List (List Native.Gen × List Native.Gen)}
    (h : pairsLetterOK p = true) (k : Nat) :
    (∀ g ∈ (p.getD k ([], [])).1, letterOK g = true) ∧
      ∀ g ∈ (p.getD k ([], [])).2, letterOK g = true := by
  rw [List.getD_eq_getElem?_getD]
  rcases hk : p[k]? with _ | x
  · simp
  · have hx := h
    unfold pairsLetterOK at hx
    rw [List.all_eq_true] at hx
    have e := hx x (List.mem_of_getElem? hk)
    simp only [Bool.and_eq_true, List.all_eq_true] at e
    exact e

end CFSG.KC.KDense

end
