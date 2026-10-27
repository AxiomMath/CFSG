module

public import Certificates.Data.CFSGNative.Fi22Pinned.Forms

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Fischer.Native

@[expose] def fi22Monomials : List (Nat × Nat) :=
  (List.range 77).flatMap fun i => (List.range (77 - i)).map fun t => (i, i + t)

@[expose] def monoBlock (i : Nat) : List (Nat × Nat) :=
  (List.range (77 - i)).map fun t => (i, i + t)

theorem fi22Monomials_eq : fi22Monomials = (List.range 77).flatMap monoBlock := rfl

theorem pairIdx_succ : ∀ i < 77, pairIdx i i + (77 - i) = pairIdx (i + 1) (i + 1) := by
  decide +kernel

theorem length_flatMap_monoBlock {i : Nat} (hi : i ≤ 77) :
    ((List.range i).flatMap monoBlock).length = pairIdx i i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih (by omega)]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, monoBlock, List.length_map,
      List.length_range]
    exact pairIdx_succ i (by omega)

theorem getElem?_fi22Monomials {i t : Nat} (hi : i < 77) (ht : t < 77 - i) :
    fi22Monomials[pairIdx i i + t]? = some (i, i + t) := by
  have e : List.range 77 = List.range i ++ (List.range (77 - i)).map (i + ·) := by
    rw [← List.range_add]
    congr 1
    omega
  have e2 : List.range (77 - i) = 0 :: (List.range (77 - i - 1)).map Nat.succ := by
    rw [← List.range_succ_eq_map]
    congr 1
    omega
  have hl := length_flatMap_monoBlock (Nat.le_of_lt hi)
  rw [fi22Monomials_eq, e, List.flatMap_append, List.getElem?_append_right (by omega), hl,
    Nat.add_sub_cancel_left, e2, List.map_cons, List.flatMap_cons,
    List.getElem?_append_left (by simp [monoBlock]; omega)]
  simp [monoBlock, List.getElem?_range ht]

theorem fi22Monomials_pairIdx : fi22Monomials.length = 3003 ∧
    ∀ i < 77, ∀ j < 77, i ≤ j → fi22Monomials[pairIdx i j]? = some (i, j) := by
  refine ⟨(length_flatMap_monoBlock (Nat.le_refl 77)).trans rfl, fun i hi j hj hij => ?_⟩
  have h := getElem?_fi22Monomials hi (t := j - i) (by omega)
  rwa [show pairIdx i i + (j - i) = pairIdx i j by simp [pairIdx],
    show i + (j - i) = j by omega] at h

end CFSG.Monster.B.Fischer
