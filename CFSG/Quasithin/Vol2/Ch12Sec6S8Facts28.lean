module

public import CFSG.Quasithin.Vol2.Ch12Sec6S8Data28

public section

namespace CFSG.Quasithin.H13.S8F

open S8E

@[expose] def R2w (g : List (List Nat)) : Prop := ∃ w, Ok1 g w

@[expose] def R3w (g : List (List Nat)) : Prop :=
  (∃ w, Ok1 g w) ∧ ((∃ w, Ok2 g w) ∨ ∃ w, OkE3 g w)

@[expose] def R4w (g : List (List Nat)) : Prop :=
  (∃ w, Ok2 g w) ∧ ((∃ w, Ok3 g w) ∨ ∃ w, OkE4 g w)

@[expose] def C2w : Prop :=
  ∀ i ∈ List.range 43, ∀ j ∈ List.range 43, i < j → CommL (iv i) (iv j) →
    R2w (grp2 (iv i) (iv j))

@[expose] def C3w : Prop :=
  ∀ i ∈ List.range 43, ∀ j ∈ List.range 43, i < j → CommL (iv i) (iv j) →
    ∀ k ∈ List.range 43, j < k → CommL (iv i) (iv k) → CommL (iv j) (iv k) →
    iv k ∉ [id8, iv i, iv j, cmp (iv i) (iv j)] → R3w (grp3 (iv i) (iv j) (iv k))

@[expose] def T4w (i j k : Nat) : Prop :=
  ∀ l ∈ List.range 43, k < l → CommL (iv i) (iv l) → CommL (iv j) (iv l) →
    CommL (iv k) (iv l) → iv l ∉ grp3 (iv i) (iv j) (iv k) →
    R4w (grp4 (grp3 (iv i) (iv j) (iv k)) (iv l)) ∧
      Max4 (grp4 (grp3 (iv i) (iv j) (iv k)) (iv l)) (iv i) (iv j) (iv k) (iv l)

@[expose] def C4w : Prop :=
  ∀ i ∈ List.range 43, ∀ j ∈ List.range 43, i < j → CommL (iv i) (iv j) →
    ∀ k ∈ List.range 43, j < k → CommL (iv i) (iv k) → CommL (iv j) (iv k) →
    iv k ∉ [id8, iv i, iv j, cmp (iv i) (iv j)] → T4w i j k

end CFSG.Quasithin.H13.S8F
