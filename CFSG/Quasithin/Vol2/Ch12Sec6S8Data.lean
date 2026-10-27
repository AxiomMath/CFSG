module

public section

namespace CFSG.Quasithin.H13.S8E

@[expose] def id8 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]

@[expose] def ap (f : List Nat) (i : Nat) : Nat := f.getD i 0

@[expose] def cmp (f g : List Nat) : List Nat := g.map (ap f)

@[expose] def prt (i : Nat) : Nat := ap [1, 0, 3, 2, 5, 4, 7, 6] i

@[expose] def ext4 (a b c d : Nat) : List Nat := [a, prt a, b, prt b, c, prt c, d, prt d]

@[expose] def Halves (f : List Nat) : Prop :=
  (∀ i ∈ [0, 1, 2, 3], ap f i < 4) ∨ ∀ i ∈ [0, 1, 2, 3], 4 ≤ ap f i

instance (f : List Nat) : Decidable (Halves f) := by
  unfold Halves
  infer_instance

@[expose] def INV : List (List Nat) :=
  [[0, 1, 2, 3, 4, 5, 7, 6], [0, 1, 2, 3, 5, 4, 6, 7], [0, 1, 2, 3, 5, 4, 7, 6],
   [0, 1, 2, 3, 6, 7, 4, 5], [0, 1, 2, 3, 7, 6, 5, 4], [0, 1, 3, 2, 4, 5, 6, 7],
   [0, 1, 3, 2, 4, 5, 7, 6], [0, 1, 3, 2, 5, 4, 6, 7], [0, 1, 3, 2, 5, 4, 7, 6],
   [0, 1, 3, 2, 6, 7, 4, 5], [0, 1, 3, 2, 7, 6, 5, 4], [1, 0, 2, 3, 4, 5, 6, 7],
   [1, 0, 2, 3, 4, 5, 7, 6], [1, 0, 2, 3, 5, 4, 6, 7], [1, 0, 2, 3, 5, 4, 7, 6],
   [1, 0, 2, 3, 6, 7, 4, 5], [1, 0, 2, 3, 7, 6, 5, 4], [1, 0, 3, 2, 4, 5, 6, 7],
   [1, 0, 3, 2, 4, 5, 7, 6], [1, 0, 3, 2, 5, 4, 6, 7], [1, 0, 3, 2, 5, 4, 7, 6],
   [1, 0, 3, 2, 6, 7, 4, 5], [1, 0, 3, 2, 7, 6, 5, 4], [2, 3, 0, 1, 4, 5, 6, 7],
   [2, 3, 0, 1, 4, 5, 7, 6], [2, 3, 0, 1, 5, 4, 6, 7], [2, 3, 0, 1, 5, 4, 7, 6],
   [2, 3, 0, 1, 6, 7, 4, 5], [2, 3, 0, 1, 7, 6, 5, 4], [3, 2, 1, 0, 4, 5, 6, 7],
   [3, 2, 1, 0, 4, 5, 7, 6], [3, 2, 1, 0, 5, 4, 6, 7], [3, 2, 1, 0, 5, 4, 7, 6],
   [3, 2, 1, 0, 6, 7, 4, 5], [3, 2, 1, 0, 7, 6, 5, 4], [4, 5, 6, 7, 0, 1, 2, 3],
   [4, 5, 7, 6, 0, 1, 3, 2], [5, 4, 6, 7, 1, 0, 2, 3], [5, 4, 7, 6, 1, 0, 3, 2],
   [6, 7, 4, 5, 2, 3, 0, 1], [6, 7, 5, 4, 3, 2, 0, 1], [7, 6, 4, 5, 2, 3, 1, 0],
   [7, 6, 5, 4, 3, 2, 1, 0]]

@[expose] def iv (n : Nat) : List Nat := INV.getD n id8

@[expose] def CommL (f g : List Nat) : Prop := cmp f g = cmp g f

instance (f g : List Nat) : Decidable (CommL f g) := by
  unfold CommL
  infer_instance

@[expose] def Fpf (f : List Nat) : Prop := ∀ i ∈ id8, ap f i ≠ i

instance (f : List Nat) : Decidable (Fpf f) := by
  unfold Fpf
  infer_instance

@[expose] def W2b (a b c : List Nat) : Prop :=
  (∃ p ∈ id8, ap a p ≠ p ∧ ap b p = p ∧ ap c p = p) ∧
    ∃ r ∈ id8, ap a r = r ∧ ap b r = r ∧ ap c r = r

instance (a b c : List Nat) : Decidable (W2b a b c) := by
  unfold W2b
  infer_instance

@[expose] def W8b (a b c : List Nat) : Prop :=
  Fpf a ∧ Fpf (cmp a b) ∧ Fpf (cmp a c) ∧ Fpf (cmp a (cmp b c))

instance (a b c : List Nat) : Decidable (W8b a b c) := by
  unfold W8b
  infer_instance

@[expose] def grp3 (x y z : List Nat) : List (List Nat) :=
  [id8, x, y, z, cmp x y, cmp x z, cmp y z, cmp x (cmp y z)]

@[expose] def grp4 (g3 : List (List Nat)) (w : List Nat) : List (List Nat) :=
  g3 ++ g3.map fun f => cmp f w

@[expose] def W3 (g : List (List Nat)) : Prop :=
  ∃ b ∈ g, b ≠ id8 ∧ ∃ a ∈ g, W2b a b b ∨ W8b a b b

instance (g : List (List Nat)) : Decidable (W3 g) := by
  unfold W3
  infer_instance

@[expose] def W4 (g : List (List Nat)) (x y z w : List Nat) : Prop :=
  (∃ b ∈ g, b ≠ id8 ∧ ∃ c ∈ g, c ≠ id8 ∧ c ≠ b ∧ ∃ a ∈ g, W2b a b c ∨ W8b a b c) ∧
    ∀ n ∈ List.range 43, CommL (iv n) x → CommL (iv n) y → CommL (iv n) z → CommL (iv n) w →
      iv n ∈ g

instance (g : List (List Nat)) (x y z w : List Nat) : Decidable (W4 g x y z w) := by
  unfold W4
  infer_instance

@[expose] def T34 (g3 : List (List Nat)) (k : Nat) (x y z : List Nat) : Prop :=
  W3 g3 ∧ ∀ l ∈ List.range 43, k < l → CommL x (iv l) → CommL y (iv l) → CommL z (iv l) →
    iv l ∉ g3 → W4 (grp4 g3 (iv l)) x y z (iv l)

instance (g3 : List (List Nat)) (k : Nat) (x y z : List Nat) : Decidable (T34 g3 k x y z) := by
  unfold T34
  infer_instance

@[expose] def K0 : Prop :=
  ∀ a ∈ id8, ∀ b ∈ id8, ∀ c ∈ id8, ∀ d ∈ id8, cmp (ext4 a b c d) (ext4 a b c d) = id8 →
    Halves (ext4 a b c d) → ext4 a b c d ≠ id8 → ext4 a b c d ∈ INV

@[expose] def K34 : Prop :=
  ∀ i ∈ List.range 43, ∀ j ∈ List.range 43, i < j → CommL (iv i) (iv j) →
    ∀ k ∈ List.range 43, j < k → CommL (iv i) (iv k) → CommL (iv j) (iv k) →
    iv k ∉ [id8, iv i, iv j, cmp (iv i) (iv j)] →
    T34 (grp3 (iv i) (iv j) (iv k)) k (iv i) (iv j) (iv k)

instance : Decidable K0 := by
  unfold K0
  infer_instance

instance : Decidable K34 := by
  unfold K34
  infer_instance

@[expose] def s8Check : Bool := decide K0 && decide K34

end CFSG.Quasithin.H13.S8E
