module

@[expose] public section

namespace Certificates.F5Seven

abbrev Tup7 := Fin 7 × Fin 7 × Fin 7 × Fin 7

def inv7 (a : Fin 7) : Fin 7 := a * a * a * a * a

def detT (x : Tup7) : Fin 7 := x.1 * x.2.2.2 - x.2.1 * x.2.2.1

def mulT (x y : Tup7) : Tup7 :=
  (x.1 * y.1 + x.2.1 * y.2.2.1, x.1 * y.2.1 + x.2.1 * y.2.2.2,
    x.2.2.1 * y.1 + x.2.2.2 * y.2.2.1, x.2.2.1 * y.2.1 + x.2.2.2 * y.2.2.2)

def invT (x : Tup7) : Tup7 :=
  (inv7 (detT x) * x.2.2.2, -(inv7 (detT x) * x.2.1), -(inv7 (detT x) * x.2.2.1),
    inv7 (detT x) * x.1)

def oneT : Tup7 := (1, 0, 0, 1)

def encode (x : Tup7) : Nat := x.1.val + 7 * (x.2.1.val + 7 * (x.2.2.1.val + 7 * x.2.2.2.val))

def decode (n : Nat) : Tup7 :=
  (⟨n % 7, Nat.mod_lt _ (by decide)⟩, ⟨n / 7 % 7, Nat.mod_lt _ (by decide)⟩,
    ⟨n / 49 % 7, Nat.mod_lt _ (by decide)⟩, ⟨n / 343 % 7, Nat.mod_lt _ (by decide)⟩)

def stepMarks (gens : List (Tup7 × Tup7)) (A : Array Bool) : Array Bool :=
  Array.ofFn (n := 2401) fun i : Fin 2401 =>
    A.getD i.val false || gens.any fun p => A.getD (encode (mulT (decode i.val) p.2)) false

def baseMarks (_ : Unit := ()) : Array Bool :=
  Array.ofFn (n := 2401) fun i : Fin 2401 => decide (i.val = encode oneT)

def iterMarks (gens : List (Tup7 × Tup7)) : Nat → Array Bool
  | 0 => baseMarks
  | k + 1 => stepMarks gens (iterMarks gens k)

def allTrue (A : Array Bool) : Bool :=
  (List.range 2401).all fun j => !decide (detT (decode j) ≠ 0) || A.getD j false

def zeta7 : Tup7 := (1, 5, 2, 1)

def sigma7 : Tup7 := (1, 0, 0, 6)

def uGens : List (Tup7 × Tup7) := [(zeta7, invT zeta7), (sigma7, invT sigma7)]

def uMarks (_ : Unit := ()) : Array Bool := iterMarks uGens 16

def coreCheck (_ : Unit := ()) : Bool :=
  (List.range 2401).all fun i =>
    !decide (detT (decode i) ≠ 0) || uMarks.getD i false ||
      allTrue (iterMarks (uGens ++ [(decode i, invT (decode i))]) 16)

end Certificates.F5Seven

end
