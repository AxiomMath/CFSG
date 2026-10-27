module

public import Certificates.Data.Kernel.SporSch.HNXPtL

public section

namespace CFSG.KC.LL.HNX

@[expose] def walk (src dst : Nat → Nat → Nat) : List Nat → List Nat → Nat → Option (List Nat × Nat)
  | [], es, p => some (es, p)
  | _ :: _, [], _ => none
  | l :: ls, e :: es, p => bif Nat.beq (src l e) p then walk src dst ls es (dst l e) else none

@[expose] def lgetL (P : List (List Nat)) (k : Nat) : List Nat := P.getD k []

@[expose] def idsOk (src dst : Nat → Nat → Nat) (TW IS : List (List Nat)) (c : Nat) :
    List (List Nat) → List Nat → Bool
  | [], es => es.isEmpty
  | (x :: k :: w) :: ids, es =>
    match walk src dst (lgetL TW x ++ [k]) es c with
    | none => false
    | some (es₁, p) =>
      match walk src dst (w ++ lgetL TW (lget (lgetL IS k) x)) es₁ c with
      | none => false
      | some (es₂, q) => Nat.beq p q && idsOk src dst TW IS c ids es₂
  | _ :: _, _ => false

@[expose] def wordPos (IS : List (List Nat)) : List Nat → Nat → Nat
  | [], x => x
  | l :: w, x => wordPos IS w (lget (lgetL IS l) x)

@[expose] def schOk (IS TW : List (List Nat)) (ids : List (List Nat)) : Bool :=
  TW.length == 50 && (lgetL TW 0).isEmpty &&
    (List.range 50).all (fun x => (lgetL TW x).all (· < 6) && wordPos IS (lgetL TW x) 0 == x) &&
    (List.range 50).all fun x => (List.range 6).all fun k =>
      lgetL TW (lget (lgetL IS k) x) == lgetL TW x ++ [k] ||
        ids.any fun i => i.take 2 == [x, k] && (i.drop 2).all (· < 5)

end CFSG.KC.LL.HNX

end
