module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatQuot

public section

namespace CFSG.Quasithin.A312S

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def e8VPow (vt : Array (Array Nat)) (n b i : Nat) : Array Nat :=
  if b = 1 then vt.getD i #[] else Array.range n

@[expose] def e8BTab (vt : Array (Array Nat)) (n : Nat) (c : List Nat) : Array Nat :=
  compArr (compArr (e8VPow vt n (c.getD 0 0) 0) (e8VPow vt n (c.getD 1 0) 1))
    (e8VPow vt n (c.getD 2 0) 2)

@[expose] def e8Col (M : List (List Nat)) (i : Nat) : List Nat := M.map fun r => r.getD i 0

@[expose] def e8NZ : List (List Nat) :=
  [[1, 0, 0], [0, 1, 0], [1, 1, 0], [0, 0, 1], [1, 0, 1], [0, 1, 1], [1, 1, 1]]

@[expose] def e8Check (n : Nat) (vt letters : Array (Array Nat)) (mats : List (List (List Nat))) :
    Bool :=
  ((List.range 3).all fun i => compArr (vt.getD i #[]) (vt.getD i #[]) == Array.range n) &&
  ((List.range 3).all fun i => (List.range 3).all fun j =>
    compArr (vt.getD i #[]) (vt.getD j #[]) == compArr (vt.getD j #[]) (vt.getD i #[])) &&
  (e8NZ.all fun c => e8BTab vt n c != Array.range n) &&
  ((List.range letters.size).all fun l => (List.range 3).all fun i =>
    compArr (letters.getD l #[]) (vt.getD i #[]) ==
      compArr (e8BTab vt n (e8Col (mats.getD l []) i)) (letters.getD l #[]))

structure KerGen where
  u : List Nat
  k : Nat
  e : Nat
  deriving Inhabited

@[expose] def kerGt (n : Nat) (R : List (Array Nat)) (c : KerGen) : Array Nat :=
  powTab n (wordTabA R.toArray n c.u) c.k

@[expose] def kerGi (n : Nat) (R : List (Array Nat)) (c : KerGen) : Array Nat :=
  powTab n (kerGt n R c) (2 ^ c.e - 1)

@[expose] def KerOK (n : Nat) (B : List Nat) (L : List (Array Nat)) (xs : List QuotGen)
    (cs : List KerGen) (vt : Array (Array Nat)) (Ts : Array (List Nat)) (par cl : Array Nat)
    (r : Nat) : Prop :=
  (∀ x ∈ xs, (∀ l ∈ x.w, l < L.length) ∧ x.m % 2 = 1) ∧
  (∀ i < xs.length, ∀ b ∈ B, img (powTab n (xs.map (quotGt n L))[i]! xs[i]!.m) b = b) ∧
  (∀ c ∈ cs, ∀ l ∈ c.u, l < xs.length) ∧
  (∀ c ∈ cs, ∀ b ∈ B, img (powTab n (kerGt n (xs.map (quotGt n L)) c) (2 ^ c.e)) b = b) ∧
  (∀ c ∈ cs, ∀ i < 3, compArr (kerGt n (xs.map (quotGt n L)) c) (vt.getD i #[]) =
    compArr (vt.getD i #[]) (kerGt n (xs.map (quotGt n L)) c)) ∧
  BaseEnumOK n B (cs.map (kerGt n (xs.map (quotGt n L))))
    (cs.map (kerGi n (xs.map (quotGt n L)))) Ts par cl ∧
  Ts.size = r

instance (n : Nat) (B : List Nat) (L : List (Array Nat)) (xs : List QuotGen) (cs : List KerGen)
    (vt : Array (Array Nat)) (Ts : Array (List Nat)) (par cl : Array Nat) (r : Nat) :
    Decidable (KerOK n B L xs cs vt Ts par cl r) := by
  unfold KerOK; infer_instance

end CFSG.Quasithin.A312S
