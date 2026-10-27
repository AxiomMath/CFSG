module

public import Certificates.Data.E6DiagRegular
public import CFSG.RankThree.E6.RootLatticeTools

public section

namespace Certificates.E6WeylDivisors

open CFSG.Blueprint.Chevalley CFSG.RankThree.E6 CFSG.HardMathSupport.Timmesfeld.Steinberg
open CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular

@[expose] def det2 (N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) (i i' j j' : Fin Tag.E6.rank) :
    ℤ :=
  N i j * N i' j' - N i j' * N i' j

@[expose] def det3 (N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ)
    (a b c x y z : Fin Tag.E6.rank) : ℤ :=
  N a x * (N b y * N c z - N b z * N c y) - N a y * (N b x * N c z - N b z * N c x) +
    N a z * (N b x * N c y - N b y * N c x)

@[expose] def pairs6 : List (Fin Tag.E6.rank × Fin Tag.E6.rank) :=
  (List.finRange Tag.E6.rank).flatMap fun i =>
    ((List.finRange Tag.E6.rank).filter fun j => i < j).map fun j => (i, j)

@[expose] def triples6 : List (Fin Tag.E6.rank × Fin Tag.E6.rank × Fin Tag.E6.rank) :=
  (List.finRange Tag.E6.rank).flatMap fun i =>
    (List.finRange Tag.E6.rank).flatMap fun j =>
      ((List.finRange Tag.E6.rank).filter fun k => i < j ∧ j < k).map fun k => (i, j, k)

@[expose] def minorIdx2 :
    List ((Fin Tag.E6.rank × Fin Tag.E6.rank) × (Fin Tag.E6.rank × Fin Tag.E6.rank)) :=
  pairs6.flatMap fun r => pairs6.map fun c => (r, c)

@[expose] def minorIdx3 :
    List ((Fin Tag.E6.rank × Fin Tag.E6.rank × Fin Tag.E6.rank) ×
      (Fin Tag.E6.rank × Fin Tag.E6.rank × Fin Tag.E6.rank)) :=
  triples6.flatMap fun r => triples6.map fun c => (r, c)

@[expose] def gcdSearch {α : Type} (m : α → ℕ) : List α → ℕ → Bool
  | [], g => decide (g ∣ 2)
  | x :: l, g => decide (Nat.gcd g (m x) ∣ 2) || gcdSearch m l (Nat.gcd g (m x))

@[expose] def gcdSearch3 (N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) : Bool :=
  gcdSearch (fun x => (det3 N x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2).natAbs) minorIdx3 0

@[expose] def gcdSearch2 (N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) : Bool :=
  gcdSearch (fun x => (det2 N x.1.1 x.1.2 x.2.1 x.2.2).natAbs) minorIdx2 0

@[expose] def matrixCheck (M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) (a : ℤ) : Bool :=
  decide (M * M = 1) || (gcdSearch3 (M + a • 1) && gcdSearch2 (M - a • 1))

end Certificates.E6WeylDivisors

end
