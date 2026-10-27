module

public import CFSG.Blueprint.ChevalleyRootArtifact
import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley

@[expose] def levTwoS3e7_cart : List (List ℤ) :=
  [([2, 0, -1, 0, 0, 0, 0] : List ℤ), ([0, 2, 0, -1, 0, 0, 0] : List ℤ),
    ([-1, 0, 2, -1, 0, 0, 0] : List ℤ), ([0, -1, -1, 2, -1, 0, 0] : List ℤ),
    ([0, 0, 0, -1, 2, -1, 0] : List ℤ), ([0, 0, 0, 0, -1, 2, -1] : List ℤ),
    ([0, 0, 0, 0, 0, -1, 2] : List ℤ)]

@[expose] def levTwoS3e7_theta : List ℤ := ([2, 2, 3, 4, 3, 2, 1] : List ℤ)

@[expose] def levTwoS3e7_roots : List (List ℤ) := Tag.artifactRoots Tag.E7

@[expose] def levTwoS3e7_dotv (a b : List ℤ) : ℤ := (List.zipWith (· * ·) a b).foldl (· + ·) 0

@[expose] def levTwoS3e7_mulC (v : List ℤ) : List ℤ := levTwoS3e7_cart.map (fun row => levTwoS3e7_dotv row v)

@[expose] def levTwoS3e7_ipf (a b : List ℤ) : ℤ := levTwoS3e7_dotv a (levTwoS3e7_mulC b)

@[expose] def levTwoS3e7_reflv (a v : List ℤ) : List ℤ :=
  let c := levTwoS3e7_ipf a v
  List.zipWith (fun x y => x - c * y) v a

@[expose] def levTwoS3e7_key (v : List ℤ) : ℕ := v.foldl (fun acc x => acc * 13 + (x + 6).toNat) 0

@[expose] def levTwoS3e7_keys : List ℕ := levTwoS3e7_roots.map levTwoS3e7_key

@[expose] def levTwoS3e7_unit (j : ℕ) : List ℤ :=
  (List.range 7).map (fun k => if k == j then 1 else 0)

@[expose] def levTwoS3e7_genVec : ℕ → List ℤ
  | 0 => levTwoS3e7_theta
  | (j + 1) => levTwoS3e7_unit j

@[expose] def levTwoS3e7_nodesOf (m : ℕ) : List ℕ := (List.range 8).filter (fun x => m.testBit x)

@[expose] def levTwoS3e7_absv (v : List ℤ) : List ℤ :=
  if v.all (fun x => decide (0 ≤ x)) then v else v.map (fun x => -x)

@[expose] def levTwoS3e7_inPat (m : ℕ) (v : List ℤ) : Bool :=
  let a := levTwoS3e7_absv v
  let c1 := (List.range 7).all (fun k => a.getD k 0 == 0 || m.testBit (k + 1))
  let d := List.zipWith (fun t x => t - x) levTwoS3e7_theta a
  let c2 := m.testBit 0 && d.all (fun x => decide (0 ≤ x)) &&
    (List.range 7).all (fun k => d.getD k 0 == 0 || m.testBit (k + 1))
  c1 || c2

@[expose] def levTwoS3e7_patMask (m : ℕ) : ℕ :=
  (List.range 126).foldl
    (fun acc i => if levTwoS3e7_inPat m (levTwoS3e7_roots.getD i []) then acc ||| (1 <<< i) else acc) 0

theorem levTwoS3e7_cart_eq :
    levTwoS3e7_cart =
      List.ofFn (fun i : Fin (Tag.rank Tag.E7) =>
        List.ofFn (fun j : Fin (Tag.rank Tag.E7) => Tag.cartan Tag.E7 i j)) := by
  decide +kernel

theorem levTwoS3e7_keys_nodup : levTwoS3e7_keys.Nodup :=
  CFSG.Decide.nodup_of_bitsetNodup (f := id) (by decide +kernel)

theorem levTwoS3e7_roots_length : levTwoS3e7_roots.length = 126 := by decide +kernel

end CFSG.StandardType.LevTwo
