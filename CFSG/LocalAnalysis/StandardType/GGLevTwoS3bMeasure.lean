module

public import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley

@[expose] def levTwoS3b_cart : List (List ℤ) :=
  [([2, 0, -1, 0, 0, 0, 0, 0] : List ℤ), ([0, 2, 0, -1, 0, 0, 0, 0] : List ℤ),
    ([-1, 0, 2, -1, 0, 0, 0, 0] : List ℤ), ([0, -1, -1, 2, -1, 0, 0, 0] : List ℤ),
    ([0, 0, 0, -1, 2, -1, 0, 0] : List ℤ), ([0, 0, 0, 0, -1, 2, -1, 0] : List ℤ),
    ([0, 0, 0, 0, 0, -1, 2, -1] : List ℤ), ([0, 0, 0, 0, 0, 0, -1, 2] : List ℤ)]

@[expose] def levTwoS3b_theta : List ℤ := ([2, 3, 4, 6, 5, 4, 3, 2] : List ℤ)

@[expose] def levTwoS3b_roots : List (List ℤ) := Tag.artifactRoots Tag.E8

@[expose] def levTwoS3b_dotv (a b : List ℤ) : ℤ := (List.zipWith (· * ·) a b).foldl (· + ·) 0

@[expose] def levTwoS3b_mulC (v : List ℤ) : List ℤ := levTwoS3b_cart.map (fun row => levTwoS3b_dotv row v)

@[expose] def levTwoS3b_ipf (a b : List ℤ) : ℤ := levTwoS3b_dotv a (levTwoS3b_mulC b)

@[expose] def levTwoS3b_reflv (a v : List ℤ) : List ℤ :=
  let c := levTwoS3b_ipf a v
  List.zipWith (fun x y => x - c * y) v a

@[expose] def levTwoS3b_key (v : List ℤ) : ℕ := v.foldl (fun acc x => acc * 13 + (x + 6).toNat) 0

@[expose] def levTwoS3b_keys : List ℕ := levTwoS3b_roots.map levTwoS3b_key

@[expose] def levTwoS3b_idxK (k : ℕ) : ℕ := levTwoS3b_keys.findIdx (· == k)

@[expose] def levTwoS3b_unit (j : ℕ) : List ℤ :=
  (List.range 8).map (fun k => if k == j then 1 else 0)

@[expose] def levTwoS3b_genVec : ℕ → List ℤ
  | 0 => levTwoS3b_theta
  | (j + 1) => levTwoS3b_unit j

@[expose] def levTwoS3b_permOf (g : List ℤ) : List ℕ :=
  levTwoS3b_roots.map (fun v => levTwoS3b_idxK (levTwoS3b_key (levTwoS3b_reflv g v)))

@[expose] def levTwoS3b_nodesOf (m : ℕ) : List ℕ := (List.range 9).filter (fun x => m.testBit x)

@[expose] def levTwoS3b_absv (v : List ℤ) : List ℤ :=
  if v.all (fun x => decide (0 ≤ x)) then v else v.map (fun x => -x)

@[expose] def levTwoS3b_inPat (m : ℕ) (v : List ℤ) : Bool :=
  let a := levTwoS3b_absv v
  let c1 := (List.range 8).all (fun k => a.getD k 0 == 0 || m.testBit (k + 1))
  let d := List.zipWith (fun t x => t - x) levTwoS3b_theta a
  let c2 := m.testBit 0 && d.all (fun x => decide (0 ≤ x)) &&
    (List.range 8).all (fun k => d.getD k 0 == 0 || m.testBit (k + 1))
  c1 || c2

@[expose] def levTwoS3b_patMask (m : ℕ) : ℕ :=
  (List.range 240).foldl
    (fun acc i => if levTwoS3b_inPat m (levTwoS3b_roots.getD i []) then acc ||| (1 <<< i) else acc) 0

end CFSG.StandardType.LevTwo
