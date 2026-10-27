module

public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompKac
import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley

@[expose] def levTwoS3e6_cart : List (List ℤ) :=
  [([2, 0, -1, 0, 0, 0] : List ℤ), ([0, 2, 0, -1, 0, 0] : List ℤ),
    ([-1, 0, 2, -1, 0, 0] : List ℤ), ([0, -1, -1, 2, -1, 0] : List ℤ),
    ([0, 0, 0, -1, 2, -1] : List ℤ), ([0, 0, 0, 0, -1, 2] : List ℤ)]

@[expose] def levTwoS3e6_theta : List ℤ := ([1, 2, 2, 3, 2, 1] : List ℤ)

@[expose] def levTwoS3e6_roots : List (List ℤ) := Tag.artifactRoots Tag.E6

theorem levTwoS3e6_roots_eq : levTwoS3e6_roots = Tag.artifactRoots Tag.E6 := rfl

theorem levTwoS3e6_cart_eq :
    levTwoS3e6_cart =
      List.ofFn (fun i : Fin (Tag.rank Tag.E6) =>
        List.ofFn (fun j : Fin (Tag.rank Tag.E6) => Tag.cartan Tag.E6 i j)) := by
  decide +kernel

theorem levTwoS3e6_theta_eq_kacE6 :
    levTwoS3e6_theta =
      List.ofFn (@CFSG.HardMathSupport.Timmesfeld.CrossChar.kacE6
).θ := by
  rfl

@[expose] def levTwoS3e6_dotv (a b : List ℤ) : ℤ := (List.zipWith (· * ·) a b).foldl (· + ·) 0

@[expose] def levTwoS3e6_mulC (v : List ℤ) : List ℤ :=
  levTwoS3e6_cart.map (fun row => levTwoS3e6_dotv row v)

@[expose] def levTwoS3e6_ipf (a b : List ℤ) : ℤ := levTwoS3e6_dotv a (levTwoS3e6_mulC b)

@[expose] def levTwoS3e6_reflv (a v : List ℤ) : List ℤ :=
  let c := levTwoS3e6_ipf a v
  List.zipWith (fun x y => x - c * y) v a

@[expose] def levTwoS3e6_key (v : List ℤ) : ℕ := v.foldl (fun acc x => acc * 13 + (x + 6).toNat) 0

@[expose] def levTwoS3e6_keys : List ℕ := levTwoS3e6_roots.map levTwoS3e6_key

theorem levTwoS3e6_keys_nodup : levTwoS3e6_keys.Nodup :=
  CFSG.Decide.nodup_of_bitsetNodup (l := levTwoS3e6_keys) id (by decide +kernel)

@[expose] def levTwoS3e6_idxK (k : ℕ) : ℕ := levTwoS3e6_keys.findIdx (· == k)

@[expose] def levTwoS3e6_unit (j : ℕ) : List ℤ :=
  (List.range 6).map (fun k => if k == j then 1 else 0)

@[expose] def levTwoS3e6_genVec : ℕ → List ℤ
  | 0 => levTwoS3e6_theta
  | (j + 1) => levTwoS3e6_unit j

@[expose] def levTwoS3e6_permOf (g : List ℤ) : List ℕ :=
  levTwoS3e6_roots.map (fun v => levTwoS3e6_idxK (levTwoS3e6_key (levTwoS3e6_reflv g v)))

@[expose] def levTwoS3e6_nodesOf (m : ℕ) : List ℕ := (List.range 7).filter (fun x => m.testBit x)

@[expose] def levTwoS3e6_absv (v : List ℤ) : List ℤ :=
  if v.all (fun x => decide (0 ≤ x)) then v else v.map (fun x => -x)

@[expose] def levTwoS3e6_inPat (m : ℕ) (v : List ℤ) : Bool :=
  let a := levTwoS3e6_absv v
  let c1 := (List.range 6).all (fun k => a.getD k 0 == 0 || m.testBit (k + 1))
  let d := List.zipWith (fun t x => t - x) levTwoS3e6_theta a
  let c2 := m.testBit 0 && d.all (fun x => decide (0 ≤ x)) &&
    (List.range 6).all (fun k => d.getD k 0 == 0 || m.testBit (k + 1))
  c1 || c2

@[expose] def levTwoS3e6_patMask (m : ℕ) : ℕ :=
  (List.range 72).foldl
    (fun acc i => if levTwoS3e6_inPat m (levTwoS3e6_roots.getD i []) then acc ||| (1 <<< i) else acc) 0

end CFSG.StandardType.LevTwo
