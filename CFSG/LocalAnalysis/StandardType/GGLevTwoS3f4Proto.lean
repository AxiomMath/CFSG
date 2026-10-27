module

public import CFSG.Blueprint.ChevalleyRootArtifact
import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley

@[expose] def levTwoS3f4_symcart : List (List ℤ) :=
  [([4, -2, 0, 0] : List ℤ), ([-2, 4, -2, 0] : List ℤ), ([0, -2, 2, -1] : List ℤ),
    ([0, 0, -1, 2] : List ℤ)]

@[expose] def levTwoS3f4_theta : List ℤ := ([2, 3, 4, 2] : List ℤ)

@[expose] def levTwoS3f4_roots : List (List ℤ) := Tag.artifactRoots Tag.F4

@[expose] def levTwoS3f4_dotv (a b : List ℤ) : ℤ := (List.zipWith (· * ·) a b).foldl (· + ·) 0

@[expose] def levTwoS3f4_mulC (v : List ℤ) : List ℤ :=
  levTwoS3f4_symcart.map (fun row => levTwoS3f4_dotv row v)

@[expose] def levTwoS3f4_ipf (a b : List ℤ) : ℤ := levTwoS3f4_dotv a (levTwoS3f4_mulC b)

@[expose] def levTwoS3f4_reflv (g v : List ℤ) : List ℤ :=
  let k := 2 * levTwoS3f4_ipf g v / levTwoS3f4_ipf g g
  List.zipWith (fun x y => x - k * y) v g

@[expose] def levTwoS3f4_key (v : List ℤ) : ℕ := v.foldl (fun acc x => acc * 13 + (x + 6).toNat) 0

@[expose] def levTwoS3f4_keys : List ℕ := levTwoS3f4_roots.map levTwoS3f4_key

@[expose] def levTwoS3f4_idxK (k : ℕ) : ℕ := levTwoS3f4_keys.findIdx (· == k)

theorem levTwoS3f4_keys_nodup : levTwoS3f4_keys.Nodup :=
  CFSG.Decide.nodup_of_bitsetNodup (fun n => n) (by decide +kernel)

@[expose] def levTwoS3f4_permOf (g : List ℤ) : List ℕ :=
  levTwoS3f4_roots.map (fun v => levTwoS3f4_idxK (levTwoS3f4_key (levTwoS3f4_reflv g v)))

@[expose] def levTwoS3f4_negPerm : List ℕ :=
  levTwoS3f4_roots.map (fun v => levTwoS3f4_idxK (levTwoS3f4_key (v.map (fun x => -x))))

@[expose] def levTwoS3f4_absv (v : List ℤ) : List ℤ :=
  if v.all (fun x => decide (0 ≤ x)) then v else v.map (fun x => -x)

@[expose] def levTwoS3f4_inPat (m : ℕ) (v : List ℤ) : Bool :=
  let a := levTwoS3f4_absv v
  let c1 := (List.range 4).all (fun k => a.getD k 0 == 0 || m.testBit (k + 1))
  let d := List.zipWith (fun t x => t - x) levTwoS3f4_theta a
  let c2 := m.testBit 0 && d.all (fun x => decide (0 ≤ x)) &&
    (List.range 4).all (fun k => d.getD k 0 == 0 || m.testBit (k + 1))
  c1 || c2

@[expose] def levTwoS3f4_inPatLen (m l : ℕ) (v : List ℤ) : Bool :=
  levTwoS3f4_inPat m v && (levTwoS3f4_ipf v v == (l : ℤ))

@[expose] def levTwoS3f4_patMask (m l : ℕ) : ℕ :=
  (List.range 48).foldl
    (fun acc i => if levTwoS3f4_inPatLen m l (levTwoS3f4_roots.getD i []) then acc ||| (1 <<< i) else acc) 0

@[expose] def levTwoS3f4_patPerms (m l : ℕ) : List (List ℕ) :=
  levTwoS3f4_negPerm ::
    ((List.range 48).filter (fun i => (levTwoS3f4_patMask m l).testBit i)).map
      (fun i => levTwoS3f4_permOf (levTwoS3f4_roots.getD i []))

end CFSG.StandardType.LevTwo
