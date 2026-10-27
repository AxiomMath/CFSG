module

public import CFSG.Permutation.FiveTransitive.PointStabilizerFixedSet
public import Mathlib.GroupTheory.Perm.Sign

public section

namespace CFSG

namespace FiveTransitive.PointStabilizerFixedSign

open MulAction SubMulAction FixedSetNormalizerPerm PointStabilizerFixedSet

theorem sign_fixedPerm (G X : Type) [Group G] [MulAction G X] [Finite X]
    (x : X) (R : Subgroup (stabilizer G x)) (g : stabilizer G x)
    (hg : g ∈ Subgroup.normalizer (R : Set (stabilizer G x))) :
    let _ := Fintype.ofFinite (fixedPoints R (ofStabilizer G x))
    let _ := Classical.decEq (fixedPoints R (ofStabilizer G x))
    let _ := Fintype.ofFinite (fixedPoints (R.map (stabilizer G x).subtype) X)
    let _ := Classical.decEq (fixedPoints (R.map (stabilizer G x).subtype) X)
    Equiv.Perm.sign (fixedPerm (stabilizer G x) (ofStabilizer G x) R g hg) =
      Equiv.Perm.sign (fixedPerm G X (R.map (stabilizer G x).subtype) g.val
        (mem_normalizer_map G X x R g hg)) := by
  classical
  dsimp only
  let F := fixedPoints (R.map (stabilizer G x).subtype) X
  let E := fixedPoints R (ofStabilizer G x)
  let _ := Fintype.ofFinite E
  let _ := Fintype.ofFinite F
  let _ := Classical.decEq E
  let _ := Classical.decEq F
  let f := fixedPerm (stabilizer G x) (ofStabilizer G x) R g hg
  let h := fixedPerm G X (R.map (stabilizer G x).subtype) g.val
    (mem_normalizer_map G X x R g hg)
  let i : E → F := fun y => ⟨y.val.val, (mem_fixed_iff G X x R y.val).mp y.property⟩
  apply Equiv.Perm.sign_bij (f := f) (g := h) (fun y _ => i y)
  · intro y _ _
    apply Subtype.ext
    rfl
  · intro y z _ _ he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : F => q.val) he
  · intro y hy
    have hne : y.val ≠ x := by
      intro he
      apply hy
      apply Subtype.ext
      change g.val • y.val = y.val
      rw [he]
      exact g.property
    let z : E := ⟨⟨y.val,hne⟩, (mem_fixed_iff G X x R ⟨y.val,hne⟩).mpr y.property⟩
    refine ⟨z, ?_, rfl⟩
    intro hz
    apply hy
    apply Subtype.ext
    exact congrArg (fun q : E => q.val.val) hz

end FiveTransitive.PointStabilizerFixedSign

end CFSG
