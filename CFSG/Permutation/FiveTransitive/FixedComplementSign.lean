module

public import CFSG.Permutation.FiveTransitive.NormalizerFixedComplement
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.FixedComplementSign

open MulAction
open scoped Classical

theorem sign_product
    {G X : Type*} [Group G] [Fintype X] [DecidableEq X] [MulAction G X]
    (Q : Subgroup G) (x : FixedNormalizerAction.Normalizer Q) :
    letI := Fintype.ofFinite (FixedNormalizerAction.Fixed (X := X) Q)
    letI := Fintype.ofFinite (NormalizerFixedComplement.Domain (X := X) Q)
    (toPerm x : Equiv.Perm (FixedNormalizerAction.Fixed (X := X) Q)).sign *
      (toPerm x : Equiv.Perm (NormalizerFixedComplement.Domain (X := X) Q)).sign =
      (toPerm x.val : Equiv.Perm X).sign := by
  classical
  let _ := Fintype.ofFinite (FixedNormalizerAction.Fixed (X := X) Q)
  let _ := Fintype.ofFinite (NormalizerFixedComplement.Domain (X := X) Q)
  let _ := Fintype.ofFinite (fixedPoints Q X)
  let E : FixedNormalizerAction.Fixed (X := X) Q ≃ fixedPoints Q X :=
    Set.equivOfEq (FixedNormalizerAction.fixed_eq Q)
  let l : Equiv.Perm (FixedNormalizerAction.Fixed (X := X) Q) := toPerm x
  let u : Equiv.Perm (fixedPoints Q X) := E.permCongr l
  let v : Equiv.Perm {t : X // t ∉ fixedPoints Q X} :=
    (toPerm x : Equiv.Perm (NormalizerFixedComplement.Domain (X := X) Q))
  have hE (t : FixedNormalizerAction.Fixed (X := X) Q) : (E t).val = t.val := rfl
  have hEinv (t : fixedPoints Q X) : (E.symm t).val = t.val := rfl
  have hu (t : fixedPoints Q X) : (u t).val = x.val • t.val := by
    change (E (l (E.symm t))).val = x.val • t.val
    rw [hE]
    change x.val • (E.symm t).val = x.val • t.val
    rw [hEinv]
  have heq : u.subtypeCongr v = (toPerm x.val : Equiv.Perm X) := by
    ext t
    rw [Equiv.Perm.subtypeCongr.apply]
    split
    · exact hu _
    · rfl
  calc
    _ = u.sign * v.sign := by rw [Equiv.Perm.sign_permCongr]; congr 3; exact Subsingleton.elim _ _
    _ = (u.subtypeCongr v).sign := by rw [Equiv.Perm.sign_subtypeCongr]; congr 3; exact Subsingleton.elim _ _
    _ = _ := congrArg Equiv.Perm.sign heq

theorem complement_odd
    {G X : Type*} [Group G] [Fintype X] [DecidableEq X] [MulAction G X]
    (Q : Subgroup G) (x : FixedNormalizerAction.Normalizer Q)
    (heven : (toPerm x.val : Equiv.Perm X).sign = 1)
    (hlocal : letI := Fintype.ofFinite (FixedNormalizerAction.Fixed (X := X) Q)
      (toPerm x : Equiv.Perm (FixedNormalizerAction.Fixed (X := X) Q)).sign = -1) :
    letI := Fintype.ofFinite (NormalizerFixedComplement.Domain (X := X) Q)
    (toPerm x : Equiv.Perm (NormalizerFixedComplement.Domain (X := X) Q)).sign = -1 := by
  classical
  let _ := Fintype.ofFinite (FixedNormalizerAction.Fixed (X := X) Q)
  let _ := Fintype.ofFinite (NormalizerFixedComplement.Domain (X := X) Q)
  have hs := sign_product (X := X) Q x
  rw [heven, hlocal] at hs
  have hh := congrArg (fun u : ℤˣ => (-1) * u) hs
  simpa using hh

end FiveTransitive.FixedComplementSign

end CFSG
