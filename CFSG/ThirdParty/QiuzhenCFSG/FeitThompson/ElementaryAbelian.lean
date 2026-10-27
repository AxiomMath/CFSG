module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Algebra.Module.ZMod

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.Basic

namespace CFSG
end CFSG
open CFSG

open scoped IsMulCommutative

universe u

/-- An *elementary abelian* `p`-group: a commutative group whose exponent divides `p`. -/
public class CFSG.IsElementaryAbelian (p : ℕ) (G : Type u) [Group G] : Prop
    extends IsMulCommutative G where
  exponent_dvd_p (p) (G) : Monoid.exponent G ∣ p

public lemma CFSG.elemPow_eq_one_of_isElementaryAbelian {p : ℕ} {G : Type*} [Group G] {A : Subgroup G}
    [IsElementaryAbelian p A] (a : G) (ha : a ∈ A) : a ^ p = 1 := by
  have ha_powA : (⟨a, ha⟩ : A) ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p A) ⟨a, ha⟩
  simpa using congrArg Subtype.val ha_powA

public theorem CFSG.IsElementaryAbelian.isPGroup (p : ℕ) (G : Type u) [Group G]
    [IsElementaryAbelian p G] : IsPGroup p G :=
  fun _ => ⟨1, by
    rcases IsElementaryAbelian.exponent_dvd_p p G with ⟨_, rfl⟩
    rw [pow_one, pow_mul, Monoid.pow_exponent_eq_one, one_pow]⟩

public theorem CFSG.IsElementaryAbelian.exponent_eq_prime
    {p : ℕ} {G : Type u} [Group G] [Finite G] [Nontrivial G] [Fact p.Prime]
    [IsElementaryAbelian p G] :
    Monoid.exponent G = p := by
  have hExp_dvd : Monoid.exponent G ∣ p := IsElementaryAbelian.exponent_dvd_p p G
  exact (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd (Monoid.exponent G) hExp_dvd |>.resolve_left
    (Nat.ne_of_gt Monoid.one_lt_exponent)

public instance CFSG.IsElementaryAbelian.isVectorSpace (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [inst : IsElementaryAbelian p G] :
    Module (ZMod p) (Additive G) :=
  have hpow : ∀ g : G, g ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp inst.exponent_dvd_p
  have hsmul : ∀ x : Additive G, p • x = 0 := fun x =>
    toMul_eq_one.mp (hpow x)
  AddCommMonoid.zmodModule (M := Additive G) (n := p) hsmul

/-- For every subgroup `B` of an elementary abelian group `A`, there exists a subgroup `C` disjoint
from `B` and such that `B` and `C` generate the whole group `A`. -/
public theorem CFSG.IsElementaryAbelian.exists_isCompl (p : ℕ) [hp : Fact p.Prime]
    (A : Type u) [Group A]
    [h : IsElementaryAbelian p A] (B : Subgroup A) :
    ∃ C : Subgroup A, IsCompl B C := by
  let φ : AddSubgroup (Additive A) ≃o Submodule (ZMod p) (Additive A) :=
    AddSubgroup.toZModSubmodule (n := p)
  let ψ : AddSubgroup (Additive A) ≃o Subgroup A :=
    (AddSubgroup.toSubgroup' : AddSubgroup (Additive A) ≃o Subgroup A)
  let S : AddSubgroup (Additive A) := Subgroup.toAddSubgroup B
  let S' : Submodule (ZMod p) (Additive A) := φ S
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl S'
  let T : AddSubgroup (Additive A) := φ.symm C'
  let C : Subgroup A := ψ T
  have hcompl_add : IsCompl S T := by
    have : IsCompl (φ S) (φ T) := isCompl_comm.mp (id (IsCompl.symm hC'))
    exact (φ.isCompl_iff).mpr this
  have hcompl : IsCompl B C :=
    IsCompl.of_orderEmbedding (RelIso.toRelEmbedding Subgroup.toAddSubgroup) hcompl_add
  exact ⟨C, hcompl⟩

/-- A subgroup of an elementary abelian group, restricted to a larger subgroup, is still elementary
abelian. -/
public theorem CFSG.IsElementaryAbelian.subgroupOf {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    {H K : Subgroup G} [IsElementaryAbelian p H] (_hHK : H ≤ K) :
    IsElementaryAbelian p (H.subgroupOf K) := by
  refine
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  apply Subtype.ext
  let xH : H := ⟨((x : H.subgroupOf K) : K), Subgroup.mem_subgroupOf.mp x.2⟩
  have hxpow : xH ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p H) xH
  simpa [xH] using congrArg (fun y : H => ((y : H) : G)) hxpow

/-- The image of an elementary abelian subgroup under the subtype map into the ambient group is
still elementary abelian. -/
public theorem CFSG.IsElementaryAbelian.map_subtype {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    {K : Subgroup G} {H : Subgroup K} [IsElementaryAbelian p H] :
    IsElementaryAbelian p (H.map K.subtype) := by
  refine
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  rcases Subgroup.mem_map.mp x.2 with ⟨y, hy, hyx⟩
  have hypow : (⟨y, hy⟩ : H) ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p H) ⟨y, hy⟩
  have hy_pow_G : ((y : G) ^ p) = 1 := by
    simpa using congrArg (fun (z : H) => ((z : H) : G)) hypow
  have hx_eq : (x : G) = (y : G) := hyx.symm
  simpa [hx_eq] using hy_pow_G

/-- The image of an elementary abelian subgroup under a homomorphism is elementary abelian. -/
public theorem CFSG.IsElementaryAbelian.map
    {p : ℕ} [Fact p.Prime] {R S : Type*} [Group R] [Group S]
    {A : Subgroup R} [IsElementaryAbelian p A] (f : R →* S) :
    IsElementaryAbelian p (A.map f) := by
  refine
    { toIsMulCommutative := by
        simpa using (Subgroup.map_isMulCommutative (f := f) (H := A))
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  rcases Subgroup.mem_map.mp x.2 with ⟨y, hyA, hyx⟩
  let yA : A := ⟨y, hyA⟩
  have hypow : yA ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p A) yA
  have hx_eq : (x : S) = f y := by simpa using hyx.symm
  calc
    (x : S) ^ p = (f y) ^ p := by simp [hx_eq]
    _ = f (y ^ p) := by simp
    _ = 1 := by simpa using congrArg f (congrArg Subtype.val hypow)

public theorem CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq
    {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p A] (hcard : Nat.card A = p ^ 2) :
    ¬ IsCyclic A := by
  intro hcyc
  have hdiv : p ^ 2 ∣ p ^ 1 := by
    simpa [hcard] using (show Nat.card A ∣ p from by
      rw [← hcyc.exponent_eq_card]
      exact IsElementaryAbelian.exponent_dvd_p p A)
  have hp_one_lt : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have : 2 ≤ 1 :=
    (Nat.pow_le_pow_iff_right hp_one_lt).mp (Nat.le_of_dvd (by positivity) hdiv)
  omega

public theorem CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one
    {p : ℕ} {G : Type*} [Group G] {x : G} (hxpow : x ^ p = 1) :
    IsElementaryAbelian p (Subgroup.zpowers x) := by
  refine
    { toIsMulCommutative := by infer_instance
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro y
  apply Subtype.ext
  have hy_dvd : orderOf ((y : Subgroup.zpowers x) : G) ∣ p := by
    exact (orderOf_dvd_of_mem_zpowers y.2).trans (orderOf_dvd_of_pow_eq_one hxpow)
  simpa using (orderOf_dvd_iff_pow_eq_one.mp hy_dvd)

public theorem CFSG.IsElementaryAbelian.sup_of_le_centralizer
    {p : ℕ} {G : Type*} [Group G] {E C : Subgroup G}
    [IsElementaryAbelian p E] [IsElementaryAbelian p C]
    (hCE : C ≤ Subgroup.centralizer (E : Set G)) :
    IsElementaryAbelian p ↥(E ⊔ C : Subgroup G) := by
  classical
  let s : Set G := (E : Set G) ∪ (C : Set G)
  have hcomm_s : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    intro x hx y hy
    rcases hx with hxE | hxC
    · rcases hy with hyE | hyC
      · simpa using congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := E)).comm ⟨x, hxE⟩ ⟨y, hyE⟩)
      · exact (Subgroup.mem_centralizer_iff.mp (hCE hyC)) x hxE
    · rcases hy with hyE | hyC
      · exact ((Subgroup.mem_centralizer_iff.mp (hCE hxC)) y hyE).symm
      · simpa using congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := C)).comm ⟨x, hxC⟩ ⟨y, hyC⟩)
  have hsup : E ⊔ C = Subgroup.closure s := by
    simpa [s] using (Subgroup.sup_eq_closure E C)
  refine
    { toIsMulCommutative := by
        rw [hsup]
        exact Subgroup.isMulCommutative_closure (fun x hx y hy _ => hcomm_s x hx y hy)
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  have hxcl : (x : G) ∈ Subgroup.closure s := by
    simpa [hsup] using x.property
  exact
    Subgroup.closure_induction (k := s)
      (p := fun z _hz => z ^ p = 1) (x := (x : G)) (by
        intro y hy
        rcases hy with hyE | hyC
        · have hypow : (⟨y, hyE⟩ : E) ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p E) ⟨y, hyE⟩
          simpa using congrArg Subtype.val hypow
        · have hypow : (⟨y, hyC⟩ : C) ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p C) ⟨y, hyC⟩
          simpa using congrArg Subtype.val hypow) (by simp) (by
        intro y z hy hz hypow hzpow
        have hyz_comm : Commute y z := by
          let : IsMulCommutative ↥(Subgroup.closure s) :=
            Subgroup.isMulCommutative_closure (fun x hx y hy _ => hcomm_s x hx y hy)
          show y * z = z * y
          simpa using congrArg Subtype.val
            (mul_comm (⟨y, hy⟩ : Subgroup.closure s) (⟨z, hz⟩ : Subgroup.closure s))
        calc
          (y * z) ^ p = y ^ p * z ^ p := by simpa using hyz_comm.mul_pow p
          _ = 1 := by simp [hypow, hzpow]) (by
        intro y _hy hypow
        simpa [inv_pow] using congrArg Inv.inv hypow) hxcl
