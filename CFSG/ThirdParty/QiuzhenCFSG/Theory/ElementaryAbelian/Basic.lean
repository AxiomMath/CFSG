module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace CFSG
end CFSG
open CFSG

open scoped IsMulCommutative

/-!
# Elementary abelian p-groups

An elementary abelian `p`-group is a commutative group whose exponent divides `p`.

Public items:
- `IsElementaryAbelian`;
- exponent and order consequences: `elemPow_eq_one_of_isElementaryAbelian`,
  `IsElementaryAbelian.exponent_eq_prime`, `IsElementaryAbelian.isPGroup`;
- closure API: `IsElementaryAbelian.subgroupOf`, `.map_subtype`, `.map`,
  `.zpowers_of_pow_eq_one`;
- `IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq`.

The vector-space complement API lives in `Theory.ElementaryAbelian.VectorSpace`, and the join
lemma lives in `Theory.ElementaryAbelian.Join`.
-/

namespace CFSG.Theory.ElementaryAbelian

universe u

/-- An *elementary abelian* `p`-group: a commutative group whose exponent divides `p`. -/
public class IsElementaryAbelian (p : ℕ) (G : Type u) [Group G] : Prop
    extends IsMulCommutative G where
  exponent_dvd_p (p) (G) : Monoid.exponent G ∣ p

public lemma elemPow_eq_one_of_isElementaryAbelian {p : ℕ} {G : Type*} [Group G] {A : Subgroup G}
    [IsElementaryAbelian p A] (a : G) (ha : a ∈ A) : a ^ p = 1 := by
  simpa using congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p p A) ⟨a, ha⟩)

public theorem IsElementaryAbelian.isPGroup (p : ℕ) (G : Type u) [Group G]
    [IsElementaryAbelian p G] : IsPGroup p G :=
  fun x => ⟨1, by simpa using
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p G) x)⟩

public theorem IsElementaryAbelian.exponent_eq_prime
    {p : ℕ} {G : Type u} [Group G] [Finite G] [Nontrivial G] [Fact p.Prime]
    [IsElementaryAbelian p G] :
    Monoid.exponent G = p := by
  have hExp_dvd : Monoid.exponent G ∣ p := IsElementaryAbelian.exponent_dvd_p p G
  exact (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd (Monoid.exponent G) hExp_dvd |>.resolve_left
    (Nat.ne_of_gt Monoid.one_lt_exponent)

/-- A subgroup of an elementary abelian group, restricted to a larger subgroup, is still elementary
abelian. -/
public theorem IsElementaryAbelian.subgroupOf {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    {H K : Subgroup G} [IsElementaryAbelian p H] (_hHK : H ≤ K) :
    IsElementaryAbelian p (H.subgroupOf K) := by
  refine
    { toIsMulCommutative := Subgroup.subgroupOf_isMulCommutative (H := H) (K := K)
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
public theorem IsElementaryAbelian.map_subtype {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    {K : Subgroup G} {H : Subgroup K} [IsElementaryAbelian p H] :
    IsElementaryAbelian p (H.map K.subtype) := by
  refine
    { toIsMulCommutative := Subgroup.map_isMulCommutative (H := H) (f := K.subtype)
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
public theorem IsElementaryAbelian.map
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

public theorem IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq
    {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p A] (hcard : Nat.card A = p ^ 2) :
    ¬ IsCyclic A := by
  intro hcyc
  have hcard_exp : Monoid.exponent A = p ^ 2 := by
    rw [hcyc.exponent_eq_card, hcard]
  have hdiv : p ^ 2 ∣ p := by
    simpa [hcard_exp] using (IsElementaryAbelian.exponent_dvd_p p A)
  have : p ^ 2 ≤ p := Nat.le_of_dvd (Fact.out : Nat.Prime p).pos hdiv
  have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
  nlinarith

public theorem IsElementaryAbelian.zpowers_of_pow_eq_one
    {p : ℕ} {G : Type*} [Group G] {x : G} (hxpow : x ^ p = 1) :
    IsElementaryAbelian p (Subgroup.zpowers x) := by
  refine
    { toIsMulCommutative := Subgroup.zpowers_isMulCommutative x
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro y
  apply Subtype.ext
  have hy_dvd : orderOf ((y : Subgroup.zpowers x) : G) ∣ p := by
    exact (orderOf_dvd_of_mem_zpowers y.2).trans (orderOf_dvd_of_pow_eq_one hxpow)
  simpa using (orderOf_dvd_iff_pow_eq_one.mp hy_dvd)

end CFSG.Theory.ElementaryAbelian
