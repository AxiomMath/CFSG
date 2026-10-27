module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.ElementaryAbelian.Basic

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace CFSG
end CFSG
open CFSG

/-!
# Elementary abelian p-groups as vector spaces

An elementary abelian `p`-group carries a `ZMod p`-vector space structure on its additive
group, and every subgroup has a complement.

Public items:
- `IsElementaryAbelian.isVectorSpace`
- `IsElementaryAbelian.exists_isCompl`
-/

namespace CFSG.Theory.ElementaryAbelian

open scoped IsMulCommutative

universe u

public instance IsElementaryAbelian.isVectorSpace (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [inst : IsElementaryAbelian p G] :
    Module (ZMod p) (Additive G) :=
  have hpow : ∀ g : G, g ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp inst.exponent_dvd_p
  have hsmul : ∀ x : Additive G, p • x = 0 := fun x =>
    toMul_eq_one.mp (hpow x)
  AddCommMonoid.zmodModule (M := Additive G) (n := p) hsmul

/-- For every subgroup `B` of an elementary abelian group `A`, there exists a subgroup `C` disjoint
from `B` and such that `B` and `C` generate the whole group `A`. -/
public theorem IsElementaryAbelian.exists_isCompl (p : ℕ) [hp : Fact p.Prime]
    (A : Type u) [Group A]
    [h : IsElementaryAbelian p A] (B : Subgroup A) :
    ∃ C : Subgroup A, IsCompl B C := by
  letI : Module (ZMod p) (Additive A) := IsElementaryAbelian.isVectorSpace (p := p) (G := A)
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

end CFSG.Theory.ElementaryAbelian
