module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
public import Mathlib.GroupTheory.IsPerfect

namespace CFSG
end CFSG
open CFSG

/-!
# Perfect subgroups lie in the two-residual

A perfect subgroup has trivial image in every `2`-group quotient.  Therefore
it lies in the intersection of all normal subgroups of `2`-power index.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A perfect subgroup of `H` lies in `O²(H)`. -/
public theorem perfect_subgroup_le_twoResidualOf
    {G : Type u} [Group G] [Finite G]
    (H K : Subgroup G) (hKH : K ≤ H) (hKperf : Group.IsPerfect K) :
    K ≤ twoResidualOf H := by
  classical
  change K ≤ pResidualOf H 2
  let R : Subgroup G := pResidualOf H 2
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : (R.subgroupOf H).Normal := by
    dsimp [R]
    exact fstar_pResidualOf_subgroupOf_normal H 2
  let K' : Subgroup H := K.subgroupOf H
  have hK'perf : Group.IsPerfect K' := by
    let e : K' ≃* K := Subgroup.subgroupOfEquivOfLe hKH
    exact Group.IsPerfect.ofSurjective
      (G := K) (G' := K') (f := e.symm.toMonoidHom) e.symm.surjective
  let q : H →* H ⧸ R.subgroupOf H := QuotientGroup.mk' (R.subgroupOf H)
  let I : Subgroup (H ⧸ R.subgroupOf H) := K'.map q
  have hIp : IsPGroup 2 I := by
    have hQp : IsPGroup 2 (H ⧸ R.subgroupOf H) :=
      fstar_isPGroup_quotient_pResidualOf H 2 Nat.prime_two
    exact hQp.to_subgroup I
  have hIperf : Group.IsPerfect I := by
    dsimp [I]
    let : Group.IsPerfect K' := hK'perf
    exact Group.IsPerfect.map q
  have hIbot : I = ⊥ := by
    by_contra hIne
    have : Nontrivial I := (Subgroup.nontrivial_iff_ne_bot I).2 hIne
    let : Group.IsPerfect I := hIperf
    have hInil : Group.IsNilpotent I := hIp.isNilpotent
    exact (Group.IsPerfect.not_isNilpotent (G := I)) hInil
  intro x hx
  have hqx : q ⟨x, hKH hx⟩ = 1 := by
    have hmem : q ⟨x, hKH hx⟩ ∈ I :=
      Subgroup.mem_map.mpr
        ⟨⟨x, hKH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    exact Subgroup.mem_bot.mp (by simpa [hIbot] using hmem)
  have hxR : (⟨x, hKH hx⟩ : H) ∈ R.subgroupOf H :=
    (QuotientGroup.eq_one_iff (N := R.subgroupOf H)
      (x := ⟨x, hKH hx⟩)).1 hqx
  exact Subgroup.mem_subgroupOf.mp hxR

end CFSG.GorensteinWalter
