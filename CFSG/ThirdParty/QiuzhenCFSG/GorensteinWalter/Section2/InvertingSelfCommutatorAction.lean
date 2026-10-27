module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas

namespace CFSG
end CFSG
open CFSG

/-!
# An inverting operator centralizes a self-commutator action

If an element `t` acts by inversion on an abelian group and a subgroup `U`
of the operator group satisfies `[U,⟨t⟩]=U`, then `U` acts trivially.  This
is the small automorphism calculation used in the solvable odd-`p` branch
of Bender 1970, §2.4.
-/

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

universe u v

private theorem actsTrivially_on_subgroup_of_self_commutator_of_action_commutes
    {A V : Type*} [Group A] [Group V] [MulDistribMulAction A V]
    (U Q : Subgroup A)
    (hUcomm : ⁅U, Q⁆ = U)
    (hcommutes : ∀ u : A, u ∈ U → ∀ q : A, q ∈ Q →
      Commute (MulDistribMulAction.toMulAut A V u)
        (MulDistribMulAction.toMulAut A V q)) :
    ∀ u : U, ∀ v : V, (u : A) • v = v := by
  let φ : A →* MulAut V := MulDistribMulAction.toMulAut A V
  have hcomm_le : ⁅U, Q⁆ ≤ φ.ker := by
    rw [Subgroup.commutator_le]
    intro u hu q hq
    change φ ⁅u, q⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (hcommutes u hu q hq)
  have hU_le : U ≤ φ.ker := by simpa [hUcomm] using hcomm_le
  intro u v
  have hu_one : φ (u : A) = 1 := by
    simpa [MonoidHom.mem_ker] using hU_le u.property
  simpa [φ, MulDistribMulAction.toMulAut_apply] using
    congrArg (fun f : MulAut V => f v) hu_one

private theorem action_commutes_with_zpowers_of_inverts
    {A V : Type*} [Group A] [CommGroup V] [MulDistribMulAction A V]
    (U : Subgroup A) (t : A)
    (hinverts : ∀ v : V, t • v = v⁻¹) :
    ∀ u : A, u ∈ U → ∀ q : A, q ∈ Subgroup.zpowers t →
      Commute (MulDistribMulAction.toMulAut A V u)
        (MulDistribMulAction.toMulAut A V q) := by
  let φ : A →* MulAut V := MulDistribMulAction.toMulAut A V
  intro u _hu q hq
  have hut : Commute (φ u) (φ t) := by
    ext v
    change u • (t • v) = t • (u • v)
    calc
      u • (t • v) = u • v⁻¹ := by rw [hinverts v]
      _ = (u • v)⁻¹ := by
        change φ u v⁻¹ = (φ u v)⁻¹
        exact (φ u).map_inv v
      _ = t • (u • v) := (hinverts (u • v)).symm
  rcases Subgroup.mem_zpowers_iff.mp hq with ⟨n, rfl⟩
  have hpow : φ (t ^ n) = (φ t) ^ n := map_zpow φ t n
  rw [hpow]
  exact hut.zpow_right n

/-- If `t` acts by inversion on an abelian group and `[U,⟨t⟩]=U`, then
every element of `U` acts trivially. -/
public theorem selfCommutator_actsTrivially_of_inverts
    {A V : Type*} [Group A] [CommGroup V] [MulDistribMulAction A V]
    (U : Subgroup A) (t : A)
    (hUcomm : ⁅U, Subgroup.zpowers t⁆ = U)
    (hinverts : ∀ v : V, t • v = v⁻¹) :
    ∀ u : U, ∀ v : V, (u : A) • v = v := by
  apply actsTrivially_on_subgroup_of_self_commutator_of_action_commutes
    U (Subgroup.zpowers t) hUcomm
  exact action_commutes_with_zpowers_of_inverts U t hinverts

end CFSG.GorensteinWalter
