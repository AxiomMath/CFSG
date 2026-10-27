module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.SubnormalPSubgroupLeQCore

namespace CFSG
end CFSG
open CFSG

/-!
# A subnormal commutator of a `p`-subgroup lies in the `p`-core

This isolates the formal endpoint after Bender 1970, §2.4 supplies
subnormality of the invariant commutator.
-/

namespace CFSG.GorensteinWalter

universe u

/-- If `Q` normalizes a `p`-subgroup `P ≤ B` and `[P,Q]` is subnormal in
`B`, then `[P,Q] ≤ O_p(B)`. -/
public theorem commutator_le_qCoreOf_of_isSubnormal
    {G : Type u} [Group G] [Finite G]
    (B P Q : Subgroup G) (p : ℕ)
    (hPB : P ≤ B) (hPp : IsPGroup p P)
    (hQP : Q ≤ Subgroup.normalizer (P : Set G))
    (hsub : ((⁅P, Q⁆ : Subgroup G).subgroupOf B).IsSubnormal) :
    ⁅P, Q⁆ ≤ qCoreOf B p := by
  let C : Subgroup G := ⁅P, Q⁆
  have hCleP : C ≤ P := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hynorm : y ∈ Subgroup.normalizer (P : Set G) := hQP hy
    have hconj : y * x⁻¹ * y⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hynorm x⁻¹).1 (P.inv_mem hx)
    simpa [C, commutatorElement_def, mul_assoc] using P.mul_mem hx hconj
  have hCB : C ≤ B := hCleP.trans hPB
  have hCp : IsPGroup p C :=
    (hPp.to_subgroup (C.subgroupOf P)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hCleP)
  exact le_qCoreOf_of_isSubnormal_isPGroup B C p hCB (by simpa [C] using hsub) hCp

end CFSG.GorensteinWalter
