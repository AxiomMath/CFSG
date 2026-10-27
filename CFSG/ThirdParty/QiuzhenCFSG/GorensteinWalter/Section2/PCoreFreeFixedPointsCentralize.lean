module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PSubgroupInfNormalNilpotentLePCore

namespace CFSG
end CFSG
open CFSG

/-!
# Fixed points in a normal nilpotent subgroup centralize a core-free
`p`-subgroup

When `O_p(X)=1`, a `p`-subgroup meets every normal nilpotent subgroup
trivially.  Thus any fixed point that normalizes the `p`-subgroup must
centralize it.
-/

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

universe u

/-- Let `F ◁ X` be nilpotent and let `U` be a `p`-subgroup with
`O_p(X)=1`.  If the centralizer of `t` normalizes `U`, then every element of
`F` fixed by `t` centralizes `U`. -/
public theorem normal_nilpotent_fixedPoints_le_centralizer_of_pCore_eq_bot
    {X : Type u} [Group X] [Finite X]
    (U F : Subgroup X) (p : ℕ) {t : X}
    (hp : p.Prime)
    (hUp : IsPGroup p U)
    (hFnormal : F.Normal)
    (hFnil : Group.IsNilpotent F)
    (hpCore : pCore p X = ⊥)
    (hUinv : Subgroup.centralizer ({t} : Set X) ≤
      Subgroup.normalizer (U : Set X)) :
    F ⊓ Subgroup.centralizer ({t} : Set X) ≤
      F ⊓ Subgroup.centralizer (U : Set X) := by
  have hIFleCore : U ⊓ F ≤ pCore p X :=
    pSubgroup_inf_normal_nilpotent_le_pCore U F p hp hUp hFnormal hFnil
  have hIFbot : U ⊓ F = ⊥ := by
    apply le_antisymm
    · exact hIFleCore.trans (le_of_eq hpCore)
    · exact bot_le
  intro c hc
  refine ⟨hc.1, ?_⟩
  change c ∈ Subgroup.centralizer (U : Set X)
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hcNormU : c ∈ Subgroup.normalizer (U : Set X) := hUinv hc.2
  have hcuU : c * u * c⁻¹ ∈ U :=
    ((Subgroup.mem_normalizer_iff.mp hcNormU) u).mp hu
  have hcommU : ⁅c, u⁆ ∈ U := by
    rw [commutatorElement_def]
    exact U.mul_mem hcuU (U.inv_mem hu)
  have hucF : u * c⁻¹ * u⁻¹ ∈ F :=
    hFnormal.conj_mem c⁻¹ (F.inv_mem hc.1) u
  have hcommF : ⁅c, u⁆ ∈ F := by
    simpa [commutatorElement_def, mul_assoc] using F.mul_mem hc.1 hucF
  have hcommOne : ⁅c, u⁆ = 1 := by
    have hmem : ⁅c, u⁆ ∈ U ⊓ F := ⟨hcommU, hcommF⟩
    rw [hIFbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact
    ((commutatorElement_eq_one_iff_mul_comm (g₁ := c) (g₂ := u)).mp
      hcommOne).symm

end CFSG.GorensteinWalter
