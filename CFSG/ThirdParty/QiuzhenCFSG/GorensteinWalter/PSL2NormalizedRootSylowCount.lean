module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2FixedPointBound
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Root Sylows normalized by a PSL₂ element

A nonidentity element of `PSL₂(K)` normalizes at most two defining-
characteristic Sylow subgroups, because those Sylows are equivariantly
parametrized by the projective line.
-/

noncomputable section
namespace CFSG.GorensteinWalter

open scoped LinearAlgebra.Projectivization MatrixGroups

universe u

/-- A nonidentity PSL₂ element normalizes at most two defining-characteristic
Sylow subgroups. -/
public theorem psl2_normalized_rootSylow_card_le_two
    (K : Type u) [Field K] [Finite K]
    {r f : ℕ} [Fact r.Prime] (hKcard : Nat.card K = r ^ f)
    (g : PSL2 K) (hg : g ≠ 1) :
    Nat.card {S : Sylow r (PSL2 K) //
      g ∈ Subgroup.normalizer ((S : Subgroup (PSL2 K)) : Set (PSL2 K))} ≤ 2 := by
  classical
  let e := psl2ProjectiveLineEquivSylow K hKcard
  let Roots := {S : Sylow r (PSL2 K) //
    g ∈ Subgroup.normalizer ((S : Subgroup (PSL2 K)) : Set (PSL2 K))}
  let Fixed := {x : PSL2ProjectiveLine K // g • x = x}
  have hfix : ∀ S : Roots, g • e.symm S.1 = e.symm S.1 := by
    intro S
    rw [← MulAction.mem_stabilizer_iff]
    rw [psl2ProjectiveLineEquivSylow_stabilizer K hKcard]
    simpa [e] using S.2
  let toFixed : Roots → Fixed := fun S => ⟨e.symm S.1, hfix S⟩
  have hinj : Function.Injective toFixed := by
    intro S T h
    apply Subtype.ext
    apply e.symm.injective
    exact congrArg Subtype.val h
  calc
    Nat.card Roots ≤ Nat.card Fixed :=
      Nat.card_le_card_of_injective toFixed hinj
    _ ≤ 2 := psl2_fixedPoint_card_le_two K g hg

end CFSG.GorensteinWalter
