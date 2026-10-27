module

public import CFSG.RankThree.Chevalley.SteinbergBTTrialitySplitPrimePlane
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.K128.FixCenter

public section

namespace CFSG.RankThree.PartOne.K133H

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.K128 CFSG.Timmesfeld.ExceptionalOrders

set_option linter.unusedSectionVars false

section Torsion

variable {K : Type} [Field K]

theorem graphFixedRootTorus_comm (σ : K →+* K) {x y : ModGL TwistTag.D4.tag K}
    (hx : x ∈ graphFixedRootTorus TwistTag.D4 K σ)
    (hy : y ∈ graphFixedRootTorus TwistTag.D4 K σ) : x * y = y * x :=
  SteinbergBT.TrialityPlane.mul_comm_of_mem_torusGroup'
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).1
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hy).1).1

@[expose] def d4Torsion (σ : K →+* K) (p : ℕ) : Subgroup (ModGL TwistTag.D4.tag K) where
  carrier := {x | x ∈ graphFixedRootTorus TwistTag.D4 K σ ∧ x ^ p = 1}
  mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
    rw [(show Commute x y from graphFixedRootTorus_comm σ hx.1 hy.1).mul_pow, hx.2, hy.2,
      one_mul]⟩
  one_mem' := ⟨one_mem _, one_pow _⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

theorem mem_d4Torsion_iff (σ : K →+* K) (p : ℕ) {x : ModGL TwistTag.D4.tag K} :
    x ∈ d4Torsion σ p ↔ x ∈ graphFixedRootTorus TwistTag.D4 K σ ∧ x ^ p = 1 :=
  Iff.rfl

end Torsion

end CFSG.RankThree.PartOne.K133H
