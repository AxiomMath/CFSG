module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocZperf

public section

namespace CFSG.Quasithin.H13.F431.D4q.Loc

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

set_option linter.unusedSectionVars false


section Zsq

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem sq_of_mem_centerOf (hK4 : 4 ≤ Nat.card K) {x : Cm σ}
    (hx : x ∈ centerOf (perfectCore (Pst0 σ))) : x * x = 1 := by
  have hP0C : P0 σ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolic_le _ _ _ _
  have h := (CFSG.Quasithin.H13.Sec53F.TriD4.mem_centerOf_subgroupOf_iff hP0C x).1 hx
  obtain ⟨f, hf⟩ := CFSG.Quasithin.H13.Sec53F.TriD4.centerOf_perfectCore_P0_form σ
    (toRingHom_pow_three_d4 σ hσ) hK4 h
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, hf]
  exact d4x₆_mul_self K f

include hσ in
theorem centerOf_Ust_le (hK4 : 4 ≤ Nat.card K) {u : Cm σ} (hu : u ∈ Ust σ)
    (hc : ∀ v ∈ Ust σ, u * v = v * u) : u ∈ centerOf (perfectCore (Pst0 σ)) := by
  obtain ⟨f, hf, hu'⟩ := centre_Ust σ hσ hu fun v hv => hc v hv
  exact d4x₆_mem_centerOf_perfectCore_Pst0 σ hσ hK4 hf hu'

end Zsq

end CFSG.Quasithin.H13.F431.D4q.Loc
