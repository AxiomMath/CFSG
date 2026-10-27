module

public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.Background.D1Statement
public import CFSG.Quasithin.Background.F8Basic

import CFSG.Quasithin.Recognition.Stroth.L2ChiefNatural

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open
open scoped commutatorElement

theorem eq_one_of_commutatorElement_eq_one_of_natural {G : Type} [Group G] [Finite G]
    {H V A : Subgroup G} {m : ℕ} (hm2 : 2 ≤ m)
    (hL2 : IsL2Quot m (oTwoQuot ↥H)) (hV : IsElemAbelian 2 V) (hVH : V ≤ H)
    (hstep : IsChiefStep H V ⊥ V) (hnc : ¬ IsCentralStep H ⊥ V)
    (hA : IsElemAbelian 2 A) (hAH : A ≤ H)
    (hstep_eq : (centralizerMod ⊥ V A).relIndex V = 2 ^ m)
    (hA_eq : (A ⊓ pCoreOf 2 H).relIndex A = 2 ^ m)
    {ω : G} (hω : ω ∈ H) (hodd : Odd (orderOf ω)) (hωO : ω ∉ pCoreOf 2 H)
    {z : G} (hz : z ∈ V) (hzω : ⁅z, ω⁆ = 1) : z = 1 := by
  have hnat := isNaturalChiefStep_of_eq hm2 hL2 hV hVH hstep hnc hA hAH hstep_eq hA_eq
  have hxd : ω * z * ω⁻¹ * z⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [Subgroup.mem_bot, ← commutatorElement_def, ← commutatorElement_inv, hzω, inv_one]
  exact Subgroup.mem_bot.mp (mem_of_conj_mem_of_isNaturalChiefStep hnat hω hωO hodd hz hxd)

end CFSG.Quasithin.Stroth

end
