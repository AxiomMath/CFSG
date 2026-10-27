
module

public import CFSG.Sporadic.Co1.Module.OddConj
public import CFSG.Monster.GMS.Facts.Co1OddPairs
public import CFSG.Sporadic.Co1.Module.OddNativeBase

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint
open CFSG.Monster.GMS (IsCo1TwoA Co1CommonFour Co1OddType Co1OddPairFacts Co1InvolutionFacts co1Fix
  co1Orbit)

attribute [local instance] vecAct vecSMul

theorem co1Fix_eq (g : NativeSporadic.Co1) : co1Fix g = {ω : Vec24 | g • ω = ω} := rfl

theorem oddType_conj (x r s : NativeSporadic.Co1) (k : Fin 3) :
    Co1OddType (x * r * x⁻¹) (x * s * x⁻¹) k ↔ Co1OddType r s k := by
  have h1 := orderOf_conj_pair x r s
  have h2 : (co1Fix (x * r * x⁻¹) ∩ co1Fix (x * s * x⁻¹)).ncard =
      (co1Fix r ∩ co1Fix s).ncard := ncard_fixInter_conj (Ω := Vec24) x r s
  have h3 := card_centralizer_inf_conj x r s
  fin_cases k <;> simp only [Co1OddType, h1, h2, h3]

theorem oddType_unique {r s : NativeSporadic.Co1} {j k : Fin 3} (hj : Co1OddType r s j)
    (hk : Co1OddType r s k) : j = k := by
  fin_cases j <;> fin_cases k <;> simp only [Co1OddType] at hj hk <;>
    first | rfl | (exfalso; omega)

theorem oddType_cent {r s z : NativeSporadic.Co1}
    (hz : z ∈ Subgroup.centralizer ({r} : Set NativeSporadic.Co1)) (k : Fin 3) :
    Co1OddType r (z * s * z⁻¹) k ↔ Co1OddType r s k := by
  have hzr : z * r * z⁻¹ = r := conj_eq_of_mem_centralizer (G := NativeSporadic.Co1) hz
  have := oddType_conj z r s k
  rwa [hzr] at this

def OddPf (r : NativeSporadic.Co1) : Prop :=
  (∀ s, IsConj r s → s ≠ r → Odd (orderOf (r * s)) → Co1CommonFour r s →
      ∃! k, Co1OddType r s k) ∧
    (∀ k, ∃ s, IsConj r s ∧ s ≠ r ∧ Co1CommonFour r s ∧ Co1OddType r s k) ∧
    (∀ k s s', IsConj r s → IsConj r s' → Co1CommonFour r s → Co1CommonFour r s' →
      Co1OddType r s k → Co1OddType r s' k →
        ∃ g ∈ Subgroup.centralizer ({r} : Set NativeSporadic.Co1), g * s * g⁻¹ = s') ∧
    (∀ k s, k ≠ 0 → IsConj r s → Co1CommonFour r s → Co1OddType r s k →
      (∀ u ∈ co1Fix r ∩ co1Fix s, (∀ v ∈ co1Fix r ∩ co1Fix s,
          CFSG.Sporadic.Co1.Module.bil₀ u v = 0) → u = 0) ∧
      ∀ g ∈ Subgroup.centralizer ({r} : Set NativeSporadic.Co1) ⊓ Subgroup.centralizer {s},
        (∀ v ∈ co1Fix r ∩ co1Fix s, CFSG.Monster.GMS.co1Act g v = v) → g = 1)

theorem co1OddPairFacts_iff : Co1OddPairFacts ↔ ∀ r : NativeSporadic.Co1, IsCo1TwoA r → OddPf r :=
  Iff.rfl

theorem mem_co1Fix_iff (g : NativeSporadic.Co1) (v : Vec24) : v ∈ co1Fix g ↔ g • v = v := Iff.rfl

theorem gmsAct_iff (g : NativeSporadic.Co1) (v : Vec24) :
    CFSG.Monster.GMS.co1Act g v = v ↔ g • v = v := Iff.rfl

theorem mem_W_conj_iff (x r s : NativeSporadic.Co1) (v : Vec24) :
    x • v ∈ co1Fix (x * r * x⁻¹) ∩ co1Fix (x * s * x⁻¹) ↔ v ∈ co1Fix r ∩ co1Fix s := by
  simp only [Set.mem_inter_iff, mem_co1Fix_iff, smul_fix_conj_iff]

theorem mem_W_conj_iff' (x r s : NativeSporadic.Co1) (v : Vec24) :
    v ∈ co1Fix (x * r * x⁻¹) ∩ co1Fix (x * s * x⁻¹) ↔ x⁻¹ • v ∈ co1Fix r ∩ co1Fix s := by
  simp only [Set.mem_inter_iff, mem_co1Fix_iff, mem_fix_conj_iff]

end CFSG.Sporadic.Co1.Module.Odd
