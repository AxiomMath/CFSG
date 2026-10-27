module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentCentralizesOddCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The inverted subgroup misses the maximal odd core
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- An odd inverted subgroup inside a component-centralizing subgroup has
trivial intersection with the maximal subgroup's odd core. -/
public theorem secondCase_inverted_inf_oddCore_eq_bot
    {G : Type u} [Group G] [Finite G]
    {M E K : Subgroup G} (s : G)
    (hsE : s ∈ E)
    (hEcentO : E ≤ Subgroup.centralizer (oddCoreOf M : Set G))
    (hKodd : Odd (Nat.card (↥K)))
    (hKinv : ∀ x : G, x ∈ K → s * x * s⁻¹ = x⁻¹) :
    K ⊓ oddCoreOf M = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hxK : x ∈ K := hx.1
  have hxO : x ∈ oddCoreOf M := hx.2
  have hxs : s * x * s⁻¹ = x := by
    have hcomm : x * s = s * x := by
      exact Subgroup.mem_centralizer_iff.mp (hEcentO hsE) x hxO
    calc
      s * x * s⁻¹ = x * s * s⁻¹ := by rw [hcomm]
      _ = x := by group
  have hxi : s * x * s⁻¹ = x⁻¹ := hKinv x hxK
  have hxsq : x ^ 2 = 1 := by
    have hxeq : x = x⁻¹ := hxs.symm.trans hxi
    rw [pow_two]
    calc
      x * x = x⁻¹ * x := congrArg (fun z => z * x) hxeq
      _ = 1 := by simp
  let xK : K := ⟨x, hxK⟩
  have hKcop : Nat.Coprime 2 (Nat.card (↥K)) :=
    Nat.coprime_two_left.mpr hKodd
  have hxKone : xK = 1 :=
    eq_one_of_sq_eq_one_of_coprime_two (G := K) hKcop (by
      apply Subtype.ext
      simpa [xK, pow_two] using hxsq)
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxKone)

end CFSG.GorensteinWalter
