module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralOddRotationCentralizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Klein-four centralizers in a reflected cyclic join

An odd-order subgroup of a generalized dihedral join lies in the cyclic
rotation subgroup.  If a Klein four in the same join centralizes that odd
subgroup, every element of the Klein four is also forced into the cyclic
rotation subgroup, which is impossible.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A Klein four contained in a reflected cyclic join cannot centralize a
nontrivial odd-order subgroup contained in the same join. -/
public theorem no_kleinFour_centralizes_odd_subgroup_of_reflected_cyclic_join
    {G : Type u} [Group G] [Finite G]
    (U A V : Subgroup G) (w : G)
    (hUcyc : IsCyclic U) (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hAle : A ≤ U ⊔ Subgroup.zpowers w)
    (hVle : V ≤ U ⊔ Subgroup.zpowers w)
    (hAne : A ≠ ⊥) (hAodd : Odd (Nat.card A))
    (hVK : IsKleinFour V)
    (hVcent : V ≤ Subgroup.centralizer (A : Set G)) :
    False := by
  classical
  have hAorder : ∀ a : G, a ∈ A → Odd (orderOf a) := by
    intro a ha
    exact Odd.of_dvd_nat hAodd (Subgroup.orderOf_dvd_natCard A ha)
  have hAleU : A ≤ U := by
    intro a ha
    rcases (mem_sup_zpowers_of_involution_inverts hwU hwsq hwinv).mp (hAle ha) with
      ⟨u, hu, haU | haw⟩
    · simpa [haU] using hu
    · have hasq : a * a = 1 := by
        rw [haw]
        calc
          (u * w) * (u * w) = u * (w * u * w⁻¹) * (w * w) := by group
          _ = u * u⁻¹ * (w * w) := by rw [hwinv u hu]
          _ = 1 := by rw [hwsq]; simp
      have hord2 : orderOf a ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hasq)
      have hordodd : Odd (orderOf a) := hAorder a ha
      have hord1 : orderOf a = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
        · exact h
        · exfalso
          exact hordodd.not_two_dvd_nat (by rw [h])
      have haone : a = 1 := orderOf_eq_one_iff.mp hord1
      simpa [haone] using U.one_mem
  have hVleU : V ≤ U := by
    intro v hv
    rcases (mem_sup_zpowers_of_involution_inverts hwU hwsq hwinv).mp (hVle hv) with
      ⟨u, hu, hvU | hvw⟩
    · simpa [hvU] using hu
    · exfalso
      obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
      have haA : (a : G) ∈ A := a.2
      have haU : (a : G) ∈ U := hAleU haA
      have haodd : Odd (orderOf (a : G)) := hAorder (a : G) haA
      have hvcomm : (u * w) * (a : G) = (a : G) * (u * w) := by
        have hcomm :=
          (Subgroup.mem_centralizer_iff.mp (hVcent hv)) (a : G) haA
        rw [hvw] at hcomm
        exact hcomm.symm
      have hfix : (u * w) * (a : G) * (u * w)⁻¹ = (a : G) := by
        calc
          (u * w) * (a : G) * (u * w)⁻¹ =
              (a : G) * (u * w) * (u * w)⁻¹ := by rw [hvcomm]
          _ = (a : G) := by group
      have hinv : (u * w) * (a : G) * (u * w)⁻¹ = (a : G)⁻¹ := by
        let : CommGroup U := IsCyclic.commGroup
        have hucomm : u * (a : G)⁻¹ = (a : G)⁻¹ * u :=
          congrArg Subtype.val
            (mul_comm (⟨u, hu⟩ : U) (⟨(a : G), haU⟩ : U)⁻¹)
        calc
          (u * w) * (a : G) * (u * w)⁻¹ =
              u * (w * (a : G) * w⁻¹) * u⁻¹ := by group
          _ = u * (a : G)⁻¹ * u⁻¹ := by rw [hwinv (a : G) haU]
          _ = (a : G)⁻¹ := by rw [hucomm]; group
      have ha_inv : (a : G) = (a : G)⁻¹ := hfix.symm.trans hinv
      have hasq : (a : G) ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 2 [ha_inv]
        simp
      have hord2 : orderOf (a : G) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one hasq
      have hordne1 : orderOf (a : G) ≠ 1 := by
        intro h
        exact ha1 (Subtype.ext (orderOf_eq_one_iff.mp h))
      rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
      · exact hordne1 h
      · exact haodd.not_two_dvd_nat (by rw [h])
  have hVcyc : IsCyclic V := Subgroup.isCyclic_of_le hVleU
  exact hVK.not_isCyclic hVcyc

end CFSG.GorensteinWalter
