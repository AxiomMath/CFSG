module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Klein four subgroups are self-centralizing in odd PGL2

The odd part of a Klein-four centralizer is excluded by the reflected-torus
theorem.  The remaining centralizer is a 2-group, so a dihedral Sylow model
reduces its centralizer to the Klein four itself.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open scoped MatrixGroups

universe u

/-- Every Klein four subgroup of `PGL2(K)` over an odd finite field is
self-centralizing. -/
public theorem pgl2_kleinFour_centralizer_eq_self
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (V : Subgroup (PGL2 K)) (hVK : IsKleinFour V) :
    Subgroup.centralizer (V : Set (PGL2 K)) = V := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let C : Subgroup (PGL2 K) := Subgroup.centralizer (V : Set (PGL2 K))
  let : IsKleinFour V := hVK
  let : IsMulCommutative V := IsKleinFour.isMulCommutative
  have hVleC : V ≤ C := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val
      ((IsKleinFour.isMulCommutative (G := V)).is_comm.comm
        ⟨w, hw⟩ ⟨v, hv⟩)
  have hCtwo : IsPGroup 2 C := by
    apply isPGroup_of_primeFactors_subset_singleton C Nat.prime_two
    intro r hr
    have hrprime : r.Prime := Nat.prime_of_mem_primeFactors hr
    by_contra hrne
    have hrodd : Odd r := hrprime.odd_of_ne_two hrne
    let : Fintype C := Fintype.ofFinite C
    let : Fact r.Prime := ⟨hrprime⟩
    have hrdiv : r ∣ Fintype.card C := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.dvd_of_mem_primeFactors hr
    obtain ⟨x, hxorder⟩ := exists_prime_orderOf_dvd_card (G := C) r hrdiv
    let a : PGL2 K := x
    let A : Subgroup (PGL2 K) := Subgroup.zpowers a
    have haorder : orderOf a = r := by
      exact (Subgroup.orderOf_coe x).trans hxorder
    have hAcyc : IsCyclic A := Subgroup.isCyclic_zpowers a
    have hAne : A ≠ ⊥ := by
      intro hbot
      have haA : a ∈ A := Subgroup.mem_zpowers a
      have haone : a = 1 := by
        rw [hbot] at haA
        exact Subgroup.mem_bot.mp haA
      have : orderOf a = 1 := by rw [haone]; simp
      rw [haorder] at this
      exact hrprime.ne_one this
    have hAodd : Odd (Nat.card A) := by
      rw [Nat.card_zpowers, haorder]
      exact hrodd
    have hVcent : V ≤ Subgroup.centralizer (A : Set (PGL2 K)) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
      have hxa : a ∈ C := x.property
      have hcomm : Commute v a := by
        exact (Subgroup.mem_centralizer_iff.mp hxa) v hv
      exact (hcomm.zpow_right n).eq.symm
    exact pgl2_no_kleinFour_centralizes_odd_cyclic
      K hK A V hAcyc hAne hAodd hVK hVcent
  obtain ⟨S, hCleS⟩ := hCtwo.exists_le_sylow
  have hVleS : V ≤ (S : Subgroup (PGL2 K)) := hVleC.trans hCleS
  let VS : Subgroup S := V.subgroupOf (S : Subgroup (PGL2 K))
  have hVSK : IsKleinFour VS := isKleinFour_subgroupOf hVleS hVK
  obtain ⟨m, hm, ⟨eS⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model K hK S
  have hcentS : Subgroup.centralizer (VS : Set S) ≤ VS :=
    centralizer_kleinFour_le_of_dihedral_mulEquiv hm eS VS hVSK
  apply le_antisymm
  · intro x hx
    have hxS : x ∈ (S : Subgroup (PGL2 K)) := hCleS hx
    let xS : S := ⟨x, hxS⟩
    have hxcentS : xS ∈ Subgroup.centralizer (VS : Set S) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hx) (v : PGL2 K)
        (Subgroup.mem_subgroupOf.mp hv)
    exact Subgroup.mem_subgroupOf.mp (hcentS hxcentS)
  · exact hVleC

end CFSG.GorensteinWalter
