module

import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSThreeFStar
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSThreeSThree
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSThreeQuot
public import CFSG.Assembly.Defs
public import CFSG.Foundations.Basic

public section

namespace CFSG.StandardType

theorem ggSThree_exists_normal {X : Type*} [Group X] [Finite X]
    {H C₁ S R₀ Q : Subgroup X} {e : X}
    (hC₁ : CFSG.IsComponent C₁) (hC₁H : C₁ ≤ H) (he : e ∈ C₁) (he3 : orderOf e = 3)
    (hcent : Subgroup.centralizer ({e} : Set X) ≤ H)
    (hSR₀ : S ≤ R₀) (hR₀H : R₀ ≤ H) (hR₀n : (R₀.subgroupOf H).Normal) (hQS : Q ≤ S)
    (hQ2 : IsPGroup 2 Q) (hQn : (Q.subgroupOf H).Normal) (hcard : Nat.card S = 3 * Nat.card Q)
    (hiso : ∀ [(Q.subgroupOf R₀).Normal],
      Nonempty (↥R₀ ⧸ Q.subgroupOf R₀ ≃* Equiv.Perm (Fin 3))) :
    ∃ R : Subgroup X, R.Normal ∧
      IsPGroup 3 ↥(R.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ∧ S ≤ R := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup X := CFSG.pPrimeCore 3 X
  let π : X →* X ⧸ N := QuotientGroup.mk' N
  let Ĥ : Subgroup (X ⧸ N) := H.map π
  have hQH : Q ≤ H := hQS.trans (hSR₀.trans hR₀H)
  have hQn' : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q :=
    fun h hh q hq => (Subgroup.normal_subgroupOf_iff hQH).mp hQn q h hq hh
  have hSH : ∀ h ∈ H, ∀ s ∈ S, h * s * h⁻¹ ∈ S :=
    ggSThree_conj_mem hSR₀ hR₀H hR₀n hQS hQn hcard hiso
  obtain ⟨hcomp, hFH⟩ := ggSThree_components_fitting_le_map hC₁ hC₁H he he3 hcent
  have hO : CFSG.pPrimeCore 3 (X ⧸ N) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  have hQmap_le : Q.map π ≤ Ĥ := Subgroup.map_mono hQH
  have hQmap_n : ∀ h ∈ Ĥ, ∀ a ∈ Q.map π, h * a * h⁻¹ ∈ Q.map π := by
    intro h hh a ha
    obtain ⟨h₀, hh₀, rfl⟩ := hh
    obtain ⟨q₀, hq₀, rfl⟩ := ha
    refine Subgroup.mem_map.mpr ⟨h₀ * q₀ * h₀⁻¹, hQn' h₀ hh₀ q₀ hq₀, ?_⟩
    simp
  have hQmap_eq_bot : Q.map π = ⊥ :=
    ggSThree_eq_bot_of_two_group hO hFH hcomp hQmap_le hQmap_n (hQ2.map π)
  have hQπ : ∀ q ∈ Q, π q = 1 := by
    intro q hq
    have hmem : π q ∈ Q.map π := Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
    rw [hQmap_eq_bot] at hmem
    simpa using hmem
  have hSmap_le : S.map π ≤ Ĥ := Subgroup.map_mono (hSR₀.trans hR₀H)
  have hSmap_n : ∀ h ∈ Ĥ, ∀ a ∈ S.map π, h * a * h⁻¹ ∈ S.map π := by
    intro h hh a ha
    obtain ⟨h₀, hh₀, rfl⟩ := hh
    obtain ⟨s₀, hs₀, rfl⟩ := ha
    refine Subgroup.mem_map.mpr ⟨h₀ * s₀ * h₀⁻¹, hSH h₀ hh₀ s₀ hs₀, ?_⟩
    simp
  have hcardS : Nat.card (S.map π) ∣ 3 := ggSThree_card_map_dvd π hQS hQπ hcard
  have hsolvS : Group.IsSolvable ↥(S.map π) :=
    ggSThree_isSolvable_of_card_dvd_three (S.map π) hcardS
  have hSmap_fit : S.map π ≤ CFSG.fittingSubgroup (X ⧸ N) :=
    ggSThree_le_fitting_of_card_dvd_three hFH hcomp hSmap_le hSmap_n hsolvS hcardS
  refine ⟨(CFSG.fittingSubgroup (X ⧸ N)).comap π, ?_, ?_, ?_⟩
  · exact (CFSG.fittingSubgroup_normal (G := X ⧸ N)).comap π
  · rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)
        (CFSG.fittingSubgroup (X ⧸ N))]
    rw [CFSG.Fitting_eq_pcore (X ⧸ N) 3 hO]
    exact CFSG.pCore_isPGroup
  · intro s hs
    exact Subgroup.mem_comap.mpr (hSmap_fit (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩))

end CFSG.StandardType
