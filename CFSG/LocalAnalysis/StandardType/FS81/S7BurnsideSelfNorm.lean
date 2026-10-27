module

import CFSG.LocalAnalysis.StandardType.FS81.S7BurnsideCover
import CFSG.LocalAnalysis.StandardType.FS81.S7CentralHall
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.StandardType.FrameRoute.FS81

theorem exists_normalComplement_of_selfNormalizing {X : Type} [Group X] [Finite X]
    {S P : Subgroup X} {σ : X} (hPS : P ≤ S) (hP : IsPGroup 2 P) (hσP : σ ∈ P)
    (hSσ : ∀ s ∈ S, s * σ = σ * s)
    (hPP : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers σ)
    (hN : ∀ x ∈ S, x ∈ Subgroup.normalizer (P : Set X) → x ∈ P) :
    ∃ O : Subgroup X, O ≤ S ∧ (O.subgroupOf S).Normal ∧ Odd (Nat.card O) ∧ S ≤ O ⊔ P := by
  obtain ⟨M, hMS, hMnorm, hσM, ⟨m, hm_odd, hMcard⟩, hSM⟩ :=
    exists_normal_odd_cover_of_selfNormalizing hPS hP hσP hSσ hPP hN
  have hNleP : Subgroup.zpowers σ ≤ P := Subgroup.zpowers_le.mpr hσP
  have hNc : ∀ n ∈ Subgroup.zpowers σ, ∀ g ∈ M, g * n = n * g := by
    intro n hn g hg
    have hσcent : σ ∈ Subgroup.centralizer (M : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hSσ y (hMS hy)
    have hncent : n ∈ Subgroup.centralizer (M : Set X) :=
      Subgroup.zpowers_le.mpr hσcent hn
    exact (Subgroup.mem_centralizer_iff.mp hncent) g hg
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hP.to_le hNleP)
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers σ)) m := by
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm_odd)
  obtain ⟨K, hKM, _, hKcard, hMKN, hKchar⟩ :=
    exists_normal_complement_of_central_hall hσM hNc hMcard hcop
  have hKS : K ≤ S := hKM.trans hMS
  refine ⟨K, hKS, ?_, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff hKS]
    intro h k hhK hkS
    have hhM : h ∈ M := hKM hhK
    have hconjM : k * h * k⁻¹ ∈ M :=
      (Subgroup.normal_subgroupOf_iff hMS).mp hMnorm h k hhM hkS
    have horder : orderOf (k * h * k⁻¹) = orderOf h := by
      simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj k) h
    rw [hKchar (k * h * k⁻¹) hconjM, horder]
    exact (hKchar h hhM).mp hhK
  · rw [hKcard]
    exact hm_odd
  · refine hSM.trans (sup_le ?_ le_sup_right)
    exact hMKN.trans (sup_le le_sup_left (hNleP.trans le_sup_right))

end CFSG.StandardType.FrameRoute.FS81

end
