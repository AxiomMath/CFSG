module

public import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Defs
public import Certificates.Certificate113
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Tits
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Transfer
import CFSG.Milestones.ASVolI.I2
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ASVolI.ChIJK CFSG.LieType.Ree
open CFSG.Blueprint (suzukiGroup)

theorem uc22sp207_hasCentralLongest_Sz {X : Type} [Group X]
    {n : ℕ} (h : IsSz X n) : HasCentralLongest X := by
  obtain ⟨-, -, a, -, F, hFld, hFin, hfa, hcard, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.suzukiModel h
  have hK : Nat.card F = 2 ^ (2 * a + 1) := hfa ▸ hcard
  have hWnot : suzukiWElt a F ∉ suzukiB a F := by
    intro h
    obtain ⟨u, v, l, hW⟩ := (mem_suzukiB_iff hK).1 h
    exact (suzuki_bruhat_normal_form hK (suzukiWElt a F)).2.1
      ⟨⟨u, v, l, hW⟩, ⟨0, 0, 1, 0, 0, by simp [suzukiSElt_zero_zero hK, suzukiDElt_one]⟩⟩
  have hcell : ∀ g : suzukiGroup a F, g ∈ suzukiB a F ∨
      ∃ b ∈ suzukiB a F, ∃ b' ∈ suzukiB a F, g = b * suzukiWElt a F * b' := by
    intro g
    rcases suzukiGroup_mem_cells hK g with hg | ⟨b, hb, x, hx, rfl⟩
    · exact Or.inl hg
    · exact Or.inr ⟨b, hb, x, suzukiU_le_suzukiB a F hx, rfl⟩
  have hwH : ∀ h ∈ suzukiT a F, suzukiWElt a F * h * (suzukiWElt a F)⁻¹ ∈ suzukiT a F := by
    intro h hh
    obtain ⟨l, rfl⟩ := mem_suzukiT_iff.1 hh
    rw [suzukiWElt_inv, suzukiWElt_D_W hK]
    exact suzukiDElt_mem_suzukiT a F _
  have hw2 : suzukiWElt a F * suzukiWElt a F ∈ suzukiT a F := by
    rw [suzukiWElt_mul_self]
    exact one_mem _
  have hbn3 : ∃ b ∈ suzukiB a F, suzukiWElt a F * b * suzukiWElt a F ∉ suzukiB a F := by
    refine ⟨suzukiSElt a F 1 0, suzukiU_le_suzukiB a F (suzukiSElt_mem_suzukiU a F 1 0),
      fun hB => ?_⟩
    obtain ⟨u₁, v₁, l, c, d, h⟩ := exists_W_S_W hK (show ((1 : F), (0 : F)) ≠ (0, 0) by simp)
    obtain ⟨u, v, l', hB'⟩ := (mem_suzukiB_iff hK).1 hB
    exact (suzuki_bruhat_normal_form hK
      (suzukiWElt a F * suzukiSElt a F 1 0 * suzukiWElt a F)).2.1
      ⟨⟨u, v, l', hB'⟩, ⟨u₁, v₁, l, c, d, h⟩⟩
  have hUn : ((suzukiU a F).subgroupOf (suzukiB a F)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (suzukiU_le_suzukiB a F)]
    exact sup_le Subgroup.le_normalizer (suzukiT_le_normalizer hK)
  have hUp : IsPGroup 2 (suzukiU a F) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := (2 * a + 1) * 2) (by
      rw [(suzuki_unipotent_structure hK).2.1, pow_mul])
  have hopp : ∀ z ∈ suzukiB a F, (suzukiWElt a F)⁻¹ * z * suzukiWElt a F ∈ suzukiB a F →
      z ∈ suzukiT a F := by
    intro z hz hz'
    obtain ⟨u, v, l, rfl⟩ := (mem_suzukiB_iff hK).1 hz
    by_cases huv : (u, v) = (0, 0)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj huv
      rw [suzukiSElt_zero_zero hK, one_mul]
      exact suzukiDElt_mem_suzukiT a F l
    · exfalso
      obtain ⟨u₁, v₁, l₁, c, d, h⟩ := exists_W_S_W hK huv
      have hW := suzukiWElt_mul_self (a := a) (K := F)
      have e : (suzukiWElt a F)⁻¹ * (suzukiSElt a F u v * suzukiDElt a F l) * suzukiWElt a F =
          (suzukiWElt a F * suzukiSElt a F u v * suzukiWElt a F) * suzukiDElt a F l⁻¹ := by
        rw [suzukiWElt_inv, ← suzukiWElt_D_W hK l]
        calc suzukiWElt a F * (suzukiSElt a F u v * suzukiDElt a F l) * suzukiWElt a F
            = suzukiWElt a F * suzukiSElt a F u v * 1 * suzukiDElt a F l * suzukiWElt a F := by
              group
          _ = suzukiWElt a F * suzukiSElt a F u v * (suzukiWElt a F * suzukiWElt a F) *
              suzukiDElt a F l * suzukiWElt a F := by rw [hW]
          _ = _ := by group
      rw [e] at hz'
      have hBW : suzukiWElt a F * suzukiSElt a F u v * suzukiWElt a F ∈ suzukiB a F := by
        have := (suzukiB a F).mul_mem hz' ((suzukiB a F).inv_mem
          (suzukiT_le_suzukiB a F (suzukiDElt_mem_suzukiT a F l⁻¹)))
        simpa using this
      obtain ⟨u', v', l', hB'⟩ := (mem_suzukiB_iff hK).1 hBW
      exact (suzuki_bruhat_normal_form hK
        (suzukiWElt a F * suzukiSElt a F u v * suzukiWElt a F)).2.1
        ⟨⟨u', v', l', hB'⟩, ⟨u₁, v₁, l₁, c, d, h⟩⟩
  have hHp : ¬ 2 ∣ Nat.card (suzukiT a F) := by
    rw [(suzuki_borel_structure hK).2.2.1]
    have h2 : 2 ^ (2 * a + 1) = 2 * 2 ^ (2 * a) := by ring
    have h3 : 0 < 2 ^ (2 * a) := Nat.two_pow_pos (2 * a)
    omega
  obtain ⟨N, hN⟩ := burnsideI2BN_rankOne Nat.prime_two (B := suzukiB a F) (H := suzukiT a F)
    (U := suzukiU a F) (w := suzukiWElt a F) hcell hWnot (suzukiT_le_suzukiB a F) hwH hw2 hbn3
    (suzukiU_le_suzukiB a F) hUn hUp (suzukiU_inf_suzukiT hK) rfl hopp hHp
  exact (uc22sp207_hasCentralLongest_of_cell hN hcell).of_mulEquiv e.symm

end CFSG.LocalAnalysis.UniquenessCase.UC22
