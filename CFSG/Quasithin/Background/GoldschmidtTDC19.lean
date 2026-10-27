module

public import CFSG.Quasithin.Background.C1PackQuasi
public import CFSG.Quasithin.Background.C1PackA4
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourCountN

public section

namespace CFSG.Quasithin.C19Bridge

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem modO2Image_le_pCore_three {H B : Subgroup G} (hB : IsBlock2 H B) (hB3 : IsAltType B 3) :
    modO2Image H B ≤ CFSG.Open.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsub : (modO2Image H B).IsSubnormal :=
    Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H)) hB.2.2
  have hgrp : IsPGroup 3 (modO2Image H B) := fun u => ⟨1, by
    have := L238.pow_three_eq_one_of_mem_img hB hB3 u.2
    exact Subtype.ext (by simpa using this)⟩
  exact S14110.Commute.le_pCore_of_isSubnormal 3 hsub le_rfl (by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top) hgrp

theorem le_oTwoThreeIn_of_isAltType_three {H B : Subgroup G} (hB : IsBlock2 H B)
    (hB3 : IsAltType B 3) : B ≤ oTwoThreeIn H := by
  intro x hx
  have hxH : x ∈ H := hB.2.1 hx
  have hmem := modO2Image_le_pCore_three hB hB3 (Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, hx, rfl⟩)
  exact ⟨⟨x, hxH⟩, hmem, rfl⟩

theorem isBlock2_oTwoThreeIn {H B : Subgroup G} (hB : IsBlock2 H B) (hB3 : IsAltType B 3) :
    IsBlock2 (oTwoThreeIn H) B := by
  have hle := le_oTwoThreeIn_of_isAltType_three hB hB3
  have hK : oTwoThreeIn H ≤ H := Subgroup.map_subtype_le _
  exact ⟨hB.1, hle, (isSubnormal_iff_subgroupOf hle).mp
    (A4.subnormal_of_le_of_le (IsBlock2.isSubnormal hB) hle hK)⟩

end CFSG.Quasithin.C19Bridge

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem asc19Statement_holds (G : Type) [Group G] [Finite G] : ASC19Statement G := by
  intro H B₁ B₂ hA3 hB₁ hB₂ hne
  rcases hB₁.1.2.2.2.1 with hq₁ | h₁
  · exact C1Pack.commutator_eq_bot_of_quasisimple hB₁ hq₁ hB₂ hne
  · rcases hB₂.1.2.2.2.1 with hq₂ | h₂
    · rw [Subgroup.commutator_comm]
      exact C1Pack.commutator_eq_bot_of_quasisimple hB₂ hq₂ hB₁ hne.symm
    · have hA₁ : IsAltType B₁ 3 := C1Pack.isAltType_three_of_card_three hB₁.1 h₁
      have hA₂ : IsAltType B₂ 3 := C1Pack.isAltType_three_of_card_three hB₂.1 h₂
      exact C1Pack.commutator_eq_bot_of_card_three (hA3 ⟨B₁, hB₁, hA₁⟩)
        (C19Bridge.isBlock2_oTwoThreeIn hB₁ hA₁) h₁ (C19Bridge.isBlock2_oTwoThreeIn hB₂ hA₂) h₂ hne

end CFSG.Quasithin
