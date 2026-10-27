module

public import CFSG.RankThree.GF2n.Tim78RootType
public import CFSG.RankThree.GF2n.Tim78S4LemA
public import CFSG.RankThree.GF2n.Tim81RootCore

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

namespace RootCore

variable [Finite G] {M B Q : Subgroup G} (H : RootCore M B Q)
include H

theorem rootTypeStep_iff : RootTypeStep M B ↔ IsRootTypeTI B := by
  constructor
  · intro hRT
    refine ⟨H.ti, fun g hg a ha c hc => ?_⟩
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hg
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    obtain ⟨hbB, hbN⟩ := Subgroup.mem_inf.mp hb
    have hbM : g⁻¹ * b * g ∈ M := by
      rw [normalizer_conjSubgroup, H.normalizer_B, mem_conjSubgroup] at hbN
      exact hbN
    have h1 := hRT g⁻¹ b hbB hb1' (by simpa using hbM)
    have h2 := H.conj_le_M_symm h1
    rw [inv_inv] at h2
    exact H.commute_of_conj_le_M h2 a ha c hc
  · rintro ⟨-, hroot⟩ g b hb hb1 hgb
    have hbN : b ∈ Subgroup.normalizer (conjSubgroup g⁻¹ B : Set G) := by
      rw [normalizer_conjSubgroup, H.normalizer_B, mem_conjSubgroup, inv_inv]
      exact hgb
    have hne : B ⊓ Subgroup.normalizer (conjSubgroup g⁻¹ B : Set G) ≠ ⊥ := by
      intro hbot
      have : b ∈ B ⊓ Subgroup.normalizer (conjSubgroup g⁻¹ B : Set G) := ⟨hb, hbN⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hb1 this
    have hc := hroot g⁻¹ hne
    have h1 : conjSubgroup g⁻¹ B ≤ M := by
      rw [← H.normalizer_B]
      exact le_normalizer_of_comm fun c hc' a ha => (hc a ha c hc').symm
    have h2 := H.conj_le_M_symm h1
    rwa [inv_inv] at h2

end RootCore

end CFSG.RankThree.GF2n.Tim78

