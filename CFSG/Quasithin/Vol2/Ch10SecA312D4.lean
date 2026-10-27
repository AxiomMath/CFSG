module

public import CFSG.Quasithin.Vol2.Ch10SecA312D2

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312D

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch10.A312C

theorem card_j2 {Y : Type} [Group Y] (h : IsSporadic .J2 Y) :
    Nat.card Y = 604800 := by
  obtain ⟨φ⟩ := h; rw [Nat.card_congr φ.toEquiv]; exact CFSG.Sporadic.J2.card_J2

variable {X : Type} [Group X] [Finite X] {B₁ B₂ : Subgroup X}

theorem case16s (hB₁ : ⁅B₁, B₁⁆ = B₁)
    (hc : ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₁ ⊓ pCoreOf 2 B₂) (e : ModO2 B₁ ≃* ModO2 B₂)
    (h : A312C16 B₁ ⊤) : False := by
  obtain ⟨⟨V, _, ⟨-, hV⟩, ⟨φ⟩⟩, hL⟩ := h
  have : IsSimpleGroup (↥B₁ ⧸ V) := φ.isSimpleGroup
  have h1 := dvd_card_of_ext hB₁ hc e hV
  rw [card_alt5 ⟨φ⟩, ← Subgroup.card_top, card_j2 hL] at h1
  norm_num at h1

theorem case18s (hB₁ : ⁅B₁, B₁⁆ = B₁)
    (hc : ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₁ ⊓ pCoreOf 2 B₂) (e : ModO2 B₁ ≃* ModO2 B₂)
    (h : IsExt ↥B₁ (fun V _ => IsZ4StarExtra2 V) (fun Y _ => IsAlt 5 Y))
    (hL : IsSporadic .HS ↥(⊤ : Subgroup X)) : False := by
  obtain ⟨V, _, hV, ⟨φ⟩⟩ := h
  have : IsSimpleGroup (↥B₁ ⧸ V) := φ.isSimpleGroup
  have h1 := dvd_card_of_ext hB₁ hc e (card_of_isZ4StarExtra2 hV)
  rw [card_alt5 ⟨φ⟩, ← Subgroup.card_top, card_hs hL] at h1
  norm_num at h1

theorem case19s (hB₁ : ⁅B₁, B₁⁆ = B₁)
    (hc : ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₁ ⊓ pCoreOf 2 B₂) (e : ModO2 B₁ ≃* ModO2 B₂)
    (h : IsExt ↥B₁ (fun V _ => IsExtraspecial2 3 V) (fun Y _ => IsPSL 3 2 1 Y))
    (hL : IsSporadic .He ↥(⊤ : Subgroup X)) : False := by
  obtain ⟨V, _, ⟨-, hV⟩, hY⟩ := h
  have : IsSimpleGroup (↥B₁ ⧸ V) := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hY).2
  have h1 := dvd_card_of_ext hB₁ hc e hV
  rw [card_l32 hY, ← Subgroup.card_top, card_he hL] at h1
  norm_num at h1

theorem case20s (hB₁ : ⁅B₁, B₁⁆ = B₁)
    (hc : ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₁ ⊓ pCoreOf 2 B₂) (e : ModO2 B₁ ≃* ModO2 B₂)
    (h : IsAlt 5 (ModO2 B₁)) (h11 : Nat.card (CFSG.pCore 2 ↥B₁) = 2 ^ 11)
    (hL : IsSporadic .Ru ↥(⊤ : Subgroup X)) : False := by
  obtain ⟨φ⟩ := h
  have : IsSimpleGroup (ModO2 B₁) := φ.isSimpleGroup
  have h1 := card_mul_card_modO2_dvd hc e (center_eq_bot (perfect_modO2 hB₁))
  rw [(CFSG.pCore 2 ↥B₁).card_eq_card_quotient_mul_card_subgroup, h11, card_alt5 ⟨φ⟩,
    ← Subgroup.card_top, card_ru hL] at h1
  norm_num at h1

end CFSG.Quasithin.Vol2.Ch10.A312D
