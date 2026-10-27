module

import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.Assembly.Defs
public import CFSG.Open.Defs
public import CFSG.Quasithin.Background.B1MoreIrr
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.D2Offenders

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B1Red

section Transfer

variable {V : Type*} [CommGroup V]

@[expose] def preimageAut (H₀ : Subgroup (MulAut V)) (U : Subgroup V)
    (Kh : Subgroup (MulAut ↥U)) : Subgroup (MulAut V) :=
  (Kh.comap (resHom U)).map (stabSub U).subtype ⊓ H₀

theorem mem_preimageAut {H₀ : Subgroup (MulAut V)} {U : Subgroup V} {Kh : Subgroup (MulAut ↥U)}
    {g : MulAut V} :
    g ∈ preimageAut H₀ U Kh ↔ g ∈ H₀ ∧ ∃ hg : g ∈ stabSub U, resHom U ⟨g, hg⟩ ∈ Kh := by
  constructor
  · rintro ⟨⟨g', hg', rfl⟩, hgH⟩
    exact ⟨hgH, g'.2, hg'⟩
  · rintro ⟨hgH, hg, hmem⟩
    exact ⟨⟨⟨g, hg⟩, hmem, rfl⟩, hgH⟩

theorem preimageAut_le (H₀ : Subgroup (MulAut V)) (U : Subgroup V) (Kh : Subgroup (MulAut ↥U)) :
    preimageAut H₀ U Kh ≤ H₀ := inf_le_right

theorem autSub_eq_range {L : Subgroup (MulAut V)} {U : Subgroup V} (hL : L ≤ stabSub U) :
    autSub L U = ((resHom U).comp (Subgroup.inclusion hL)).range := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, hgL, rfl⟩ := mem_autSub.1 hφ
    exact ⟨⟨g, hgL⟩, rfl⟩
  · rintro ⟨l, rfl⟩
    exact mem_autSub.2 ⟨Subgroup.inclusion hL l, l.2, rfl⟩

theorem isQuasisimple_autSub {L : Subgroup (MulAut V)} {U : Subgroup V} (hL : L ≤ stabSub U)
    (hq : CFSG.Open.IsQuasisimple ↥L) (hne : ¬ L ≤ centSub U) :
    CFSG.Open.IsQuasisimple ↥(autSub L U) := by
  rw [autSub_eq_range hL]
  refine CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top hq _ ?_
  intro htop
  apply hne
  intro l hl u hu
  have : (⟨l, hl⟩ : ↥L) ∈ ((resHom U).comp (Subgroup.inclusion hL)).ker := by rw [htop]; trivial
  rw [MonoidHom.mem_ker] at this
  have h2 := congrArg (fun φ : MulAut ↥U => ((φ ⟨u, hu⟩ : ↥U) : V)) this
  exact h2

theorem isFFStarOffender_autSub [Finite V] {H A : Subgroup (MulAut V)} {U : Subgroup V}
    (hA : IsFFStarOffender H A) (hAU : ∀ a ∈ A, ∀ w ∈ U, a w ∈ U) (hnt : ¬ A ≤ centSub U) :
    IsFFStarOffender (autSub H U) (autSub A U) := by
  refine B1_5_1 hA hAU ?_
  intro h
  apply hnt
  intro a ha u hu
  exact (commSub_eq_bot_iff.1 h) hu a ha

theorem mem_irrPlus_of_autSub {L : Subgroup (MulAut V)} {U : Subgroup V} (hL : L ≤ stabSub U)
    {Î : Subgroup ↥U} (hÎ : Î ∈ IrrPlus (autSub L U) (⊤ : Subgroup ↥U)) :
    Î.map U.subtype ∈ IrrPlus L (⊤ : Subgroup V) := by
  obtain ⟨hinv, hcomm, hlt, hirr⟩ := (mem_irrPlus_top_iff).1 hÎ
  rw [mem_irrPlus_top_iff]
  set I := Î.map U.subtype with hI
  have hIU : I ≤ U := Subgroup.map_subtype_le Î
  have hfix : (Î ⊓ fixV (autSub L U)).map U.subtype = I ⊓ fixV L := by
    rw [Subgroup.map_inf _ _ _ U.subtype_injective, map_subtype_fixV_autSub hL, ← inf_assoc,
      inf_eq_left.2 hIU]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx w hw
    obtain ⟨u, hu, rfl⟩ := hw
    exact ⟨resHom U ⟨x, hL hx⟩ u,
      hinv _ (mem_autSub.2 ⟨⟨x, hL hx⟩, hx, rfl⟩) u hu, rfl⟩
  · rw [← map_commSub_autSub hL Î, hcomm]
  · refine lt_of_le_of_ne inf_le_left fun h => hlt.ne ?_
    apply Subgroup.map_injective U.subtype_injective
    rw [hfix]
    exact h
  · intro J hJinv hJ1 hJ2
    set Ĵ : Subgroup ↥U := J.comap U.subtype with hĴ
    have hJU : J ≤ U := hJ2.trans hIU
    have hĴmap : Ĵ.map U.subtype = J := by
      rw [hĴ, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_eq_right.2 hJU]
    have hĴinv : ∀ y ∈ autSub L U, ∀ w ∈ Ĵ, y w ∈ Ĵ := by
      intro y hy w hw
      obtain ⟨g, hgL, rfl⟩ := mem_autSub.1 hy
      exact hJinv _ hgL _ hw
    have hĴ1 : Î ⊓ fixV (autSub L U) ≤ Ĵ := by
      intro u hu
      have : (u : V) ∈ (Î ⊓ fixV (autSub L U)).map U.subtype := ⟨u, hu, rfl⟩
      rw [hfix] at this
      exact hJ1 this
    have hĴ2 : Ĵ ≤ Î := by
      intro u hu
      have h1 : (u : V) ∈ I := hJ2 hu
      obtain ⟨u', hu', hu'u⟩ := h1
      have : u' = u := U.subtype_injective hu'u
      exact this ▸ hu'
    rcases hirr Ĵ hĴinv hĴ1 hĴ2 with h | h
    · left
      rw [← hĴmap, h, hfix]
    · right
      rw [← hĴmap, h]

end Transfer

end B1Red

end CFSG.Quasithin
