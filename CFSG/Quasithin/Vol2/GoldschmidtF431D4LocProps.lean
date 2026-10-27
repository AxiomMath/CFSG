module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Props
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocMain

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin

section Iso

variable {G : Type} [Group G] {H₁ H₂ : Subgroup G}
  (e : (RankTwoAmalgam.ofSubgroups d4H d4N).Iso (RankTwoAmalgam.ofSubgroups H₁ H₂))

@[expose] noncomputable def isoB1 : ↥d4H →* G := H₁.subtype.comp (d4IsoV1 e).toMonoidHom

@[expose] noncomputable def isoB2 : ↥d4N →* G := H₂.subtype.comp (d4IsoV2 e).toMonoidHom

theorem isoComp : F431Comp d4H d4N (isoB1 e) (isoB2 e) where
  inj₁ := Subtype.val_injective.comp (d4IsoV1 e).injective
  inj₂ := Subtype.val_injective.comp (d4IsoV2 e).injective
  agree g h1 h2 := by
    have c1 := congrArg Subtype.val (e.comm1 ⟨g, h1, h2⟩)
    have c2 := congrArg Subtype.val (e.comm2 ⟨g, h1, h2⟩)
    exact c1.symm.trans c2

theorem range_isoB1 : (isoB1 e).range = H₁ := by
  ext m
  constructor
  · rintro ⟨x, rfl⟩
    exact (d4IsoV1 e x).2
  · intro hm
    exact ⟨(d4IsoV1 e).symm ⟨m, hm⟩, by simp [isoB1]⟩

theorem range_isoB2 : (isoB2 e).range = H₂ := by
  ext m
  constructor
  · rintro ⟨x, rfl⟩
    exact (d4IsoV2 e x).2
  · intro hm
    exact ⟨(d4IsoV2 e).symm ⟨m, hm⟩, by simp [isoB2]⟩

theorem amalgamMap_isoB1 (x : ↥d4H) :
    amalgamMap (isoB1 e) (isoB2 e) (x : D) = ((d4IsoV1 e x : ↥H₁) : G) := by
  rw [amalgamMap_of_mem₁ _ _ x.2]
  rfl

end Iso

section NonFusion


theorem d4_nonFusion (zH tH : ↥d4H) (hz : (zH : D) = d4z) (ht : (tH : D) = d4t) :
    D4NonFusion zH tH := by
  intro G _ _ H₁ H₂ e hcent
  have hz' := amalgamMap_isoB1 e zH
  have ht' := amalgamMap_isoB1 e tH
  rw [hz] at hz'
  rw [ht] at ht'
  rw [← hz', ← ht']
  refine d4_not_conj (isoComp e) ?_
  rw [hz', range_isoB1]
  exact hcent

end NonFusion

section LocalCent


theorem d4_localCent (zH tH : ↥d4H) (hz : (zH : D) = d4z) (ht : (tH : D) = d4t) :
    D4LocalCent zH tH := by
  intro G _ _ H₁ H₂ e hcent
  have hz' := amalgamMap_isoB1 e zH
  have ht' := amalgamMap_isoB1 e tH
  rw [hz] at hz'
  rw [ht] at ht'
  have h := d4_localCent_comp (isoComp e) (by rw [hz', range_isoB1]; exact hcent)
  rw [ht', range_isoB2] at h
  exact h

end LocalCent

end CFSG.Quasithin.D4Hex
