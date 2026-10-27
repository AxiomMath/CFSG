module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4D3Props
public import CFSG.Quasithin.Vol2.GoldschmidtF431D3NF

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin

section IsoG

variable {Mb : Type} [Group Mb] {P1 P2 : Subgroup Mb} {G : Type} [Group G] {H₁ H₂ : Subgroup G}
  (e : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups H₁ H₂))

@[expose] def isoMap1 : ↥P1 →* G := H₁.subtype.comp (d4IsoV1 e).toMonoidHom

@[expose] def isoMap2 : ↥P2 →* G := H₂.subtype.comp (d4IsoV2 e).toMonoidHom

theorem isoMapComp : F431Comp P1 P2 (isoMap1 e) (isoMap2 e) where
  inj₁ := Subtype.val_injective.comp (d4IsoV1 e).injective
  inj₂ := Subtype.val_injective.comp (d4IsoV2 e).injective
  agree g h1 h2 := by
    have c1 := congrArg Subtype.val (e.comm1 ⟨g, h1, h2⟩)
    have c2 := congrArg Subtype.val (e.comm2 ⟨g, h1, h2⟩)
    exact c1.symm.trans c2

theorem range_isoMap1 : (isoMap1 e).range = H₁ := by
  ext m
  constructor
  · rintro ⟨x, rfl⟩
    exact (d4IsoV1 e x).2
  · intro hm
    exact ⟨(d4IsoV1 e).symm ⟨m, hm⟩, by simp [isoMap1]⟩

theorem range_isoMap2 : (isoMap2 e).range = H₂ := by
  ext m
  constructor
  · rintro ⟨x, rfl⟩
    exact (d4IsoV2 e x).2
  · intro hm
    exact ⟨(d4IsoV2 e).symm ⟨m, hm⟩, by simp [isoMap2]⟩

theorem amalgamMap_isoMap1 (x : ↥P1) :
    amalgamMap (isoMap1 e) (isoMap2 e) (x : Mb) = ((d4IsoV1 e x : ↥H₁) : G) := by
  rw [amalgamMap_of_mem₁ _ _ x.2]
  rfl

end IsoG

section Inputs


theorem d3_nonFusion (hs : IsSimpleGroup D)
    (hCU : ∀ x : D, (∀ u ∈ d4U, x * u = u * x) → x = 1 ∨ x = d4z)
    (hodd : ¬ 2 ∣ (MulAut.conj : D →* MulAut D).range.index)
    (zH tH : ↥(autStab d4H)) (hz : (zH : MulAut D) = d3z) (ht : (tH : MulAut D) = d3t) :
    D3NonFusion zH tH := by
  intro G _ _ H₁ H₂ e hcent
  have hz' := amalgamMap_isoMap1 e zH
  have ht' := amalgamMap_isoMap1 e tH
  rw [hz] at hz'
  rw [ht] at ht'
  rw [← hz', ← ht']
  refine d3_not_conj hs hCU hodd (isoMapComp e) ?_
  rw [hz', range_isoMap1]
  exact hcent

end Inputs

section LocalCentIn


theorem d3_localCent (hs : IsSimpleGroup D)
    (hCU : ∀ x : D, (∀ u ∈ d4U, x * u = u * x) → x = 1 ∨ x = d4z)
    (hodd : ¬ 2 ∣ (MulAut.conj : D →* MulAut D).range.index)
    (hcard : Nat.card (MulAut D) ∣ 3 * Nat.card D)
    (zH tH : ↥(autStab d4H)) (hz : (zH : MulAut D) = d3z) (ht : (tH : MulAut D) = d3t) :
    D3LocalCent zH tH := by
  intro G _ _ H₁ H₂ e hcent
  have hz' := amalgamMap_isoMap1 e zH
  have ht' := amalgamMap_isoMap1 e tH
  rw [hz] at hz'
  rw [ht] at ht'
  have h := d3_localCent_comp hs hCU hodd hcard (isoMapComp e)
    (by rw [hz', range_isoMap1]; exact hcent)
  rw [ht', range_isoMap2] at h
  exact h

end LocalCentIn

end CFSG.Quasithin.D4Hex
