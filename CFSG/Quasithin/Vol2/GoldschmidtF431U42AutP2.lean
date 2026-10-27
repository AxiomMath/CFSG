module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP2Tr

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

theorem u42AutSylow :
    U42AutSylow := by
  intro G _ _ M₁ M₂ z c T hT
  have hxB : xA ∈ Bh := That_le_Bh xA_mem_That
  have hzx : c.iso.toG ⟨xA, hxB⟩ = z := c.iso.toG_xA c.z2 c.z1 c.zc
  obtain ⟨b, hbB, hTb⟩ := B6.isSylowTwoOf_exists_conj (isSylowTwoOf_imgG_That c.iso) hT
  have hzcB : ∀ u ∈ M₁ ⊓ M₂, u * z = z * u := Subgroup.mem_centralizer_iff.1 c.zc.2
  have hbz : b⁻¹ * z * b = z := by
    have := hzcB b hbB
    calc b⁻¹ * z * b = b⁻¹ * (z * b) := by group
      _ = b⁻¹ * (b * z) := by rw [this]
      _ = z := by group
  have hzimg : z ∈ c.iso.imgG That := c.iso.mem_imgG.2 ⟨⟨xA, hxB⟩, xA_mem_That, hzx⟩
  have hzT : z ∈ T := by
    rw [hTb]
    exact B6.mem_conjSub.2 (by rw [hbz]; exact hzimg)
  have hzc' : ∀ t ∈ T, z * t = t * z := fun t ht => (hzcB t (hT.1 ht)).symm
  have hZ : ∀ w ∈ T, (∀ t ∈ T, w * t = t * w) → w = 1 ∨ w = z := by
    intro w hw hwc
    have hw0 : b⁻¹ * w * b ∈ c.iso.imgG That := by
      rw [hTb] at hw
      exact B6.mem_conjSub.1 hw
    obtain ⟨wh, hwh, hwe⟩ := c.iso.mem_imgG.1 hw0
    have hcen : ∀ t ∈ That, (wh : Ah) * t = t * (wh : Ah) := by
      intro t ht
      have hth : c.iso.toG ⟨t, That_le_Bh ht⟩ ∈ c.iso.imgG That :=
        c.iso.mem_imgG.2 ⟨⟨t, That_le_Bh ht⟩, ht, rfl⟩
      have hmem : b * c.iso.toG ⟨t, That_le_Bh ht⟩ * b⁻¹ ∈ T := by
        rw [hTb]
        refine B6.mem_conjSub.2 ?_
        have : b⁻¹ * (b * c.iso.toG ⟨t, That_le_Bh ht⟩ * b⁻¹) * b =
            c.iso.toG ⟨t, That_le_Bh ht⟩ := by group
        rw [this]
        exact hth
      have h1 := hwc _ hmem
      have h2 : (b⁻¹ * w * b) * c.iso.toG ⟨t, That_le_Bh ht⟩ =
          c.iso.toG ⟨t, That_le_Bh ht⟩ * (b⁻¹ * w * b) := by
        calc (b⁻¹ * w * b) * c.iso.toG ⟨t, That_le_Bh ht⟩
            = b⁻¹ * (w * (b * c.iso.toG ⟨t, That_le_Bh ht⟩ * b⁻¹)) * b := by group
          _ = b⁻¹ * ((b * c.iso.toG ⟨t, That_le_Bh ht⟩ * b⁻¹) * w) * b := by rw [h1]
          _ = c.iso.toG ⟨t, That_le_Bh ht⟩ * (b⁻¹ * w * b) := by group
      rw [← hwe, ← c.iso.toG_mul, ← c.iso.toG_mul] at h2
      exact congrArg Subtype.val (c.iso.toG_injective h2)
    rcases center_That hwh hcen with h | h
    · left
      have h1 : wh = 1 := Subtype.ext h
      rw [h1, c.iso.toG_one] at hwe
      calc w = b * (b⁻¹ * w * b) * b⁻¹ := by group
        _ = 1 := by rw [← hwe]; group
    · right
      have h1 : wh = ⟨xA, hxB⟩ := Subtype.ext h
      rw [h1, hzx] at hwe
      calc w = b * (b⁻¹ * w * b) * b⁻¹ := by group
        _ = b * z * b⁻¹ := by rw [← hwe]
        _ = z := by
          have := hzcB b hbB
          calc b * z * b⁻¹ = z * b * b⁻¹ := by rw [this]
            _ = z := by group
  have hB2 : twoPart (M₁ ⊓ M₂) = 128 := by
    rw [twoPart_eq_of_card_eq (k := 7) (m := 3) (by norm_num) (by rw [c.iso.card_B]; norm_num)]
    norm_num
  have hM2 : twoPart M₁ = 128 := by
    rw [twoPart_eq_of_card_eq (k := 7) (m := 9) (by norm_num) (by rw [c.iso.card_M₁]; norm_num)]
    norm_num
  have hTM : IsSylowTwoOf T M₁ :=
    isSylowTwoOf_of_card_eq (hT.1.trans inf_le_left) hT.2.1 (by rw [hT.card_eq, hB2, hM2])
  exact isSylowTwoOf_top_of_center hTM hzT c.z1 hzc' hZ c.cz

end CFSG.Quasithin.H13.F431.U42Aut
