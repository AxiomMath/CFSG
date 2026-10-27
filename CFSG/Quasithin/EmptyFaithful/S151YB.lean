module

public import CFSG.Quasithin.EmptyFaithful.S151YA
public import CFSG.Quasithin.EmptyFaithful.S151XD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem ya7_isSylowTwoOf_map {G : Type} [Group G] {H T : Subgroup G} {D : Type} [Group D]
    (α : ↥H →* D) (hT : IsSylowTwoOf T H) :
    IsSylowTwoOf ((T.subgroupOf H).map α) α.range := by
  refine ⟨Subgroup.map_le_range _ _, ?_, ?_⟩
  · have h2 : IsPGroup 2 (T.subgroupOf H) := by
      have : IsPGroup 2 ↥T := hT.2.1
      exact this.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
    exact h2.of_surjective (α.subgroupMap _) (α.subgroupMap_surjective _)
  · have heq : ((T.subgroupOf H).map α).subgroupOf α.range =
        (T.subgroupOf H).map α.rangeRestrict := by
      ext y
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨t, ht, hty⟩
        exact ⟨t, ht, Subtype.ext hty⟩
      · rintro ⟨t, ht, hty⟩
        exact ⟨t, ht, congrArg Subtype.val hty⟩
    rw [heq]
    intro hdvd
    exact hT.2.2 (hdvd.trans (Subgroup.index_map_dvd _ α.rangeRestrict_surjective))

theorem ya7_permWeight_one (v : ↥(evenWeight 7)) :
    permWeight 7 (1 : Equiv.Perm (Fin 7)) v = v :=
  (ya7_permWeight_eq_iff 1 v).mpr (by simp)

theorem ya7_sup_eq {G : Type} [Group G] {L M Mz : Subgroup G} (α : ↥L →* alternatingGroup (Fin 7))
    (hsurj : Function.Surjective α) (v : ↥(evenWeight 7)) (hv : HasWeightTwo (v : Fin 7 → ZMod 2))
    (hMz : ∀ x : ↥L, (x : G) ∈ Mz ↔ permWeight 7 (α x : Equiv.Perm (Fin 7)) v = v)
    (P : Finset (Finset (Fin 7)))
    (hPM : ∀ x : ↥L, StabilizesPartition (α x : Equiv.Perm (Fin 7)) P → (x : G) ∈ M)
    (hmove : ∃ x : ↥L, StabilizesPartition (α x : Equiv.Perm (Fin 7)) P ∧
      permWeight 7 (α x : Equiv.Perm (Fin 7)) v ≠ v) :
    (M ⊓ L) ⊔ (Mz ⊓ L) = L := by
  apply le_antisymm (sup_le inf_le_right inf_le_right)
  set K : Subgroup G := (M ⊓ L) ⊔ (Mz ⊓ L) with hK
  have hKz : (Mz ⊓ L) ≤ K := le_sup_right
  have hKm : (M ⊓ L) ≤ K := le_sup_left
  set A : Subgroup (alternatingGroup (Fin 7)) := (K.subgroupOf L).map α with hA
  have hAtop : A = ⊤ := by
    apply ya7_eq_top_of_stab_le v hv A
    · intro σ hσ
      obtain ⟨x, rfl⟩ := hsurj σ
      refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact hKz ⟨(hMz x).mpr hσ, x.2⟩
    · obtain ⟨x, hxP, hxv⟩ := hmove
      refine ⟨α x, Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩, hxv⟩
      rw [Subgroup.mem_subgroupOf]
      exact hKm ⟨hPM x hxP, x.2⟩
  intro y hy
  have hmem : α ⟨y, hy⟩ ∈ A := hAtop ▸ Subgroup.mem_top _
  obtain ⟨z, hzK, hz⟩ := Subgroup.mem_map.mp hmem
  have hker : α (⟨y, hy⟩ * z⁻¹) = 1 := by
    rw [map_mul, map_inv, hz, mul_inv_cancel]
  have hMzmem : ((⟨y, hy⟩ * z⁻¹ : ↥L) : G) ∈ Mz := by
    rw [hMz, hker]
    exact ya7_permWeight_one v
  have hKmem : ((⟨y, hy⟩ * z⁻¹ : ↥L) : G) ∈ K := hKz ⟨hMzmem, (⟨y, hy⟩ * z⁻¹ : ↥L).2⟩
  have hz' : (z : G) ∈ K := Subgroup.mem_subgroupOf.mp hzK
  have := K.mul_mem hKmem hz'
  simpa using this

@[expose] def Input15122A7Bang : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G)
    (α : ↥L →* alternatingGroup (Fin 7)) (v : ↥(evenWeight 7)) (P : Finset (Finset (Fin 7))),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → IsAltBlockTypeWith L 7 α → HasWeightTwo (v : Fin 7 → ZMod 2) →
    (∀ x : ↥L, (x : G) ∈ s1516 T Z₁ → permWeight 7 (α x : Equiv.Perm (Fin 7)) v = v) →
    (∀ x : ↥L, (x : G) ∈ mZ1516 Mc Z₁ ↔ permWeight 7 (α x : Equiv.Perm (Fin 7)) v = v) →
    IsPartitionOfType P {2, 2, 2, 1} → ya7Supp v ∈ P →
    (∀ x : ↥L, (x : G) ∈ s1516 T Z₁ → StabilizesPartition (α x : Equiv.Perm (Fin 7)) P) →
    (∃ x : ↥L, StabilizesPartition (α x : Equiv.Perm (Fin 7)) P ∧
      permWeight 7 (α x : Equiv.Perm (Fin 7)) v ≠ v) →
    ∀ x : ↥L, StabilizesPartition (α x : Equiv.Perm (Fin 7)) P → (x : G) ∈ M

theorem input15122A7_of_bang (hbang : Input15122A7Bang) : Input15122A7 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hB hA7
  obtain ⟨hshort, α, hα⟩ := hA7
  have hsurj : Function.Surjective α := hα.1
  obtain ⟨v, hv2, hvS, hvM⟩ := hB.2.2.2 hc.hL.comp α hα
  have hD : IsSylowTwoOf ((((s1516 T Z₁ ⊓ L).subgroupOf L)).map α) ⊤ := by
    have h := ya7_isSylowTwoOf_map α hc.h20.sylow
    rwa [MonoidHom.range_eq_top.mpr hsurj] at h
  have hDmem : ∀ x : ↥L, (x : G) ∈ s1516 T Z₁ →
      α x ∈ (((s1516 T Z₁ ⊓ L).subgroupOf L)).map α := fun x hx =>
    Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr ⟨hx, x.2⟩, rfl⟩
  have hDs : ∀ d ∈ (((s1516 T Z₁ ⊓ L).subgroupOf L)).map α,
      (ya7Supp v).image (d : Equiv.Perm (Fin 7)) = ya7Supp v := by
    intro d hd
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hd
    exact (ya7_permWeight_eq_iff _ v).mp (hvS x (Subgroup.mem_subgroupOf.mp hx).1)
  obtain ⟨P, hPpart, hsP, hPstab, σ, hσP, hσmove⟩ :=
    ya7_partition_data _ hD (ya7Supp v) hv2 hDs
  have hstabS : ∀ x : ↥L, (x : G) ∈ s1516 T Z₁ →
      StabilizesPartition (α x : Equiv.Perm (Fin 7)) P := fun x hx => hPstab _ (hDmem x hx)
  have hmove : ∃ x : ↥L, StabilizesPartition (α x : Equiv.Perm (Fin 7)) P ∧
      permWeight 7 (α x : Equiv.Perm (Fin 7)) v ≠ v := by
    obtain ⟨x, hx⟩ := hsurj σ
    refine ⟨x, ?_, ?_⟩
    · rw [hx]
      exact hσP
    · rw [hx]
      intro h
      exact hσmove ((ya7_permWeight_eq_iff _ v).mp h)
  have hPM := hbang G T Mc M Z₁ Z₂ V₁ V₂ L α v P hc hα hv2 hvS hvM hPpart hsP hstabS hmove
  refine ⟨⟨hshort, α, hα⟩, ya7_sup_eq α hsurj v hv2 hvM P hPM hmove, ?_, α, hα,
    ⟨P, hPpart, hstabS, hPM⟩, v, hv2, hvS, hvM⟩
  exact lt_of_le_of_ne inf_le_right fun h => hc.h20.one (h ▸ inf_le_left)

theorem lemma15122InputU_of_named_inputs_bang (nDich : Input15122Dichotomy) (nNoB : Input15122NoBorel)
    (nBang : Input15122A7Bang) (nR2 : Input15122Rank2Block) (nL45 : Input15122L45Block)
    (nC : Input15122ThreeC) (nD : Input15122ThreeD) (nE : Input15122ThreeE) :
    Lemma15122InputU :=
  lemma15122InputU_of_named_inputs nDich nNoB (input15122A7_of_bang nBang) nR2 nL45 nC nD nE

end CFSG.Quasithin
