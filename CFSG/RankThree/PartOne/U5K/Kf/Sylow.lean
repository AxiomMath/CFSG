module

public import CFSG.RankThree.PartOne.U5K.Hyp.Aut

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

open CFSG CFSG.RankThree.PartOne.U5K.Hyp CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

theorem exists_isSylowOf_ge {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H X : Subgroup G} (hXH : X ≤ H) (hX : IsPGroup p X) :
    ∃ P : Subgroup G, IsSylowOf p P H ∧ X ≤ P := by
  have hX' : IsPGroup p (X.subgroupOf H) :=
    hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXH).symm
  obtain ⟨Q, hQ⟩ := hX'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥H).map H.subtype, ⟨Subgroup.map_subtype_le _, ?_, ?_⟩, ?_⟩
  · exact Q.isPGroup'.map H.subtype
  · have hsub : ((Q : Subgroup ↥H).map H.subtype).subgroupOf H = (Q : Subgroup ↥H) :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    have : ((Q : Subgroup ↥H).map H.subtype).relIndex H = (Q : Subgroup ↥H).index := by
      unfold Subgroup.relIndex
      rw [hsub]
    rw [this]
    exact Q.not_dvd_index
  · intro x hx
    have hxH : x ∈ H := hXH hx
    have : (⟨x, hxH⟩ : ↥H) ∈ X.subgroupOf H := hx
    exact ⟨⟨x, hxH⟩, hQ this, rfl⟩

variable {f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData 2 f K}

theorem exists_sylow_Uh (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥)
    {H : Subgroup (MulAut (hypPSU hK 2 1))} (hH : Pi hK ≤ H) :
    ∃ T : Subgroup (MulAut (hypPSU hK 2 1)), IsSylowOf 2 T H ∧ T ⊓ Pi hK = Uh hK := by
  have := finite_mulAut_hyp hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl := (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 (isSylow_Uh hZ)
  obtain ⟨hUP, hU2, hUidx⟩ := hSyl
  obtain ⟨T, hT, hUT⟩ := exists_isSylowOf_ge (p := 2) (hUP.trans hH) hU2
  refine ⟨T, hT, le_antisymm ?_ (le_inf hUT hUP)⟩
  set Y : Subgroup (MulAut (hypPSU hK 2 1)) := T ⊓ Pi hK with hY
  have hUY : Uh hK ≤ Y := le_inf hUT hUP
  have hYP : Y ≤ Pi hK := inf_le_right
  have hY2 : IsPGroup 2 Y := hT.2.1.to_le inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex (Uh hK) Y (Pi hK) hUY hYP
  have hodd : ¬ 2 ∣ (Uh hK).relIndex Y := fun hd =>
    hUidx (hmul ▸ Dvd.dvd.mul_right hd _)
  have hpow : ∃ n : ℕ, (Uh hK).relIndex Y = 2 ^ n := by
    have hU2' : IsPGroup 2 ((Uh hK).subgroupOf Y) := hU2.comap_subtype
    have := hY2
    exact (hY2.index ((Uh hK).subgroupOf Y))
  obtain ⟨n, hn⟩ := hpow
  have hn0 : n = 0 := by
    by_contra hne
    exact hodd (hn ▸ dvd_pow_self 2 hne)
  rw [hn0, pow_zero] at hn
  exact (Subgroup.relIndex_eq_one.1 hn)

end CFSG.RankThree.PartOne.U5K.Kf
