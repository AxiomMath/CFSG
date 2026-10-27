module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs
public import CFSG.RankThree.PartTwo.Sec21.HeringFFGF2

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowOf (p : ℕ) [Fact p.Prime] (H : Subgroup G) :
    ∃ P : Subgroup G, IsSylowOf p P H := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p H))
  refine ⟨(P : Subgroup H).map H.subtype, Subgroup.map_subtype_le _, P.2.map _, ?_⟩
  rw [Subgroup.relIndex, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective H)]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 P.not_dvd_index

theorem ff84Extraspecial_of_items_m (h21 : FF84_2_1) (h22 : FF84_2_2) (h35 : FF84_3_5)
    (h36 : FF84_3_6) (h47 : FF84_4_7) (h48 : FF84_4_8) (h410 : FF84_4_10m)
    (h411 : FF84_4_11m) : FF84Extraspecial := by
  intro G _ _ hsimple hnab hchar b hb L hLC hLN hquasi hmodel hcyc hnsc hrank hi hii₁ hii₂ hiii
  have hyp : FF84Hyp b L :=
    ⟨hsimple, hnab, hchar, hb, hLC, hLN, hquasi, hmodel, hcyc, hnsc, hrank, hi, hii₁, hii₂, hiii⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨B, hB⟩ := exists_isSylowOf 3 (Cen b)
  obtain ⟨b₁, hb₁, b₂, hb₂, hgen, hmono, hfus⟩ := h21 G b L hyp B hB
  rcases h22 G b L B b₁ b₂ hyp hB hb₁ hb₂ hgen hmono with hA | ⟨K, hK⟩
  · have hs : FF84Sec3 b L B b₁ b₂ := ⟨hyp, hB, hb₁, hb₂, hgen, hmono, hfus, hA⟩
    obtain ⟨t, ht, htL, htb, hN, -⟩ := h35 G b L B b₁ b₂ hs
    exact ⟨t, ht, (h36 G b L B b₁ b₂ hs t ht htL htb hN).1⟩
  · have hs : FF84Sec4 b L B K b₁ b₂ := ⟨hyp, hB, hb₁, hb₂, hgen, hmono, hfus, hK⟩
    obtain ⟨U, U', -, hPi, -⟩ := h47 G b L B K b₁ b₂ hs
    have hU : U ∈ PiStar (Cen b) B 2 := by rw [hPi]; exact Or.inl rfl
    obtain ⟨s, t, hD⟩ := h410 G b L B K b₁ b₂ hs U hU
    have hE : IsElemAb 2 6 (Op 2 (Nor U)) := (h48 G b L B K b₁ b₂ hs U hU).2.1
    have ht : orderOf t = 2 := by
      haveI := hE.1
      exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t hD.2.2.1) hD.2.2.2.2.1
    exact ⟨t, ht, (h411 G b L B K b₁ b₂ hs U hU s t hD).1⟩

end CFSG.RankThree.PartTwo.Sec21.FF84
