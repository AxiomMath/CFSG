module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148JStruct
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
  Ronan148M

variable {G : Type} [Group G] [Finite G] {A Y : Subgroup G} [(ker148 A Y).Normal]

omit [Finite G] in
theorem img148_centPre148_eq {J : Subgroup G} :
    img148 A Y (centPre148 A Y J) =
      img148 A Y Y ⊓ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨g, hg, hgC, rfl⟩ := mem_img148_iff.mp hx
    obtain ⟨hgY, hc⟩ := Ronan148M.mem_centPre148_iff.mp hgC
    exact Subgroup.mem_inf.mpr ⟨mem_img148_iff.mpr ⟨g, hg, hgY, rfl⟩, hc⟩
  · intro x hx
    obtain ⟨hxY, hxc⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨g, hg, hgY, rfl⟩ := mem_img148_iff.mp hxY
    exact mem_img148_iff.mpr ⟨g, hg, Ronan148M.mem_centPre148_iff.mpr ⟨hgY, hxc⟩, rfl⟩

theorem pPrimeCoreOf_centPre148_eq_of_isComponent (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    {J : Subgroup G} (hJY : J ≤ Y) (hJc : IsComponent (img148 A Y J))
    (h3 : 3 ∣ Nat.card (img148 A Y J)) :
    pPrimeCoreOf 3 (centPre148 A Y J) = pPrimeCoreOf 3 Y := by
  have hR3 : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 (centPre148 A Y J)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hF3 : ¬ 3 ∣ Nat.card (img148 A Y (pPrimeCoreOf 3 (centPre148 A Y J))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_img148 hR3)
  have hF : img148 A Y (pPrimeCoreOf 3 (centPre148 A Y J)) = ⊥ := by
    refine Item148Res5.eq_bot_of_normal_centralizer_component hJc h3 (img148_mono hJY)
      (fun P hPY hPN hP3 => Item148Res5.eq_bot_of_le_img148_of_coprime hPY hPN hP3) ?_ ?_ hF3
    · rw [← img148_centPre148_eq]
      exact img148_mono (pPrimeCoreOf_le 3 _)
    · rw [← img148_centPre148_eq]
      exact img148_le_normalizer (le_normalizer_pPrimeCoreOf 3 _)
  refine le_antisymm ?_ Ronan148M.pPrimeCoreOf_le_pPrimeCoreOf_centPre148
  intro g hg
  have hgY : g ∈ Y := Ronan148M.centPre148_le (pPrimeCoreOf_le 3 _ hg)
  have hgM : g ∈ Y ⊔ A := Subgroup.mem_sup_left hgY
  have hmem : QuotientGroup.mk' (ker148 A Y) (⟨g, hgM⟩ : ↥(Y ⊔ A)) ∈
      img148 A Y (pPrimeCoreOf 3 (centPre148 A Y J)) :=
    mem_img148_iff.mpr ⟨g, hgM, hg, rfl⟩
  rw [hF, Subgroup.mem_bot] at hmem
  exact mk'_ker148_eq_one_iff.mp hmem

theorem nonempty_img148_deltaZero_centPre148_equiv (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    {J : Subgroup G} (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hJY : J ≤ Y)
    (hJc : IsComponent (img148 A Y J)) (h3 : 3 ∣ Nat.card (img148 A Y J))
    (LB : Subgroup G → Subgroup G) :
    letI := ker148_normal (le_normalizer_centPre148 (J := J) hAY hAJ)
    Nonempty (↥(img148 A (centPre148 A Y J) (deltaZero A LB (centPre148 A Y J))) ≃*
      ↥(img148 A Y (deltaZero A LB (centPre148 A Y J)))) := by
  haveI := ker148_normal (le_normalizer_centPre148 (J := J) hAY hAJ)
  have hle : deltaZero A LB (centPre148 A Y J) ≤ centPre148 A Y J :=
    sSup_le fun _ hQ => hQ.2
  exact Ronan148M.nonempty_img148_centPre148_equiv
    (pPrimeCoreOf_centPre148_eq_of_isComponent hAY hJY hJc h3) (hle.trans le_sup_left)

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
