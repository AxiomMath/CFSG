module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.LocalAnalysis.AGLEmbedding.EscapeTwoCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff isSylowOf_of_card)

variable {G : Type} [Group G] [Finite G]

@[expose] def R912A5 (D : Data G) : Prop :=
  ∀ Y H D₃ S : Subgroup G, Hyp97 D Y H D₃ S → IsAlt (Bar2 (Opp 3 Y)) 5 → pCoreOf 2 Y ≠ ⊥ →
    CFSG.ABGLocalTools.IsSylowOf 2 S H ∧ pCoreOf 2 Y ∈ InvStar9 H Y 2

omit [Finite G] in
theorem opp_le_self (p : ℕ) (Y : Subgroup G) : Opp p Y ≤ Y := by
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  exact (closure_le Y).2 fun _ hx => hx.1

theorem le_of_le_of_isSylowOf {X Y L S : Subgroup G} (hXL : X ≤ L) (hSL : S ≤ L)
    (hS : IsSylowOf 2 S Y) (hidx : ∃ k : ℕ, (X.subgroupOf Y).index = 2 ^ k) : Y ≤ L := by
  obtain ⟨k, hk⟩ := hidx
  have h1 : ((L ⊓ Y).subgroupOf Y).index ∣ 2 ^ k := by
    rw [← hk]
    exact index_dvd_of_le fun y hy => mem_subgroupOf.2 (mem_inf.2 ⟨hXL (mem_subgroupOf.1 hy), y.2⟩)
  have h2 : ((L ⊓ Y).subgroupOf Y).index ∣ (S.subgroupOf Y).index :=
    index_dvd_of_le fun y hy => mem_subgroupOf.2 (mem_inf.2 ⟨hSL (mem_subgroupOf.1 hy), y.2⟩)
  have hodd : ¬ 2 ∣ ((L ⊓ Y).subgroupOf Y).index := fun h =>
    (isSylowOf_iff.1 hS).2.2 (h.trans h2)
  have hone : ((L ⊓ Y).subgroupOf Y).index = 1 :=
    Nat.Coprime.eq_one_of_dvd (((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd).symm.pow_right k)
      h1
  intro y hy
  have hy' : (⟨y, hy⟩ : Y) ∈ (L ⊓ Y).subgroupOf Y := by
    rw [index_eq_one.1 hone]
    exact mem_top _
  exact (mem_inf.1 (mem_subgroupOf.1 hy')).1

theorem isSylowOf_of_inf_normalizer_le {S K L : Subgroup G} (hSK : S ≤ K)
    (hKL : K ⊓ normalizer (S : Set G) ≤ L) (hSL : IsSylowOf 2 S L) : IsSylowOf 2 S K := by
  obtain ⟨Q, hQ⟩ := (hSL.isPGroup.comap_subtype (K := K)).exists_le_sylow
  have hP : IsSylowOf 2 ((Q : Subgroup K).map K.subtype) K := ⟨Q, rfl⟩
  have hSP : S ≤ (Q : Subgroup K).map K.subtype := fun s hs =>
    mem_map.2 ⟨⟨s, hSK hs⟩, hQ (mem_subgroupOf.2 hs), rfl⟩
  have hPS : (Q : Subgroup K).map K.subtype ⊓ normalizer (S : Set G) = S :=
    hSL.eq_of_le (le_inf hSP le_normalizer) ((inf_le_inf_right _ hP.le).trans hKL)
      (hP.isPGroup.to_le inf_le_left)
  rcases hSP.lt_or_eq with hlt | heq
  · obtain ⟨x, hxP, hxS, hxN⟩ :=
      CFSG.AGLEmbedding.exists_mem_normalizer_not_mem_of_lt_of_isPGroup hP.isPGroup hlt
    refine absurd ?_ hxS
    rw [← hPS]
    exact mem_inf.2 ⟨hxP, hxN⟩
  · rw [heq]
    exact hP

omit [Finite G] in
theorem normalizer_le_normalizer_of_char {C S : Subgroup G} (hCS : C ≤ S)
    (hchar : (C.subgroupOf S).Characteristic) :
    normalizer (S : Set G) ≤ normalizer (C : Set G) := by
  haveI := hchar
  have := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (C.subgroupOf S)
  rwa [subgroupOf_map_subtype, inf_eq_left.2 hCS] at this

theorem not_le_normalizer_of_hyp97 {D : Data G} (h910 : R910 D) (h9R5 : R9R5 D)
    {Y H D₃ S : Subgroup G} (hY : Hyp97 D Y H D₃ S) (hS : ¬ IsSylowOf 2 S H)
    {C : Subgroup G} (hCS : C ≤ S) (hC : C ≠ ⊥) (hchar : (C.subgroupOf S).Characteristic) :
    ¬ Y ≤ normalizer (C : Set G) := by
  intro hYC
  have hSY : IsSylowOf 2 S Y := hY.2.2.2
  have hSH : S ≤ H := hSY.le.trans hY.1.2.1.1
  have hNSC := normalizer_le_normalizer_of_char hCS hchar
  have hSM : ¬ IsSylowOf 2 S D.M := fun h => hS ((isSylowOf_of_card le_top
    (h.card_eq.trans (D.sylowM.card_eq.symm.trans D.sylowG.card_eq))).of_le hSH le_top)
  have hSMC : ¬ IsSylowOf 2 S (D.M ⊓ normalizer (C : Set G)) := fun h =>
    hSM (isSylowOf_of_inf_normalizer_le (hSY.le.trans hY.1.1.1) (inf_le_inf_left _ hNSC) h)
  have hU : calMOf (D.M ⊓ normalizer (C : Set G)) = {D.M} := h910 Y hY.2.1 C hC (hCS.trans hSY.le)
    ((normal_subgroupOf_iff_le_normalizer (hCS.trans hSY.le)).2 hYC) ⟨S, hSY, hSMC⟩
  have hCM : normalizer (C : Set G) ≤ D.M := by
    have hloc : IsTwoLocal (normalizer (C : Set G)) := ⟨C, hC, hSY.isPGroup.to_le hCS, rfl⟩
    obtain ⟨M', hCM', hmax⟩ := Finite.exists_le_maximal hloc
    have hmem : M' ∈ calMOf (D.M ⊓ normalizer (C : Set G)) :=
      ⟨⟨hmax.1, fun K hK hMK => le_antisymm (hmax.2 hK hMK) hMK⟩, inf_le_right.trans hCM'⟩
    rw [hU] at hmem
    exact hmem ▸ hCM'
  exact hS (isSylowOf_of_inf_normalizer_le hSH
    (le_inf inf_le_left (inf_le_right.trans (hNSC.trans hCM))) (h9R5 Y H D₃ S hY).2)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
