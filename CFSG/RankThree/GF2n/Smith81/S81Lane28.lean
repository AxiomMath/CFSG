module

public import CFSG.RankThree.GF2n.Smith81.S81BLane
public import CFSG.RankThree.GF2n.Smith81.Orth216Odd
public import CFSG.RankThree.GF2n.Smith81.ELane

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

@[expose] def Smith28E3UStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3U M Q Z B → ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
      ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X

@[expose] def Smith28E3LStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3L M Q Z B → ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
      ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X

@[expose] def Smith28E4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE4 M Q Z B → ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
      ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X

@[expose] def Smith28E5Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE5 M Q Z B → ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
      ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X

theorem smith28E_iff_cases :
    Smith28EStatement ↔ Smith28E3UStatement ∧ Smith28E3LStatement ∧ Smith28E4Statement ∧
      Smith28E5Statement := by
  constructor
  · intro h
    exact ⟨fun G _ _ M Q Z B IH hc _ => h G M Q Z B IH hc,
      fun G _ _ M Q Z B IH hc _ => h G M Q Z B IH hc,
      fun G _ _ M Q Z B IH hc _ => h G M Q Z B IH hc,
      fun G _ _ M Q Z B IH hc _ => h G M Q Z B IH hc⟩
  · rintro ⟨h3U, h3L, h4, h5⟩ G _ _ M Q Z B IH hc
    rcases hc.inCase with hh | hh | hh | hh
    · exact h3U G M Q Z B IH hc hh
    · exact h3L G M Q Z B IH hc hh
    · exact h4 G M Q Z B IH hc hh
    · exact h5 G M Q Z B IH hc hh

theorem smith28E_of_cases (h3U : Smith28E3UStatement) (h3L : Smith28E3LStatement)
    (h4 : Smith28E4Statement) (h5 : Smith28E5Statement) : Smith28EStatement :=
  smith28E_iff_cases.mpr ⟨h3U, h3L, h4, h5⟩

section Lane

theorem smith216EOdd_of_28_nonfused (h28 : Smith28EStatement) (hN : Smith212ENonfusedStatement)
    (h213 : Smith213EStatement) (hCount : Smith216ECountStatement) : Smith216EOddStatement := by
  intro G _ _ M Q Z B IH hc z hz hz1 x z' w y hx hz' hw hy hxz hzw hwy hxw _ ho1 _
  refine Smith216Odd.odd_reduce hc.ctx.hyp hz hz1 ?_ (h213 G M Q Z B IH hc z hz hz1) ?_
    (fun X x' hs => h28 G M Q Z B IH hc X x' hs) hx hz' hw hy hxz hzw hwy hxw ho1
  · intro x' hxM hxQ hxc y' hy'cos hy'c
    have h1 : conjClassSet z ∩ cosetSet x' Z = {x'} :=
      conjClassSet_inter_cosetSet_eq hxc (hN G M Q Z B IH hc z hz hz1 x' hxM hxQ hxc)
    have hmem : y' ∈ conjClassSet z ∩ cosetSet x' Z := ⟨hy'c, hy'cos⟩
    rw [h1] at hmem
    exact hmem
  · exact fun A C hA hC hAC hCA => hCount G M Q Z B IH hc z hz hz1 A C hA hC hAC hCA

theorem smithLaneE_of_28 (hT : TimmesfeldOutcomeStatement)
    (hN : Smith212ENonfusedStatement) (h213 : Smith213EStatement)
    (hCount : Smith216ECountStatement) (h28 : Smith28EStatement) (h217 : Smith217Statement)
    (hInsp : Smith219EInspectionStatement) : LaneEStep := by
  have h216 := smith216E_of_nonfused hN h213 hCount
    (smith216EOdd_of_28_nonfused h28 hN h213 hCount)
  intro G _ _ hb M Q Z hH B hB hBQ hBZ hC
  have hcfg : Cfg M Q Z B := ⟨⟨hH, hB, hBQ, hBZ⟩, hC⟩
  have key : ECase M Q Z B → SmithLaneE M Q Z B := by
    intro hE
    have hEC : SmithECfg M Q Z B := ⟨hcfg, hE⟩
    obtain ⟨z₀, hz₀, hz₀1, -⟩ := exists_mem_Z_ne hH 1
    have hroot := smith218E_of_statements h213 h216 h217 G M Q Z B hb hEC
    exact hInsp G M Q Z B hb hEC hroot
      (outcome_of_conjClassSet hT hH hz₀ hz₀1 (hroot z₀ hz₀ hz₀1))
  refine ⟨fun t ht h => ?_, fun t ht h => ?_, fun t ht h => ?_, fun t ht h => ?_⟩
  · exact (key ⟨t, ht, Or.inl ((caseE3_iff M Q Z B).mpr (Or.inl h))⟩).1 t ht h
  · exact (key ⟨t, ht, Or.inl ((caseE3_iff M Q Z B).mpr (Or.inr h))⟩).2.1 t ht h
  · exact (key ⟨t, ht, Or.inr (Or.inl h)⟩).2.2.1 t ht h
  · exact (key ⟨t, ht, Or.inr (Or.inr h)⟩).2.2.2 t ht h

end Lane

end CFSG.RankThree.GF2n.Smith81
