module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseBasic
import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuterU3
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwoLinTwo
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.LinTwo
import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.RankOneA1Index
import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open
open scoped Pointwise commutatorElement

theorem phase45_exists_gen_linTwo_thirtyOne {X : Type} [Group X] [Finite X]
    {L A₁ T : Subgroup X} {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.p = 31 ∧ d.1 = .A 1 q)
    (e : ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) (hA1L : A₁ ≤ L) (hA1 : Nat.card A₁ = 31)
    (hTL : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L) :
    ∃ C : Subgroup X, IsMulCommutative C ∧ A₁ ≤ C ∧
      L ≤ (T ⊓ L) ⊔ (L ⊓ normalizer (C : Set X)) := by
  obtain ⟨q, hq31, hdq⟩ := hd
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hqpos : 1 ≤ q.exponent := q.exponent_pos
  obtain ⟨e2⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
    (p := 31) (n := q.exponent) (d := d) ⟨q, hdq, hq31, rfl⟩
  let eL : ↥L ≃* CFSG.AGLEmbedding.PSL2GF 31 q.exponent := e.trans e2
  have hA1subcard : Nat.card (A₁.subgroupOf L) = 31 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA1L).toEquiv, hA1]
  have hA1subP : IsPGroup 31 (A₁.subgroupOf L) :=
    IsPGroup.of_card (n := 1) (by rw [hA1subcard, pow_one])
  obtain ⟨U, hA1U⟩ := hA1subP.exists_le_sylow
  haveI hUab : IsMulCommutative ↥(U : Subgroup ↥L) := by
    haveI : IsMulCommutative ↥((U : Subgroup ↥L).map eL.toMonoidHom) :=
      (CFSG.AGLEmbedding.psl2GF_sylow 31 q.exponent hqpos
        (U.mapSurjective (f := eL.toMonoidHom) eL.surjective)).1.1
    have h := Subgroup.comap_injective_isMulCommutative
      ((U : Subgroup ↥L).map eL.toMonoidHom) (f := eL.toMonoidHom) eL.injective
    rwa [Subgroup.comap_map_eq_self_of_injective eL.injective] at h
  let C : Subgroup X := (U : Subgroup ↥L).map L.subtype
  have hCab : IsMulCommutative C :=
    Subgroup.map_isMulCommutative (U : Subgroup ↥L) L.subtype
  have hA1C : A₁ ≤ C := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hA1L]
    exact Subgroup.map_mono hA1U
  refine ⟨C, hCab, hA1C, ?_⟩
  let N : Subgroup ↥L := Subgroup.normalizer ((U : Subgroup ↥L) : Set ↥L)
  have hcoat : IsCoatom N :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.isCoatom_normalizer_of_mulEquiv_psl2GF
      (p := 31) (n := q.exponent) (by norm_num) hqpos eL U
  have hNindex : N.index = 31 ^ q.exponent + 1 :=
    CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.index_normalizer_of_equiv
      (p := 31) (n := q.exponent) (by norm_num) hqpos eL U
  obtain ⟨Q, hQ⟩ := hTL.exists_sylow_eq_subgroupOf
  have hnotle : ¬ (Q : Subgroup ↥L) ≤ N := by
    intro hQN
    have hdvd : N.index ∣ (Q : Subgroup ↥L).index := Subgroup.index_dvd_of_le hQN
    have hodd : ¬ 2 ∣ N.index := fun h2 => (Sylow.not_dvd_index Q) (h2.trans hdvd)
    apply hodd
    rw [hNindex]
    exact even_iff_two_dvd.mp ((show Odd 31 by norm_num).pow.add_one)
  have hsup : (Q : Subgroup ↥L) ⊔ N = ⊤ := by
    have hne : (Q : Subgroup ↥L) ⊔ N ≠ N := fun h =>
      hnotle (le_sup_left.trans (le_of_eq h))
    exact (hcoat.ne_iff_eq_top le_sup_right).mp hne
  have hmap : ((Q : Subgroup ↥L).map L.subtype) ⊔ (N.map L.subtype) = L := by
    have h := congrArg (Subgroup.map L.subtype) hsup
    simpa only [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] using h
  have hQmap : ((Q : Subgroup ↥L).map L.subtype) = T ⊓ L := by
    rw [hQ, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (show T ⊓ L ≤ L from inf_le_right)]
  have hCrange : C ≤ L.subtype.range := by
    rw [Subgroup.range_subtype]
    exact Subgroup.map_subtype_le (U : Subgroup ↥L)
  have hcomap : (Subgroup.normalizer (C : Set X)).comap L.subtype = N := by
    rw [Subgroup.comap_normalizer_eq_of_le_range (f := L.subtype) (H := C) hCrange,
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective (U : Subgroup ↥L)]
  have hNmap : N.map L.subtype = L ⊓ Subgroup.normalizer (C : Set X) := by
    rw [← hcomap, Subgroup.map_comap_eq, Subgroup.range_subtype]
  rw [hQmap, hNmap] at hmap
  exact hmap.ge

theorem phase45_false_of_rankOne_thirtyOne (hK4 : K45UnitaryThirtyOneGen) {X : Type} [Group X]
    [Finite X] {L A₁ A₂ B T ML : Subgroup X} (hc : PhaseConfig45 L A₁ A₂ B T ML)
    {d : TauCeti.ValidLieTypeIndex} (e : ↥L ≃* (TauCeti.CFSGIndex.lie d).Group)
    (h31 : d.1.characteristic = 31) (hd : RankOneIndex45 d.1) : False := by
  rcases hd with ⟨q, hq | hq⟩
  · have hq31 : q.p = 31 := by
      rw [hq, TauCeti.LieTypeIndex.characteristic_A] at h31
      exact h31
    haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
    have hqpos : 1 ≤ q.exponent := q.exponent_pos
    obtain ⟨e2⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
      (p := 31) (n := q.exponent) (d := d) ⟨q, hq, hq31, rfl⟩
    have hout : CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuter.IsPByAbelian 3
        (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L) :=
      CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuter.IsPByAbelian.of_commutative
        (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo.outer_comm_of_mulEquiv_psl2GF
          (e.trans e2))
    have hA1L : A₁ ≤ L :=
      le_trans le_sup_left
        (phase45_sup_le_of_isPByAbelian_outer hc.hLn hc.hCL hc.hA1 hc.hA2 hc.hA12c hc.hcomm hout)
    obtain ⟨C, hCab, hA1C, hgen⟩ :=
      phase45_exists_gen_linTwo_thirtyOne ⟨q, hq31, hq⟩ e hA1L hc.hA1 hc.hTL
    exact phase45_false_of_generation hc.hML hc.hMLne hc.hTML hc.hC5 hCab hA1C hgen
  · have hq31 : q.p = 31 := by
      rw [hq, TauCeti.LieTypeIndex.characteristic_twistedA] at h31
      exact h31
    have hout : CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuter.IsPByAbelian 3
        (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L) :=
      CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuter.IsPByAbelian.map_equiv
        (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).symm
        (CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuter.isPByAbelian_outer_twistedA_two d q hq)
    have hA1L : A₁ ≤ L :=
      le_trans le_sup_left
        (phase45_sup_le_of_isPByAbelian_outer hc.hLn hc.hCL hc.hA1 hc.hA2 hc.hA12c hc.hcomm hout)
    obtain ⟨C, hCab, hA1C, hgen⟩ :=
      hK4 X L A₁ T d ⟨e⟩ ⟨q, hq31, hq⟩ hA1L hc.hA1 hc.hTL
    exact phase45_false_of_generation hc.hML hc.hMLne hc.hTML hc.hC5 hCab hA1C hgen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
