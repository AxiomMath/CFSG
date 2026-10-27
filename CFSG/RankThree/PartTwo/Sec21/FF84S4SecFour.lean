module

public import CFSG.RankThree.PartTwo.Sec21.FF84S21
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma13b
public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnHolds
public import CFSG.RankThree.PartTwo.Sec21.FF79GL33
public import CFSG.RankThree.PartTwo.Sec21.FF84S3B
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec4.Census.Transfer
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.Assembly.RankThreeEven (localRank)

section

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem localRank_three_le_three_of_ff84Hyp
    (h : FF84Hyp b L) : localRank 3 G ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF := ff79Hyp_four_of_ff84Hyp h
  have hbd : ∀ E : Subgroup ↥(Cen b), CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 27 := by
    intro E hE
    have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
    obtain ⟨P, hP⟩ := hEp.exists_le_sylow
    have hBS : IsSylowOf 3 (Subgroup.map (Cen b).subtype (P : Subgroup ↥(Cen b))) (Cen b) := by
      refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map _, ?_⟩
      have hsub : (Subgroup.map (Cen b).subtype (P : Subgroup ↥(Cen b))).subgroupOf (Cen b) = P := by
        ext x
        simp [Subgroup.mem_subgroupOf, Subgroup.mem_map_iff_mem (Cen b).subtype_injective]
      rw [Subgroup.relIndex, hsub]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 P.not_dvd_index
    have h27 := (FF79.ff79_1_3_of FF79.ff79KTypeLn_holds FF79.ff79KTypeLnNorm_holds
        FF79.ff79KGL33_holds G 4 (Or.inl rfl) b L hF _ hBS).1.2
    rw [Subgroup.card_map_of_injective (Cen b).subtype_injective] at h27
    calc Nat.card E ≤ Nat.card (P : Subgroup ↥(Cen b)) := Subgroup.card_le_of_le hP
      _ = 27 := by rw [h27]; norm_num
  have hle3 : ∀ E : Subgroup ↥(Cen b), CFSG.Open.IsElemAbelian 3 E → ∀ k, Nat.card E = 3 ^ k →
      k ≤ 3 := by
    intro E hE k hk
    have := hbd E hE
    rw [hk] at this
    by_contra hlt
    have h4 : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hp1 : CFSG.Open.pRank 3 (Cen b) ≤ 3 := by
    refine csSup_le' ?_
    rintro k ⟨E, hEC, hE, hk⟩
    exact hle3 (E.subgroupOf (Cen b)) (CFSG.Open.IsElemAbelian.subgroupOf hE (Cen b)) k
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv]; exact hk)
  rw [hF.rank]
  exact hp1

theorem sectionFourHyp_of_ff84Hyp
    (h : FF84Hyp b L) (D : Subgroup G) (hD : D ≠ ⊤) : PartTwo.SectionFourHyp ↥D := by
  have hK : KCore.KGroupNonab Assembly.InCatalog ↥D := S3.B_kgroup h.iii D hD
  have h3 := localRank_three_le_three_of_ff84Hyp h
  have hlt : ∀ p : ℕ, p.Prime → 3 < p → localRank p ↥D < 3 := fun p hp hp3 =>
    (localRank_subgroup_le hp D).trans_lt (lt_of_le_of_lt (h.i p hp hp3) (by norm_num))
  refine ⟨KCore.KGroupNonab.kGroupAllSimple Assembly.inCatalog_isoInvariant
      Assembly.inCatalog_containsAbelianSimple hK, ?_, hlt⟩
  refine Sec4.Census.evenRank_le_of_localRank_le fun p hp hp2 => ?_
  rcases (show p = 3 ∨ 3 < p by have := hp.two_le; omega) with rfl | hp3
  · exact (localRank_subgroup_le hp D).trans h3
  · exact (hlt p hp hp3).le.trans (by norm_num)

end

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
