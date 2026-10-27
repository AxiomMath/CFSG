module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneONanFrame
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddKF7
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight70Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3

variable (c : Ctx82E3 D)

private lemma exists_perfect_le_inf_normalizer_of_onan
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ∃ J : Subgroup G, J ≤ c.L ⊓ Subgroup.normalizer
        (((P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) : Subgroup G) :
          Set G) ∧
      ⁅J, J⁆ = J ∧ Nat.card c.Lbar ∣ Nat.card J := by
  classical
  let Z : Subgroup G := (P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G)
  let H : Subgroup G := Subgroup.normalizer (Z : Set G)
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)
  let N : Subgroup ↥c.L := H.subgroupOf c.L
  have hNtop : N.map π = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro ℓ
    obtain ⟨n, hnH, hnmk⟩ := c.exists_mem_normalizer_mk_eq_of_onan hON hP ℓ
    exact Subgroup.mem_map.mpr
      ⟨n, Subgroup.mem_subgroupOf.mpr (by simpa [H, Z] using hnH), by simpa [π] using hnmk⟩
  haveI : Group.IsPerfect c.Lbar := Group.isPerfect_def.mpr hON.1.1
  let f : ↥N →* c.Lbar := π.comp N.subtype
  have hfsurj : Function.Surjective f := by
    intro x
    have hx : x ∈ N.map π := by rw [hNtop]; exact Subgroup.mem_top x
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨y, hy⟩, hyx⟩
  obtain ⟨P₀, hP₀perf, hP₀map⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.exists_perfect_map_eq_top f hfsurj
  let g : ↥N →* G := c.L.subtype.comp N.subtype
  let J : Subgroup G := P₀.map g
  have hginj : Function.Injective g := c.L.subtype_injective.comp N.subtype_injective
  have hJleL : J ≤ c.L := by
    rintro x ⟨y, -, rfl⟩
    exact (N.subtype y).2
  have hJleH : J ≤ H := by
    rintro x ⟨y, -, rfl⟩
    have hy : N.subtype y ∈ H.subgroupOf c.L := by simpa [N] using y.2
    exact Subgroup.mem_subgroupOf.mp hy
  have hJperf : ⁅J, J⁆ = J :=
    (Subgroup.map_commutator P₀ P₀ g).symm.trans (by rw [hP₀perf])
  have hcarddvd : Nat.card c.Lbar ∣ Nat.card P₀ := by
    simpa [hP₀map] using Subgroup.card_map_dvd P₀ f
  have hJdvd : Nat.card c.Lbar ∣ Nat.card J := by
    rw [Subgroup.card_map_of_injective hginj]
    exact hcarddvd
  exact ⟨J, le_inf hJleL hJleH, hJperf, hJdvd⟩

theorem normalizer_inf_centralizer_le_of_onan
    (hKF7 : UC22.KF7Use D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (h7 : 7 ∈ D.sig) {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    Subgroup.normalizer
      (((P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) : Subgroup G) :
        Set G) ≤ D.M := by
  classical
  let Z : Subgroup G := (P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G)
  let H : Subgroup G := Subgroup.normalizer (Z : Set G)
  change H ≤ D.M
  by_contra hHM
  have h7prime : Nat.Prime 7 := by norm_num
  have hHne : H ≠ ⊤ := by
    haveI : IsSimpleGroup G := D.standing.simple
    have hcard : Nat.card Z = 3 := c.card_inf_centralizer_of_onan hON hP
    exact CFSG.RankThree.PartOne.Sec9Excl.normalizer_ne_top_of_simple D.standing.nonab
      Nat.prime_three hcard
  have hrank : 1 < CFSG.Open.pRank 7 (H ⊓ D.M) := by
    have h3 : 3 ≤ CFSG.Open.pRank 7 (H ⊓ D.M) := by
      simpa [H, Z] using c.three_le_pRank_normalizer_inf_of_onan hON hP h7
    omega
  have hsec : UC22.F07.Sec7Hyp D 7 H :=
    ⟨h7prime, by norm_num, c.isStronglyPEmbedded_of_mem_sigma h7, hHne, hHM, hrank⟩
  have hsol : Group.IsSolvable ↥(((H ⊓ D.M).subgroupOf H).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 7 ↥H))) := by
    rcases hKF7 7 h7 H hsec with h | ⟨h75, -⟩
    · exact h
    · omega
  obtain ⟨J, hJle, hJperf, hJdvd⟩ := exists_perfect_le_inf_normalizer_of_onan c hON hP
  have h7J : 1 ≤ CFSG.Open.pRank 7 J := PartTwo.s13_one_le_pRank_of_dvd J h7prime
    ((seven_dvd_card_of_threeCover_onan hON).trans hJdvd)
  exact Section8.eight70_not_isSolvable h7prime
    (le_inf (hJle.trans inf_le_right) ((hJle.trans inf_le_left).trans c.hyp81.1)) hJperf h7J hsol

end Ctx82E3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
