module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABDA1B
public import CFSG.GroupTheory.PRankBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16h_sl28_seven_pRank_le_inf_centralizer_add_one {X : Type} [Group X] [Finite X]
    {L E : Subgroup X} (hL : IsSLn ↥L 2 3)
    (hEN : E ≤ Subgroup.normalizer (L : Set X)) :
    CFSG.Open.pRank 7 E ≤
      CFSG.Open.pRank 7 (E ⊓ Subgroup.centralizer (L : Set X)) + 1 := by
  let φ : ↥E →* MulAut ↥L :=
    (Subgroup.normalizerMonoidHom (H := L)).comp (Subgroup.inclusion hEN)
  have hineq := CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map
    (p := 7) Nat.prime_seven φ (⊤ : Subgroup ↥E)
  rw [top_inf_eq, ← MonoidHom.range_eq_map] at hineq
  have hker_eq : φ.ker = (Subgroup.centralizer (L : Set X)).comap E.subtype := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    change Subgroup.normalizerMonoidHom (H := L) (Subgroup.inclusion hEN e) = 1 ↔
      (e : X) ∈ Subgroup.centralizer (L : Set X)
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
      Subgroup.coe_inclusion]
  have hmap : φ.ker.map E.subtype = E ⊓ Subgroup.centralizer (L : Set X) := by
    rw [hker_eq, Subgroup.map_comap_eq E.subtype, Subgroup.range_subtype]
  have hker : CFSG.Open.pRank 7 φ.ker ≤
      CFSG.Open.pRank 7 (E ⊓ Subgroup.centralizer (L : Set X)) := by
    calc CFSG.Open.pRank 7 φ.ker
        ≤ CFSG.Open.pRank 7 (φ.ker.map E.subtype) :=
          CFSG.SectionRank.pRank_le_map (by norm_num : 1 < 7) E.subtype
            E.subtype_injective φ.ker
      _ = CFSG.Open.pRank 7 (E ⊓ Subgroup.centralizer (L : Set X)) := by rw [hmap]
  have hrange : CFSG.Open.pRank 7 φ.range ≤ 1 := by
    refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (H := φ.range) (p := 7) (k := 1)
      Nat.prime_seven ?_
    intro hdiv
    have hdvd : Nat.card ↥φ.range ∣ Nat.card (MulAut ↥L) := by
      simpa only [Subgroup.card_top] using
        Subgroup.card_dvd_of_le (H := φ.range) le_top
    rw [s16h_sl28_card_mulAut_of_isSLn hL] at hdvd
    exact (by norm_num : ¬ 7 ^ 2 ∣ 1512) (hdiv.trans hdvd)
  have hleft : CFSG.Open.pRank 7 E = CFSG.Open.pRank 7 (⊤ : Subgroup ↥E) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup E
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo