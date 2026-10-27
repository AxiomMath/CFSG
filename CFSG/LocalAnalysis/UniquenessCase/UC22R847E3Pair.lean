module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem pRank_add_one_le_of_commute {H : Type} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) {B C : Subgroup H} {t : H} (htp : t ^ p = 1) (htB : t ∉ B)
    (htc : ∀ b ∈ B, t * b = b * t) (hBC : B ≤ C) (htC : t ∈ C) :
    CFSG.Open.pRank p B + 1 ≤ CFSG.Open.pRank p C := by
  obtain ⟨E, hEB, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt B
  exact CFSG.AGLEmbedding.succ_le_pRank_of_isElemAbelian_of_mem_centralizer hp hE hcard htp
    (fun h => htB (hEB h)) (mem_centralizer_iff.mpr fun e he => (htc e (hEB he)).symm)
    (hEB.trans hBC) htC

private theorem exists_pow_eq_one_not_mem_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {M J : Subgroup G} (hJ : J ∈ calC M) (hJ1 : 1 ≤ CFSG.Open.pRank p J) :
    ∃ z ∈ barImage M J, z ^ p = 1 ∧ z ∉ centralizer (barImage M J : Set (Bar2 M)) := by
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hJ
  have hq : CFSG.Open.IsQuasisimple ↥(barImage M J) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hJ.2.2
  have hdvd : p ∣ Nat.card ↥(barImage M J) := by
    obtain ⟨E, hEJ, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (barImage M J)
    rw [PartTwo.s13_pRank_barImage hp hp2 (PartTwo.s13_le_of_mem_calC hJ)] at hE
    exact (dvd_pow_self p (by omega)).trans (hE ▸ card_dvd_of_le hEJ)
  obtain ⟨z, hz, hzZ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center hq hp
      hp2 hdvd
  refine ⟨z, z.2, by rw [← hz, ← orderOf_coe, pow_orderOf_eq_one], fun h => hzZ ?_⟩
  exact mem_center_iff.mpr fun w => Subtype.ext (mem_centralizer_iff.mp h w w.2)

theorem pRank_centE_add_two_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M Y K : Subgroup G}
    (hY : Y ∈ calC M) (hK : K ∈ calC M) (hYK : Y ≠ K) (hY1 : 1 ≤ CFSG.Open.pRank p Y)
    (hK1 : 1 ≤ CFSG.Open.pRank p K) :
    CFSG.Open.pRank p (barPreimage M (centE M)) + 2 ≤ CFSG.Open.pRank p M := by
  have hC : ∀ {J : Subgroup G}, J ∈ calC M →
      centE M ≤ centralizer (barImage M J : Set (Bar2 M)) := fun hJ =>
    centralizer_le (CFSG.LocalCores.component_le_layer (PartTwo.s13_barImage_isComponent hJ))
  obtain ⟨x, hxK, hxp, hxc⟩ := exists_pow_eq_one_not_mem_centralizer hp hp2 hK hK1
  obtain ⟨y, hyY, hyp, hyc⟩ := exists_pow_eq_one_not_mem_centralizer hp hp2 hY hY1
  have hB : zpowers x ⊔ centE M ≤ centralizer (barImage M Y : Set (Bar2 M)) :=
    sup_le (zpowers_le.mpr (mem_centralizer_iff.mpr fun a ha =>
      uc22p22l_barImage_commute hY hK hYK a ha x hxK)) (hC hY)
  have h1 := pRank_add_one_le_of_commute (B := centE M) (C := zpowers x ⊔ centE M) hp hxp
    (fun h => hxc (hC hK h)) (fun b hb => mem_centralizer_iff.mp (hC hK hb) x hxK) le_sup_right
    (mem_sup_left (mem_zpowers x))
  have h2 := pRank_add_one_le_of_commute (B := zpowers x ⊔ centE M) (C := ⊤) hp hyp
    (fun h => hyc (hB h)) (fun b hb => mem_centralizer_iff.mp (hB hb) y hyY) le_top (mem_top y)
  have hCp : CFSG.Open.pRank p (barPreimage M (centE M)) = CFSG.Open.pRank p (centE M) := by
    rw [← PartTwo.s13_pRank_barImage (P := barPreimage M (centE M)) hp hp2 (map_subtype_le _),
      barImage_barPreimage]
  rw [pRank_bar2_eq_of_odd hp hp2] at h2
  omega

theorem r847ThinPair_of_r847E3Thin {D : Data G} (h847 : R847E3Thin D) (he : evenRank G = 3)
    (hsig : D.sig.Nonempty) :
    ∀ Y ∈ calC D.M, (Y.subgroupOf D.M).Normal → F08.Thin8 Y → 1 ≤ CFSG.Open.pRank 3 Y →
      ∀ K ∈ calC D.M, K ≠ Y → 1 ≤ CFSG.Open.pRank 3 K →
      ∀ X : Subgroup G, X ≤ Y → (Nat.card X).Prime → Nat.card X ≠ 2 →
      normalizer (X : Set G) ≤ D.M := by
  intro Y hY hYN hthin hY1 K hK hKY hK1 X hXY hXp hX2
  obtain ⟨p, hp⟩ := hsig
  rcases h847 Y hY hYN hthin X hXY _ hXp hX2 rfl p hp with h | ⟨-, h2⟩
  · exact h
  · have h4 := pRank_centE_add_two_le Nat.prime_three (by norm_num) hY hK hKY.symm hY1 hK1
    have h3 := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) D.M D.maxLocal.1
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
