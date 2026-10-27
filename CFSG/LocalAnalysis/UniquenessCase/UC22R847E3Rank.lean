module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3
import CFSG.LocalAnalysis.AGLEmbedding.RankTools
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem pRank_add_le_pRank_sup_of_le_centralizer {H : Type} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) {A B : Subgroup H} (hBA : B ≤ centralizer (A : Set H))
    (hZ : ¬ p ∣ Nat.card (center A)) :
    CFSG.Open.pRank p A + CFSG.Open.pRank p B ≤ CFSG.Open.pRank p (A ⊔ B) := by
  have hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    mem_centralizer_iff.mp (hBA hy) x hx
  have hle : A ⊓ B ≤ (center A).map A.subtype := fun x hx =>
    ⟨⟨x, hx.1⟩, mem_center_iff.mpr fun a => Subtype.ext (hc a a.2 x hx.2), rfl⟩
  have hdvd : Nat.card ↥(A ⊓ B) ∣ Nat.card (center A) := by
    have h := card_dvd_of_le hle
    rwa [card_map_of_injective A.subtype_injective] at h
  exact CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime hp hc
    (hp.coprime_iff_not_dvd.mpr fun h => hZ (h.trans hdvd))

theorem pRank_add_pRank_add_pRank_centE_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {M Y K : Subgroup G} (hY : Y ∈ calC M) (hK : K ∈ calC M) (hYK : Y ≠ K)
    (hZY : ¬ p ∣ Nat.card (center (Bar2 Y))) (hZK : ¬ p ∣ Nat.card (center (Bar2 K))) :
    CFSG.Open.pRank p Y + CFSG.Open.pRank p K + CFSG.Open.pRank p (barPreimage M (centE M)) ≤
      CFSG.Open.pRank p M := by
  have hZ : ∀ {J : Subgroup G}, J ∈ calC M → ¬ p ∣ Nat.card (center (Bar2 J)) →
      ¬ p ∣ Nat.card (center (barImage M J)) := fun hJ hZJ => by
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hJ
    rwa [← Nat.card_congr (centerCongr e).toEquiv]
  have hC : ∀ {J : Subgroup G}, J ∈ calC M →
      centE M ≤ centralizer (barImage M J : Set (Bar2 M)) := fun hJ =>
    centralizer_le (CFSG.LocalCores.component_le_layer (PartTwo.s13_barImage_isComponent hJ))
  have hKY : barImage M K ≤ centralizer (barImage M Y : Set (Bar2 M)) := fun b hb =>
    mem_centralizer_iff.mpr fun a ha => uc22p22l_barImage_commute hY hK hYK a ha b hb
  have h1 := pRank_add_le_pRank_sup_of_le_centralizer hp (hC hK) (hZ hK hZK)
  have h2 := pRank_add_le_pRank_sup_of_le_centralizer hp (sup_le hKY (hC hY)) (hZ hY hZY)
  have h3 : CFSG.Open.pRank p (barImage M Y ⊔ (barImage M K ⊔ centE M)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (Bar2 M)) :=
    CFSG.SectionRank.pRank_mono hp.one_lt le_top
  have hCp : CFSG.Open.pRank p (barPreimage M (centE M)) = CFSG.Open.pRank p (centE M) := by
    rw [← PartTwo.s13_pRank_barImage (P := barPreimage M (centE M)) hp hp2 (map_subtype_le _),
      barImage_barPreimage]
  rw [pRank_bar2_eq_of_odd hp hp2] at h3
  rw [PartTwo.s13_pRank_barImage hp hp2 (PartTwo.s13_le_of_mem_calC hY)] at h2
  rw [PartTwo.s13_pRank_barImage hp hp2 (PartTwo.s13_le_of_mem_calC hK)] at h1
  omega

theorem R847E3.normalizer_le_of_thin_of_ne {D : Data G} (h847 : R847E3Thin D)
    (he : evenRank G = 3) (hsig : D.sig.Nonempty) {Y K : Subgroup G} (hY : Y ∈ calC D.M)
    (hYN : (Y.subgroupOf D.M).Normal) (hthin : F08.Thin8 Y) (hK : K ∈ calC D.M) (hYK : Y ≠ K)
    (hZY : ¬ 3 ∣ Nat.card (center (Bar2 Y))) (hZK : ¬ 3 ∣ Nat.card (center (Bar2 K)))
    (hY1 : 1 ≤ CFSG.Open.pRank 3 Y) (hK1 : 1 ≤ CFSG.Open.pRank 3 K) {X : Subgroup G}
    (hXY : X ≤ Y) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hXq : Nat.card X = q) :
    normalizer (X : Set G) ≤ D.M := by
  obtain ⟨p, hp⟩ := hsig
  rcases h847 Y hY hYN hthin X hXY q hq hq2 hXq p hp with h | ⟨-, h2⟩
  · exact h
  · have h4 := pRank_add_pRank_add_pRank_centE_le Nat.prime_three (by norm_num) hY hK hYK hZY hZK
    have h3 := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) D.M D.maxLocal.1
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
