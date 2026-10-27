module

public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.LargeEvenClassification.LocalRank
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Rank

variable {G : Type} [Group G] [Finite G]

theorem le_twoLocalRank_of_normalizes {p : ℕ} (hp : p.Prime) {U E : Subgroup G} (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hE : IsElemAbelian p E) (hEU : E ≤ Subgroup.normalizer (U : Set G))
    {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ LargeEvenTwoLocalRank p G := by
  have hloc : CFSG.Open.IsTwoLocal (Subgroup.normalizer (U : Set G)) := ⟨U, hU, hU2, rfl⟩
  exact (CFSG.SectionRank.le_pRank hp.one_lt hEU hE hk).trans
    (CFSG.LargeEvenClassification.Helpers.pRank_le_twoLocalPRank hp.one_lt _ hloc)

theorem isElemAbelian_sup_zpowers_of_card {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) {z : G} (hzp : z ^ p = 1)
    (hzE : z ∉ E) (hz : ∀ e ∈ E, e * z = z * e) :
    IsElemAbelian p (E ⊔ Subgroup.zpowers z) ∧
      Nat.card (E ⊔ Subgroup.zpowers z : Subgroup G) = p ^ (k + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hz1 : z ≠ 1 := fun h => hzE (h ▸ E.one_mem)
  have hcardz : Nat.card (Subgroup.zpowers z) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hzp hz1]
  have hnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer (E : Set G) (Subgroup.mem_centralizer_iff.mpr hz)
  have hdisj : Disjoint E (Subgroup.zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro g hgE hgz
    have : Fact (Nat.card (Subgroup.zpowers z)).Prime := ⟨by rw [hcardz]; exact hp⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (E.subgroupOf (Subgroup.zpowers z)) with h | h
    · have hg : (⟨g, hgz⟩ : Subgroup.zpowers z) ∈ E.subgroupOf (Subgroup.zpowers z) := hgE
      rw [h] at hg
      exact congrArg Subtype.val (Subgroup.mem_bot.1 hg)
    · exfalso
      have hf : (⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z) ∈
          E.subgroupOf (Subgroup.zpowers z) := by
        rw [h]
        trivial
      exact hzE hf
  refine ⟨CFSG.Open.IsElemAbelian.sup_of_commute hE (CFSG.Open.isElemAbelian_zpowers hzp) ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (hz a ha) n).eq
  · rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E _ hnorm hdisj, hk,
      hcardz, pow_succ]

theorem five_le_twoLocalRank_of_normalizing {L : Subgroup G} {x : G}
    (hxL : L ≤ Subgroup.centralizer ({x} : Set G)) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    {U E : Subgroup L} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hEU : E ≤ Subgroup.normalizer (U : Set L)) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 5 ∨ (Nat.card E = 3 ^ 4 ∧ E ⊓ Subgroup.center L = ⊥)) :
    5 ≤ LargeEvenTwoLocalRank 3 G := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hU' : U.map L.subtype ≠ ⊥ := fun h =>
    hU ((Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 h)
  have hU'2 : IsPGroup 2 (U.map L.subtype) := hU2.map L.subtype
  have hE' : IsElemAbelian 3 (E.map L.subtype) := CFSG.Open.IsElemAbelian.map hE L.subtype
  have hE'N : E.map L.subtype ≤ Subgroup.normalizer (U.map L.subtype : Set G) :=
    (Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map L.subtype)
  have hE'card : Nat.card (E.map L.subtype) = Nat.card E :=
    Subgroup.card_map_of_injective L.subtype_injective
  rcases hcard with h5 | ⟨h4, hZ⟩
  · exact le_twoLocalRank_of_normalizes hp hU' hU'2 hE' hE'N (by rw [hE'card, h5])
  · have hEL : ∀ e ∈ E.map L.subtype, e ∈ L := by
      rintro _ ⟨e, -, rfl⟩
      exact e.2
    have hcomm : ∀ e ∈ E.map L.subtype, e * x = x * e := fun e he =>
      Subgroup.mem_centralizer_singleton_iff.1 (hxL (hEL e he))
    have hxE : x ∉ E.map L.subtype := by
      intro hx
      obtain ⟨e, he, hex'⟩ := hx
      have hex : (e : G) = x := hex'
      have hec : e ∈ Subgroup.center L := by
        rw [Subgroup.mem_center_iff]
        intro l
        apply Subtype.ext
        change (l : G) * (e : G) = (e : G) * l
        rw [hex]
        exact Subgroup.mem_centralizer_singleton_iff.1 (hxL l.2)
      have he1 : e = 1 := by
        have : e ∈ E ⊓ Subgroup.center L := ⟨he, hec⟩
        rw [hZ] at this
        exact Subgroup.mem_bot.1 this
      apply hx1
      rw [← hex, he1]
      rfl
    obtain ⟨hab, hcard'⟩ := isElemAbelian_sup_zpowers_of_card hp hE' (k := 4)
      (by rw [hE'card, h4]) hx3 hxE hcomm
    have hxU : x ∈ Subgroup.centralizer (U.map L.subtype : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.1
        (hxL (Subgroup.map_subtype_le _ hh))
    have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (U.map L.subtype : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le_normalizer _ hxU
    exact le_twoLocalRank_of_normalizes hp hU' hU'2 hab (sup_le hE'N hxN) hcard'

theorem five_le_twoLocalRank_of_twE6 (hE6 : GGTwE6LocalRankInput) {L : Subgroup G} {x : G}
    (hxL : L ≤ Subgroup.centralizer ({x} : Set G)) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hM : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twE6 ∧ LargeEvenSplit 3 lab)) :
    5 ≤ LargeEvenTwoLocalRank 3 G := by
  have hM' := largeEvenMarking_and_labelAll_simple_imp
    (S := fun lab => lab.tag = .twE6 ∧ LargeEvenSplit 3 lab)
    (P' := fun R _ _ _ => GGTwE6LocalRank R)
    (fun lab hlab hS => largeEvenLabelAll_twE6_rank hE6 hlab hS.1 hS.2) hM
  obtain ⟨hLperf, lab, hlab, hraw⟩ := hM'
  obtain ⟨R, _, I, F, hs, hna, θ, hθ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hS, hrank⟩ := hθ
  obtain ⟨U, hU, hU2, E, hEU, hE, hcard⟩ := hrank hS L hLperf θ
  exact five_le_twoLocalRank_of_normalizing hxL hx1 hx3 hU hU2 hEU hE hcard

end Rank

end CFSG.StandardType
