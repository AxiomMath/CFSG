module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace P22fin3

theorem mem_centralizer_barImage_sup {M : Subgroup G} {a b : G} (haM : a ∈ M) (hbM : b ∈ M)
    {x : Bar2 M} (ha : Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩) x)
    (hb : Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩) x) :
    x ∈ centralizer (barImage M (zpowers b ⊔ zpowers a) : Set (Bar2 M)) := by
  have hT : zpowers b ⊔ zpowers a ≤
      ((centralizer {x}).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype :=
    sup_le (zpowers_le.2 ⟨⟨b, hbM⟩, Subgroup.mem_centralizer_singleton_iff.2 hb.eq, rfl⟩)
      (zpowers_le.2 ⟨⟨a, haM⟩, Subgroup.mem_centralizer_singleton_iff.2 ha.eq, rfl⟩)
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨e, he, rfl⟩
  obtain ⟨e', he', hee⟩ := hT (Subgroup.mem_subgroupOf.1 he)
  obtain rfl : e' = e := Subtype.ext hee
  exact Subgroup.mem_centralizer_singleton_iff.1 he'

theorem two_le_pRank_centralizer {M E : Subgroup G} (hEM : E ≤ M) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hE : IsPGroup r E) {x₁ x₂ : Bar2 M} (h₁ : orderOf x₁ = 3)
    (h₂ : orderOf x₂ = 3) (h12 : Commute x₁ x₂) (hx : x₂ ∉ zpowers x₁)
    (hc₁ : x₁ ∈ centralizer (barImage M E : Set (Bar2 M)))
    (hc₂ : x₂ ∈ centralizer (barImage M E : Set (Bar2 M))) :
    2 ≤ CFSG.Open.pRank 3 (M ⊓ centralizer (E : Set G)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).exists_card_eq
  have hrN : ¬ r ∣ Nat.card (CFSG.pCore 2 ↥M) := fun h => by
    rw [hk] at h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  have h3N : Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥M)) := by
    rw [hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hcen := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime r (CFSG.pCore 2 ↥M) hrN
    (E.subgroupOf M) hE.comap_subtype
  have hx1 : x₁ ≠ 1 := fun h => by
    rw [h, orderOf_one] at h₁
    norm_num at h₁
  obtain ⟨hW, hWc⟩ := CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_card_sup_zpowers Nat.prime_three
    (h₁ ▸ pow_orderOf_eq_one x₁) (h₂ ▸ pow_orderOf_eq_one x₂) hx1 hx h12.eq
  have hWle : zpowers x₁ ⊔ zpowers x₂ ≤
      (centralizer ((E.subgroupOf M : Subgroup ↥M) : Set ↥M)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := by
    rw [hcen]
    exact sup_le (zpowers_le.2 hc₁) (zpowers_le.2 hc₂)
  have h2 := UC6S846.le_pRank' Nat.prime_three hWle hW hWc
  rw [CFSG.AGLEmbedding.pRank_map_mk_eq_pRank_map_subtype Nat.prime_three _ h3N] at h2
  refine h2.trans (CFSG.SectionRank.pRank_mono (by norm_num) ?_)
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨c.2, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
  exact Subtype.ext_iff.1
    (Subgroup.mem_centralizer_iff.1 hc ⟨e, hEM he⟩ (Subgroup.mem_subgroupOf.2 he))

theorem false_of_two_le_pRank (D : Data G) {Ch : Choice2011 G} (h76 : F07.R76 D)
    (h1930 : H1930 D) (c : Ctx21 D Ch) (hk1 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    {r : ℕ} (hr : r.Prime) {E : Subgroup G} (hEM : E ≤ D.M) (hE : CFSG.Open.IsElemAbelian r E)
    (hEc : Nat.card E = r ^ 2) {b : G} (hbB : b ∈ c.B0) (hbE : b ∈ E) (hb : orderOf b = r)
    (h2 : 2 ≤ CFSG.Open.pRank 3 (D.M ⊓ centralizer (E : Set G))) : False := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hΓ := h76 3 Nat.prime_three (by norm_num) hk1 r hr E hEM hE hEc (by omega)
    fun X hX _ => (show 1 < 2 by norm_num).trans_le (h2.trans (CFSG.SectionRank.pRank_mono
      (by norm_num) (inf_le_inf_left _
        ((Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hX)).trans
          (Subgroup.centralizer_le_normalizer _)))))
  have hb1 : 1 ≤ CFSG.Open.pRank r (zpowers b) := UC6S846.le_pRank' hr le_rfl
    (CFSG.Open.isElemAbelian_zpowers (hb ▸ pow_orderOf_eq_one b))
    (by rw [Nat.card_zpowers, hb, pow_one])
  exact s21_2 D Ch h1930 { c with B := c.B0, hB := c.hB0, hle := le_rfl } _ (zpowers_le.2 hbB)
    ((CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 r E (zpowers b)
      (zpowers_le.2 hbE) hb1).trans hΓ)

end P22fin3

end CFSG.LocalAnalysis.UniquenessCase.UC22
