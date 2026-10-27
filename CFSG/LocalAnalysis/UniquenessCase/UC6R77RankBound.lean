module

public import CFSG.LocalAnalysis.UniquenessCase.UC6R77Heis
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1Num7
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6R77

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem card_range_dvd_of_elemAbelian {p r : ℕ} [Fact r.Prime] {P : Subgroup G}
    (hPel : IsElemAbelian p P) (χ : ↥P →* (ZMod r)ˣ) :
    Nat.card χ.range ∣ p ∧ Nat.card χ.range ∣ r - 1 := by
  refine ⟨?_, ?_⟩
  · rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext ?_
    obtain ⟨y, hy⟩ := x.2
    have hyp : y ^ p = 1 := Subtype.ext (by simpa using hPel.2 y y.2)
    rw [SubgroupClass.coe_pow, ← hy, ← map_pow, hyp, map_one, OneMemClass.coe_one]
  · have h := Subgroup.card_subgroup_dvd_card χ.range
    rwa [Nat.card_eq_fintype_card (α := (ZMod r)ˣ), ZMod.card_units r] at h

theorem rankThreeGamma_le_of_rank_bound {p r : ℕ} [hp : Fact p.Prime] [hr : Fact r.Prime]
    (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hpr : p ≠ r) {M X : Subgroup G}
    (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M)
    (h76 : PartOne.Section7.Conclusion76 M p) (hXM : X ≤ M) (hX : IsPGroup r X)
    (hnc : ¬ IsCyclic X) (hexp : ∀ x ∈ X, x ^ r = 1) (hcl : ⁅⁅X, X⁆, X⁆ = ⊥)
    (hrank : CFSG.Open.pRank r X ≤ 3) (hdisj : CFSG.Open.pRank r X ≤ 2 ∨ r + 1 < p)
    (h2 : 2 < CFSG.Open.pRank p (M ⊓ normalizer (X : Set G))) : rankThreeGamma 1 r X ≤ M := by
  obtain ⟨P, hPN, hPel, hPcard⟩ :=
    CFSG.SectionRank.exists_pRank hp.out.one_lt (M ⊓ normalizer (X : Set G))
  set m := CFSG.Open.pRank p (M ⊓ normalizer (X : Set G)) with hm
  have hPM : P ≤ M := hPN.trans inf_le_left
  have hPX : P ≤ normalizer (X : Set G) := hPN.trans inf_le_right
  have hKel : IsElemAbelian p (P ⊓ centralizer (X : Set G)) := hPel.mono inf_le_left
  obtain ⟨i, hi⟩ := hKel.isPGroup.exists_card_eq
  have hEle : ∀ k, CFSG.Open.pRank r X ≤ k → ∀ E : Subgroup G, E ≤ X →
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ r = 1) → Nat.card E ≤ r ^ k := by
    intro k hk E hEX hEc hEe
    obtain ⟨j, hj⟩ := (hX.to_le hEX).exists_card_eq
    have hEel : IsElemAbelian r E := ⟨⟨⟨fun a b => Subtype.ext (hEc a a.2 b b.2)⟩⟩, hEe⟩
    rw [hj]
    exact Nat.pow_le_pow_right hr.out.pos
      ((CFSG.SectionRank.le_pRank hr.out.one_lt hEX hEel hj).trans hk)
  obtain ⟨χ, hχ⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1.exists_rank_bound_ge5
    hr2 hp.out hpr hX hPX (hEle 3 hrank) (hdisj.imp (hEle 2) id)
  have hEP : χ.ker.map P.subtype ≤ P := map_subtype_le _
  have hker : Nat.card χ.ker ≤ p ^ (i + 1) := by
    have h := hχ _ hEP (fun a ha b hb => hPel.comm (hEP ha) (hEP hb))
      (fun a ha => hPel.2 a (hEP ha)) fun a ha => by
        obtain ⟨b, hb, rfl⟩ := ha
        exact (MonoidHom.mem_ker).1 hb
    rw [card_map_of_injective P.subtype_injective] at h
    rw [pow_succ']
    refine h.trans (Nat.mul_le_mul_left p ?_)
    rw [← hi]
    exact card_le_of_le (inf_le_inf_right _ hEP)
  have hbound : p ^ m ≤ Nat.card χ.range * p ^ (i + 1) := by
    rw [← hPcard, Subgroup.card_eq_card_quotient_mul_card_subgroup χ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv]
    exact Nat.mul_le_mul_left _ hker
  obtain ⟨hRp, hRr⟩ := card_range_dvd_of_elemAbelian hPel χ
  by_cases hi2 : 2 ≤ i
  · exact PartOne.Section7.rankThreeGamma_le_of_two_le_pRank_inf_centralizer hM h76 hXM hX
      (CFSG.LocalAnalysis.RankThreeTheoremC.two_le_pRank_of_not_isCyclic hr.out hr2 hX hnc)
      (hi2.trans (CFSG.SectionRank.le_pRank hp.out.one_lt (inf_le_inf_right _ hPM) hKel hi))
  rcases (Nat.dvd_prime hp.out).mp hRp with h1 | h1
  · rw [h1, one_mul] at hbound
    have := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hbound
    omega
  rw [h1, ← pow_succ'] at hbound
  have hmi := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hbound
  have hpr1 : p ∣ r - 1 := h1 ▸ hRr
  have hrank2 : CFSG.Open.pRank r X ≤ 2 := hdisj.resolve_right fun h => by
    have := Nat.le_of_dvd (by have := hr.out.two_le; omega) hpr1
    omega
  have hi1 : i = 1 := by omega
  by_cases hab : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a
  ·
    have hXel : IsElemAbelian r X := ⟨⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩, hexp⟩
    obtain ⟨n, hn⟩ := hX.exists_card_eq
    have hn2 : n ≤ 2 := (CFSG.SectionRank.le_pRank hr.out.one_lt le_rfl hXel hn).trans hrank2
    have hn2' : 2 ≤ n :=
      (CFSG.LocalAnalysis.RankThreeTheoremC.two_le_pRank_of_not_isCyclic hr.out hr2 hX hnc).trans
        (CFSG.SectionRank.pRank_le hr.out.one_lt fun E hEX _ => (card_le_of_le hEX).trans hn.le)
    obtain rfl : n = 2 := by omega
    exact rankThreeGamma_le_of_two_lt_pRank hpr h76 hXM hXel hn h2
  push Not at hab
  obtain ⟨a, ha, b, hb, hab⟩ := hab
  refine rankThreeGamma_le_of_pRank_le_two hp2 hpr hpr1 hM h76 hXM hX hexp hcl hrank2 ha hb hab hPM
    hPX hPel ?_ ?_ (by omega)
  · rw [hi, hPcard, ← pow_add]
    exact Nat.pow_le_pow_right hp.out.pos (by omega)
  · intro h
    rw [h, card_bot, hi1, pow_one] at hi
    exact hp.out.one_lt.ne hi
