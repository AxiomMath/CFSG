module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fix
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
import CFSG.LocalAnalysis.UniquenessCase.FundamentalOddCore
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirteenFund
import CFSG.ClassicalInvolution.Asc77.AscOddCoreNormalEng
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.Quasithin.Vol2.GoldschmidtF134OddDickson

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]


theorem uc22s2112r34_fund_onto_psl2 {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime]
    (hq : 3 < p ^ f) {K : Subgroup X} (h : IsFundamentalOver (p ^ f) K) :
    ∃ k : ℕ, 1 ≤ k ∧ p ^ f ≤ p ^ k ∧
      ∃ g : ↥K →* PSL(2, GaloisField p k), Function.Surjective g := by
  have hp : p.Prime := Fact.out
  obtain ⟨-, q', ⟨r, k, hr, -, hq'eq, hk, hm⟩, hq', -⟩ :=
    PartTwo.S17.isFundamentalOver_quasisimple_shape hq h
  have hrq : r ∣ p ^ f := by
    have h1 : r ∣ q' := by
      rw [hq'eq]
      exact dvd_pow_self r (by omega)
    rcases hq' with h2 | h2
    · rwa [h2] at h1
    · rw [h2] at h1
      exact hr.dvd_of_dvd_pow h1
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow hrq)
  obtain ⟨e⟩ := CFSG.Quasithin.H13.NQCore.nonempty_mulEquiv_psl2_odd
    (CFSG.Blueprint.LieModel.statedClassicalModel hm (by decide))
  refine ⟨k, hk, ?_, e.toMonoidHom.comp (QuotientGroup.mk' (center ↥K)),
    e.surjective.comp (QuotientGroup.mk'_surjective _)⟩
  rw [← hq'eq]
  rcases hq' with h2 | h2
  · exact h2.ge
  · rw [h2]
    exact Nat.le_self_pow (by norm_num) _

theorem uc22s2112r34_pair_elemAbelian {X : Type} [Group X] [Finite X] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq : 3 < p ^ f) {K₂ K₃ : Subgroup X} (h₂ : IsFundamentalOver (p ^ f) K₂)
    (h₃ : IsFundamentalOver (p ^ f) K₃) (hc : ⁅K₂, K₃⁆ = ⊥) :
    ∃ E : Subgroup X, E ≤ K₂ ⊔ K₃ ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : ∀ {K : Subgroup X}, IsFundamentalOver (p ^ f) K →
      p ∣ Nat.card K ∧ 2 ∣ Nat.card K := by
    intro K hK
    obtain ⟨k, hk, hfk, g, hg⟩ := uc22s2112r34_fund_onto_psl2 hq hK
    obtain ⟨-, -, -, hpk⟩ := uc22s2112r2_psl2_facts hp2 hk (by omega)
    have hS := Subgroup.card_dvd_of_surjective hg
    exact ⟨((dvd_pow_self p (by omega)).trans hpk).trans hS,
      (CFSG.RankThree.PartTwo.Sec4.Census.two_dvd_card_PSL2 _).trans hS⟩
  obtain ⟨x₂, hx₂⟩ := exists_prime_orderOf_dvd_card' p (hdvd h₂).1
  obtain ⟨x₃, hx₃⟩ := exists_prime_orderOf_dvd_card' p (hdvd h₃).1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 (hdvd h₂).2
  have hO : CFSG.ClassicalInvolution.Asc77.oddCoreOf K₂ = ⊥ :=
    oddCoreOf_eq_bot_of_isFundamentalOver h₂ ⟨y, y.2, (Subgroup.orderOf_coe y).trans hy⟩
  have hK23 : K₂ ≤ centralizer (K₃ : Set X) := commutator_eq_bot_iff_le_centralizer.1 hc
  rw [← Subgroup.orderOf_coe] at hx₂ hx₃
  have hcomm : (x₂ : X) * x₃ = x₃ * x₂ := (mem_centralizer_iff.1 (hK23 x₂.2) x₃ x₃.2).symm
  have hx₃n : (x₃ : X) ∉ zpowers (x₂ : X) := by
    intro hmem
    have hx₃K₂ : (x₃ : X) ∈ K₂ := zpowers_le.2 x₂.2 hmem
    have hle : zpowers (x₃ : X) ≤ CFSG.ClassicalInvolution.Asc77.oddCoreOf K₂ := by
      refine CFSG.ClassicalInvolution.Asc77.AscFusion.le_oddCoreOf_of_normal_odd_gen
        (zpowers_le.2 hx₃K₂) ?_ ?_
      · exact (hK23.trans (centralizer_le (SetLike.coe_subset_coe.2 (zpowers_le.2 x₃.2)))).trans
          (centralizer_le_normalizer _)
      · rw [Nat.card_zpowers, hx₃]
        exact hp.odd_of_ne_two hp2
    rw [hO] at hle
    have h1 : (x₃ : X) = 1 := mem_bot.1 (hle (mem_zpowers _))
    rw [h1, orderOf_one] at hx₃
    exact hp.one_lt.ne hx₃
  have hx₂1 : (x₂ : X) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx₂
    exact hp.one_lt.ne hx₂
  obtain ⟨hel, hcard⟩ := CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_card_sup_zpowers hp
    (by rw [← hx₂]; exact pow_orderOf_eq_one _) (by rw [← hx₃]; exact pow_orderOf_eq_one _)
    hx₂1 hx₃n hcomm
  exact ⟨_, sup_le_sup (zpowers_le.2 x₂.2) (zpowers_le.2 x₃.2), hel, hcard⟩

theorem uc22s2112r34_false_of_pair {D : Data G} {Ch : Choice2011 G} (hKF7 : KF7Use D)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hLM : L ≤ D.M) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq : 7 ≤ p ^ f) (hpσ : p ∈ D.sig) (hMs : IsStronglyPEmbedded p D.M) {b : G}
    (hbB : b ∈ c.B0) (hb : b ∈ normalizer (L : Set G)) (hbp : (orderOf b).Prime)
    (hbN : ¬ orderOf b ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L)) {K₂ K₃ : Subgroup (BarInf L)}
    (h₂ : IsFundamentalOver (p ^ f) K₂) (h₃ : IsFundamentalOver (p ^ f) K₃) (hc : ⁅K₂, K₃⁆ = ⊥)
    (hK : K₂ ⊔ K₃ ≤ signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEK, hEel, hEc⟩ := uc22s2112r34_pair_elemAbelian hp hp2 (by omega) h₂ h₃ hc
  obtain ⟨k, hk, hfk, g, hg⟩ := uc22s2112r34_fund_onto_psl2 (by omega) h₂
  obtain ⟨hs, hns, -, hdvd⟩ := uc22s2112r2_psl2_facts hp2 hk (by omega)
  have := hs
  refine uc22s2112r34_false_of_fixed hKF7 hH c hLM hpσ hMs hbB hb hbp hbN hpN
    (UC6S846.le_pRank' hp (hEK.trans hK) hEel hEc) (le_sup_left.trans hK) hns g hg
    ((dvd_pow_self p (by omega)).trans hdvd) ?_
  rintro rfl ⟨e⟩
  have h7 : 7 ≤ 5 ^ k := hq.trans hfk
  have hk2 : 2 ≤ k := by
    by_contra h
    interval_cases k
    norm_num at h7
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have h25 := (pow_dvd_pow 5 hk2).trans hdvd
  rw [Nat.card_congr e.toEquiv, h60] at h25
  norm_num at h25

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
