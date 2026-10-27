module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.ClassicalInvolution.Q3.GL4Two
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly

@[expose] def SectionalTwoRankLEFour (G : Type*) [Group G] : Prop :=
  ∀ P : Subgroup G, IsPGroup 2 P → ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P

namespace SectionalRank

theorem isPGroup_pCoreOf (p : ℕ) {G : Type*} [Group G] (M : Subgroup G) :
    IsPGroup p (pCoreOf p M) :=
  (CFSG.Assembly.Dichotomy.CentralizerContainment.pCore_isPGroup_assembly p M).map M.subtype

theorem pCoreOf_subgroupOf (p : ℕ) {G : Type*} [Group G] (M : Subgroup G) :
    (pCoreOf p M).subgroupOf M = Assembly.pCore p M :=
  Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

theorem le_normalizer_pCoreOf (p : ℕ) {G : Type*} [Group G] (M : Subgroup G) :
    M ≤ Subgroup.normalizer (pCoreOf p M : Set G) := by
  have hN : ((pCoreOf p M).subgroupOf M).Normal := by
    rw [pCoreOf_subgroupOf]
    exact CFSG.Assembly.Dichotomy.CentralizerContainment.pCore_normal_assembly p M
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp hN

theorem frattini_quotient_elementary_of_rank_le_four {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (hrank : Group.rank Q ≤ 4) :
    ∃ d : ℕ, d ≤ 4 ∧ Nat.card (Q ⧸ frattini Q) = 2 ^ d ∧
      (∀ a b : Q ⧸ frattini Q, a * b = b * a) ∧ ∀ a : Q ⧸ frattini Q, a ^ 2 = 1 := by
  obtain ⟨-, hcomm, hpow, helem, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hQ
  have hcard := CFSG.elementaryAbelian_card_eq_pow_generatorRank (p := 2) (Q ⧸ frattini Q)
  refine ⟨CFSG.generatorRank (Q ⧸ frattini Q), ?_, hcard, fun a b => hcomm.is_comm.comm a b,
    hpow⟩
  rw [CFSG.generatorRank_eq_group_rank]
  exact (Group.rank_le_of_surjective (QuotientGroup.mk' (frattini Q))
    (QuotientGroup.mk'_surjective _)).trans hrank

theorem card_mulAut_frattini_quotient_dvd {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (hrank : Group.rank Q ≤ 4) : Nat.card (MulAut (Q ⧸ frattini Q)) ∣ 20160 := by
  obtain ⟨d, hd, hcard, hcomm, hpow⟩ := frattini_quotient_elementary_of_rank_le_four hQ hrank
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow hcard
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  exact CFSG.ClassicalInvolution.Q3.GL4Two.prod_dvd_of_le_four hd

theorem odd_orderOf_of_pow_prime_eq_one {X : Type*} [Group X] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {x : X} (hx : x ^ r = 1) : Odd (orderOf x) :=
  Odd.of_dvd_nat (hr.odd_of_ne_two hr2) (orderOf_dvd_of_pow_eq_one hx)

theorem exists_injective_hom_mulAut_frattini_quotient {G : Type*} [Group G] [Finite G]
    {Q E : Subgroup G} (hQ : IsPGroup 2 Q) (hEN : E ≤ Subgroup.normalizer (Q : Set G)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hEr : ∀ x ∈ E, x ^ r = 1)
    (hcore : ∀ x ∈ E, (∀ q ∈ Q, q * x = x * q) → x ∈ Q) :
    ∃ ψ : E →* MulAut (Q ⧸ frattini Q), Function.Injective ψ := by
  let ρ : E →* MulAut Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hEN)
  let f := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini Q)
  refine ⟨f.comp ρ, (injective_iff_map_eq_one _).2 fun e he => ?_⟩
  have hker : ρ e ∈ f.ker := he
  have hpowr : ρ e ^ r = 1 := by
    have : e ^ r = 1 := Subtype.ext (by simpa using hEr e e.2)
    rw [← map_pow, this, map_one]
  have hρ : ρ e = 1 :=
    CFSG.Assembly.Dichotomy.CentralizerContainment.eq_one_of_mem_of_odd_orderOf
      (CFSG.OrderReductions.FrattiniAutomorphisms.frattini_automorphism_kernel_isPGroup 2 hQ)
      hker (odd_orderOf_of_pow_prime_eq_one hr hr2 hpowr)
  have hcomm : ∀ q ∈ Q, q * e = e * q := fun q hq => by
    have h1 := congrArg (fun a : MulAut Q => ((a ⟨q, hq⟩ : Q) : G)) hρ
    simp only [ρ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_inclusion, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  exact Subtype.ext (CFSG.Assembly.Dichotomy.CentralizerContainment.eq_one_of_mem_of_odd_orderOf
    hQ (hcore e e.2 hcomm) (odd_orderOf_of_pow_prime_eq_one hr hr2 (hEr e e.2)))

theorem le_two_of_prime_pow_dvd_20160 {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : r ^ k ∣ 20160) : k ≤ 2 := by
  by_contra hk
  have h3 : r ^ 3 ∣ 20160 := (pow_dvd_pow r (by omega)).trans h
  have hle : r ^ 3 ≤ 20160 := Nat.le_of_dvd (by norm_num) h3
  have hr27 : r ≤ 27 := by
    by_contra hgt
    have : 28 ^ 3 ≤ r ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases r <;> first | omega | exact absurd hr (by decide)

theorem elemAbelian_oddPrime_rank_le_two {G : Type} [Group G] [Finite G]
    (hchar : IsCharTwoType G) (hsec : SectionalTwoRankLEFour G) {M : Subgroup G}
    (hM : IsTwoLocal M) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {E : Subgroup G} (hEM : E ≤ M)
    (hE : IsElemAbelian r E) {k : ℕ} (hk : Nat.card E = r ^ k) : k ≤ 2 := by
  have hQ : IsPGroup 2 (pCoreOf 2 M) := isPGroup_pCoreOf 2 M
  obtain ⟨s, hs4, hs⟩ := hsec _ hQ
  have hrank : Group.rank (pCoreOf 2 M) ≤ 4 := by
    rw [← hs]
    exact (Subgroup.rank_closure_finset_le_card s).trans hs4
  obtain ⟨ψ, hψ⟩ := exists_injective_hom_mulAut_frattini_quotient hQ
    (hEM.trans (le_normalizer_pCoreOf 2 M)) hr hr2 (fun x hx => hE.2 x hx)
    fun x hx hc => hchar M hM ⟨hEM hx, Subgroup.mem_centralizer_iff.2 hc⟩
  have hdvd := Subgroup.card_dvd_of_injective ψ hψ
  rw [hk] at hdvd
  exact le_two_of_prime_pow_dvd_20160 hr hr2
    (hdvd.trans (card_mulAut_frattini_quotient_dvd hQ hrank))

end SectionalRank

theorem evenRank_le_two_of_sectionalTwoRankLEFour {G : Type} [Group G] [Finite G]
    (hchar : CFSG.Assembly.IsCharTwoType G) (hsec : SectionalTwoRankLEFour G) :
    CFSG.Assembly.evenRank G ≤ 2 := by
  refine csSup_le' ?_
  rintro k ⟨p, H, hp, hp2, hH, rfl⟩
  refine csSup_le' ?_
  rintro j ⟨E, hEH, hE, hj⟩
  exact SectionalRank.elemAbelian_oddPrime_rank_le_two hchar hsec hH hp hp2 hEH hE hj

end CFSG.RankThree.PartOne
