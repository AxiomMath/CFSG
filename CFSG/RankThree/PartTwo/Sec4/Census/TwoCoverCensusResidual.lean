module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4CoverCert
public import CFSG.Sporadic.Recognition.HeMultiplierCert
public import CFSG.Sporadic.Bridge.J4Surj
public import CFSG.Sporadic.Bridge.HeSurj
public import CFSG.Sporadic.Bridge.LySurj
public import CFSG.Sporadic.Bridge.Co3Surj
public import CFSG.Sporadic.Bridge.HNSurj
public import CFSG.Sporadic.Bridge.ThSurj
public import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.Sporadic.Presentation.McLExact
public import CFSG.Sporadic.Presentation.Co2Exact
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverSmall
import CFSG.Sporadic.Bridge.M12
import CFSG.Sporadic.Bridge.M22
import CFSG.Sporadic.Bridge.J2
public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanksTwo
public import CFSG.RankThree.PartTwo.Sec4.Census.Wiring

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Subgroup
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels
  GriessMultipliersCentralCovers)
open CFSG.GH74.Generic (centralQuotientMap centralQuotientMap_surjective centralQuotientMap_ker)
open CFSG.LocalAnalysis.ComponentInitial (alternating_perfect_central_two_kernel_order_at_most_two
  PSL2_four_alternating_five_model PSL3_two_PSL2_seven_paired_isomorphism)
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks

structure SporadicTwoCoverResidual : Prop where
  m11 : NoRankThreeTwoCover (Spor .M11)
  m23 : NoRankThreeTwoCover (Spor .M23)
  j1 : NoRankThreeTwoCover (Spor .J1)
  j3 : NoRankThreeTwoCover (Spor .J3)
  onan : NoRankThreeTwoCover NativeSporadic.ON

namespace SporadicTwoCover

theorem noRankThreeTwoCover_m22 : NoRankThreeTwoCover (Spor .M22) := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have h₀ : NoRankThreeTwoCover NativeSporadic.M22 := noRankThreeTwoCover_of_datum m22_e8Datum
  have e' : NativeSporadic.M22 ≃* Spor .M22 := e
  exact noRankThreeTwoCover_of_mulEquiv (X := NativeSporadic.M22) (Y := Spor .M22) e' h₀

theorem noRankThreeTwoCover_hs :
    NoRankThreeTwoCover (Spor .HS) := by
  obtain ⟨a₁, a₂, a₃, n, h⟩ := hs_e8Datum
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have h₀ : NoRankThreeTwoCover NativeSporadic.HS := noRankThreeTwoCover_of_datum h
  have e' : NativeSporadic.HS ≃* Spor .HS := e
  exact noRankThreeTwoCover_of_mulEquiv (X := NativeSporadic.HS) (Y := Spor .HS) e' h₀

theorem noRankThreeTwoCover_ru :
    NoRankThreeTwoCover (Spor .Ru) := by
  obtain ⟨a₁, a₂, a₃, n, h⟩ := ru_e8Datum
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  have h₀ : NoRankThreeTwoCover NativeSporadic.Ru := noRankThreeTwoCover_of_datum h
  have e' : NativeSporadic.Ru ≃* Spor .Ru := e
  exact noRankThreeTwoCover_of_mulEquiv (X := NativeSporadic.Ru) (Y := Spor .Ru) e' h₀

theorem not_isTwoCover_of_noPerfectDoubleCover {J X : Type} [Group J] [Finite J] [Group X]
    (hX : CFSG.Monster.Schur.NoPerfectDoubleCover X) : ¬ IsTwoCover J X := by
  rintro ⟨hq, hZ2, hZnt, ⟨e⟩⟩
  have hperf : commutator J = ⊤ := hq.1.commutator_eq_top
  have hJ := CFSG.GH74.KGroups.center_quotient_eq_bot hperf hq.2.1
  obtain ⟨C, _, _, -, -, -, hperfC, hcard, ⟨eC⟩⟩ := CFSG.GH74.KGroups.exists_double_cover hperf
    hZ2 ((Subgroup.nontrivial_iff_ne_bot _).mp hZnt) hJ
  have : Group.IsPerfect C := Group.isPerfect_def.mpr hperfC
  exact hX C (centralQuotientMap (eC.trans e)) (centralQuotientMap_surjective _) inferInstance
    (by rw [centralQuotientMap_ker]; exact hcard)

theorem not_isTwoCover_m24
    {J : Type} [Group J] [Finite J] :
    ¬ IsTwoCover J (Spor .M24) := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  have e' : NativeSporadic.M24 ≃* Spor .M24 := e
  exact not_isTwoCover_of_noPerfectDoubleCover
    (CFSG.Monster.Schur.NoPerfectDoubleCover.of_mulEquiv e'
      CFSG.Monster.Schur.noPerfectDoubleCover_nativeM24)

theorem not_isTwoCover_j4
    {J : Type} [Group J] [Finite J] : ¬ IsTwoCover J (Spor .J4) := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have e' : NativeSporadic.J4 ≃* Spor .J4 := e
  have h₀ : CFSG.Monster.Schur.NoPerfectDoubleCover NativeSporadic.J4 :=
    CFSG.Sporadic.Recognition.J4Multiplier.noPerfectDoubleCover_J4
      CFSG.ComponentClassification.RankTwoSporadic.J4.j4_foxCert
      CFSG.ComponentClassification.RankTwoSporadic.J4.j4_formCert
  have h₁ : CFSG.Monster.Schur.NoPerfectDoubleCover (Spor .J4) :=
    CFSG.Monster.Schur.NoPerfectDoubleCover.of_mulEquiv (G := NativeSporadic.J4)
      (H := Spor .J4) e' h₀
  exact not_isTwoCover_of_noPerfectDoubleCover h₁

theorem not_isTwoCover_he
    {J : Type} [Group J]
    [Finite J] : ¬ IsTwoCover J (Spor .He) := by
  rintro ⟨hq, -, hZnt, ⟨f⟩⟩
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have e' : NativeSporadic.He ≃* Spor .He := e
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hZnt
    (CFSG.Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate J hq
      ⟨f.trans e'.symm⟩)

theorem three_lt_pRank_of_elem {Y X : Type} [Group Y] [Group X] [Finite Y]
    (hE : ∃ E : Subgroup Y, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4) (e : Y ≃* X) :
    3 < CFSG.pRank 3 X := by
  obtain ⟨E, hE, hc⟩ := hE
  have hEA : IsElementaryAbelian 3 E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hE.2 x x.2) }
  have h4 := CFSG.LieType.SteinbergBR.le_pRank_of_card (by norm_num) E hEA hc
  have : Finite X := Finite.of_equiv _ e.toEquiv
  have heq : CFSG.pRank 3 Y = CFSG.pRank 3 X := pRank_congr_mulEquiv (by norm_num) e
  omega

theorem three_lt_pRank_mcl :
    3 < CFSG.pRank 3 (Spor .McL) := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  exact three_lt_pRank_of_elem CFSG.SectionRank.McL_elementary_three_rank_four e

theorem three_lt_pRank_ly :
    3 < CFSG.pRank 3 (Spor .Ly) := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv
  exact three_lt_pRank_of_elem CFSG.SectionRank.Ly_elementary_three_rank_four e

theorem three_lt_pRank_co2 :
    3 < CFSG.pRank 3 (Spor .Co2) := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  exact three_lt_pRank_of_elem CFSG.SectionRank.Co2_elementary_three_rank_four e

theorem three_lt_pRank_co3 :
    3 < CFSG.pRank 3 (Spor .Co3) := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  exact three_lt_pRank_of_elem CFSG.SectionRank.Co3_elementary_three_rank_four e

theorem three_lt_pRank_hn :
    3 < CFSG.pRank 3 (Spor .HN) := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  exact three_lt_pRank_of_elem CFSG.SectionRank.HN_elementary_three_rank_four e

theorem three_lt_pRank_th :
    3 < CFSG.pRank 3 (Spor .Th) := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  exact three_lt_pRank_of_elem CFSG.SectionRank.Th_elementary_three_rank_four e

theorem three_lt_pRank_onan :
    3 < CFSG.pRank 3 (Spor .ONan) := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  exact three_lt_pRank_of_elem CFSG.SectionRank.ON_elementary_three_rank_four e

end SporadicTwoCover

open SporadicTwoCover

section Census

theorem twoCoverCensus_of_residual (h42 : Item4_2) (hGA : GriessMultipliersAllModels)
    (hGC : GriessMultipliersCentralCovers) (hres : SporadicTwoCoverResidual)
    (hcov : TwoCoverRanks) : TwoCoverCensus := by
  intro J _ _ hq _ hS hZ2 hZnt hm2 hstar hstar3
  have : IsSimpleGroup (J ⧸ center J) := hq.2.1
  have hc : ∀ {X : Type} [Group X], (J ⧸ center J ≃* X) → IsTwoCover J X :=
    fun e => ⟨hq, hZ2, hZnt, ⟨e⟩⟩
  have h2Z := two_dvd_card_center hZ2 hZnt
  have h3 : CFSG.pRank 3 (J ⧸ center J) ≤ 3 := by
    rcases hstar3 with h | h
    · exact h
    · exact (hres.onan J ⟨hq, hZ2, hZnt, h⟩ hm2).elim
  have hr3 : ∀ {X : Type} [Group X], (J ⧸ center J ≃* X) → 3 < CFSG.pRank 3 X → False :=
    fun e h => by
      have : Finite _ := Finite.of_equiv _ e.toEquiv
      rw [← pRank_congr_mulEquiv (by norm_num) e] at h
      omega
  have hrp : ∀ {X : Type} [Group X] (q : ℕ), q.Prime → 3 < q → (J ⧸ center J ≃* X) →
      3 ≤ CFSG.pRank q X → False := fun q hq' hq3 e h => by
    have : Finite _ := Finite.of_equiv _ e.toEquiv
    rw [← pRank_congr_mulEquiv hq'.one_lt e] at h
    have := hstar q hq' hq3
    omega
  rcases h42 (J ⧸ center J) hS this hq.2.2 with
    ⟨p, e, _, hp, he, hf⟩ | ⟨p, e, _, hp, he, -, hf | hf⟩ | ⟨hr, hf⟩ |
    ⟨p, _, hp, ⟨q, hqp, hqe, hG2⟩ | hf | hf | hf⟩ | ⟨n, hn5, hn12, hf⟩ | ⟨s, hs, hf⟩ |
    h7 | h8 | h9
  ·
    obtain ⟨f⟩ := hf
    have hpp : p.Prime := Fact.out
    by_cases h3e : p ^ e = 3
    · obtain ⟨rfl, rfl⟩ := Nat.prime_three.pow_eq_iff.mp h3e
      exact (not_isTwoCover_projSL_two 3 (Or.inr rfl) (hc f)).elim
    · have hodd' : Odd (p ^ e) := (hpp.odd_of_ne_two hp).pow
      have hadm : StatedLieAdmissible .PSL 2 p e := by
        refine ⟨hpp, he, le_refl 2, fun h => ?_, fun h => h3e (Prod.mk.inj h).2⟩
        have h2 := (Prod.mk.inj h).2
        rw [h2] at hodd'
        exact (Nat.not_even_iff_odd.mpr hodd') even_two
      have hm := blueprint_lieModel_of_classical (by decide)
        (lieModel_of_mulEquiv f (lieModel_projSL hadm))
      have := pRank_two_le_of_psl_two hGA hGC hq hZ2 hZnt hpp hp hm
      omega
  ·
    obtain ⟨f⟩ := hf
    have hm := lieModel_projSL (n := 3) (p := p) (e := e)
      ⟨Fact.out, he, by norm_num, fun h => by simp at h, fun h => by simp at h⟩
    exact (not_isTwoCover_of_noTwoCover
      (CFSG.GH74.Generic.noTwoCover_psl3_of_griess hGA (by omega) hm) (hc f)).elim
  ·
    obtain ⟨f⟩ := hf
    have hpp : p.Prime := Fact.out
    have hm := lieModel_projSU (n := 3) (p := p) (e := e)
      ⟨hpp, he, le_refl 3, fun h => by
        have h2 := (Prod.mk.inj h).2
        have : p ≤ p ^ e := Nat.le_self_pow (by omega) p
        omega⟩
    exact (not_isTwoCover_of_noTwoCover
      (CFSG.GH74.Generic.noTwoCover_psu3_of_griess hGA hm) (hc f)).elim
  ·
    obtain ⟨f⟩ := hf
    have hm := lieModel_lie (t := .twistedG2) (p := 3) (f := 3)
      ⟨Nat.prime_three, by norm_num, by decide⟩ ⟨.reeG2 1, hr⟩ ⟨rfl, rfl⟩
    exact (not_isTwoCover_of_noTwoCover
      (CFSG.GH74.Generic.noTwoCover_ree_of_griess hGA hm) (hc f)).elim
  ·
    obtain ⟨hqv, ⟨g⟩⟩ := hG2
    have h3 : 3 ≤ q.p ^ q.exponent := by
      have h := ((TauCeti.LieTypeIndex.valid_iff _).mp hqv).1
      simpa using h
    have hm := lieModel_lie (t := .G2) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl, h3⟩ ⟨.G2 q, hqv⟩ ⟨rfl, rfl⟩
    exact (not_isTwoCover_of_noTwoCover
      (CFSG.GH74.Generic.noTwoCover_g2_of_griess hGA (by omega) hm) (hc g)).elim
  ·
    obtain ⟨f⟩ := hf
    have := le_pRank_projSp_two (GaloisField p 1) (GaloisField.card p 1 one_ne_zero)
    exact (hrp p Fact.out hp f (by omega)).elim
  ·
    obtain ⟨f⟩ := hf
    have := le_pRank_projSL_four (GaloisField p 1) (GaloisField.card p 1 one_ne_zero)
    exact (hrp p Fact.out hp f (by omega)).elim
  ·
    obtain ⟨f⟩ := hf
    have := le_pRank_projSU_four (p := p) (f := 1) le_rfl
    exact (hrp p Fact.out hp f (by omega)).elim
  ·
    obtain ⟨f⟩ := hf
    have : Group.IsPerfect J := hq.1
    have hle := alternating_perfect_central_two_kernel_order_at_most_two hn5
      (centralQuotientMap f) (centralQuotientMap_surjective f) (centralQuotientMap_ker f).le
      (by rw [centralQuotientMap_ker]; exact hZ2)
    rw [centralQuotientMap_ker f] at hle
    have hZ : Nat.card (center J) = 2 := by
      have := Nat.le_of_dvd Nat.card_pos h2Z
      omega
    rcases (by omega : n = 5 ∨ 6 ≤ n) with rfl | hn6
    · have := pRank_two_le_of_psl_two hGA hGC hq hZ2 hZnt (by norm_num) (by norm_num)
        (lieModel_psl_two_five_of_alternating f)
      omega
    · exact (hcov.alternating n hn6 hn12 J hq hZ ⟨f⟩ hm2).elim
  ·
    obtain ⟨f⟩ := hf
    simp only [sporadics42, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      exact (hres.m11 J (hc f) hm2).elim
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
      exact Or.inl ⟨f.trans b.symm⟩
    ·
      exact (noRankThreeTwoCover_m22 J (hc f) hm2).elim
    ·
      exact (hres.m23 J (hc f) hm2).elim
    ·
      exact (not_isTwoCover_m24 (hc f)).elim
    ·
      exact (hres.j1 J (hc f) hm2).elim
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
      exact Or.inr (Or.inr (Or.inl ⟨f.trans b.symm⟩))
    ·
      exact (hres.j3 J (hc f) hm2).elim
    ·
      exact (not_isTwoCover_j4 (hc f)).elim
    ·
      exact (hr3 f three_lt_pRank_mcl).elim
    ·
      exact (hr3 f three_lt_pRank_ly).elim
    ·
      exact (noRankThreeTwoCover_hs J (hc f) hm2).elim
    ·
      exact (not_isTwoCover_he (hc f)).elim
    ·
      exact (hr3 f hcov.suz).elim
    ·
      exact (noRankThreeTwoCover_ru J (hc f) hm2).elim
    ·
      exact (hr3 f three_lt_pRank_onan).elim
    ·
      exact (hr3 f three_lt_pRank_co3).elim
    ·
      exact (hr3 f three_lt_pRank_co2).elim
    ·
      exact (hr3 f three_lt_pRank_hn).elim
    ·
      exact (hr3 f three_lt_pRank_th).elim
  ·
    rcases h7 with ⟨n, hn, hf | hf | hf | hf | hf⟩ | ⟨q, hq2, hG2⟩ | ⟨q, hqv, -, hf⟩ |
      ⟨m, hm, hf⟩ | ⟨m, hm, hf⟩ | ⟨ht, hf⟩
    ·
      obtain ⟨f⟩ := hf
      rcases (by omega : n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | hn3
      · exact (not_isTwoCover_projSL_two 2 (Or.inl rfl) (hc f)).elim
      · have hm := lieModel_projSL (n := 2) (p := 2) (e := 2)
          ⟨Nat.prime_two, by norm_num, by decide⟩
        obtain ⟨e5⟩ := PSL2_four_alternating_five_model _
          (blueprint_lieModel_of_classical (by decide) (lieModel_of_mulEquiv f hm))
        have := pRank_two_le_of_psl_two hGA hGC hq hZ2 hZnt (by norm_num) (by norm_num)
          (lieModel_psl_two_five_of_alternating e5)
        omega
      · have hm := lieModel_projSL (n := 2) (p := 2) (e := n)
          ⟨Nat.prime_two, by omega, le_refl 2, fun h => by
            have h2 := (Prod.mk.inj h).2
            have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn3
            omega, fun h => by
            have h2 := (Prod.mk.inj h).2
            have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn3
            omega⟩
        exact (not_isTwoCover_of_odd_tableOrder hGA hm (odd_tableOrder_psl_two_even hn3)
          (hc f)).elim
    ·
      obtain ⟨f⟩ := hf
      rcases (by omega : n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | hn3
      · have hm := lieModel_projSL (n := 3) (p := 2) (e := 1)
          ⟨Nat.prime_two, by norm_num, by decide⟩
        have := pRank_two_le_of_psl_two hGA hGC hq hZ2 hZnt (by norm_num) (by norm_num)
          (PSL3_two_PSL2_seven_paired_isomorphism _
            (blueprint_lieModel_of_classical (by decide) (lieModel_of_mulEquiv f hm)))
        omega
      · obtain ⟨hcyc, hZ⟩ := hcov.psl34 J (hc f) hm2
        exact Or.inr (Or.inr (Or.inr ⟨⟨f⟩, hcyc, hZ⟩))
      · have hm := lieModel_projSL (n := 3) (p := 2) (e := n)
          ⟨Nat.prime_two, by omega, by norm_num, fun h => by simp at h, fun h => by simp at h⟩
        exact (not_isTwoCover_of_odd_tableOrder hGA hm (odd_tableOrder_psl_three_even hn3)
          (hc f)).elim
    ·
      obtain ⟨f⟩ := hf
      rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
      · exact (not_isTwoCover_projSU_three_two (hc f)).elim
      · have hm := lieModel_projSU (n := 3) (p := 2) (e := n)
          ⟨Nat.prime_two, by omega, le_refl 3, fun h => by
            have h2 := (Prod.mk.inj h).2
            have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn2
            omega⟩
        exact (not_isTwoCover_of_noTwoCover
          (CFSG.GH74.Generic.noTwoCover_psu3_of_griess hGA hm) (hc f)).elim
    ·
      obtain ⟨f⟩ := hf
      rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
      · exact (not_isTwoCover_projSp_two_two (hc f)).elim
      · have hm := lieModel_projSp (n := 2) (p := 2) (e := n)
          ⟨Nat.prime_two, by omega, le_refl 2, fun h => by
            have h2 := (Prod.mk.inj h).2
            have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn2
            omega⟩
        exact (not_isTwoCover_of_odd_tableOrder hGA hm (odd_tableOrder_psp_two_even hn)
          (hc f)).elim
    ·
      obtain ⟨f⟩ := hf
      rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
      · have hm := lieModel_projSU (n := 4) (p := 2) (e := 1)
          ⟨Nat.prime_two, le_rfl, by decide⟩
        exact (hcov.psu42 J hq (card_center_eq_two_of_tableOrder hGA hq hZnt f hm (by decide))
          ⟨f⟩ hm2).elim
      · have hm := lieModel_projSU (n := 4) (p := 2) (e := n)
          ⟨Nat.prime_two, by omega, by norm_num, fun h => by simp at h⟩
        exact (not_isTwoCover_of_odd_tableOrder hGA hm (odd_tableOrder_psu_four_even hn2)
          (hc f)).elim
    ·
      obtain ⟨hqv, ⟨g⟩⟩ := hG2
      have h3 : 3 ≤ q.p ^ q.exponent := by
        have h := ((TauCeti.LieTypeIndex.valid_iff _).mp hqv).1
        simpa using h
      rw [hq2] at h3
      have hm := lieModel_lie (t := .G2) (p := 2) (f := q.exponent)
        ⟨Nat.prime_two, q.exponent_pos, rfl, h3⟩ ⟨.G2 q, hqv⟩ ⟨hq2, rfl⟩
      have he2 : 2 ≤ q.exponent := by
        by_contra he
        have : q.exponent = 1 := by have := q.exponent_pos; omega
        rw [this] at h3
        norm_num at h3
      rcases (by omega : q.exponent = 2 ∨ 3 ≤ q.exponent) with he | he
      · have hZ := card_center_eq_two_of_tableOrder hGA hq hZnt g hm (by rw [he]; decide)
        exact (hcov.g24 q hqv hq2 he J hq hZ ⟨g⟩ hm2).elim
      · exact (not_isTwoCover_of_odd_tableOrder hGA hm (odd_tableOrder_g2_even he)
          (hc g)).elim
    ·
      obtain ⟨f⟩ := hf
      have hm := lieModel_lie (t := .trialityD4) (p := q.p) (f := q.exponent)
        ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.trialityD4 q, hqv⟩ ⟨rfl, rfl⟩
      exact (not_isTwoCover_of_noTwoCover
        (CFSG.GH74.Generic.noTwoCover_3D4_of_griess hGA hm) (hc f)).elim
    ·
      obtain ⟨f⟩ := hf
      have hm1 : 1 ≤ m := by
        have h := ((TauCeti.LieTypeIndex.valid_iff _).mp hm).1
        simpa using h
      rcases (by omega : m = 1 ∨ 2 ≤ m) with rfl | hm2'
      · exact (hcov.sz8 hm J (hc f) hm2).elim
      · have hmod := lieModel_lie (t := .twistedB2) (p := 2) (f := 2 * m + 1)
          ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.suzuki m, hm⟩ ⟨rfl, rfl⟩
        exact (not_isTwoCover_of_odd_tableOrder hGA hmod (odd_tableOrder_suzuki hm2')
          (hc f)).elim
    ·
      obtain ⟨f⟩ := hf
      have hm1 : 1 ≤ m := by
        have h := ((TauCeti.LieTypeIndex.valid_iff _).mp hm).1
        simpa using h
      have hmod := lieModel_lie (t := .twistedF4) (p := 2) (f := 2 * m + 1)
        ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeF4 m, hm⟩ ⟨rfl, rfl⟩
      exact (not_isTwoCover_of_odd_tableOrder hGA hmod (odd_tableOrder_ree_f4 m) (hc f)).elim
    ·
      obtain ⟨f⟩ := hf
      have hmod := lieModel_lie (t := .Tits) (p := 2) (f := 1)
        ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩ ⟨.tits, ht⟩ ⟨rfl, rfl⟩
      exact (not_isTwoCover_of_odd_tableOrder hGA hmod (by decide) (hc f)).elim
  ·
    rcases h8 with hf | hf | hf | hf | hf | hf | hf | hf | ⟨b, c, hbc, hf⟩ | hf | hf | hf | hf |
      hf
    all_goals obtain ⟨f⟩ := hf
    ·
      have hm := lieModel_projSL (n := 5) (p := 2) (e := 1) ⟨Nat.prime_two, le_rfl, by decide⟩
      exact (not_isTwoCover_of_noTwoCover
        (CFSG.GH74.Generic.noTwoCover_psl5_of_griess hGA hm) (hc f)).elim
    ·
      have hm := lieModel_projSU (n := 5) (p := 2) (e := 1) ⟨Nat.prime_two, le_rfl, by decide⟩
      exact (not_isTwoCover_of_noTwoCover
        (CFSG.GH74.Generic.noTwoCover_psu5_of_griess hGA hm) (hc f)).elim
    ·
      have hm := lieModel_projSL (n := 6) (p := 2) (e := 1) ⟨Nat.prime_two, le_rfl, by decide⟩
      exact (not_isTwoCover_of_odd_tableOrder hGA hm (by decide) (hc f)).elim
    ·
      exact (hr3 f three_lt_pRank_projSU_six_two).elim
    ·
      have hm := lieModel_projSL (n := 7) (p := 2) (e := 1) ⟨Nat.prime_two, le_rfl, by decide⟩
      exact (not_isTwoCover_of_odd_tableOrder hGA hm (by decide) (hc f)).elim
    ·
      have hm := lieModel_projSp (n := 3) (p := 2) (e := 1) ⟨Nat.prime_two, le_rfl, by decide⟩
      exact (hcov.sp62 J hq (card_center_eq_two_of_tableOrder hGA hq hZnt f hm (by decide))
        ⟨f⟩ hm2).elim
    ·
      have hm := lieModel_projSp (n := 4) (p := 2) (e := 1) ⟨Nat.prime_two, le_rfl, by decide⟩
      exact (not_isTwoCover_of_odd_tableOrder hGA hm (by decide) (hc f)).elim
    ·
      exact (hr3 f hcov.omegaPlus).elim
    ·
      have hm := lieModel_projOmegaMinus (n := 4) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, le_refl 4⟩ hbc
      exact (not_isTwoCover_of_odd_tableOrder hGA hm (by decide) (hc f)).elim
    ·
      have hm := lieModel_projSL (n := 4) (p := 2) (e := 2)
        ⟨Nat.prime_two, by norm_num, by decide⟩
      exact (not_isTwoCover_of_odd_tableOrder hGA hm (by decide) (hc f)).elim
    ·
      have hm := lieModel_projSp (n := 3) (p := 2) (e := 2)
        ⟨Nat.prime_two, by norm_num, by decide⟩
      exact (not_isTwoCover_of_odd_tableOrder hGA hm (by decide) (hc f)).elim
    ·
      have hm := lieModel_projSU (n := 5) (p := 2) (e := 2)
        ⟨Nat.prime_two, by norm_num, by decide⟩
      exact (not_isTwoCover_of_noTwoCover
        (CFSG.GH74.Generic.noTwoCover_psu5_of_griess hGA hm) (hc f)).elim
    ·
      have hm := lieModel_projSU (n := 5) (p := 2) (e := 3)
        ⟨Nat.prime_two, by norm_num, by decide⟩
      exact (not_isTwoCover_of_noTwoCover
        (CFSG.GH74.Generic.noTwoCover_psu5_of_griess hGA hm) (hc f)).elim
    ·
      exact (hr3 f hcov.f42).elim
  ·
    rcases h9 with ⟨e, he1, he3, hf | hf⟩ | hf | hf | hf
    all_goals obtain ⟨f⟩ := hf
    ·
      have hm := lieModel_projSL (n := 3) (p := 3) (e := e)
        ⟨Nat.prime_three, he1, by norm_num, fun h => by simp at h, fun h => by simp at h⟩
      exact (not_isTwoCover_of_noTwoCover
        (CFSG.GH74.Generic.noTwoCover_psl3_of_griess hGA (by norm_num) hm) (hc f)).elim
    ·
      have hm := lieModel_projSU (n := 3) (p := 3) (e := e)
        ⟨Nat.prime_three, he1, le_refl 3, fun h => by
          have h2 := (Prod.mk.inj h).2
          have := Nat.le_self_pow (by omega : e ≠ 0) 3
          omega⟩
      exact (not_isTwoCover_of_noTwoCover
        (CFSG.GH74.Generic.noTwoCover_psu3_of_griess hGA hm) (hc f)).elim
    ·
      have hm := lieModel_lie (t := .G2) (p := 3) (f := 1)
        ⟨Nat.prime_three, le_rfl, rfl, le_refl 3⟩ g2ThreeIndex ⟨rfl, rfl⟩
      exact (not_isTwoCover_of_noTwoCover
        (CFSG.GH74.Generic.noTwoCover_g2_of_griess hGA (by norm_num) hm) (hc f)).elim
    ·
      have := le_pRank_projSL_four (GaloisField 3 1) (GaloisField.card 3 1 one_ne_zero)
      exact (hr3 f (by omega)).elim
    ·
      have := le_pRank_projSU_four (p := 3) (f := 1) le_rfl
      exact (hr3 f (by omega)).elim


theorem quasisimpleCensus_of_residual (h41 : Item4_1) (hGA : GriessMultipliersAllModels)
    (hres : SporadicTwoCoverResidual) : QuasisimpleCensus :=
  quasisimpleCensus_of h41 (twoCoverCensus_of_residual rank3II_4_2 hGA
    griessMultipliersCentralCovers hres
    (TwoCoverRanks.of_open (TwoCoverRanksOpen.of_open' (TwoCoverRanksOpen'.of_open''
      twoCoverRanksOpen''))))


theorem rank3II_4_4_of_residual (h41 : Item4_1) (hGA : GriessMultipliersAllModels)
    (hres : SporadicTwoCoverResidual) (hL34 : FourL34NotSLFourOdd) : Item4_4 :=
  rank3II_4_4_of_census (quasisimpleCensus_of_residual h41 hGA hres) hL34

end Census

end CFSG.RankThree.PartTwo.Sec4.Census
