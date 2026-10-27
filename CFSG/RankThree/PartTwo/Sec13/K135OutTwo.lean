module

public import CFSG.RankThree.PartTwo.Sec13.K135OutTwoFam
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanO10CentOut
public import CFSG.RankThree.PartTwo.Sec13.K135OutP
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1RowEight

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.Assembly.LowTwoRank CFSG.Models Matrix Subgroup
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Census
open CFSG.RankThree.PartOne.OutStructure
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

structure OutTwoInputs : Prop where
  ree : ∀ (hr : (TauCeti.LieTypeIndex.reeG2 1).Valid) {Y : Type} [Group Y],
    Y ≃* (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group → IsCyclic (Outer Y)
  g2 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    {Y : Type} [Group Y], Y ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group → OutPNice 2 Y
  d4 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
    ∀ {Y : Type} [Group Y],
      Y ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group → OutPNice 2 Y
  sz : ∀ (m : ℕ) (hv : (TauCeti.LieTypeIndex.suzuki m).Valid)
    {Y : Type} [Group Y], Y ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group → OutPNice 2 Y
  f4r : ∀ (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid)
    {Y : Type} [Group Y], Y ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group → OutPNice 2 Y
  tits : ∀ (hv : TauCeti.LieTypeIndex.tits.Valid) {Y : Type} [Group Y] [Finite Y],
    Y ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group → Nat.card (Outer Y) = 2
  f42 : ∀ {Y : Type} [Group Y], Y ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group → OutPNice 2 Y
  spor : ∀ (s : TauCeti.SporadicName) {Y : Type} [Group Y] [IsSimpleGroup Y],
    Y ≃* (TauCeti.CFSGIndex.sporadic s).Group → Nat.card (Outer Y) ∣ 2

theorem odd_gcd_three (m : ℕ) : ¬ 2 ∣ Nat.gcd 3 m := fun h =>
  absurd (h.trans (Nat.gcd_dvd_left 3 m)) (by norm_num)

theorem kFactOutTwo_of_inputs (hI : OutTwoInputs) : KFactOutTwo := by
  refine kFactOutTwo_of_gen fun S _ _ hS hnab h42 => ?_
  rcases h42 with
    ⟨p0, e, _, hp0, he, hf⟩ | ⟨p0, e, _, hp0, he, -, hf | hf⟩ | ⟨hr, hf⟩ |
    ⟨p0, _, hp0, ⟨q, hqp, hqe, hG2⟩ | hf | hf | hf⟩ | ⟨n, hn5, hn12, hf⟩ | ⟨s, hs, hf⟩ |
    hc7 | hc8 | hc9
  ·
    obtain ⟨f⟩ := hf
    have hpp : p0.Prime := Fact.out
    by_cases h3e : p0 ^ e = 3
    · obtain ⟨rfl, rfl⟩ := Nat.prime_three.pow_eq_iff.mp h3e
      exact (not_simple_projSL_two 3 (Or.inr rfl) hS hnab f).elim
    · have hodd' : Odd (p0 ^ e) := (hpp.odd_of_ne_two hp0).pow
      have hadm : StatedLieAdmissible .PSL 2 p0 e := by
        refine ⟨hpp, he, le_refl 2, fun h => ?_, fun h => h3e (Prod.mk.inj h).2⟩
        have h2 := (Prod.mk.inj h).2
        rw [h2] at hodd'
        exact (Nat.not_even_iff_odd.mpr hodd') even_two
      exact tg_psl_two_odd hp0 (stated_of_lieModel f (lieModel_projSL hadm) (by norm_num))
  ·
    obtain ⟨f⟩ := hf
    exact tg_psl (n := 3) (by norm_num) (stated_of_lieModel f (lieModel_projSL (n := 3) (p := p0)
      (e := e) ⟨Fact.out, he, by norm_num, fun h => by simp at h, fun h => by simp at h⟩)
      (by norm_num)) (Or.inl (odd_gcd_three _))
  ·
    obtain ⟨f⟩ := hf
    have hpp : p0.Prime := Fact.out
    exact tg_psu (stated_of_lieModel f (lieModel_projSU (n := 3) (p := p0) (e := e)
      ⟨hpp, he, le_refl 3, fun h => by
        have h2 := (Prod.mk.inj h).2
        have : p0 ≤ p0 ^ e := Nat.le_self_pow (by omega) p0
        omega⟩) (by norm_num))
  ·
    obtain ⟨f⟩ := hf
    exact outTwoGen_of_outPNice_two (outPNice_of_isCyclic_outer Nat.prime_two (hI.ree hr f))
  ·
    obtain ⟨hqv, ⟨g⟩⟩ := hG2
    exact outTwoGen_of_outPNice_two (hI.g2 q hqv g)
  ·
    obtain ⟨f⟩ := hf
    have hpp : p0.Prime := Fact.out
    exact tg_psp_two_odd hpp (stated_of_lieModel f (lieModel_projSp (n := 2)
      (p := p0) (e := 1) ⟨hpp, le_rfl, le_refl 2, fun h => by
        have h2 := (Prod.mk.inj h).2
        rw [pow_one] at h2
        omega⟩) (by norm_num))
  ·
    obtain ⟨f⟩ := hf
    exact tg_psl (n := 4) (by norm_num) (stated_of_lieModel f (lieModel_projSL (n := 4) (p := p0)
      (e := 1) ⟨Fact.out, le_rfl, by norm_num, fun h => by simp at h, fun h => by simp at h⟩)
      (by norm_num)) (Or.inr rfl)
  ·
    obtain ⟨f⟩ := hf
    exact tg_psu (stated_of_lieModel f (lieModel_projSU (n := 4) (p := p0) (e := 1)
      ⟨Fact.out, le_rfl, by norm_num, fun h => by simp at h⟩) (by norm_num))
  ·
    obtain ⟨f⟩ := hf
    exact outTwoGen_of_card_le_four
      ((Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence f).toEquiv).trans_le
        (CFSG.RankThree.PartOne.card_outer_alternating_le_four hn5))
  ·
    obtain ⟨f⟩ := hf
    haveI := hS
    exact outTwoGen_of_card_dvd (m := 1) (by decide) ((hI.spor s f).trans (by norm_num))
  ·
    rcases hc7 with ⟨n, hn, hf | hf | hf | hf | hf⟩ | ⟨q, hq2, hG2⟩ | ⟨q, hqv, hq2, hf⟩ |
      ⟨m, hm, hf⟩ | ⟨m, hm, hf⟩ | ⟨ht, hf⟩
    ·
      obtain ⟨f⟩ := hf
      rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
      · exact (not_simple_projSL_two 2 (Or.inl rfl) hS hnab f).elim
      · have hne := two_pow_ne_of_two_le' hn2
        exact outTwoGen_of_outPNice_two (outPNice_PSL_two Nat.prime_two
          (stated_of_lieModel f (lieModel_projSL (n := 2) (p := 2) (e := n)
            ⟨Nat.prime_two, by omega, le_refl 2, fun h => hne.1 (Prod.mk.inj h).2,
              fun h => hne.2 (Prod.mk.inj h).2⟩) (by norm_num)))
    ·
      obtain ⟨f⟩ := hf
      exact tg_psl (n := 3) (by norm_num) (stated_of_lieModel f (lieModel_projSL (n := 3)
        (p := 2) (e := n) ⟨Nat.prime_two, by omega, by norm_num, fun h => by simp at h,
          fun h => by simp at h⟩) (by norm_num)) (Or.inl (odd_gcd_three _))
    ·
      obtain ⟨f⟩ := hf
      rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
      · exact (not_simple_projSU_three_two hS hnab f).elim
      · have hne := two_pow_ne_of_two_le' hn2
        exact tg_psu (stated_of_lieModel f (lieModel_projSU (n := 3) (p := 2) (e := n)
          ⟨Nat.prime_two, by omega, le_refl 3, fun h => hne.1 (Prod.mk.inj h).2⟩) (by norm_num))
    ·
      obtain ⟨f⟩ := hf
      rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
      · exact (not_simple_projSp_two_two hS hnab f).elim
      · have hne := two_pow_ne_of_two_le' hn2
        exact outTwoGen_of_outPNice_two (outPNice_PSp_two Nat.prime_two
          (stated_of_lieModel f (lieModel_projSp (n := 2) (p := 2) (e := n)
            ⟨Nat.prime_two, by omega, le_refl 2, fun h => hne.1 (Prod.mk.inj h).2⟩) (by norm_num)))
    ·
      obtain ⟨f⟩ := hf
      exact tg_psu (stated_of_lieModel f (lieModel_projSU (n := 4) (p := 2) (e := n)
        ⟨Nat.prime_two, by omega, by norm_num, fun h => by simp at h⟩) (by norm_num))
    ·
      obtain ⟨hqv, ⟨g⟩⟩ := hG2
      exact outTwoGen_of_outPNice_two (hI.g2 q hqv g)
    ·
      obtain ⟨f⟩ := hf
      exact outTwoGen_of_outPNice_two (hI.d4 q hqv hq2 f)
    ·
      obtain ⟨f⟩ := hf
      exact outTwoGen_of_outPNice_two (hI.sz m hm f)
    ·
      obtain ⟨f⟩ := hf
      exact outTwoGen_of_outPNice_two (hI.f4r m hm f)
    ·
      obtain ⟨f⟩ := hf
      exact outTwoGen_of_card_dvd (m := 1) (by decide) (by rw [hI.tits ht f]; norm_num)
  ·
    rcases hc8 with hf | hf | hf | hf | hf | hf | hf | hf | ⟨b, c, hbc, hf⟩ | hf | hf | hf | hf |
      hf
    all_goals obtain ⟨f⟩ := hf
    ·
      exact tg_psl (n := 5) (by norm_num) (stated_of_lieModel f (lieModel_projSL (n := 5) (p := 2)
        (e := 1) ⟨Nat.prime_two, le_rfl, by decide⟩) (by norm_num)) (Or.inl (by norm_num))
    ·
      exact tg_psu (stated_of_lieModel f (lieModel_projSU (n := 5) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, by decide⟩) (by norm_num))
    ·
      exact tg_psl (n := 6) (by norm_num) (stated_of_lieModel f (lieModel_projSL (n := 6) (p := 2)
        (e := 1) ⟨Nat.prime_two, le_rfl, by decide⟩) (by norm_num)) (Or.inl (by norm_num))
    ·
      exact tg_psu (stated_of_lieModel f (lieModel_projSU (n := 6) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, by decide⟩) (by norm_num))
    ·
      exact tg_psl (n := 7) (by norm_num) (stated_of_lieModel f (lieModel_projSL (n := 7) (p := 2)
        (e := 1) ⟨Nat.prime_two, le_rfl, by decide⟩) (by norm_num)) (Or.inl (by norm_num))
    ·
      exact outTwoGen_of_outPNice_two (outPNice_PSp_ge_three Nat.prime_two (r := 3) (by norm_num)
        (stated_of_lieModel f (lieModel_projSp (n := 3) (p := 2) (e := 1)
          ⟨Nat.prime_two, le_rfl, by decide⟩) (by norm_num)))
    ·
      exact outTwoGen_of_outPNice_two (outPNice_PSp_ge_three Nat.prime_two (r := 4) (by norm_num)
        (stated_of_lieModel f (lieModel_projSp (n := 4) (p := 2) (e := 1)
          ⟨Nat.prime_two, le_rfl, by decide⟩) (by norm_num)))
    ·
      refine outTwoGen_of_card_dvd (m := 15) (by decide) ?_
      rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence f).toEquiv]
      exact (CFSG.RankThree.PartTwo.Sec14.Ronan148K.card_outer_projOmegaPlus_four_two_dvd).trans
        (by norm_num)
    ·
      refine outTwoGen_of_card_dvd (m := 1) (by decide) ?_
      have hcl := stated_of_lieModel f (lieModel_projOmegaMinus (n := 4) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, le_refl 4⟩ hbc) (by norm_num)
      exact (CFSG.AGLEmbedding.O10Cent.card_outer_dvd_two (by norm_num) hcl).trans (by norm_num)
    ·
      exact tg_psl (n := 4) (by norm_num) (stated_of_lieModel f (lieModel_projSL (n := 4) (p := 2)
        (e := 2) ⟨Nat.prime_two, by norm_num, by decide⟩) (by norm_num)) (Or.inl (by norm_num))
    ·
      exact outTwoGen_of_outPNice_two (outPNice_PSp_ge_three Nat.prime_two (r := 3) (by norm_num)
        (stated_of_lieModel f (lieModel_projSp (n := 3) (p := 2) (e := 2)
          ⟨Nat.prime_two, by norm_num, by decide⟩) (by norm_num)))
    ·
      exact tg_psu (stated_of_lieModel f (lieModel_projSU (n := 5) (p := 2) (e := 2)
        ⟨Nat.prime_two, by norm_num, by decide⟩) (by norm_num))
    ·
      exact tg_psu (stated_of_lieModel f (lieModel_projSU (n := 5) (p := 2) (e := 3)
        ⟨Nat.prime_two, by norm_num, by decide⟩) (by norm_num))
    ·
      exact outTwoGen_of_outPNice_two (hI.f42 f)
  ·
    rcases hc9 with ⟨e, he1, he3, hf | hf⟩ | hf | hf | hf
    all_goals obtain ⟨f⟩ := hf
    ·
      exact tg_psl (n := 3) (by norm_num) (stated_of_lieModel f (lieModel_projSL (n := 3) (p := 3)
        (e := e) ⟨Nat.prime_three, he1, by norm_num, fun h => by simp at h,
          fun h => by simp at h⟩) (by norm_num)) (Or.inl (odd_gcd_three _))
    ·
      exact tg_psu (stated_of_lieModel f (lieModel_projSU (n := 3) (p := 3) (e := e)
        ⟨Nat.prime_three, he1, le_refl 3, fun h => by
          have h2 := (Prod.mk.inj h).2
          have := Nat.le_self_pow (by omega : e ≠ 0) 3
          omega⟩) (by norm_num))
    ·
      exact outTwoGen_of_outPNice_two (hI.g2 _ _ f)
    ·
      exact tg_psl (n := 4) (by norm_num) (stated_of_lieModel f (lieModel_projSL (n := 4) (p := 3)
        (e := 1) ⟨Nat.prime_three, le_rfl, by norm_num, fun h => by simp at h,
          fun h => by simp at h⟩) (by norm_num)) (Or.inr rfl)
    ·
      exact tg_psu (stated_of_lieModel f (lieModel_projSU (n := 4) (p := 3) (e := 1)
        ⟨Nat.prime_three, le_rfl, by norm_num, fun h => by simp at h⟩) (by norm_num))

end CFSG.RankThree.PartTwo.Sec13.F135Last
