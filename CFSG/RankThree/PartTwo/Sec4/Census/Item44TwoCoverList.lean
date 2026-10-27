module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCover
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverSmall
import CFSG.LocalAnalysis.ComponentClassification.TBLitPSLCover
import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.Sporadic.Bridge.M12
import CFSG.Sporadic.Bridge.M22
import CFSG.Sporadic.Bridge.J2
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Subgroup
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels
  GriessMultipliersCentralCovers)
open CFSG.GH74.Generic (card_center_dvd_hopfMultiplier centralQuotientMap
  centralQuotientMap_surjective centralQuotientMap_ker)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.RankThree.PerfectCover (hopfMultiplier)
open CFSG.LocalAnalysis.ComponentInitial (alternating_perfect_central_two_kernel_order_at_most_two
  PSL2_four_alternating_five_model PSL3_two_PSL2_seven_paired_isomorphism)

@[expose] def sporadicMultiplierOrder : TauCeti.SporadicName → ℕ
  | .M12 => 2 | .M22 => 12 | .J2 => 2 | .J3 => 3 | .HS => 2 | .McL => 3 | .Suz => 6
  | .Ru => 2 | .ONan => 3 | .Co1 => 2 | .Fi22 => 6 | .Fi24Prime => 3 | .B => 2 | _ => 1

@[expose] def SporadicMultipliers : Prop :=
  (∀ s : TauCeti.SporadicName, Nat.card (hopfMultiplier (Spor s)) = sporadicMultiplierOrder s) ∧
    Nat.card (hopfMultiplier NativeSporadic.ON) = 3

@[expose] def NoRankThreeDoubleCover (X : Type) [Group X] : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → Nat.card (center J) = 2 →
    Nonempty (J ⧸ center J ≃* X) → CFSG.pRank 2 J ≠ 3

@[expose] def NoRankThreeTwoCover (X : Type) [Group X] : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsTwoCover J X → CFSG.pRank 2 J ≠ 3

structure TwoCoverRanks : Prop where
  alternating : ∀ n : ℕ, 6 ≤ n → n ≤ 12 → NoRankThreeDoubleCover (alternatingGroup (Fin n))
  hs : NoRankThreeDoubleCover (Spor .HS)
  ru : NoRankThreeDoubleCover (Spor .Ru)
  m22 : NoRankThreeDoubleCover (Spor .M22)
  suz : 3 < CFSG.pRank 3 (Spor .Suz)
  psu42 : NoRankThreeDoubleCover (projSU 4 2 1)
  psl34 : ∀ (J : Type) [Group J] [Finite J], IsTwoCover J (projSL 3 (GaloisField 2 2)) →
    CFSG.pRank 2 J = 3 → IsCyclic (center J) ∧ Nat.card (center J) = 4
  g24 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 →
    q.exponent = 2 → NoRankThreeDoubleCover (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  sz8 : ∀ hm : (TauCeti.LieTypeIndex.suzuki 1).Valid,
    NoRankThreeTwoCover (TauCeti.CFSGIndex.lie ⟨.suzuki 1, hm⟩).Group
  sp62 : NoRankThreeDoubleCover (projSp 3 (GaloisField 2 1))
  omegaPlus : 3 < CFSG.pRank 3 (projOmegaPlus 4 (GaloisField 2 1))
  f42 : 3 < CFSG.pRank 3 (TauCeti.CFSGIndex.lie f4TwoIndex).Group

theorem odd_tableOrder_psl_two_even {n : ℕ} (hn : 3 ≤ n) : Odd (tableOrder .PSL 2 2 n) := by
  refine odd_tableOrder (odd_gcd_of_odd_right (odd_two_pow_sub_one (by omega))) odd_one ?_
  unfold exceptionalOrders
  split <;> simp_all

theorem odd_tableOrder_psl_three_even {n : ℕ} (hn : 3 ≤ n) : Odd (tableOrder .PSL 3 2 n) := by
  refine odd_tableOrder (odd_gcd_of_odd_right (odd_two_pow_sub_one (by omega))) odd_one ?_
  unfold exceptionalOrders
  split <;> simp_all

theorem odd_tableOrder_psp_two_even {n : ℕ} (hn : 1 ≤ n) : Odd (tableOrder .PSp 2 2 n) := by
  refine odd_tableOrder (odd_gcd_of_odd_right (odd_two_pow_sub_one hn)) odd_one ?_
  unfold exceptionalOrders
  split <;> simp_all

theorem odd_tableOrder_psu_four_even {n : ℕ} (hn : 2 ≤ n) : Odd (tableOrder .PSU 4 2 n) := by
  refine odd_tableOrder (odd_gcd_of_odd_right (odd_two_pow_add_one (by omega))) odd_one ?_
  unfold exceptionalOrders
  split <;> simp_all

theorem odd_tableOrder_g2_even {f : ℕ} (hf : 3 ≤ f) : Odd (tableOrder .G2 0 2 f) := by
  refine odd_tableOrder odd_one odd_one ?_
  unfold exceptionalOrders
  split <;> simp_all

theorem odd_tableOrder_suzuki {m : ℕ} (hm : 2 ≤ m) :
    Odd (tableOrder .twistedB2 0 2 (2 * m + 1)) := by
  refine odd_tableOrder odd_one odd_one ?_
  unfold exceptionalOrders
  split <;> simp_all

theorem odd_tableOrder_ree_f4 (m : ℕ) : Odd (tableOrder .twistedF4 0 2 (2 * m + 1)) := by
  refine odd_tableOrder odd_one odd_one ?_
  unfold exceptionalOrders
  split <;> simp_all

theorem pRank_two_le_of_psl_two (hGA : GriessMultipliersAllModels)
    (hGC : GriessMultipliersCentralCovers) {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (hZ2 : IsPGroup 2 (center J)) (hZnt : Nontrivial (center J)) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : CFSG.Blueprint.LieModel (J ⧸ center J) .PSL 2 p f) :
    CFSG.pRank 2 J ≤ 1 := by
  obtain ⟨-, _, ⟨g⟩⟩ := CFSG.ComponentClassification.TBLit.psl_two_double_cover hGA hGC hq
    hZ2 ((Subgroup.nontrivial_iff_ne_bot _).mp hZnt) hp hp2 hm
  have h2F : (2 : GaloisField p f) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p f) p]; exact hp2)
  have : Finite (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p f)) :=
    Finite.of_equiv _ g.toEquiv
  rw [pRank_congr_mulEquiv one_lt_two g]
  exact pRank_two_SL2_le h2F

theorem lieModel_psl_two_five_of_alternating {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : CFSG.Blueprint.LieModel X .PSL 2 5 1 := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hK : Nat.card (GaloisField 5 1) = 5 ^ 1 := GaloisField.card 5 1 one_ne_zero
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 5 1) (Or.inr (by rw [hK, pow_one]))
  have hadm : StatedLieAdmissible .PSL 2 5 1 := ⟨by norm_num, le_rfl, by decide⟩
  exact Or.inl ⟨by decide, hadm, GaloisField 5 1, inferInstance, inferInstance, hK,
    ⟨e.trans e5.symm⟩⟩

theorem twoCoverCensus_of (h42 : Item4_2) (hGA : GriessMultipliersAllModels)
    (hGC : GriessMultipliersCentralCovers) (hSpor : SporadicMultipliers)
    (hcov : TwoCoverRanks) : TwoCoverCensus := by
  intro J _ _ hq _ hS hZ2 hZnt hm2 hstar hstar3
  have : IsSimpleGroup (J ⧸ center J) := hq.2.1
  have hc : ∀ {X : Type} [Group X], (J ⧸ center J ≃* X) → IsTwoCover J X :=
    fun e => ⟨hq, hZ2, hZnt, ⟨e⟩⟩
  have h2Z := two_dvd_card_center hZ2 hZnt
  have hodd : ∀ {m : ℕ}, Odd m → Nat.card (center J) ∣ m → False := fun hm hd =>
    (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr (h2Z.trans hd))
  have h3 : CFSG.pRank 3 (J ⧸ center J) ≤ 3 := by
    rcases hstar3 with h | h
    · exact h
    · obtain ⟨e⟩ := h
      have hd : Nat.card (center J) ∣ Nat.card (hopfMultiplier NativeSporadic.ON) :=
        card_center_dvd_hopfMultiplier hq e
      rw [hSpor.2] at hd
      exact (hodd (by decide) hd).elim
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
    have hdvd := card_center_dvd_hopfMultiplier hq f
    rw [hSpor.1 s] at hdvd
    simp only [sporadics42, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact (hodd (by decide) hdvd).elim
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
      exact Or.inl ⟨f.trans b.symm⟩
    ·
      have hd : Nat.card (center J) ∣ 12 := hdvd
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := hZ2.exists_card_eq
      rw [hk] at hd h2Z
      have hk4 : k < 4 := by
        by_contra hk4
        have := Nat.le_of_dvd (by norm_num) ((pow_dvd_pow 2 (not_lt.mp hk4)).trans hd)
        norm_num at this
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
      interval_cases k
      · norm_num at h2Z
      · exact (hcov.m22 J hq (by rw [hk]; norm_num) ⟨f⟩ hm2).elim
      · exact Or.inr (Or.inl ⟨⟨f.trans b.symm⟩, by rw [hk]; norm_num⟩)
      · norm_num at hd
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
      exact Or.inr (Or.inr (Or.inl ⟨f.trans b.symm⟩))
    ·
      exact (hcov.hs J hq (card_center_eq_two_of_dvd hZnt hdvd) ⟨f⟩ hm2).elim
    ·
      exact (hr3 f hcov.suz).elim
    ·
      exact (hcov.ru J hq (card_center_eq_two_of_dvd hZnt hdvd) ⟨f⟩ hm2).elim
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

theorem quasisimpleCensus_of_inputs (h41 : Item4_1) (h42 : Item4_2)
    (hGA : GriessMultipliersAllModels) (hGC : GriessMultipliersCentralCovers)
    (hSpor : SporadicMultipliers) (hcov : TwoCoverRanks) : QuasisimpleCensus :=
  quasisimpleCensus_of h41 (twoCoverCensus_of h42 hGA hGC hSpor hcov)

theorem rank3II_4_4_of_inputs (h41 : Item4_1) (h42 : Item4_2)
    (hGA : GriessMultipliersAllModels) (hGC : GriessMultipliersCentralCovers)
    (hSpor : SporadicMultipliers) (hcov : TwoCoverRanks) (hL34 : FourL34NotSLFourOdd) :
    Item4_4 :=
  rank3II_4_4_of_census (quasisimpleCensus_of_inputs h41 h42 hGA hGC hSpor hcov) hL34

end CFSG.RankThree.PartTwo.Sec4.Census
