module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63LieOut
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63G2Sylow
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63F4Sylow
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.StormerG2Prime
import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy
import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem k1471l1_lt_of_primitive {r a n : ℕ} (hr : r.Prime) (ha : 0 < a) (hn : 0 < n)
    (hd : r ∣ a ^ n - 1) (hprim : ∀ k : ℕ, 0 < k → k < n → ¬ r ∣ a ^ k - 1) : n < r := by
  have := Fact.mk hr
  have hx : (a : ZMod r) ^ n = 1 :=
    (CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff ha n).1 hd
  have hord : orderOf (a : ZMod r) = n := by
    refine (orderOf_eq_iff hn).2 ⟨hx, fun k hkn hk hxk => hprim k hk hkn ?_⟩
    exact (CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff ha k).2 hxk
  have hx0 : (a : ZMod r) ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne'] at hx
    exact zero_ne_one hx
  have hdvd : n ∣ r - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hx0
  have h2 := hr.two_le
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega

private theorem k1471l1_of_primitive {p f r : ℕ} (hp : p.Prime) (hf : 2 ≤ f) (hr : r.Prime)
    (hd : r ∣ p ^ (2 * f) - 1) (hprim : ∀ k : ℕ, 0 < k → k < 2 * f → ¬ r ∣ p ^ k - 1) :
    5 ≤ r ∧ r ∣ (p ^ f) ^ 2 - 1 ∧ ¬ r ∣ 2 * f := by
  have hlt : 2 * f < r := k1471l1_lt_of_primitive hr hp.pos (by omega) hd hprim
  refine ⟨by omega, ?_, fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)⟩
  rw [← pow_mul, mul_comm f 2]
  exact hd

theorem exists_prime_g2_outer_free {p f : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hq : 3 ≤ p ^ f) (h5 : p ^ f ≠ 5) (h7 : p ^ f ≠ 7) (h17 : p ^ f ≠ 17) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ (p ^ f) ^ 2 - 1 ∧ ¬ r ∣ 2 * f := by
  rcases Nat.eq_or_lt_of_le hf with rfl | hf2
  · rw [pow_one] at hq h5 h7 h17 ⊢
    have h2 := hp.two_le
    have h5le : 5 ≤ p := by
      rcases (by omega : p = 4 ∨ 5 ≤ p) with rfl | h
      · exact absurd hp (by norm_num)
      · exact h
    obtain ⟨r, hr, hr5, hrd⟩ := exists_prime_five_le_dvd_sq_sub_one hp h5le h5 h7 h17
    exact ⟨r, hr, hr5, hrd, fun h => absurd (Nat.le_of_dvd (by norm_num) h) (by omega)⟩
  · by_cases hp8 : p = 2 ∧ f = 3
    · obtain ⟨rfl, rfl⟩ := hp8
      exact ⟨7, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · obtain ⟨r, hr, hd, hprim⟩ : ∃ r : ℕ, r.Prime ∧ r ∣ p ^ (2 * f) - 1 ∧
          ∀ k : ℕ, 0 < k → k < 2 * f → ¬ r ∣ p ^ k - 1 := by
        by_cases hp2 : p = 2
        · subst hp2
          exact CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (2 * f) (by omega)
            (by omega)
        · exact CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one
            (by have := hp.two_le; omega) (by omega)
      obtain ⟨h5r, h1, h2⟩ := k1471l1_of_primitive hp (by omega) hr hd hprim
      exact ⟨r, hr, h5r, h1, h2⟩

private theorem k1471l2_lt_of_primitive {r a n : ℕ} (hr : r.Prime) (ha : 0 < a) (hn : 0 < n)
    (hd : r ∣ a ^ n - 1) (hprim : ∀ k : ℕ, 0 < k → k < n → ¬ r ∣ a ^ k - 1) : n < r := by
  have := Fact.mk hr
  have hx : (a : ZMod r) ^ n = 1 :=
    (CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff ha n).1 hd
  have hord : orderOf (a : ZMod r) = n := by
    refine (orderOf_eq_iff hn).2 ⟨hx, fun k hkn hk hxk => hprim k hk hkn ?_⟩
    exact (CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff ha k).2 hxk
  have hx0 : (a : ZMod r) ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne'] at hx
    exact zero_ne_one hx
  have hdvd : n ∣ r - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hx0
  have h2 := hr.two_le
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega

private theorem k1471l2_dvd_sq_add {q r : ℕ} (hr : r.Prime) (hq : 1 ≤ q) (hd : r ∣ q ^ 3 - 1)
    (hq1 : ¬ r ∣ q - 1) : r ∣ q ^ 2 + q + 1 := by
  have key : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact Nat.sub_eq_of_eq_add (by ring)
  rw [key] at hd
  exact (hr.dvd_mul.1 hd).resolve_left hq1

private theorem k1471l2_of_primitive {p f r : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hr : r.Prime)
    (hd : r ∣ p ^ (3 * f) - 1) (hprim : ∀ k : ℕ, 0 < k → k < 3 * f → ¬ r ∣ p ^ k - 1) :
    5 ≤ r ∧ r ∣ (p ^ f) ^ 2 + p ^ f + 1 ∧ ¬ r ∣ 3 * f := by
  have hlt : 3 * f < r := k1471l2_lt_of_primitive hr hp.pos (by omega) hd hprim
  have hr4 : r ≠ 4 := by
    rintro rfl
    exact absurd hr (by norm_num)
  refine ⟨by omega, ?_, fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)⟩
  refine k1471l2_dvd_sq_add hr (Nat.one_le_pow _ _ hp.pos) ?_ (hprim f (by omega) (by omega))
  rw [← pow_mul, mul_comm f 3]
  exact hd

theorem exists_prime_triality_outer_free {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ (p ^ f) ^ 2 + p ^ f + 1 ∧ ¬ r ∣ 3 * f := by
  by_cases hp8 : p = 2 ∧ f = 2
  · obtain ⟨rfl, rfl⟩ := hp8
    exact ⟨7, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · obtain ⟨r, hr, hd, hprim⟩ : ∃ r : ℕ, r.Prime ∧ r ∣ p ^ (3 * f) - 1 ∧
        ∀ k : ℕ, 0 < k → k < 3 * f → ¬ r ∣ p ^ k - 1 := by
      by_cases hp2 : p = 2
      · subst hp2
        exact CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (3 * f) (by omega)
          (by omega)
      · exact CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one
          (by have := hp.two_le; omega) (by omega)
    obtain ⟨h5, h1, h2⟩ := k1471l2_of_primitive hp hf hr hd hprim
    exact ⟨r, hr, h5, h1, h2⟩

private theorem k1471l3_lt_of_primitive {r a n : ℕ} (hr : r.Prime) (ha : 0 < a) (hn : 0 < n)
    (hd : r ∣ a ^ n - 1) (hprim : ∀ k : ℕ, 0 < k → k < n → ¬ r ∣ a ^ k - 1) : n < r := by
  have := Fact.mk hr
  have hx : (a : ZMod r) ^ n = 1 :=
    (CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff ha n).1 hd
  have hord : orderOf (a : ZMod r) = n := by
    refine (orderOf_eq_iff hn).2 ⟨hx, fun k hkn hk hxk => hprim k hk hkn ?_⟩
    exact (CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff ha k).2 hxk
  have hx0 : (a : ZMod r) ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne'] at hx
    exact zero_ne_one hx
  have hdvd : n ∣ r - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hx0
  have h2 := hr.two_le
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega

theorem exists_prime_ree_outer_free {f : ℕ} (hf : 3 ≤ f) (hodd : Odd f) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ 2 ^ f - 1 ∧ ¬ r ∣ f := by
  have hf6 : f ≠ 6 := by
    have := Nat.odd_iff.mp hodd
    omega
  obtain ⟨r, hr, hd, hprim⟩ :=
    CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one f (by omega) hf6
  have hlt : f < r := k1471l3_lt_of_primitive hr (by norm_num) (by omega) hd hprim
  have hr4 : r ≠ 4 := by
    rintro rfl
    exact absurd hr (by norm_num)
  exact ⟨r, hr, by omega, hd, fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)⟩

@[expose] def StarWitness (K : Type) [Group K] [Finite K] (r : ℕ) : Prop :=
  r.Prime ∧ 5 ≤ r ∧ ¬ r ∣ Nat.card (Outer K) ∧
    ∃ S : Sylow r K, IsMulCommutative ↥(S : Subgroup K) ∧
      ∃ E : Subgroup K, E ≤ (S : Subgroup K) ∧ (∀ e ∈ E, e ^ r = 1) ∧ Nat.card E = r ^ 2

@[expose] def G2NonsplitSylowInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p f r : ℕ), LieModel K .G2 0 p f → r.Prime → 5 ≤ r →
    r ∣ p ^ f + 1 → ∃ S : Sylow r K, IsMulCommutative ↥(S : Subgroup K) ∧
      ∃ E : Subgroup K, E ≤ (S : Subgroup K) ∧ (∀ e ∈ E, e ^ r = 1) ∧ Nat.card E = r ^ 2

@[expose] def TrialityTorusSylowInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p f r : ℕ), LieModel K .trialityD4 0 p f → r.Prime → 5 ≤ r →
    r ∣ (p ^ f) ^ 2 + p ^ f + 1 → ∃ S : Sylow r K, IsMulCommutative ↥(S : Subgroup K) ∧
      ∃ E : Subgroup K, E ≤ (S : Subgroup K) ∧ (∀ e ∈ E, e ^ r = 1) ∧ Nat.card E = r ^ 2

theorem not_dvd_card_outer_of_lieModel_g2
    {K : Type} [Group K] [Finite K] {p f r : ℕ}
    (hK : LieModel K .G2 0 p f) (hp : p.Prime) (hrf : ¬ r ∣ 2 * f) :
    ¬ r ∣ Nat.card (Outer K) := by
  have hc : CFSG.Blueprint.ChevalleyExceptionalModel K .G2 p f :=
    LieModel.chevalleyExceptionalModel hK (by decide)
  obtain ⟨K', _, _, hKcard, ⟨eX⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hc.2
  have hf : 1 ≤ f := hc.1.2.1
  have h3 : 3 ≤ Nat.card K' := by
    rw [hKcard]
    exact hc.1.2.2.2
  have hdvd : Nat.card (Outer (CFSG.Blueprint.Chevalley.adjointGroup .G2 K')) ∣ 2 * f :=
    card_outer_adjointGroup_G2_dvd hp hf hKcard h3
  have hcard : Nat.card (Outer K) =
      Nat.card (Outer (CFSG.Blueprint.Chevalley.adjointGroup .G2 K')) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eX).toEquiv
  rw [hcard]
  exact fun hd => hrf (hd.trans hdvd)

private theorem k1471l5_exists_sylow_abelian_of_mulEquiv {G H : Type} [Group G] [Group H]
    [Finite H] {r : ℕ} (hr : r.Prime) (e : H ≃* G) (hab : ∀ S : Sylow r H, IsMulCommutative ↥S)
    (h2 : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup H)) :
    ∃ S : Sylow r G, IsMulCommutative ↥(S : Subgroup G) ∧
      ∃ E : Subgroup G, E ≤ (S : Subgroup G) ∧ (∀ x ∈ E, x ^ r = 1) ∧ Nat.card E = r ^ 2 := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨A, -, hA, hAcard⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.exists_elemAbelian_card_of_le_pRank hr (k := 2) h2
  obtain ⟨S₀, hS₀⟩ := hA.isPGroup.exists_le_sylow
  have := hab S₀
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨S₀.mapSurjective hsurj, ?_, A.map e.toMonoidHom, Subgroup.map_mono hS₀,
    (hA.map e.toMonoidHom).2, ?_⟩
  · rw [Sylow.coe_mapSurjective]
    infer_instance
  · rw [Subgroup.card_map_of_injective e.injective, hAcard]

theorem exists_sylow_abelian_of_lieModel_g2_split
    {K : Type} [Group K] [Finite K] {p f r : ℕ}
    (hK : LieModel K .G2 0 p f) (hr : r.Prime) (hr5 : 5 ≤ r) (hrd : r ∣ p ^ f - 1) :
    ∃ S : Sylow r K, IsMulCommutative ↥(S : Subgroup K) ∧
      ∃ E : Subgroup K, E ≤ (S : Subgroup K) ∧ (∀ e ∈ E, e ^ r = 1) ∧ Nat.card E = r ^ 2 := by
  have hc := LieModel.chevalleyExceptionalModel hK (by decide)
  obtain ⟨K', _, _, hKcard, ⟨eX⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hc.2
  have hrd' : r ∣ Nat.card K' - 1 := by
    rw [hKcard]
    exact hrd
  obtain ⟨h2, hab⟩ := two_le_pRank_and_sylow_abelian_adjointGroup_G2 hr (by omega) hrd'
  exact k1471l5_exists_sylow_abelian_of_mulEquiv hr eX.symm hab h2

theorem not_dvd_card_outer_of_lieModel_trialityD4_of_not_dvd_three_mul
    {K : Type} [Group K] [Finite K] {p f r : ℕ} (hK : LieModel K .trialityD4 0 p f)
    (hp : p.Prime) (hrf : ¬ r ∣ 3 * f) : ¬ r ∣ Nat.card (Outer K) := by
  have hc := LieModel.chevalleyExceptionalModel hK (by decide)
  have hf : 1 ≤ f := hc.1.2.1
  have hdvd : Nat.card (Outer K) ∣ 3 * f := card_outer_twistedChevalleyModel_D4_dvd hp hf hc.2
  exact fun hd => hrf (hd.trans hdvd)

theorem not_dvd_card_outer_of_lieModel_twistedF4
    {K : Type} [Group K] [Finite K] {f r : ℕ}
    (hK : LieModel K .twistedF4 0 2 f) (hrf : ¬ r ∣ f) : ¬ r ∣ Nat.card (Outer K) := by
  have hRT : CFSG.Blueprint.ReeTitsModel K .twistedF4 2 f :=
    (LieModel.reeTitsModel hK (by decide)).2
  have hdvd : Nat.card (Outer K) ∣ f := card_outer_reeTitsModel_twistedF4_dvd hRT
  exact fun hd => hrf (hd.trans hdvd)

theorem exists_sylow_abelian_of_lieModel_twistedF4_witness
    {K : Type} [Group K] [Finite K] {f r : ℕ}
    (hK : LieModel K .twistedF4 0 2 f) (hr : r.Prime) (hr5 : 5 ≤ r) (hrd : r ∣ 2 ^ f - 1) :
    ∃ S : Sylow r K, IsMulCommutative ↥(S : Subgroup K) ∧
      ∃ E : Subgroup K, E ≤ (S : Subgroup K) ∧ (∀ e ∈ E, e ^ r = 1) ∧ Nat.card E = r ^ 2 := by
  obtain ⟨hab, h2⟩ := exists_sylow_abelian_of_lieModel_twistedF4 hK hr (by omega : 3 < r) hrd
  obtain ⟨A, -, hA, hAcard⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.exists_elemAbelian_card_of_le_pRank hr (k := 2) h2
  obtain ⟨S, hS⟩ := hA.isPGroup.exists_le_sylow
  exact ⟨S, hab S, A, hS, hA.2, hAcard⟩

theorem exists_starWitness_of_lieModel_g2
    (hNS : G2NonsplitSylowInput)
    {K : Type} [Group K] [Finite K] {p f : ℕ} (hK : LieModel K .G2 0 p f) (hp : p.Prime)
    (hp3 : p ≠ 3) (hf : 1 ≤ f) (hq : 3 ≤ p ^ f) (h5 : p ^ f ≠ 5) (h7 : p ^ f ≠ 7)
    (h17 : p ^ f ≠ 17) : ∃ r : ℕ, StarWitness K r := by
  obtain ⟨r, hr, hr5, hrd, hrf⟩ := exists_prime_g2_outer_free hp hp3 hf hq h5 h7 h17
  have hrd' : r ∣ (p ^ f - 1) * (p ^ f + 1) := by
    have key : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
      obtain ⟨m, hm⟩ : ∃ m, p ^ f = m + 1 := ⟨p ^ f - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel]
      rw [show (m + 1) ^ 2 - 1 = m * (m + 2) by
        rw [Nat.sub_eq_of_eq_add]
        ring]
    rwa [key] at hrd
  refine ⟨r, hr, hr5, not_dvd_card_outer_of_lieModel_g2 hK hp hrf, ?_⟩
  rcases (Nat.Prime.dvd_mul hr).1 hrd' with h | h
  · exact exists_sylow_abelian_of_lieModel_g2_split hK hr hr5 h
  · exact hNS K p f r hK hr hr5 h

theorem exists_starWitness_of_lieModel_trialityD4
    (hTri : TrialityTorusSylowInput)
    {K : Type} [Group K] [Finite K] {p f : ℕ} (hK : LieModel K .trialityD4 0 p f) (hp : p.Prime)
    (hf : 1 ≤ f) : ∃ r : ℕ, StarWitness K r := by
  obtain ⟨r, hr, hr5, hrd, hrf⟩ := exists_prime_triality_outer_free hp hf
  exact ⟨r, hr, hr5,
    not_dvd_card_outer_of_lieModel_trialityD4_of_not_dvd_three_mul hK hp hrf,
    hTri K p f r hK hr hr5 hrd⟩

theorem exists_starWitness_of_lieModel_twistedF4
    {K : Type} [Group K] [Finite K] {f : ℕ}
    (hK : LieModel K .twistedF4 0 2 f) (hf : 3 ≤ f) (hodd : Odd f) :
    ∃ r : ℕ, StarWitness K r := by
  obtain ⟨r, hr, hr5, hrd, hrf⟩ := exists_prime_ree_outer_free hf hodd
  exact ⟨r, hr, hr5, not_dvd_card_outer_of_lieModel_twistedF4 hK hrf,
    exists_sylow_abelian_of_lieModel_twistedF4_witness hK hr hr5 hrd⟩

theorem exists_starWitness_of_lie_families
    (hNS : G2NonsplitSylowInput)
    (hTri : TrialityTorusSylowInput) {K : Type} [Group K] [Finite K]
    (h : (∃ p f : ℕ, LieModel K .G2 0 p f ∧ p.Prime ∧ p ≠ 3 ∧ 1 ≤ f ∧ 3 ≤ p ^ f ∧
          p ^ f ≠ 5 ∧ p ^ f ≠ 7 ∧ p ^ f ≠ 17) ∨
        (∃ p f : ℕ, LieModel K .trialityD4 0 p f ∧ p.Prime ∧ 1 ≤ f) ∨
        (∃ f : ℕ, LieModel K .twistedF4 0 2 f ∧ 3 ≤ f ∧ Odd f)) :
    ∃ r : ℕ, StarWitness K r := by
  rcases h with ⟨p, f, hK, hp, hp3, hf, hq, h5, h7, h17⟩ | ⟨p, f, hK, hp, hf⟩ | ⟨f, hK, hf, hodd⟩
  · exact exists_starWitness_of_lieModel_g2 hNS hK hp hp3 hf hq h5 h7 h17
  · exact exists_starWitness_of_lieModel_trialityD4 hTri hK hp hf
  · exact exists_starWitness_of_lieModel_twistedF4 hK hf hodd

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
