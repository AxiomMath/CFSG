module

public import CFSG.RankThree.PartTwo.Sec13.F135LastKF135
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverSmall
public import CFSG.RankThree.PartOne.Mult.Alternating
public import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.CharacterTheory.Burnside
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.KFacts.K71Sp4

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.Assembly.LowTwoRank CFSG.Models Matrix Subgroup
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Census
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.ComponentClassification.PresentationLocal (sympFour antidiagGram omegaPerm)

theorem generic_dvd (t : StatedLieTag) (n p f ℓ : ℕ) (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ)
    (h : ℓ ∣ (genericOrders t n p f).1 ∨ ℓ ∣ (genericOrders t n p f).2) :
    (t = .PSL ∨ t = .PSU) ∧ ℓ ∣ n := by
  have h1 : ¬ ℓ ∣ 1 := fun h => by have := Nat.le_of_dvd one_pos h; omega
  have h2 : ¬ ℓ ∣ 2 := fun h => by have := Nat.le_of_dvd two_pos h; omega
  have h3 : ¬ ℓ ∣ 4 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have h4 : ¬ ℓ ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  rcases h with h | h <;> cases t <;> simp only [genericOrders] at h <;> (try split_ifs at h) <;>
    (try simp only [Nat.dvd_gcd_iff] at h) <;>
    first
    | exact ⟨Or.inl rfl, h.1⟩
    | exact ⟨Or.inr rfl, h.1⟩
    | (exfalso; simp_all)

theorem exceptional_dvd (t : StatedLieTag) (n p f ℓ : ℕ) (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ)
    (h : ℓ ∣ (exceptionalOrders t n p f).1 ∨ ℓ ∣ (exceptionalOrders t n p f).2) : False := by
  have h1 : ¬ ℓ ∣ 1 := fun h => by have := Nat.le_of_dvd one_pos h; omega
  have h2 : ¬ ℓ ∣ 2 := fun h => by have := Nat.le_of_dvd two_pos h; omega
  have h3 : ¬ ℓ ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have h4 : ¬ ℓ ∣ 4 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  unfold exceptionalOrders at h
  split at h <;> simp_all

theorem prime_dvd_tableOrder {t : StatedLieTag} {n p f ℓ : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ)
    (h : ℓ ∣ tableOrder t n p f) : (t = .PSL ∨ t = .PSU) ∧ ℓ ∣ n := by
  unfold tableOrder at h
  rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
    · exact generic_dvd t n p f ℓ hℓ h5 (Or.inl h)
    · exact generic_dvd t n p f ℓ hℓ h5 (Or.inr h)
  · rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
    · exact (exceptional_dvd t n p f ℓ hℓ h5 (Or.inl h)).elim
    · exact (exceptional_dvd t n p f ℓ hℓ h5 (Or.inr h)).elim

theorem not_quasisimple_of_card_dvd {J X : Type} [Group J] [Finite J] [Group X] {a b : ℕ}
    (hX : Nat.card X ∣ 2 ^ a * 3 ^ b) (hq : IsQuasisimple J) (e : J ⧸ center J ≃* X) : False := by
  have : IsSimpleGroup (J ⧸ center J) := hq.2.1
  have hcard : Nat.card (J ⧸ center J) ∣ 2 ^ a * 3 ^ b := by rwa [Nat.card_congr e.toEquiv]
  obtain ⟨d₁, d₂, hd₁, hd₂, hd⟩ := dvd_mul.mp hcard
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd₂
  have := Fintype.ofFinite (J ⧸ center J)
  have hsolv : Group.IsSolvable (J ⧸ center J) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hd])
  obtain ⟨x, y, hxy⟩ := hq.2.2
  exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv x y)

theorem not_quasisimple_projSL_two {J : Type} [Group J] [Finite J] (p : ℕ) [Fact p.Prime]
    (hp : p = 2 ∨ p = 3) (hq : IsQuasisimple J)
    (e : J ⧸ center J ≃* projSL 2 (GaloisField p 1)) : False := by
  rcases hp with rfl | rfl
  · exact not_quasisimple_of_card_dvd (a := 1) (b := 1) (card_projSL_two_dvd 2) hq e
  · exact not_quasisimple_of_card_dvd (a := 4) (b := 1) (card_projSL_two_dvd 3) hq e

theorem not_quasisimple_projSU_three_two {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (e : J ⧸ center J ≃* projSU 3 2 1) : False := by
  have : IsSimpleGroup (J ⧸ center J) := hq.2.1
  have := Sec13.isSolvable_projSU_two
  have hsolv : Group.IsSolvable (J ⧸ center J) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨x, y, hxy⟩ := hq.2.2
  exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv x y)

theorem not_quasisimple_projSp_two_two {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (e : J ⧸ center J ≃* projSp 2 F2) : False := by
  have : Group.IsPerfect J := hq.1
  let ε := CFSG.RankThree.PartTwo.KFacts.statedSpEquivProjSpOfCharTwo F2
  let χ : J →* ℤˣ := Equiv.Perm.sign.comp (omegaPerm.comp (sp4Hom.comp
    (ε.symm.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center J))))))
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (center J) (e.symm (ε sp4Transvection))
  have hχ : χ y = -1 := by
    change Equiv.Perm.sign (omegaPerm (sp4Hom (ε.symm (e (QuotientGroup.mk' (center J) y))))) =
      -1
    rw [hy, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply, sp4Hom_transvection,
      sign_omegaPerm_t03]
  have hker : y ∈ χ.ker :=
    Abelianization.commutator_subset_ker χ (Group.IsPerfect.mem_commutator (g := y))
  rw [MonoidHom.mem_ker, hχ] at hker
  exact absurd hker (by decide)

theorem two_pow_ne_of_two_le {n : ℕ} (hn : 2 ≤ n) : 2 ^ n ≠ 2 ∧ 2 ^ n ≠ 3 := by
  have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

theorem kFactMultPrime_of_inputs (hGA : GriessMultipliersAllModels) (hSpor : ∀ {s :
    TauCeti.SporadicName}, s ∈ CFSG.RankThree.PartOne.Census3.sporadicsThm3 → ∀ {M : Type} [Group M]
    [Finite M], CFSG.IsQuasisimple M → (M ⧸ center M ≃* (TauCeti.CFSGIndex.sporadic s).Group) → ∀ {ℓ
    : ℕ}, ℓ.Prime → 7 ≤ ℓ → ¬ ℓ ∣ Nat.card (center M)) :
    KFactMultPrime := by
  intro J _ _ hq h42 ℓ hℓ h7 hdvd
  have hsimp : IsSimpleGroup (J ⧸ center J) := hq.2.1
  have hsmall : ∀ {X : Type} [Group X] (e : J ⧸ center J ≃* X) {t : StatedLieTag} {n p f : ℕ},
      LieModel X t n p f → 0 < n → n < 7 → False := by
    intro X _ e t n p f hm hn0 hn7
    have h := (prime_dvd_tableOrder hℓ (by omega)
      (hdvd.trans (card_center_dvd_tableOrder hGA hq e hm))).2
    have := Nat.le_of_dvd hn0 h
    omega
  have hnot : ∀ {X : Type} [Group X] (e : J ⧸ center J ≃* X) {t : StatedLieTag} {n p f : ℕ},
      LieModel X t n p f → t ≠ .PSL → t ≠ .PSU → False := by
    intro X _ e t n p f hm h1 h2
    have h := (prime_dvd_tableOrder hℓ (by omega)
      (hdvd.trans (card_center_dvd_tableOrder hGA hq e hm))).1
    rcases h with h | h
    · exact h1 h
    · exact h2 h
  rcases h42 with
    ⟨p, e, _, hp, he, hf⟩ | ⟨p, e, _, hp, he, -, hf | hf⟩ | ⟨hr, hf⟩ |
    ⟨p, _, hp, ⟨q, hqp, hqe, hG2⟩ | hf | hf | hf⟩ | ⟨n, hn5, hn12, hf⟩ | ⟨s, hs, hf⟩ |
    hc7 | hc8 | hc9
  ·
    obtain ⟨f⟩ := hf
    have hpp : p.Prime := Fact.out
    by_cases h3e : p ^ e = 3
    · obtain ⟨rfl, rfl⟩ := Nat.prime_three.pow_eq_iff.mp h3e
      exact not_quasisimple_projSL_two 3 (Or.inr rfl) hq f
    · have hodd' : Odd (p ^ e) := (hpp.odd_of_ne_two hp).pow
      have hadm : StatedLieAdmissible .PSL 2 p e := by
        refine ⟨hpp, he, le_refl 2, fun h => ?_, fun h => h3e (Prod.mk.inj h).2⟩
        have h2 := (Prod.mk.inj h).2
        rw [h2] at hodd'
        exact (Nat.not_even_iff_odd.mpr hodd') even_two
      exact hsmall f (lieModel_projSL hadm) (by norm_num) (by norm_num)
  ·
    obtain ⟨f⟩ := hf
    exact hsmall f (lieModel_projSL (n := 3) (p := p) (e := e)
      ⟨Fact.out, he, by norm_num, fun h => by simp at h, fun h => by simp at h⟩)
      (by norm_num) (by norm_num)
  ·
    obtain ⟨f⟩ := hf
    have hpp : p.Prime := Fact.out
    exact hsmall f (lieModel_projSU (n := 3) (p := p) (e := e)
      ⟨hpp, he, le_refl 3, fun h => by
        have h2 := (Prod.mk.inj h).2
        have : p ≤ p ^ e := Nat.le_self_pow (by omega) p
        omega⟩) (by norm_num) (by norm_num)
  ·
    obtain ⟨f⟩ := hf
    have hm := lieModel_lie (t := .twistedG2) (p := 3) (f := 3)
      ⟨Nat.prime_three, by norm_num, by decide⟩ ⟨.reeG2 1, hr⟩ ⟨rfl, rfl⟩
    exact hnot f hm (by decide) (by decide)
  ·
    obtain ⟨hqv, ⟨g⟩⟩ := hG2
    have h3 : 3 ≤ q.p ^ q.exponent := by
      have h := ((TauCeti.LieTypeIndex.valid_iff _).mp hqv).1
      simpa using h
    have hm := lieModel_lie (t := .G2) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl, h3⟩ ⟨.G2 q, hqv⟩ ⟨rfl, rfl⟩
    exact hnot g hm (by decide) (by decide)
  ·
    obtain ⟨f⟩ := hf
    have hpp : p.Prime := Fact.out
    exact hnot f (lieModel_projSp (n := 2) (p := p) (e := 1)
      ⟨hpp, le_rfl, le_refl 2, fun h => by
        have h2 := (Prod.mk.inj h).2
        rw [pow_one] at h2
        omega⟩) (by decide) (by decide)
  ·
    obtain ⟨f⟩ := hf
    have hpp : p.Prime := Fact.out
    exact hsmall f (lieModel_projSL (n := 4) (p := p) (e := 1)
      ⟨hpp, le_rfl, by norm_num, fun h => by simp at h, fun h => by simp at h⟩)
      (by norm_num) (by norm_num)
  ·
    obtain ⟨f⟩ := hf
    have hpp : p.Prime := Fact.out
    exact hsmall f (lieModel_projSU (n := 4) (p := p) (e := 1)
      ⟨hpp, le_rfl, by norm_num, fun h => by simp at h⟩) (by norm_num) (by norm_num)
  ·
    obtain ⟨f⟩ := hf
    have : Group.IsPerfect J := hq.1
    exact CFSG.RankThree.PartOne.Mult.alternating_center_small_primes hn5 f hℓ (by omega) hdvd
  ·
    obtain ⟨f⟩ := hf
    exact hSpor hs hq f hℓ h7 hdvd
  ·
    rcases hc7 with ⟨n, hn, hf | hf | hf | hf | hf⟩ | ⟨q, hq2, hG2⟩ | ⟨q, hqv, -, hf⟩ |
      ⟨m, hm, hf⟩ | ⟨m, hm, hf⟩ | ⟨ht, hf⟩
    ·
      obtain ⟨f⟩ := hf
      rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
      · exact not_quasisimple_projSL_two 2 (Or.inl rfl) hq f
      · have hne := two_pow_ne_of_two_le hn2
        exact hsmall f (lieModel_projSL (n := 2) (p := 2) (e := n)
          ⟨Nat.prime_two, by omega, le_refl 2, fun h => hne.1 (Prod.mk.inj h).2,
            fun h => hne.2 (Prod.mk.inj h).2⟩) (by norm_num) (by norm_num)
    ·
      obtain ⟨f⟩ := hf
      exact hsmall f (lieModel_projSL (n := 3) (p := 2) (e := n)
        ⟨Nat.prime_two, by omega, by norm_num, fun h => by simp at h, fun h => by simp at h⟩)
        (by norm_num) (by norm_num)
    ·
      obtain ⟨f⟩ := hf
      rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
      · exact not_quasisimple_projSU_three_two hq f
      · have hne := two_pow_ne_of_two_le hn2
        exact hsmall f (lieModel_projSU (n := 3) (p := 2) (e := n)
          ⟨Nat.prime_two, by omega, le_refl 3, fun h => hne.1 (Prod.mk.inj h).2⟩)
          (by norm_num) (by norm_num)
    ·
      obtain ⟨f⟩ := hf
      rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
      · exact not_quasisimple_projSp_two_two hq f
      · have hne := two_pow_ne_of_two_le hn2
        exact hnot f (lieModel_projSp (n := 2) (p := 2) (e := n)
          ⟨Nat.prime_two, by omega, le_refl 2, fun h => hne.1 (Prod.mk.inj h).2⟩)
          (by decide) (by decide)
    ·
      obtain ⟨f⟩ := hf
      exact hsmall f (lieModel_projSU (n := 4) (p := 2) (e := n)
        ⟨Nat.prime_two, by omega, by norm_num, fun h => by simp at h⟩) (by norm_num)
        (by norm_num)
    ·
      obtain ⟨hqv, ⟨g⟩⟩ := hG2
      have h3 : 3 ≤ q.p ^ q.exponent := by
        have h := ((TauCeti.LieTypeIndex.valid_iff _).mp hqv).1
        simpa using h
      rw [hq2] at h3
      have hm := lieModel_lie (t := .G2) (p := 2) (f := q.exponent)
        ⟨Nat.prime_two, q.exponent_pos, rfl, h3⟩ ⟨.G2 q, hqv⟩ ⟨hq2, rfl⟩
      exact hnot g hm (by decide) (by decide)
    ·
      obtain ⟨f⟩ := hf
      have hm := lieModel_lie (t := .trialityD4) (p := q.p) (f := q.exponent)
        ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.trialityD4 q, hqv⟩ ⟨rfl, rfl⟩
      exact hnot f hm (by decide) (by decide)
    ·
      obtain ⟨f⟩ := hf
      have hm1 : 1 ≤ m := by
        have h := ((TauCeti.LieTypeIndex.valid_iff _).mp hm).1
        simpa using h
      have hmod := lieModel_lie (t := .twistedB2) (p := 2) (f := 2 * m + 1)
        ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.suzuki m, hm⟩ ⟨rfl, rfl⟩
      exact hnot f hmod (by decide) (by decide)
    ·
      obtain ⟨f⟩ := hf
      have hm1 : 1 ≤ m := by
        have h := ((TauCeti.LieTypeIndex.valid_iff _).mp hm).1
        simpa using h
      have hmod := lieModel_lie (t := .twistedF4) (p := 2) (f := 2 * m + 1)
        ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeF4 m, hm⟩ ⟨rfl, rfl⟩
      exact hnot f hmod (by decide) (by decide)
    ·
      obtain ⟨f⟩ := hf
      have hmod := lieModel_lie (t := .Tits) (p := 2) (f := 1)
        ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩ ⟨.tits, ht⟩ ⟨rfl, rfl⟩
      exact hnot f hmod (by decide) (by decide)
  ·
    rcases hc8 with hf | hf | hf | hf | hf | hf | hf | hf | ⟨b, c, hbc, hf⟩ | hf | hf | hf | hf |
      hf
    all_goals obtain ⟨f⟩ := hf
    ·
      exact hsmall f (lieModel_projSL (n := 5) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, by decide⟩) (by norm_num) (by norm_num)
    ·
      exact hsmall f (lieModel_projSU (n := 5) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, by decide⟩) (by norm_num) (by norm_num)
    ·
      exact hsmall f (lieModel_projSL (n := 6) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, by decide⟩) (by norm_num) (by norm_num)
    ·
      exact hsmall f (lieModel_projSU (n := 6) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, by decide⟩) (by norm_num) (by norm_num)
    ·
      have hm := lieModel_projSL (n := 7) (p := 2) (e := 1) ⟨Nat.prime_two, le_rfl, by decide⟩
      have h1 : tableOrder .PSL 7 2 1 = 1 := by decide
      have h := hdvd.trans (card_center_dvd_tableOrder hGA hq f hm)
      rw [h1] at h
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp h)
    ·
      exact hnot f (lieModel_projSp (n := 3) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, by decide⟩) (by decide) (by decide)
    ·
      exact hnot f (lieModel_projSp (n := 4) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, by decide⟩) (by decide) (by decide)
    ·
      exact hnot f (lieModel_projOmegaPlus (n := 4) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, le_refl 4⟩) (by decide) (by decide)
    ·
      exact hnot f (lieModel_projOmegaMinus (n := 4) (p := 2) (e := 1)
        ⟨Nat.prime_two, le_rfl, le_refl 4⟩ hbc) (by decide) (by decide)
    ·
      exact hsmall f (lieModel_projSL (n := 4) (p := 2) (e := 2)
        ⟨Nat.prime_two, by norm_num, by decide⟩) (by norm_num) (by norm_num)
    ·
      exact hnot f (lieModel_projSp (n := 3) (p := 2) (e := 2)
        ⟨Nat.prime_two, by norm_num, by decide⟩) (by decide) (by decide)
    ·
      exact hsmall f (lieModel_projSU (n := 5) (p := 2) (e := 2)
        ⟨Nat.prime_two, by norm_num, by decide⟩) (by norm_num) (by norm_num)
    ·
      exact hsmall f (lieModel_projSU (n := 5) (p := 2) (e := 3)
        ⟨Nat.prime_two, by norm_num, by decide⟩) (by norm_num) (by norm_num)
    ·
      have hm := lieModel_lie (t := .F4) (p := 2) (f := 1) ⟨Nat.prime_two, le_rfl, rfl⟩
        f4TwoIndex ⟨rfl, rfl⟩
      exact hnot f hm (by decide) (by decide)
  ·
    rcases hc9 with ⟨e, he1, he3, hf | hf⟩ | hf | hf | hf
    all_goals obtain ⟨f⟩ := hf
    ·
      exact hsmall f (lieModel_projSL (n := 3) (p := 3) (e := e)
        ⟨Nat.prime_three, he1, by norm_num, fun h => by simp at h, fun h => by simp at h⟩)
        (by norm_num) (by norm_num)
    ·
      exact hsmall f (lieModel_projSU (n := 3) (p := 3) (e := e)
        ⟨Nat.prime_three, he1, le_refl 3, fun h => by
          have h2 := (Prod.mk.inj h).2
          have := Nat.le_self_pow (by omega : e ≠ 0) 3
          omega⟩) (by norm_num) (by norm_num)
    ·
      have hm := lieModel_lie (t := .G2) (p := 3) (f := 1)
        ⟨Nat.prime_three, le_rfl, rfl, le_refl 3⟩ g2ThreeIndex ⟨rfl, rfl⟩
      exact hnot f hm (by decide) (by decide)
    ·
      exact hsmall f (lieModel_projSL (n := 4) (p := 3) (e := 1)
        ⟨Nat.prime_three, le_rfl, by norm_num, fun h => by simp at h, fun h => by simp at h⟩)
        (by norm_num) (by norm_num)
    ·
      exact hsmall f (lieModel_projSU (n := 4) (p := 3) (e := 1)
        ⟨Nat.prime_three, le_rfl, by norm_num, fun h => by simp at h⟩) (by norm_num)
        (by norm_num)

end CFSG.RankThree.PartTwo.Sec13.F135Last
