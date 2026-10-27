module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S208KCommon
import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeCensus
import CFSG.Adapters.LieModelTorusRank
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.GroupTheory.PRankQuotientLift
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubUR
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194OmegaTorus
import CFSG.Quasithin.Vol2.Ch10SecKRRc
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.Timmesfeld.Orders.Bang
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Blueprint

abbrev S208kPerfectDvd (Y : Type) [Group Y] (p : ℕ) : Prop :=
  ∀ (T : Sylow 2 Y) (J : Subgroup Y), normalizer ((T : Subgroup Y) : Set Y) ≤ J →
    J ≠ normalizer ((T : Subgroup Y) : Set Y) →
      ∃ V : Subgroup Y, V ≤ J ∧ ⁅V, V⁆ = V ∧ p ∣ Nat.card V

private theorem s208k_core_of_parabCore {Y : Type} [Group Y] {m : ℕ}
    (h : CFSG.AGLEmbedding.ParabPrime.ParabCore Y (2 ^ m)) :
    ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ (2 ^ m) ^ 2 - 1 → S208kPerfectDvd Y p :=
  fun p hp hp5 hpq T J hTJ hJ => (h T J hTJ hJ p hp hp5).1 hpq

theorem s208k_perfectDvd_of_quotient {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    (h : S208kPerfectDvd (Y ⧸ center Y) p) : S208kPerfectDvd Y p := by
  intro T J hTJ hJ
  have hπ : Function.Surjective (QuotientGroup.mk' (center Y)) := QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (center Y)).ker = center Y := QuotientGroup.ker_mk' _
  have hkN : (QuotientGroup.mk' (center Y)).ker ≤ normalizer ((T : Subgroup Y) : Set Y) := by
    rw [hker]
    exact center_le_normalizer _
  have hle : normalizer (((T.mapSurjective hπ : Sylow 2 (Y ⧸ center Y)) :
      Subgroup (Y ⧸ center Y)) : Set (Y ⧸ center Y)) ≤
        (normalizer ((T : Subgroup Y) : Set Y)).map (QuotientGroup.mk' (center Y)) := by
    rw [Sylow.coe_mapSurjective]
    exact CFSG.AGLEmbedding.ParabPrime.normalizer_map_le T hπ hker.le
  obtain ⟨V, hVJ, hV, hpV⟩ := h _ (J.map (QuotientGroup.mk' (center Y)))
    (hle.trans (map_mono hTJ)) fun he => hJ (le_antisymm ((le_comap_map _ J).trans
      ((comap_mono (he.le.trans hle)).trans (comap_map_eq_self hkN).le)) hTJ)
  obtain ⟨W, hW, hWV, hWm⟩ := CFSG.AGLEmbedding.ParabPrime.exists_perfect_map_eq _ hker.le hV
    (by rw [MonoidHom.range_eq_top_of_surjective _ hπ]; exact le_top)
  refine ⟨W, ?_, hW, hpV.trans (by rw [← hWm]; exact card_map_dvd _ _)⟩
  rw [← comap_map_eq_self (hkN.trans hTJ)]
  exact hWV.trans (comap_mono hVJ)

variable {X : Type} [Group X] [Finite X]

theorem s208k_dvd_card_of_perfectDvd {p : ℕ} (h : S208kPerfectDvd X p) (hp : p.Prime)
    (hp2 : p ≠ 2) {P : Subgroup X} (hP : IsParabolicTwo X P) {n : ℕ} (hQ : S208kQ P n) :
    p ∣ Nat.card (Bar2 (Hinf P)) := by
  obtain ⟨T, hTP⟩ := hP
  obtain ⟨V, hVP, hV, hpV⟩ := h T P hTP (s208k_ne_normalizer hQ T)
  exact s208k_dvd_card_bar2 hVP hV hp hp2 hpV

theorem s208k_exists_prime_five_le {g : ℕ} (hg : 3 ≤ g) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ 2 ^ g - 1 := by
  by_cases h6 : g = 6
  · subst h6
    exact ⟨7, by norm_num, by norm_num, by norm_num⟩
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := g) (by omega) h6
  refine ⟨p, hp.prime, hp.prime.five_le_of_ne_two_of_ne_three (hp.ne_two (by omega))
    fun h => ?_, hp.dvd⟩
  have := hp.eq_two_of_dvd_three (by omega) (dvd_of_eq h)
  omega

theorem s208k_exists_bang_prime {m : ℕ} (hm : 3 ≤ m) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ (2 ^ m) ^ 2 - 1 ∧ ∀ a : ℕ, r ∣ 2 ^ (2 * a) - 1 → m ∣ a := by
  by_cases h3 : m = 3
  · subst h3
    have h7 : CFSG.Timmesfeld.IsPrimitivePrimeDivisor 7 3 :=
      ⟨by norm_num, by norm_num, fun j hj0 hj => by interval_cases j <;> norm_num⟩
    refine ⟨7, by norm_num, by norm_num, by norm_num, fun a ha => ?_⟩
    have := (h7.dvd_sub_one_iff (by norm_num) (2 * a)).mp ha
    omega
  obtain ⟨r, hr⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 2 * m) (by omega)
    (by omega)
  refine ⟨r, hr.prime, hr.prime.five_le_of_ne_two_of_ne_three (hr.ne_two (by omega)) fun h => ?_,
    by rw [← pow_mul, mul_comm]; exact hr.dvd, fun a ha => ?_⟩
  · have := hr.eq_two_of_dvd_three (by omega) (dvd_of_eq h)
    omega
  · exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) ((hr.dvd_sub_one_iff (by omega) _).mp ha)

theorem s208k_two_pow_sub_one_dvd_factor {A : Type} [Group A] {n : ℕ}
    (hA : IsL2 A n ∨ IsSz A n) : 2 ^ n - 1 ∣ Nat.card A := by
  rcases hA with hA | hA
  · rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two
      (LieModel.statedClassicalModel hA (by decide)),
      show (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) by rw [← Nat.sq_sub_sq, one_pow]]
    exact (dvd_mul_left _ _).mul_left _
  · obtain ⟨a, -, rfl, hc⟩ := s208k_card_of_isSz hA
    rw [hc]
    exact dvd_mul_left _ _

theorem s208k_exists_dvd_of_factor {A : Type} [Group A] {m n r : ℕ} (hm : 3 ≤ m)
    (hr : r.Prime) (hr2 : r ≠ 2) (hrm : ∀ a : ℕ, r ∣ 2 ^ (2 * a) - 1 → m ∣ a)
    (hA : IsL2 A n ∨ IsSz A n) (hrA : r ∣ Nat.card A) : ∃ g : ℕ, 3 ≤ g ∧ g ∣ m ∧ g ∣ n := by
  have hr2k : ∀ k, ¬ r ∣ 2 ^ k := fun k h =>
    hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  have hsq : ∀ k : ℕ, (2 ^ k) ^ 2 = 2 ^ (2 * k) := fun k => by rw [← pow_mul, mul_comm]
  rcases hA with hA | hA
  · rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two
      (LieModel.statedClassicalModel hA (by decide))] at hrA
    rcases hr.dvd_mul.mp hrA with h | h
    · exact absurd h (hr2k n)
    · exact ⟨m, hm, dvd_rfl, hrm n (hsq n ▸ h)⟩
  obtain ⟨a, -, rfl, hc⟩ := s208k_card_of_isSz hA
  rw [hc] at hrA
  rcases hr.dvd_mul.mp hrA with h | h
  · rcases hr.dvd_mul.mp h with h | h
    · have h4 : r ∣ 2 ^ (2 * (2 * (2 * a + 1))) - 1 := by
        rw [CFSG.Timmesfeld.IsPrimitivePrimeDivisor.two_pow_two_mul_sub_one]
        exact dvd_mul_of_dvd_right (hsq _ ▸ h) _
      have hmd := hrm _ h4
      by_cases h2m : 2 ∣ m
      · obtain ⟨g, rfl⟩ := h2m
        have hg : g ∣ 2 * a + 1 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hmd
        have hg2 : g ≠ 2 := by
          rintro rfl
          omega
        exact ⟨g, by omega, dvd_mul_left g 2, hg⟩
      · exact ⟨_, hm, dvd_rfl, Nat.Coprime.dvd_of_dvd_mul_left
          ((Nat.prime_two.coprime_iff_not_dvd.mpr h2m).symm) (mul_comm 2 _ ▸ hmd)⟩
    · exact absurd (hsq _ ▸ h) (hr2k _)
  · exact ⟨m, hm, dvd_rfl,
      hrm _ (h.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_left _ 2)))⟩

omit [Finite X] in
theorem s208k_exists_factor {P : Subgroup X} {n r : ℕ} (hQ : S208kQ P n) (hr : r.Prime)
    (hrQ : r ∣ Nat.card (Bar2 (Hinf P))) :
    ∃ (A : Type) (_ : Group A), (IsL2 A n ∨ IsSz A n) ∧ r ∣ Nat.card A := by
  rcases hQ with h | h | ⟨A, C, _, _, ⟨e⟩, hA, hC⟩
  · exact ⟨_, _, Or.inl h, hrQ⟩
  · exact ⟨_, _, Or.inr h, hrQ⟩
  · rw [Nat.card_congr e.toEquiv, Nat.card_prod] at hrQ
    rcases hr.dvd_mul.mp hrQ with h | h
    · exact ⟨A, _, hA.symm, h⟩
    · exact ⟨C, _, hC.symm, h⟩

theorem s208k_exists_prime_of_core {m : ℕ} (hm : 3 ≤ m)
    (hcore : ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ (2 ^ m) ^ 2 - 1 → S208kPerfectDvd X p)
    {P : Subgroup X} (hP : IsParabolicTwo X P) {n : ℕ} (hQ : S208kQ P n) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ 2 ^ m - 1 ∧ p ∣ 2 ^ n - 1 := by
  obtain ⟨r, hr, hr5, hrq, hrm⟩ := s208k_exists_bang_prime hm
  obtain ⟨A, _, hA, hrA⟩ := s208k_exists_factor hQ hr
    (s208k_dvd_card_of_perfectDvd (hcore r hr hr5 hrq) hr (by omega) hP hQ)
  obtain ⟨g, hg, hgm, hgn⟩ := s208k_exists_dvd_of_factor hm hr (by omega) hrm hA hrA
  obtain ⟨p, hp, hp5, hpg⟩ := s208k_exists_prime_five_le hg
  exact ⟨p, hp, hp5, hpg.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hgm),
    hpg.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hgn)⟩

theorem s208k_goal_of_core_two {m : ℕ} (hm : 3 ≤ m)
    (hcore : ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ (2 ^ m) ^ 2 - 1 → S208kPerfectDvd X p)
    (hrank : ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ 2 ^ m - 1 → 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X))
    {P : Subgroup X} (hP : IsParabolicTwo X P) {n : ℕ}
    (hQ : IsL2 (Bar2 (Hinf P)) n ∨ IsSz (Bar2 (Hinf P)) n) : S208kGoal P n := by
  obtain ⟨p, hp, hp5, hpm, hpn⟩ := s208k_exists_prime_of_core hm hcore hP (hQ.imp_right Or.inl)
  exact s208k_goal_of_two_le hQ hp (by omega) hpn (hrank p hp hp5 hpm)

theorem s208k_goal_of_core_three {m : ℕ} (hm : 3 ≤ m)
    (hcore : ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ (2 ^ m) ^ 2 - 1 → S208kPerfectDvd X p)
    (hrank : ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ 2 ^ m - 1 → 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X))
    {P : Subgroup X} (hP : IsParabolicTwo X P) {n : ℕ} (hQ : S208kQ P n) : S208kGoal P n := by
  obtain ⟨p, hp, hp5, hpm, hpn⟩ := s208k_exists_prime_of_core hm hcore hP hQ
  exact s208k_goal_of_three_le hQ hp (by omega) hpn (hrank p hp hp5 hpm)

private theorem s208k_dvd_sq_sub_one {p q : ℕ} (h : p ∣ q - 1) : p ∣ q ^ 2 - 1 :=
  h.trans (by simpa using Nat.sub_dvd_pow_sub_pow q 1 2)

private theorem s208k_not_dvd_two_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    ¬ p ∣ 2 ^ k :=
  fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))

section Tori

variable {Y : Type} [Group Y] [Finite Y] {m p : ℕ}

theorem s208k_two_le_pRank_of_isL3 (hY : IsL3 Y m) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpm : p ∣ 2 ^ m - 1) : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) :=
  LieModel.le_pRank_psl_of_dvd hY hp hpm (by norm_num)
    (Or.inr fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)

theorem s208k_two_le_pRank_of_isSL3 (hY : IsSL3 Y m) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpm : p ∣ 2 ^ m - 1) : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) :=
  CFSG.GroupTheory.two_le_pRank_of_quotient (center Y) hp (by omega)
    (s208k_two_le_pRank_of_isL3 hY.2 hp hp5 hpm)

theorem s208k_le_pRank_of_psp {k : ℕ} (hY : LieModel Y .PSp k 2 m) (hp : p.Prime)
    (hpm : p ∣ 2 ^ m - 1) : k ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := LieModel.statedClassicalModel hY (by decide)
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  exact CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.le_pRank_statedProj_sp hp
    (hcard ▸ s208k_dvd_sq_sub_one hpm)

theorem s208k_two_le_pRank_of_isU4 (hY : IsU4 Y m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : p ∣ (2 ^ m) ^ 2 - 1) : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) :=
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.two_le_pRank_psu_of_dvd le_rfl
    (LieModel.statedClassicalModel hY (by decide)) hp hp2 hpm

theorem s208k_three_le_pRank_of_psl4 (hY : LieModel Y .PSL 4 2 m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : p ∣ 2 ^ m - 1) : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) :=
  LieModel.le_pRank_psl_of_dvd hY hp hpm (by norm_num)
    (Or.inr fun h => s208k_not_dvd_two_pow hp hp2 2 (by norm_num; exact h))

theorem s208k_three_le_pRank_of_isOmega8m (hY : IsOmega8m Y m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : p ∣ 2 ^ m - 1) : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) := by
  obtain ⟨-, F, _, _, hcard, b, c, -, ⟨e⟩⟩ := LieModel.statedClassicalModel hY (by decide)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  exact CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.le_pRank_omegaMinus_torus
    (n := 4) hp hp2 (by rw [Nat.card_units, hcard]; exact hpm) b c

end Tori

theorem s208k_goal_of_classical_rankTwo {m : ℕ} (hX : IsL3 X m ∨ IsSL3 X m ∨ IsSp4 X m ∨ IsU4 X m)
    (hm : 2 < m) {P : Subgroup X} (hP : IsParabolicTwo X P) {n : ℕ}
    (hQ : IsL2 (Bar2 (Hinf P)) n ∨ IsSz (Bar2 (Hinf P)) n) : S208kGoal P n := by
  rcases hX with h | h | h | h
  · exact s208k_goal_of_core_two hm (s208k_core_of_parabCore
      (CFSG.AGLEmbedding.ParabPrime.parabCore_of_model_psl
        (LieModel.statedClassicalModel h (by decide)) hm.le))
      (fun p hp hp5 hpm => s208k_two_le_pRank_of_isL3 h hp hp5 hpm) hP hQ
  · exact s208k_goal_of_core_two hm (fun p hp hp5 hpq => s208k_perfectDvd_of_quotient
      (s208k_core_of_parabCore (CFSG.AGLEmbedding.ParabPrime.parabCore_of_model_psl
        (LieModel.statedClassicalModel h.2 (by decide)) hm.le) p hp hp5 hpq))
      (fun p hp hp5 hpm => s208k_two_le_pRank_of_isSL3 h hp hp5 hpm) hP hQ
  · exact s208k_goal_of_core_two hm (s208k_core_of_parabCore
      (CFSG.AGLEmbedding.ParabPrime.parabCore_of_model_psp
        (LieModel.statedClassicalModel h (by decide)) hm.le))
      (fun p hp _ hpm => s208k_le_pRank_of_psp h hp hpm) hP hQ
  · exact s208k_goal_of_core_two hm (s208k_core_of_parabCore
      (CFSG.AGLEmbedding.ParabPrime.parabCore_of_model_psu
        (LieModel.statedClassicalModel h (by decide)) hm.le))
      (fun p hp hp5 hpm => s208k_two_le_pRank_of_isU4 h hp (by omega) (s208k_dvd_sq_sub_one hpm))
      hP hQ

theorem s208k_goal_of_rankThree {m : ℕ}
    (hX : LieModel X .PSL 4 2 m ∨ LieModel X .PSp 3 2 m ∨ IsOmega8m X m) (hm : 2 < m)
    {P : Subgroup X} (hP : IsParabolicTwo X P) {n : ℕ} (hQ : S208kQ P n) : S208kGoal P n := by
  rcases hX with h | h | h
  · exact s208k_goal_of_core_three hm (s208k_core_of_parabCore
      (CFSG.AGLEmbedding.ParabPrime.parabCore_of_model_psl
        (LieModel.statedClassicalModel h (by decide)) hm.le))
      (fun p hp hp5 hpm => s208k_three_le_pRank_of_psl4 h hp (by omega) hpm) hP hQ
  · exact s208k_goal_of_core_three hm (s208k_core_of_parabCore
      (CFSG.AGLEmbedding.ParabPrime.parabCore_of_model_psp
        (LieModel.statedClassicalModel h (by decide)) hm.le))
      (fun p hp _ hpm => s208k_le_pRank_of_psp h hp hpm) hP hQ
  · exact s208k_goal_of_core_three hm (s208k_core_of_parabCore
      (CFSG.AGLEmbedding.ParabPrime.parabCore_of_model_pomegaMinus
        (LieModel.statedClassicalModel h (by decide)) hm.le))
      (fun p hp hp5 hpm => s208k_three_le_pRank_of_isOmega8m h hp (by omega) hpm) hP hQ

omit [Finite X] in
theorem s208k_two_pow_sub_one_dvd_card {P : Subgroup X} {n : ℕ} (hQ : S208kQ P n) :
    2 ^ n - 1 ∣ Nat.card X := by
  refine Dvd.dvd.trans ?_ ((card_quotient_dvd_card (CFSG.pCore 2 ↥(Hinf P))).trans
    (card_subgroup_dvd_card (Hinf P)))
  rcases hQ with h | h | ⟨A, C, _, _, ⟨e⟩, hA, hC⟩
  · exact s208k_two_pow_sub_one_dvd_factor (Or.inl h)
  · exact s208k_two_pow_sub_one_dvd_factor (Or.inr h)
  · rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    exact (s208k_two_pow_sub_one_dvd_factor hA.symm).mul_right _

private theorem s208k_lt_of_dvd {n N k : ℕ} (h : 2 ^ n - 1 ∣ N) (hN : 0 < N)
    (hk : N < 2 ^ k - 1) : n < k := by
  have h1 := Nat.le_of_dvd hN h
  by_contra hnk
  have : 2 ^ k ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

private theorem s208k_check_u44 : ∀ n < 30, 2 < n → 2 ^ n - 1 ∣ 1018368000 → 3 ∣ 2 ^ n - 1 := by
  decide

private theorem s208k_check_u54 :
    ∀ n < 46, 2 < n → 2 ^ n - 1 ∣ 53443952640000 → 5 ∣ 2 ^ n - 1 := by
  decide

private theorem s208k_check_o84 :
    ∀ n < 57, 2 < n → (2 ^ n - 1) ^ 2 ∣ 67536471195648000 → 3 ∣ 2 ^ n - 1 := by
  decide

theorem s208k_goal_of_isU4_two (hX : IsU4 X 2) {P : Subgroup X} {n : ℕ} (hn : 2 < n)
    (hQ : IsL2 (Bar2 (Hinf P)) n ∨ IsSz (Bar2 (Hinf P)) n) : S208kGoal P n := by
  have hd := s208k_two_pow_sub_one_dvd_card (hQ.imp_right Or.inl)
  rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_four
    (LieModel.statedClassicalModel hX (by decide))] at hd
  exact s208k_goal_of_two_le hQ Nat.prime_three (by norm_num)
    (s208k_check_u44 n (s208k_lt_of_dvd hd (by norm_num) (by norm_num)) hn hd)
    (s208k_two_le_pRank_of_isU4 hX Nat.prime_three (by norm_num) (by norm_num))

theorem s208k_goal_of_isU5_two (hX : IsU5 X 2) {P : Subgroup X} {n : ℕ} (hn : 2 < n)
    (hQ : S208kQ P n) : S208kGoal P n := by
  have hd := s208k_two_pow_sub_one_dvd_card hQ
  rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_four
    (LieModel.statedClassicalModel hX (by decide))] at hd
  exact s208k_goal_of_three_le hQ (by norm_num) (by norm_num)
    (s208k_check_u54 n (s208k_lt_of_dvd hd (by norm_num) (by norm_num)) hn hd)
    (LieModel.le_pRank_psu_of_dvd hX (by norm_num) (by norm_num) (by norm_num)
      (Or.inl (by norm_num)))

theorem s208k_goal_of_isOmega8m_two (hX : IsOmega8m X 2) {P : Subgroup X}
    (hP : IsParabolicTwo X P) {n : ℕ} (hn : 2 < n) (hQ : S208kQ P n) : S208kGoal P n := by
  have hS := LieModel.statedClassicalModel hX (by decide)
  have h3 : 3 ∣ 2 ^ n - 1 := by
    rcases hQ with h | h | ⟨A, C, _, _, ⟨e⟩, hA, hC⟩
    · have h5 := s208k_dvd_card_of_perfectDvd (s208k_core_of_parabCore
        (CFSG.AGLEmbedding.ParabPrime.parabCore_of_model_pomegaMinus hS le_rfl) 5
          (by norm_num) le_rfl (by norm_num)) (by norm_num) (by norm_num) hP (Or.inl h)
      rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two
        (LieModel.statedClassicalModel h (by decide))] at h5
      have h5' := (Nat.prime_five.dvd_mul.mp h5).resolve_left
        (s208k_not_dvd_two_pow Nat.prime_five (by norm_num) n)
      have hp5 : CFSG.Timmesfeld.IsPrimitivePrimeDivisor 5 4 :=
        ⟨by norm_num, by norm_num, fun j hj0 hj => by interval_cases j <;> norm_num⟩
      have h4 := (hp5.dvd_sub_one_iff (by norm_num) (2 * n)).mp
        (by rwa [← pow_mul, mul_comm] at h5')
      exact (Nat.pow_sub_one_dvd_pow_sub_one 2 (show 2 ∣ n by omega) : 2 ^ 2 - 1 ∣ 2 ^ n - 1)
    · exact absurd (s208k_dvd_card_of_perfectDvd (fun T J h1 h2 =>
        CFSG.AGLEmbedding.ParabHub.exists_perfect_three_dvd_of_model_pomegaMinus hS le_rfl T J
          h1 h2) Nat.prime_three (by norm_num) hP (Or.inr (Or.inl h)))
        (s208k_not_three_dvd_card_of_isSz h)
    · have hd : (2 ^ n - 1) ^ 2 ∣ Nat.card X := by
        refine Dvd.dvd.trans ?_ ((card_quotient_dvd_card (CFSG.pCore 2 ↥(Hinf P))).trans
          (card_subgroup_dvd_card (Hinf P)))
        rw [Nat.card_congr e.toEquiv, Nat.card_prod, sq]
        exact Nat.mul_dvd_mul (s208k_two_pow_sub_one_dvd_factor hA.symm)
          (s208k_two_pow_sub_one_dvd_factor hC.symm)
      rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hS,
        show CFSG.EvenSmallLie.CatalogOrders.lieOrd .POmegaMinus 4 (2 ^ 2) =
          67536471195648000 by decide] at hd
      exact s208k_check_o84 n (s208k_lt_of_dvd ((dvd_pow_self _ two_ne_zero).trans hd)
        (by norm_num) (by norm_num)) hn hd
  exact s208k_goal_of_three_le hQ Nat.prime_three (by norm_num) h3
    (s208k_three_le_pRank_of_isOmega8m hX Nat.prime_three (by norm_num) (by norm_num))

section Certified


theorem s208k_goal_of_isG2 {m : ℕ} (hX : IsG2 X m) (hm : 2 < m) {P : Subgroup X}
    (hP : IsParabolicTwo X P) {n : ℕ} (hQ : IsL2 (Bar2 (Hinf P)) n ∨ IsSz (Bar2 (Hinf P)) n) :
    S208kGoal P n := by
  have hU := (LieModel.chevalleyExceptionalModel hX (by decide)).2
  refine s208k_goal_of_core_two hm (s208k_core_of_parabCore ?_) (fun p hp _ hpm => ?_) hP hQ
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hU
    have := Fintype.ofFinite K
    have : CharP K 2 :=
      charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card]; exact hK)
    rw [← hK]
    exact CFSG.AGLEmbedding.ParabPrime.parabCore_g2 e
      (hK ▸ CFSG.AGLEmbedding.ParabHub.four_le_two_pow_of_le hm.le)
  · rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.Quasithin.Vol2.Ch10.SecB.KRR.two_le_pRank_G2_of_dvd hp hpm hU

end Certified

end CFSG.LocalAnalysis.UniquenessCase.UC22
