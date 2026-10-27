module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData
import CFSG.ClassicalGroups.UnitaryFlag.SplitTorus
import CFSG.GroupTheory.TwoPowOrderFactorization
import CFSG.HardMathSupport.Timmesfeld.LinearRank.GLValuation
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcULevi

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Matrix

private theorem uc22s2114r3f_card_sub_one {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) : Nat.card K - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
  rw [h.card, show 2 * f = f * 2 by ring, pow_mul, mul_comm, ← Nat.sq_sub_sq (2 ^ f) 1, one_pow]

private theorem uc22s2114r3f_modEq {f r : ℕ} (hrq : r ∣ 2 ^ f - 1) : 2 ^ f ≡ 1 [MOD r] :=
  ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr hrq).symm

private theorem uc22s2114r3f_not_dvd_oddProd {f r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : r ∣ 2 ^ f - 1) (n : ℕ) :
    ¬ r ∣ CFSG.LocalAnalysis.RankFourTheoremC.CrossExcU.crossExcUOddProd (2 ^ f) n := by
  intro hd
  unfold CFSG.LocalAnalysis.RankFourTheoremC.CrossExcU.crossExcUOddProd at hd
  obtain ⟨i, -, hdi⟩ := (hr.prime.dvd_finsetProd_iff _).1 hd
  split_ifs at hdi
  · have h0 := CFSG.GroupTheory.factorization_pow_add_one_eq_zero (k := i) hr hr2
      (uc22s2114r3f_modEq hrq)
    have h1 := (hr.dvd_iff_one_le_factorization (by positivity)).1 hdi
    omega
  · exact hr.one_lt.ne' (Nat.dvd_one.1 hdi)

private theorem uc22s2114r3f_factorization_aux {f r N O : ℕ} (hf : 1 ≤ f) (hr : r.Prime)
    (hr5 : 5 ≤ r) (hrq : r ∣ 2 ^ f - 1) (hO : ¬ r ∣ O) :
    ((2 ^ f) ^ N * (∏ j ∈ Finset.range 3, ((2 ^ f) ^ (2 * (j + 1)) - 1)) * O).factorization r =
      3 * (2 ^ f - 1).factorization r := by
  have hr2 : r ≠ 2 := by omega
  have hq1 : 1 < 2 ^ f := Nat.one_lt_pow (by omega) (by norm_num)
  have hO0 : O ≠ 0 := by
    rintro rfl
    exact hO (dvd_zero r)
  have hsub : ∀ j ∈ Finset.range 3, (2 ^ f) ^ (2 * (j + 1)) - 1 ≠ 0 := fun j _ => by
    have := Nat.one_lt_pow (by omega : 2 * (j + 1) ≠ 0) hq1
    omega
  have hprod0 : ∏ j ∈ Finset.range 3, ((2 ^ f) ^ (2 * (j + 1)) - 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hsub
  have hqN : (2 ^ f) ^ N ≠ 0 := by positivity
  have hqfac : (2 ^ f).factorization r = 0 := Nat.factorization_eq_zero_of_not_dvd
    (CFSG.GroupTheory.not_dvd_of_modEq_one_of_prime hr (uc22s2114r3f_modEq hrq))
  have hterm : ∀ j ∈ Finset.range 3,
      ((2 ^ f) ^ (2 * (j + 1)) - 1).factorization r = (2 ^ f - 1).factorization r := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hnd : ¬ r ∣ 2 * (j + 1) := by
      intro hd
      rcases (Nat.Prime.dvd_mul hr).1 hd with h2 | h2
      · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
      · exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)
    rw [CFSG.HardMathSupport.Timmesfeld.LinearRank.factorization_pow_sub_one hr hr2 hq1 hrq
      (by omega), Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]
  have hprodfac : (∏ j ∈ Finset.range 3, ((2 ^ f) ^ (2 * (j + 1)) - 1)).factorization r =
      3 * (2 ^ f - 1).factorization r := by
    calc (∏ j ∈ Finset.range 3, ((2 ^ f) ^ (2 * (j + 1)) - 1)).factorization r
        = ∑ j ∈ Finset.range 3, ((2 ^ f) ^ (2 * (j + 1)) - 1).factorization r := by
          rw [Nat.factorization_prod hsub, Finsupp.finsetSum_apply]
      _ = ∑ _j ∈ Finset.range 3, (2 ^ f - 1).factorization r := Finset.sum_congr rfl hterm
      _ = 3 * (2 ^ f - 1).factorization r := by simp
  rw [Nat.factorization_mul (mul_ne_zero hqN hprod0) hO0, Nat.factorization_mul hqN hprod0,
    Finsupp.add_apply, Finsupp.add_apply, hprodfac, Nat.factorization_eq_zero_of_not_dvd hO,
    Nat.factorization_pow, Finsupp.smul_apply, hqfac, smul_zero]
  ring

private theorem uc22s2114r3f_factorization_card_hypSU {f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 f K) {ε : ℕ} (hε : ε ≤ 1) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrq : r ∣ 2 ^ f - 1) :
    (Nat.card (hypSU h 3 ε)).factorization r = 3 * (2 ^ f - 1).factorization r := by
  rw [CFSG.LocalAnalysis.RankFourTheoremC.CrossExcU.crossExcU_card_hypSU_nat h (r := 3) hε
    (by omega)]
  exact uc22s2114r3f_factorization_aux h.one_le hr hr5 hrq
    (uc22s2114r3f_not_dvd_oddProd hr (by omega) hrq _)

private theorem uc22s2114r3f_factorization_card_hypPSU {f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 f K) {ε : ℕ} (hε : ε ≤ 1) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrq : r ∣ 2 ^ f - 1) :
    (Nat.card (hypPSU h 3 ε)).factorization r = 3 * (2 ^ f - 1).factorization r := by
  have hrZ : ¬ r ∣ Nat.card (hypScalars h 3 ε) := by
    rw [card_hypScalars h (r := 3) (ε := ε) (by omega)]
    intro hd
    have h2 : r ∣ (2 ^ f + 1) - (2 ^ f - 1) :=
      Nat.dvd_sub (hd.trans (Nat.gcd_dvd_right _ _)) hrq
    rw [show (2 ^ f + 1) - (2 ^ f - 1) = 2 by have := Nat.one_le_two_pow (n := f); omega] at h2
    exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
  have hS := uc22s2114r3f_factorization_card_hypSU h hε hr hr5 hrq
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (hypScalars h 3 ε),
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hrZ, add_zero] at hS
  exact hS

private theorem uc22s2114r3f_ker {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (ε : ℕ) : ∀ s, hypProj h 3 ε s = 1 → s ∈ hypScalars h 3 ε := fun s hs => by
  rw [← ker_hypProj h 3 ε, MonoidHom.mem_ker]
  exact hs

private theorem uc22s2114r3f_exists_conj_torus {f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 f K) {ε : ℕ} (hε : ε ≤ 1) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrq : r ∣ 2 ^ f - 1) (x : hypPSU h 3 ε) (hx : orderOf x = r) :
    ∃ c : hypPSU h 3 ε →* hypPSU h 3 ε, Function.Injective c ∧
      x ∈ ((hypTorus h 3 ε).map (hypProj h 3 ε)).map c := by
  have : Fact r.Prime := ⟨hr⟩
  have hq1 : 1 < 2 ^ f := Nat.one_lt_pow (by have := h.one_le; omega) (by norm_num)
  have hqsub : 2 ^ f - 1 ≠ 0 := by omega
  have hdvd : r ^ (2 ^ f - 1).factorization r ∣ 2 ^ f - 1 :=
    (hr.pow_dvd_iff_le_factorization hqsub).2 le_rfl
  have ha1 : 1 ≤ (2 ^ f - 1).factorization r := (hr.dvd_iff_one_le_factorization hqsub).1 hrq
  obtain ⟨ζ, hζ⟩ := CFSG.GroupTheory.WeirSylow.exists_units_orderOf_eq (L := K)
    (d := r ^ (2 ^ f - 1).factorization r)
    (by rw [uc22s2114r3f_card_sub_one h]; exact dvd_mul_of_dvd_left hdvd _)
  have hμ : SplitInv h (Subgroup.zpowers ζ) :=
    splitInv_zpowers h (d := r ^ (2 ^ f - 1).factorization r)
      (Nat.one_lt_pow (by omega) hr.one_lt) (by rw [← hζ]; exact pow_orderOf_eq_one ζ) hdvd
  have hcardμ : Nat.card (Subgroup.zpowers ζ) = r ^ (2 ^ f - 1).factorization r := by
    rw [Nat.card_zpowers, hζ]
  have hoddμ : Odd (Nat.card (Subgroup.zpowers ζ)) := by
    rw [hcardμ]
    exact (hr.odd_of_ne_two (by omega)).pow
  have hcardD : Nat.card ((splitTorusHom h 3 ε _ hμ).range.map (hypProj h 3 ε)) =
      r ^ (Nat.card (hypPSU h 3 ε)).factorization r := by
    rw [splitTorusHom_range_map_card hμ hoddμ _ (uc22s2114r3f_ker h ε), hcardμ,
      uc22s2114r3f_factorization_card_hypPSU h hε hr hr5 hrq, ← pow_mul, mul_comm]
  let P0 : Sylow r (hypPSU h 3 ε) := Sylow.ofCard _ hcardD
  have hP0 : (P0 : Subgroup (hypPSU h 3 ε)) =
      (splitTorusHom h 3 ε _ hμ).range.map (hypProj h 3 ε) := Sylow.coe_ofCard _ _
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card (p := r) (n := 1)
    (by rw [Nat.card_zpowers, hx, pow_one] :
      Nat.card (Subgroup.zpowers x) = r ^ 1)).exists_le_sylow
  have : Finite (Sylow r (hypPSU h 3 ε)) :=
    Finite.of_injective (fun Q : Sylow r (hypPSU h 3 ε) => (Q : Subgroup (hypPSU h 3 ε)))
      fun _ _ hQR => Sylow.ext hQR
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (hypPSU h 3 ε) P0 Q
  have hxQ : x ∈ (Q : Subgroup (hypPSU h 3 ε)) := hQ (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, hP0] at hxQ
  refine ⟨(MulAut.conj g).toMonoidHom, (MulAut.conj g).injective, ?_⟩
  have hxQ' : x ∈ ((splitTorusHom h 3 ε _ hμ).range.map (hypProj h 3 ε)).map
      (MulAut.conj g).toMonoidHom := hxQ
  refine Subgroup.map_mono (Subgroup.map_mono ?_) hxQ'
  rintro _ ⟨s, rfl⟩
  exact splitTorusHom_mem_hypTorus hμ s

private theorem uc22s2114r3f_exists_elemAb {f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 f K) (ε : ℕ) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrq : r ∣ 2 ^ f - 1) :
    ∃ E ≤ (hypTorus h 3 ε).map (hypProj h 3 ε), Nat.card E = r ^ 3 ∧ ∀ z ∈ E, z ^ r = 1 := by
  obtain ⟨ζ, hζ⟩ := CFSG.GroupTheory.WeirSylow.exists_units_orderOf_eq (L := K) (d := r)
    (by rw [uc22s2114r3f_card_sub_one h]; exact dvd_mul_of_dvd_left hrq _)
  have hμ : SplitInv h (Subgroup.zpowers ζ) :=
    splitInv_zpowers h (d := r) hr.one_lt (by rw [← hζ]; exact pow_orderOf_eq_one ζ) hrq
  have hcardμ : Nat.card (Subgroup.zpowers ζ) = r := by rw [Nat.card_zpowers, hζ]
  have hoddμ : Odd (Nat.card (Subgroup.zpowers ζ)) := by
    rw [hcardμ]
    exact hr.odd_of_ne_two (by omega)
  refine ⟨(splitTorusHom h 3 ε _ hμ).range.map (hypProj h 3 ε), Subgroup.map_mono ?_, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact splitTorusHom_mem_hypTorus hμ s
  · rw [splitTorusHom_range_map_card hμ hoddμ _ (uc22s2114r3f_ker h ε), hcardμ]
  · rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    have hs : s ^ r = 1 := by
      funext i
      rw [Pi.pow_apply, ← hcardμ]
      exact pow_card_eq_one'
    rw [← map_pow, ← map_pow, hs, map_one, map_one]

private theorem uc22s2114r3f_exists_pTorus {f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 f K) (ε : ℕ) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ f + 1) :
    ∃ P ≤ (hypTorus h 3 ε).map (hypProj h 3 ε), Nat.card P = p ^ 2 ∧ ∀ z ∈ P, z ^ p = 1 := by
  obtain ⟨ζ, hζ⟩ := CFSG.GroupTheory.WeirSylow.exists_units_orderOf_eq (L := K) (d := p)
    (by rw [uc22s2114r3f_card_sub_one h]; exact dvd_mul_of_dvd_right hpq _)
  have hcardμ : Nat.card (Subgroup.zpowers ζ) = p := by rw [Nat.card_zpowers, hζ]
  obtain ⟨a, ha_apply⟩ : ∃ a : (Fin 2 → Subgroup.zpowers ζ) →* (Fin 3 → Kˣ), ∀ m,
      a m = invPairParams (0 : Fin 3) 1 (m 0 : Kˣ) * invPairParams (1 : Fin 3) 2 (m 1 : Kˣ) :=
    ⟨(invPairParams (0 : Fin 3) 1).comp
        ((Subgroup.zpowers ζ).subtype.comp (Pi.evalMonoidHom _ 0)) *
      (invPairParams (1 : Fin 3) 2).comp
        ((Subgroup.zpowers ζ).subtype.comp (Pi.evalMonoidHom _ 1)), fun _ => rfl⟩
  have ha : ∀ m, torusRatio h (a m) (1 : Fin ε → Kˣ) = 1 := fun m => by
    rw [ha_apply, ← mul_one (1 : Fin ε → Kˣ), torusRatio_mul,
      torusRatio_invPairParams h (i := (0 : Fin 3)) (j := 1) (by decide),
      torusRatio_invPairParams h (i := (1 : Fin 3)) (j := 2) (by decide), mul_one]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin 2 → Subgroup.zpowers ζ) →* hypSU h 3 ε, ∀ m,
      Φ m ∈ hypTorus h 3 ε ∧
        (((Φ m : hypSU h 3 ε) : GL (HypIndex 3 ε) K) : Matrix (HypIndex 3 ε) (HypIndex 3 ε) K) =
          diagonal (torusEntries h (a m) (1 : Fin ε → Kˣ)) :=
    ⟨torusHomOfRatio h 3 ε a ha, fun m => torusFunOfRatio_spec a ha m⟩
  have hpow : ∀ m : Fin 2 → Subgroup.zpowers ζ, m ^ p = 1 := fun m => by
    funext i
    rw [Pi.pow_apply, ← hcardμ]
    exact pow_card_eq_one'
  have hinj : Function.Injective ((hypProj h 3 ε).comp Φ) := by
    rw [injective_iff_map_eq_one]
    intro m hm
    obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 (uc22s2114r3f_ker h ε _ hm)
    have hmat : diagonal (torusEntries h (a m) (1 : Fin ε → Kˣ)) =
        Matrix.scalar (HypIndex 3 ε) (c : K) := by
      rw [← (hΦ m).2, hc, GeneralLinearGroup.coe_scalar]
    have hentry : ∀ i : Fin 3, a m i = c := fun i => by
      have := congrFun (congrFun hmat (Sum.inl i)) (Sum.inl i)
      rw [diagonal_apply_eq, Matrix.scalar_apply, diagonal_apply_eq] at this
      exact Units.ext this
    have h0 := hentry 0
    have h1 := hentry 1
    have h2 := hentry 2
    rw [ha_apply, Pi.mul_apply, invPairParams_apply_left (i := (0 : Fin 3)) (j := 1) (by decide),
      invPairParams_apply_of_ne (i := (1 : Fin 3)) (j := 2) (k := 0) (by decide) (by decide),
      mul_one] at h0
    rw [ha_apply, Pi.mul_apply, invPairParams_apply_right (i := (0 : Fin 3)) (j := 1) (by decide),
      invPairParams_apply_left (i := (1 : Fin 3)) (j := 2) (by decide)] at h1
    rw [ha_apply, Pi.mul_apply,
      invPairParams_apply_of_ne (i := (0 : Fin 3)) (j := 1) (k := 2) (by decide) (by decide),
      invPairParams_apply_right (i := (1 : Fin 3)) (j := 2) (by decide), one_mul] at h2
    have hv : ((m 1 : Subgroup.zpowers ζ) : Kˣ) = c⁻¹ := by rw [← h2, inv_inv]
    rw [h0, hv] at h1
    have hc3 : c ^ 3 = 1 := by
      calc c ^ 3 = c ^ 2 * c := pow_succ c 2
        _ = c ^ 2 * (c⁻¹ * c⁻¹) := by rw [h1]
        _ = 1 := by group
    have hcp : c ^ p = 1 := by
      have hm0 : m 0 ^ p = 1 := by
        rw [← hcardμ]
        exact pow_card_eq_one'
      have := congrArg Subtype.val hm0
      rw [Subgroup.coe_pow, h0] at this
      exact this
    have hc1 : c = 1 := by
      rw [← orderOf_eq_one_iff]
      have hcop : Nat.gcd 3 p = 1 := (Nat.coprime_primes (by norm_num) hp).2 (by omega)
      exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc3)
        (orderOf_dvd_of_pow_eq_one hcp))
    funext i
    fin_cases i
    · exact Subtype.ext (h0.trans hc1)
    · exact Subtype.ext (hv.trans (inv_eq_one.mpr hc1))
  refine ⟨((hypProj h 3 ε).comp Φ).range, ?_, ?_, ?_⟩
  · rintro _ ⟨m, rfl⟩
    exact ⟨Φ m, (hΦ m).1, rfl⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_fun, hcardμ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  · rintro _ ⟨m, rfl⟩
    rw [← map_pow, hpow m, map_one]

theorem uc22s2114r3f_exists_comm_hypPSU {f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 f K) {ε : ℕ} (hε : ε ≤ 1) {r p : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrq : r ∣ 2 ^ f - 1) (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1)
    (x : hypPSU h 3 ε) (hx : orderOf x = r) :
    ∃ A : Subgroup (hypPSU h 3 ε), IsMulCommutative ↥A ∧ x ∈ A ∧
      (∃ y ∈ A, orderOf y = r ∧ y ∉ Subgroup.zpowers x) ∧
      ∃ P : Subgroup (hypPSU h 3 ε), P ≤ A ∧ IsPGroup p ↥P ∧ ¬ IsCyclic ↥P := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨c, hcinj, hxA⟩ := uc22s2114r3f_exists_conj_torus h hε hr hr5 hrq x hx
  obtain ⟨E, hET, hcardE, hexpE⟩ := uc22s2114r3f_exists_elemAb h ε hr hr5 hrq
  obtain ⟨P, hPT, hcardP, hexpP⟩ := uc22s2114r3f_exists_pTorus h ε hp hp5 hpq
  have : IsMulCommutative (hypTorus h 3 ε) := .of_setLike_mul_comm fun _ ha _ hb =>
    CFSG.Quasithin.H13.Sec53F.Unit.hypTorus_comm h ha hb
  refine ⟨((hypTorus h 3 ε).map (hypProj h 3 ε)).map c, inferInstance, hxA, ?_,
    P.map c, Subgroup.map_mono hPT, IsPGroup.of_card (n := 2) ?_, ?_⟩
  · have hex : ∃ y ∈ E.map c, y ∉ Subgroup.zpowers x := by
      by_contra hne
      have hsub : E.map c ≤ Subgroup.zpowers x := fun y hy => by
        by_contra hyx
        exact hne ⟨y, hy, hyx⟩
      have hle := Subgroup.card_le_of_le hsub
      rw [Subgroup.card_map_of_injective hcinj, hcardE, Nat.card_zpowers, hx] at hle
      have hlt : r ^ 1 < r ^ 3 := Nat.pow_lt_pow_right hr.one_lt (by norm_num)
      rw [pow_one] at hlt
      exact absurd hle (not_le.mpr hlt)
    obtain ⟨y, hyE, hyx⟩ := hex
    refine ⟨y, Subgroup.map_mono hET hyE, ?_, hyx⟩
    have hy1 : y ≠ 1 := fun h1 => hyx (by rw [h1]; exact Subgroup.one_mem _)
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hyE
    exact orderOf_eq_prime (by rw [← map_pow, hexpE z hz, map_one]) hy1
  · rw [Subgroup.card_map_of_injective hcinj, hcardP]
  · intro hcyc
    have hexp : Monoid.exponent (P.map c) ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one
      fun z => by
        obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp z.2
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← hwz, ← map_pow, hexpP w hw, map_one]
    rw [IsCyclic.exponent_eq_card, Subgroup.card_map_of_injective hcinj, hcardP] at hexp
    have hlt : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at hlt
    exact absurd (Nat.le_of_dvd hp.pos hexp) (not_le.mpr hlt)

end CFSG.LocalAnalysis.UniquenessCase.UC22
