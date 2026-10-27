module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapUniqueOuter
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapUniqueType
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeDet

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.Timmesfeld (IsPrimitivePrimeDivisor exists_isPrimitivePrimeDivisor)
open CFSG.ComponentClassification.UnbalancedCatalog (UnitaryFieldTransfer.fixedField_finite)

section Arith

theorem prod_Icc_two_two_mul_add_one (g : ℕ → ℕ) (r : ℕ) :
    ∏ i ∈ Finset.Icc 2 (2 * r + 1), g i =
      (∏ j ∈ Finset.Icc 1 r, g (2 * j)) * ∏ j ∈ Finset.Icc 1 r, g (2 * j + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have e1 : 2 * (r + 1) + 1 = (2 * r + 1 + 1) + 1 := by ring
    have e2 : 2 * (r + 1) = 2 * r + 1 + 1 := by ring
    rw [e1, Finset.prod_Icc_succ_top (a := 2) (b := 2 * r + 1 + 1) (by omega),
      Finset.prod_Icc_succ_top (a := 2) (b := 2 * r + 1) (by omega), ih,
      Finset.prod_Icc_succ_top (a := 1) (b := r) (by omega) (fun j => g (2 * j)),
      Finset.prod_Icc_succ_top (a := 1) (b := r) (by omega) (fun j => g (2 * j + 1)), e2]
    ring

theorem ordTwistedA_numerator_eq (q r : ℕ) (hq : 1 ≤ q) :
    q ^ (2 * r * (2 * r + 1) / 2) *
        ∏ i ∈ Finset.Icc 2 (2 * r + 1), ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat =
      q ^ (2 * r * (2 * r + 1) / 2) * ((∏ j ∈ Finset.Icc 1 r, (q ^ (2 * j) - 1)) *
        ∏ j ∈ Finset.Icc 1 r, (q ^ (2 * j + 1) + 1)) := by
  rw [prod_Icc_two_two_mul_add_one]
  congr 2
  · refine Finset.prod_congr rfl fun j _ => ?_
    have h1 : 1 ≤ q ^ (2 * j) := Nat.one_le_pow _ _ hq
    rw [Even.neg_one_pow ⟨j, by ring⟩, show ((q : ℤ) ^ (2 * j) - 1) = ((q ^ (2 * j) - 1 : ℕ) : ℤ)
      by push_cast [h1]; ring, Int.toNat_natCast]
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [Odd.neg_one_pow ⟨j, rfl⟩, show ((q : ℤ) ^ (2 * j + 1) - -1) =
      ((q ^ (2 * j + 1) + 1 : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]

theorem not_sq_card_statedSp_dvd_ordTwistedA {f r : ℕ} (hf : 1 ≤ f) (hr : 2 ≤ r) :
    ¬ ((2 ^ f) ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, ((2 ^ f) ^ (2 * j) - 1)) ^ 2 ∣
      CFSG.Open.ordTwistedA (2 * r) (2 ^ f) := by
  set q := 2 ^ f with hq
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  set D := ∏ j ∈ Finset.Icc 1 r, (q ^ (2 * j) - 1) with hD
  set E := ∏ j ∈ Finset.Icc 1 r, (q ^ (2 * j + 1) + 1) with hE
  set N := 2 * r * (2 * r + 1) / 2 with hN
  intro hdvd
  unfold CFSG.Open.ordTwistedA at hdvd
  rw [ordTwistedA_numerator_eq q r hq1] at hdvd
  have hg : Nat.gcd (2 * r + 1) (q + 1) ∣ q ^ N * (D * E) := by
    have h1 : q + 1 ∣ q ^ (2 * 1 + 1) + 1 := by
      have := Odd.nat_add_dvd_pow_add_pow q 1 (n := 2 * 1 + 1) ⟨1, rfl⟩
      rwa [one_pow] at this
    have h2 : q ^ (2 * 1 + 1) + 1 ∣ E :=
      Finset.dvd_prod_of_mem (fun j => q ^ (2 * j + 1) + 1) (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
    exact (Nat.gcd_dvd_right _ _).trans (h1.trans (h2.trans ((dvd_mul_left E D).trans
      (dvd_mul_left _ _))))
  have hX := hdvd.trans (Nat.div_dvd_of_dvd hg)
  have hDpos : 0 < D := Finset.prod_pos fun j hj => by
    have : 2 ≤ q ^ (2 * j) := by
      calc 2 ≤ 2 ^ (f * (2 * j)) := by
            have : 1 ≤ f * (2 * j) := by
              have := (Finset.mem_Icc.1 hj).1
              nlinarith
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (f * (2 * j)) := Nat.pow_le_pow_right (by norm_num) this
        _ = q ^ (2 * j) := by rw [hq, ← pow_mul]
    omega
  have hDD : D * D ∣ D * (q ^ N * E) := by
    have h1 : D * D ∣ ((q ^ (r ^ 2)) * D) ^ 2 := ⟨(q ^ (r ^ 2)) ^ 2, by ring⟩
    have h2 := h1.trans hX
    rwa [show q ^ N * (D * E) = D * (q ^ N * E) by ring] at h2
  have hDE : D ∣ q ^ N * E := Nat.dvd_of_mul_dvd_mul_left hDpos hDD
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 4 * f) (by omega) (by omega)
  have hk0 : 0 < 4 * f := by omega
  have hpD : p ∣ D := by
    have h1 : p ∣ q ^ (2 * 2) - 1 := by
      rw [hq, ← pow_mul, show f * (2 * 2) = 4 * f by ring]
      exact hp.dvd
    exact h1.trans (Finset.dvd_prod_of_mem (fun j => q ^ (2 * j) - 1)
      (Finset.mem_Icc.2 ⟨by omega, hr⟩))
  have hpr := hp.prime
  rcases (Nat.Prime.dvd_mul hpr).1 (hpD.trans hDE) with h1 | h1
  · have h2 : p ∣ 2 := hpr.dvd_of_dvd_pow (show p ∣ 2 ^ (f * N) by rwa [pow_mul, ← hq])
    exact hp.ne_two hk0 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).1 h2)
  · obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff hpr.prime _).1 h1
    have h3 : p ∣ 2 ^ (f * (2 * j + 1)) + 1 := by rwa [pow_mul, ← hq]
    obtain ⟨⟨m, hm⟩, -⟩ := (hp.dvd_add_one_iff hk0 _).1 h3
    have h4 : f * (2 * (2 * j + 1)) = f * (4 * m) := by
      calc f * (2 * (2 * j + 1)) = 2 * (f * (2 * j + 1)) := by ring
        _ = 4 * f * m := hm
        _ = f * (4 * m) := by ring
    have h5 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) h4
    omega

theorem pair_arith_even {f m a b v : ℕ} (hf : 1 ≤ f) (hm : 3 ≤ m) (hv : v < f)
    (ha : f * m ^ 2 ≤ a) (hb : f * m ^ 2 ≤ b) (hab : a + b + f * m ≤ 2 + 2 * (f * m ^ 2) + v) :
    False := by
  have h2 : 3 * f ≤ f * m :=
    calc 3 * f = f * 3 := by ring
      _ ≤ f * m := Nat.mul_le_mul_left f hm
  omega

theorem pair_arith_odd {f m a b v : ℕ} (hf : 1 ≤ f) (hm : 3 ≤ m) (hv : v < f)
    (ha : f * m ^ 2 + 2 * (f * m) ≤ a) (hb : f * m ^ 2 ≤ b)
    (hab : a + b ≤ 2 + 2 * (f * m ^ 2) + f * m + v) : False := by
  have h2 : 3 * f ≤ f * m :=
    calc 3 * f = f * 3 := by ring
      _ ≤ f * m := Nat.mul_le_mul_left f hm
  omega

end Arith

@[expose] def UnitaryInnerInvolutionTwoPart {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (n : ℕ) : Prop :=
  ∀ y : unitaryPSU h n, orderOf y = 2 →
    f * (n / 2 * (n / 2 + 2 * (n % 2))) ≤
      (Nat.card (centralizer ({y} : Set (unitaryPSU h n)))).factorization 2

theorem unitaryInnerInvolutionTwoPart_of_twoSubgroup {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {n : ℕ}
    (hQ : ∀ y : unitaryPSU h n, orderOf y = 2 → ∃ Q : Subgroup (unitaryPSU h n), IsPGroup 2 Q ∧
      Q ≤ centralizer ({y} : Set (unitaryPSU h n)) ∧
      2 ^ (f * (n / 2 * (n / 2 + 2 * (n % 2)))) ≤ Nat.card Q) :
    UnitaryInnerInvolutionTwoPart h n := by
  intro y hy
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ2, hQC, hQcard⟩ := hQ y hy
  obtain ⟨a, ha⟩ := hQ2.exists_card_eq
  have hdvd : 2 ^ a ∣ Nat.card (centralizer ({y} : Set (unitaryPSU h n))) :=
    ha ▸ Subgroup.card_dvd_of_le hQC
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
  rw [ha] at hQcard
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hQcard
  omega

section Pair

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

omit [Field K] in
theorem fixedSubgroup_conj_eq_centralizer {X : Type*} [Group X] (y : X) :
    fixedSubgroup (MulAut.conj y) = centralizer ({y} : Set X) := by
  ext x
  rw [mem_centralizer_singleton_iff]
  change MulAut.conj y x = x ↔ _
  rw [MulAut.conj_apply]
  constructor
  · intro hx
    calc x * y = (y * x * y⁻¹) * y := by rw [hx]
      _ = y * x := by group
  · intro hx
    rw [← hx]
    group

theorem inner_or_outer_bound (hI : UnitaryInnerInvolutionTwoPart h n) (hn : 6 ≤ n)
    (φ : MulAut (unitaryPSU h n)) (hφ : φ * φ = 1) (hφ1 : φ ≠ 1) :
    f * (n / 2 * (n / 2 + 2 * (n % 2))) ≤ (Nat.card (fixedSubgroup φ)).factorization 2 ∨
      (φ ∉ (MulAut.conj : unitaryPSU h n →* MulAut (unitaryPSU h n)).range ∧
        f * (n / 2) ^ 2 ≤ (Nat.card (fixedSubgroup φ)).factorization 2) := by
  have := h.finite
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h3 => by
    have := congrArg Prod.fst h3
    simp only at this
    omega
  have hφo : orderOf φ = 2 := orderOf_eq_prime (by rw [sq]; exact hφ) hφ1
  by_cases hin : φ ∈ (MulAut.conj : unitaryPSU h n →* MulAut (unitaryPSU h n)).range
  · left
    obtain ⟨y, rfl⟩ := hin
    have hZ := center_unitaryPSU_eq_bot h (by omega) hnq
    have hyy : y * y = 1 := by
      have h1 : MulAut.conj (y * y) = 1 := by rw [map_mul]; exact hφ
      have h2 : y * y ∈ center (unitaryPSU h n) := by
        rw [mem_center_iff]
        intro g
        have := congrArg (fun α : MulAut (unitaryPSU h n) => α g) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc g * (y * y) = (y * y) * g * (y * y)⁻¹ * (y * y) := by rw [this]
          _ = (y * y) * g := by group
      rw [hZ, mem_bot] at h2
      exact h2
    have hy1 : y ≠ 1 := fun hy => hφ1 (by rw [hy, map_one])
    have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hyy) hy1
    rw [fixedSubgroup_conj_eq_centralizer]
    exact hI y hyo
  · right
    refine ⟨hin, ?_⟩
    obtain ⟨hev, hodd⟩ := unitary_outer_fixed h (by omega) hnq φ hφo hin
    have h0 : Nat.card (fixedSubgroup φ) ≠ 0 := Nat.card_pos.ne'
    rcases Nat.even_or_odd n with ⟨r, hr⟩ | ⟨r, hr⟩
    · have hd := hev r (by omega)
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two h0).1 hd
      rwa [show n / 2 = r by omega]
    · obtain ⟨e₂⟩ := hodd r hr
      have := UnitaryFieldTransfer.fixedField_finite h
      have hd : 2 ^ (f * r ^ 2) ∣ Nat.card (fixedSubgroup φ) := by
        rw [Nat.card_congr e₂.toEquiv]
        have := LinearPilot.pow_dvd_card_statedSp (F := h.fixedField) r
        rwa [h.card_fixedField, ← pow_mul] at this
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two h0).1 hd
      rwa [show n / 2 = r by omega]

theorem unitarySwapPairExclusion_of_innerTwoPart (hI : UnitaryInnerInvolutionTwoPart h n)
    (hn : 6 ≤ n) : UnitarySwapPairExclusion h n := by
  intro θ θ' hθ hθ1 hθ' hθ'1 h2 hpc
  have := h.finite
  have hf := h.one_le
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h3 => by
    have := congrArg Prod.fst h3
    simp only at this
    omega
  have hV := factorization_card_mulAut_unitaryPSU_le h (by omega) hnq
  have hV2 : (2 * Nat.card (MulAut (unitaryPSU h n))).factorization 2 =
      1 + (Nat.card (MulAut (unitaryPSU h n))).factorization 2 := by
    rw [Nat.factorization_mul two_ne_zero Nat.card_pos.ne', Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two]
  have hvf : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  have hab : (Nat.card (fixedSubgroup θ)).factorization 2 +
      (Nat.card (fixedSubgroup θ')).factorization 2 ≤
        2 + f * (n * (n - 1) / 2) + f.factorization 2 := by omega
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  ·
    have hn2 : n / 2 = m := by omega
    have hn2' : n % 2 = 0 := by omega
    have hM : f * (n * (n - 1) / 2) + f * m = 2 * (f * m ^ 2) := by
      have : n * (n - 1) / 2 = m * (2 * m - 1) := by
        rw [show n = 2 * m by omega]
        rw [show 2 * m * (2 * m - 1) = 2 * (m * (2 * m - 1)) by ring]
        exact Nat.mul_div_cancel_left _ two_pos
      rw [this]
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
      ring
    have hbd : ∀ φ : MulAut (unitaryPSU h n), φ * φ = 1 → φ ≠ 1 →
        f * m ^ 2 ≤ (Nat.card (fixedSubgroup φ)).factorization 2 := by
      intro φ hφ hφ1
      rcases inner_or_outer_bound h hI hn φ hφ hφ1 with hA | ⟨-, hA⟩
      · rw [hn2, hn2', mul_zero, add_zero] at hA
        rwa [sq]
      · rwa [hn2] at hA
    exact pair_arith_even hf (by omega) hvf (hbd θ hθ hθ1) (hbd θ' hθ' hθ'1) (by omega)
  · have hn2 : n / 2 = m := by omega
    have hn2' : n % 2 = 1 := by omega
    have hM : f * (n * (n - 1) / 2) = 2 * (f * m ^ 2) + f * m := by
      have : n * (n - 1) / 2 = m * (2 * m + 1) := by
        rw [show n - 1 = 2 * m by omega, hm,
          show (2 * m + 1) * (2 * m) = 2 * (m * (2 * m + 1)) by ring]
        exact Nat.mul_div_cancel_left _ two_pos
      rw [this]
      ring
    have hin : ∀ φ : MulAut (unitaryPSU h n),
        f * (n / 2 * (n / 2 + 2 * (n % 2))) ≤ (Nat.card (fixedSubgroup φ)).factorization 2 →
        f * m ^ 2 + 2 * (f * m) ≤ (Nat.card (fixedSubgroup φ)).factorization 2 := by
      intro φ hφ
      rw [hn2, hn2'] at hφ
      calc f * m ^ 2 + 2 * (f * m) = f * (m * (m + 2 * 1)) := by ring
        _ ≤ _ := hφ
    have hout : ∀ φ : MulAut (unitaryPSU h n),
        f * (n / 2) ^ 2 ≤ (Nat.card (fixedSubgroup φ)).factorization 2 →
        f * m ^ 2 ≤ (Nat.card (fixedSubgroup φ)).factorization 2 := by
      intro φ hφ
      rwa [hn2] at hφ
    have hinout : ∀ φ : MulAut (unitaryPSU h n),
        f * m ^ 2 + 2 * (f * m) ≤ (Nat.card (fixedSubgroup φ)).factorization 2 →
        f * m ^ 2 ≤ (Nat.card (fixedSubgroup φ)).factorization 2 := fun φ hφ => by omega
    rcases inner_or_outer_bound h hI hn θ hθ hθ1 with hA | ⟨hAo, hA⟩ <;>
      rcases inner_or_outer_bound h hI hn θ' hθ' hθ'1 with hB | ⟨hBo, hB⟩
    · exact pair_arith_odd hf (by omega) hvf (hin θ hA) (hinout θ' (hin θ' hB)) (by omega)
    · exact pair_arith_odd hf (by omega) hvf (hin θ hA) (hout θ' hB) (by omega)
    · exact pair_arith_odd hf (by omega) hvf (hin θ' hB) (hout θ hA) (by omega)
    ·
      have hm3 : 3 ≤ m := by omega
      have hθo : orderOf θ = 2 := orderOf_eq_prime (by rw [sq]; exact hθ) hθ1
      have hθo' : orderOf θ' = 2 := orderOf_eq_prime (by rw [sq]; exact hθ') hθ'1
      obtain ⟨-, hoddA⟩ := unitary_outer_fixed h (by omega) hnq θ hθo hAo
      obtain ⟨-, hoddB⟩ := unitary_outer_fixed h (by omega) hnq θ' hθo' hBo
      obtain ⟨eA⟩ := hoddA m hm
      obtain ⟨eB⟩ := hoddB m hm
      have := UnitaryFieldTransfer.fixedField_finite h
      have hSp : Group.IsPerfect (StatedSp m h.fixedField) :=
        CFSG.SeitzReduction.LinearOuter.isPerfect_statedSp_of_card h.one_le h.card_fixedField
          (Or.inr hm3)
      have hcardPC : ∀ φ : MulAut (unitaryPSU h n), (fixedSubgroup φ ≃* StatedSp m h.fixedField) →
          Nat.card (perfectCore (fixedSubgroup φ)) = Nat.card (StatedSp m h.fixedField) := by
        intro φ e
        have : Group.IsPerfect (fixedSubgroup φ) :=
          Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
        rw [CFSG.Quasithin.perfectCore_eq_self_of_perfect (Subgroup.isPerfect_iff.1 this)]
        exact Nat.card_congr e.toEquiv
      rw [hcardPC θ eA, hcardPC θ' eB, SymplecticFlag.card_statedSp, h.card_fixedField,
        natCard_unitaryPSU_eq_ordTwistedA h (by omega) hnq, show n - 1 = 2 * m by omega] at hpc
      exact not_sq_card_statedSp_dvd_ordTwistedA (r := m) hf (by omega) (by rw [sq]; exact hpc)

end Pair

end CFSG.SeitzReduction.UnitaryPilot
