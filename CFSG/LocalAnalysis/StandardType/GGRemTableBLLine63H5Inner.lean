module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5StepOne
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeCases

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.SectionRank.OddCover CFSG.Assembly
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.Classical2 CFSG.StandardType.TableBU63

variable {K : Type} [Field K] {n : ℕ}

@[expose] def IsInner (n : ℕ) (M : GL (Fin 6) K) : Prop :=
  ∃ (t : Kˣ) (s : ↥(unitarySU 2 n K 6)), M = GeneralLinearGroup.scalar (Fin 6) t * (s : GL _ _)

theorem det_eq_pow_six_of_isInner {M : GL (Fin 6) K} (h : IsInner n M)
    (hKd : UnitaryFieldData 2 n K) :
    ∃ t : Kˣ, ((M : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = (t : K) ^ 6 := by
  obtain ⟨t, s, rfl⟩ := h
  refine ⟨t, ?_⟩
  have h1 := ((mem_unitarySU_iff hKd).mp s.2).1
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.det_mul, Matrix.det_diagonal, h1, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, mul_one]

theorem bar_det_mul_det (hKd : UnitaryFieldData 2 n K) {M : GL (Fin 6) K}
    (hM : M ∈ primeFormUnitary hKd (idGram K 6)) :
    hKd.bar ((M : Matrix (Fin 6) (Fin 6) K).det) * (M : Matrix (Fin 6) (Fin 6) K).det = 1 := by
  have h1 := mem_primeFormUnitary.mp hM
  simp only [idGram, Units.val_one, Matrix.mul_one] at h1
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h2
  rw [← h2]
  congr 1
  exact (RingHom.map_det hKd.bar (M : Matrix (Fin 6) (Fin 6) K))

theorem eq_one_of_pow_six_of_pow_sub_one (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1) {y : K}
    (hy6 : y ^ 6 = 1) (hyq : y ^ (2 ^ n - 1) = 1) : y = 1 := by
  have hodd : Nat.Coprime 2 (2 ^ n - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro h
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h3 : 2 ∣ 2 ^ n - (2 ^ n - 1) := Nat.dvd_sub h2 h
    have h4 : 2 ^ n - (2 ^ n - 1) = 1 := by omega
    rw [h4] at h3
    omega
  have hcop : Nat.Coprime 6 (2 ^ n - 1) :=
    Nat.Coprime.mul_left hodd (coprime_three_two_pow_sub_one hn hpq)
  have h := pow_gcd_eq_one.mpr ⟨hy6, hyq⟩
  rwa [hcop, pow_one] at h

theorem isInner_of_det_eq_pow_six [Finite K] (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {M : GL (Fin 6) K} (hM : M ∈ primeFormUnitary hKd (idGram K 6)) {t : Kˣ}
    (ht : ((M : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = (t : K) ^ 6) : IsInner n M := by
  have hn : 1 ≤ n := hKd.one_le
  haveI := Fintype.ofFinite K
  have hnorm := bar_det_mul_det hKd hM
  rw [ht, map_pow, UnitaryFieldData.bar_apply, ← mul_pow, ← pow_succ] at hnorm
  have htq : (t : K) ^ (2 ^ n + 1) = 1 := by
    set y : K := (t : K) ^ (2 ^ n + 1) with hy
    have hy6 : y ^ 6 = 1 := hnorm
    have hyq : y ^ (2 ^ n - 1) = 1 := by
      have h0 : (t : K) ≠ 0 := t.ne_zero
      have := FiniteField.pow_card_sub_one_eq_one (t : K) h0
      have hc : Fintype.card K = (2 ^ n) ^ 2 := by
        rw [← Nat.card_eq_fintype_card, hKd.card, ← pow_mul, mul_comm]
      have e : (2 ^ n + 1) * (2 ^ n - 1) = Fintype.card K - 1 := by
        rw [hc]
        have := Nat.sq_sub_sq (2 ^ n) 1
        simpa using this.symm
      rw [hy, ← pow_mul, e]
      exact this
    exact eq_one_of_pow_six_of_pow_sub_one hn hpq hy6 hyq
  have hscal : (GeneralLinearGroup.scalar (Fin 6) t⁻¹ : GL (Fin 6) K) ∈
      primeFormUnitary hKd (idGram K 6) := by
    rw [mem_primeFormUnitary]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    rw [← diagHom_const_eq_scalar]
    refine diagHom_unitary hKd (n := 6) (d := fun _ => t⁻¹) fun _ => ?_
    simp only [Units.val_inv_eq_inv_val, inv_pow, htq, inv_one]
  have hs : (GeneralLinearGroup.scalar (Fin 6) t⁻¹ : GL (Fin 6) K) * M ∈
      primeFormUnitary hKd (idGram K 6) := Subgroup.mul_mem _ hscal hM
  have hdet : (((GeneralLinearGroup.scalar (Fin 6) t⁻¹ : GL (Fin 6) K) * M : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K).det = 1 := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_mul,
      Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ht]
    have h0 : (t : K) ≠ 0 := t.ne_zero
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  refine ⟨t, ⟨_, TableBUE.mem_unitarySU_of_mem_primeFormUnitary hKd hs hdet⟩, ?_⟩
  show M = _ * ((GeneralLinearGroup.scalar (Fin 6) t⁻¹ : GL (Fin 6) K) * M)
  rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem zpow_mem_range_sixth_iff [Finite K] {g : Kˣ} (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g)
    (h3 : 3 ∣ Nat.card Kˣ) (h2 : ¬ 2 ∣ Nat.card Kˣ) (a : ℤ) :
    g ^ a ∈ (powMonoidHom 6 : Kˣ →* Kˣ).range ↔ (3 : ℤ) ∣ a := by
  have hN : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨c, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg d)
    have h1 : g ^ (c * 6) = g ^ a := by
      rw [_root_.zpow_mul]
      simpa using hd
    have h2' : g ^ (a - c * 6) = 1 := by
      rw [_root_.zpow_sub, h1, mul_inv_cancel]
    have h3' : (orderOf g : ℤ) ∣ a - c * 6 := orderOf_dvd_iff_zpow_eq_one.mpr h2'
    rw [hN] at h3'
    have h4 : (3 : ℤ) ∣ (Nat.card Kˣ : ℤ) := by exact_mod_cast h3
    have h5 : (3 : ℤ) ∣ a - c * 6 := h4.trans h3'
    omega
  · rintro ⟨a', rfl⟩
    obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.card Kˣ = 2 * m + 1 := by
      have : Nat.card Kˣ % 2 = 1 := by omega
      exact ⟨Nat.card Kˣ / 2, by omega⟩
    refine ⟨g ^ (a' * (m + 1 : ℕ)), ?_⟩
    show (g ^ (a' * ((m + 1 : ℕ) : ℤ))) ^ 6 = g ^ (3 * a')
    rw [← zpow_natCast, ← _root_.zpow_mul]
    have h1 : g ^ (Nat.card Kˣ : ℤ) = 1 := by rw [zpow_natCast, ← hN, pow_orderOf_eq_one]
    have h6 : (a' * ((m + 1 : ℕ) : ℤ)) * ((6 : ℕ) : ℤ) = 3 * a' + (a' * 3) * (Nat.card Kˣ : ℤ) := by
      rw [hm]
      push_cast
      ring
    have hfin : g ^ ((a' * 3) * (Nat.card Kˣ : ℤ)) = 1 := by
      rw [mul_comm, _root_.zpow_mul, h1, _root_.one_zpow]
    rw [h6, _root_.zpow_add, hfin, mul_one]

theorem exists_pow_mul_mem_range_sixth [Finite K] (h3 : 3 ∣ Nat.card Kˣ)
    (h2 : ¬ 2 ∣ Nat.card Kˣ) {u v : Kˣ} (hu : u ∉ (powMonoidHom 6 : Kˣ →* Kˣ).range)
    (hv : v ∉ (powMonoidHom 6 : Kˣ →* Kˣ).range) :
    ∃ ε : ℕ, (ε = 1 ∨ ε = 2) ∧ v * u ^ ε ∈ (powMonoidHom 6 : Kˣ →* Kˣ).range := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg v)
  rw [zpow_mem_range_sixth_iff hg h3 h2] at hu hv
  have key : ∀ ε : ℕ, g ^ b * (g ^ a) ^ ε = g ^ (b + a * ε) := by
    intro ε
    rw [← zpow_natCast (g ^ a) ε, ← _root_.zpow_mul, ← _root_.zpow_add]
  by_cases h : (3 : ℤ) ∣ b + a
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [key, zpow_mem_range_sixth_iff hg h3 h2]
    simpa using h
  · refine ⟨2, Or.inr rfl, ?_⟩
    rw [key, zpow_mem_range_sixth_iff hg h3 h2]
    push_cast
    have ha3 : a % 3 = 1 ∨ a % 3 = 2 := by omega
    have hb3 : b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases ha3 with ha3 | ha3 <;> rcases hb3 with hb3 | hb3 <;> omega

theorem isInner_scalar_mul_iff (t : Kˣ) (M : GL (Fin 6) K) :
    IsInner n (GeneralLinearGroup.scalar (Fin 6) t * M) ↔ IsInner n M := by
  constructor
  · rintro ⟨u, s, hs⟩
    refine ⟨t⁻¹ * u, s, ?_⟩
    rw [map_mul, mul_assoc, ← hs, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  · rintro ⟨u, s, hs⟩
    refine ⟨t * u, s, ?_⟩
    rw [hs, map_mul, mul_assoc]

theorem card_units_dvd_odd [Finite K] (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1) :
    3 ∣ Nat.card Kˣ ∧ ¬ 2 ∣ Nat.card Kˣ := by
  have hn : 1 ≤ n := hKd.one_le
  rw [Nat.card_units, hKd.card, pow_mul', sq]
  have e := Nat.mul_self_sub_mul_self_eq (2 ^ n) 1
  rw [mul_one] at e
  rw [e]
  refine ⟨Dvd.dvd.mul_right hpq _, fun h => ?_⟩
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have hodd : ¬ 2 ∣ 2 ^ n + 1 := by
    intro h'
    have := (Nat.dvd_add_right h2).mp h'
    omega
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h' | h'
  · exact hodd h'
  · have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h3 : 2 ∣ 2 ^ n - (2 ^ n - 1) := Nat.dvd_sub h2 h'
    have h4 : 2 ^ n - (2 ^ n - 1) = 1 := by omega
    rw [h4] at h3
    omega

theorem exists_inner_noncomm [Finite K] (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {S : Subgroup (GL (Fin 6) K)} (hS : ∀ M ∈ S, M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n))
    {M₁ M₂ : GL (Fin 6) K} (h₁ : M₁ ∈ S) (h₂ : M₂ ∈ S) (hne : M₁ * M₂ ≠ M₂ * M₁) :
    ∃ P ∈ S, ∃ Q ∈ S, IsInner n Q ∧ P * Q ≠ Q * P := by
  by_cases hi2 : IsInner n M₂
  · exact ⟨M₁, h₁, M₂, h₂, hi2, hne⟩
  by_cases hi1 : IsInner n M₁
  · exact ⟨M₂, h₂, M₁, h₁, hi1, fun h => hne h.symm⟩
  obtain ⟨u₁, hu₁⟩ := exists_unitary_of_gu hKd (hS M₁ h₁)
  obtain ⟨u₂, hu₂⟩ := exists_unitary_of_gu hKd (hS M₂ h₂)
  obtain ⟨h3, h2⟩ := card_units_dvd_odd hKd hpq
  set U₁ : GL (Fin 6) K := GeneralLinearGroup.scalar (Fin 6) u₁ * M₁ with hU₁
  set U₂ : GL (Fin 6) K := GeneralLinearGroup.scalar (Fin 6) u₂ * M₂ with hU₂
  have hn1 : ∀ t : Kˣ, ¬ (GeneralLinearGroup.det U₁ = t ^ 6) := by
    intro t ht
    apply hi1
    rw [← isInner_scalar_mul_iff u₁]
    refine isInner_of_det_eq_pow_six hKd hpq hu₁ (t := t) ?_
    rw [← Matrix.GeneralLinearGroup.val_det_apply, ht]
    simp
  have hn2 : ∀ t : Kˣ, ¬ (GeneralLinearGroup.det U₂ = t ^ 6) := by
    intro t ht
    apply hi2
    rw [← isInner_scalar_mul_iff u₂]
    refine isInner_of_det_eq_pow_six hKd hpq hu₂ (t := t) ?_
    rw [← Matrix.GeneralLinearGroup.val_det_apply, ht]
    simp
  obtain ⟨ε, hε, t, ht⟩ := exists_pow_mul_mem_range_sixth h3 h2
    (u := GeneralLinearGroup.det U₁) (v := GeneralLinearGroup.det U₂)
    (fun ⟨t, ht⟩ => hn1 t (by simpa using ht.symm)) (fun ⟨t, ht⟩ => hn2 t (by simpa using ht.symm))
  have hUε : U₂ * U₁ ^ ε ∈ primeFormUnitary hKd (idGram K 6) :=
    Subgroup.mul_mem _ hu₂ (Subgroup.pow_mem _ hu₁ ε)
  have ht' : t ^ 6 = GeneralLinearGroup.det U₂ * GeneralLinearGroup.det U₁ ^ ε := ht
  have hdet : ((U₂ * U₁ ^ ε : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = (t : K) ^ 6 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_pow, ← ht',
      Units.val_pow_eq_pow_val]
  have hinner : IsInner n (U₂ * U₁ ^ ε) := isInner_of_det_eq_pow_six hKd hpq hUε hdet
  have hUeq : U₂ * U₁ ^ ε =
      GeneralLinearGroup.scalar (Fin 6) (u₂ * u₁ ^ ε) * (M₂ * M₁ ^ ε) := by
    have hpowU : U₁ ^ ε = GeneralLinearGroup.scalar (Fin 6) (u₁ ^ ε) * M₁ ^ ε := by
      rw [hU₁, ((commute_scalar u₁ M₁).symm).mul_pow, map_pow]
    rw [hpowU, hU₂, map_mul]
    have hc := (commute_scalar (u₁ ^ ε) M₂).eq
    calc GeneralLinearGroup.scalar (Fin 6) u₂ * M₂ *
          (GeneralLinearGroup.scalar (Fin 6) (u₁ ^ ε) * M₁ ^ ε)
        = GeneralLinearGroup.scalar (Fin 6) u₂ *
            (M₂ * GeneralLinearGroup.scalar (Fin 6) (u₁ ^ ε)) * M₁ ^ ε := by group
      _ = GeneralLinearGroup.scalar (Fin 6) u₂ *
            (GeneralLinearGroup.scalar (Fin 6) (u₁ ^ ε) * M₂) * M₁ ^ ε := by rw [hc]
      _ = GeneralLinearGroup.scalar (Fin 6) u₂ * GeneralLinearGroup.scalar (Fin 6) (u₁ ^ ε) *
            (M₂ * M₁ ^ ε) := by group
  refine ⟨M₁, h₁, M₂ * M₁ ^ ε, S.mul_mem h₂ (S.pow_mem h₁ ε), ?_, ?_⟩
  · rw [← isInner_scalar_mul_iff (u₂ * u₁ ^ ε), ← hUeq]
    exact hinner
  · intro hc
    apply hne
    have hcm : M₁ * M₁ ^ ε = M₁ ^ ε * M₁ := (Commute.self_pow M₁ ε).eq
    have h' : M₁ * M₂ * M₁ ^ ε = M₂ * M₁ * M₁ ^ ε := by
      calc M₁ * M₂ * M₁ ^ ε = M₁ * (M₂ * M₁ ^ ε) := by group
        _ = (M₂ * M₁ ^ ε) * M₁ := hc
        _ = M₂ * (M₁ ^ ε * M₁) := by group
        _ = M₂ * (M₁ * M₁ ^ ε) := by rw [hcm]
        _ = M₂ * M₁ * M₁ ^ ε := by group
    exact mul_right_cancel h'

end CFSG.StandardType.Line63.H5

end
