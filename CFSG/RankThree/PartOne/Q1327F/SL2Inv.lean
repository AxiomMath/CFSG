module

public import CFSG.RankThree.PartOne.Q1327F.SL2Odd
import CFSG.RankThree.PartOne.N143.SectionGroup
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.RankThree.PartOne.K133.KillL2
public import CFSG.RankThree.PartOne.Q1327T.Item7Basic
public import CFSG.RankThree.PartOne.S11d.OutCentral

public section

namespace CFSG.RankThree.PartOne.Q1327F

open Matrix CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Q1327T

section Trace

variable {K : Type} [Field K]

theorem pow_succ_of_sq_eq_zero (ε : K) (N : Matrix (Fin 2) (Fin 2) K) (hN : N * N = 0) (k : ℕ) :
    ((ε • (1 : Matrix (Fin 2) (Fin 2) K)) + N) ^ (k + 1) =
      (ε ^ (k + 1)) • (1 : Matrix (Fin 2) (Fin 2) K) + (((k + 1 : ℕ) : K) * ε ^ k) • N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hN, smul_zero,
      add_zero]
    push_cast
    module

theorem eq_one_of_trace_sq_eq_four (h2 : (2 : K) ≠ 0) (z : SpecialLinearGroup (Fin 2) K) {m : ℕ}
    (hm : Odd m) (hmK : (m : K) ≠ 0) (hz : z ^ m = 1)
    (ht : ((z : Matrix (Fin 2) (Fin 2) K) 0 0 + (z : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2 = 4) :
    z = 1 := by
  set A : Matrix (Fin 2) (Fin 2) K := (z : Matrix (Fin 2) (Fin 2) K) with hA
  obtain ⟨ε, hε, htε⟩ : ∃ ε : K, ε * ε = 1 ∧ A 0 0 + A 1 1 = 2 * ε := by
    have h : (A 0 0 + A 1 1 - 2) * (A 0 0 + A 1 1 + 2) = 0 := by linear_combination ht
    rcases mul_eq_zero.1 h with h | h
    · exact ⟨1, by norm_num, by linear_combination h⟩
    · exact ⟨-1, by norm_num, by linear_combination h⟩
  have hε0 : ε ≠ 0 := fun h0 => by simp [h0] at hε
  have hCH : A * A = (A 0 0 + A 1 1) • A - 1 := by
    have h1 : A * adjugate A = 1 := by
      rw [mul_adjugate, hA, z.2]
      simp
    rw [adjugate_fin_two_eq, mul_sub, Matrix.mul_smul, mul_one] at h1
    calc A * A = (A 0 0 + A 1 1) • A - ((A 0 0 + A 1 1) • A - A * A) := by abel
      _ = (A 0 0 + A 1 1) • A - 1 := by rw [h1]
  set N : Matrix (Fin 2) (Fin 2) K := A - ε • 1 with hNdef
  have hN : N * N = 0 := by
    have e1 : N * N = A * A - ε • A - ε • A + (ε * ε) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      simp only [hNdef, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
        smul_smul]
      abel
    rw [e1, hCH, htε, hε]
    module
  have hAeq : A = ε • (1 : Matrix (Fin 2) (Fin 2) K) + N := by
    rw [hNdef]
    abel
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by obtain ⟨j, hj⟩ := hm; omega⟩
  have hpow := pow_succ_of_sq_eq_zero ε N hN k
  rw [← hAeq] at hpow
  have hAm : A ^ (k + 1) = 1 := by
    rw [hA, ← Matrix.SpecialLinearGroup.coe_pow, hz]
    rfl
  rw [hAm] at hpow
  have hc : (((k + 1 : ℕ) : K) * ε ^ k) ≠ 0 := mul_ne_zero hmK (pow_ne_zero _ hε0)
  have e01 := congrFun (congrFun hpow 0) 1
  have e10 := congrFun (congrFun hpow 1) 0
  have e00 := congrFun (congrFun hpow 0) 0
  have e11 := congrFun (congrFun hpow 1) 1
  have hN01 : N 0 1 = 0 := by
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne, smul_eq_mul, mul_zero,
      zero_add, ne_eq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true] at e01
    exact (mul_eq_zero.1 e01.symm).resolve_left hc
  have hN10 : N 1 0 = 0 := by
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne, smul_eq_mul, mul_zero,
      zero_add, ne_eq, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, not_false_eq_true] at e10
    exact (mul_eq_zero.1 e10.symm).resolve_left hc
  have hNtr : N 0 0 + N 1 1 = 0 := by
    simp only [hNdef, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one]
    linear_combination htε
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    mul_one] at e00 e11
  have hεk : ε ^ (k + 1) = 1 := by
    have : 2 * ε ^ (k + 1) = 2 := by
      linear_combination -e00 - e11 - (((k + 1 : ℕ) : K) * ε ^ k) * hNtr
    exact mul_left_cancel₀ h2 (by linear_combination this)
  have hN00 : N 0 0 = 0 := by
    have : (((k + 1 : ℕ) : K) * ε ^ k) * N 0 0 = 0 := by linear_combination -e00 - hεk
    exact (mul_eq_zero.1 this).resolve_left hc
  have hN11 : N 1 1 = 0 := by linear_combination hNtr - hN00
  have hN0 : N = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hN00, hN01, hN10, hN11]
  have hε1 : ε = 1 := by
    obtain ⟨j, hj⟩ := hm
    have : k + 1 = 2 * j + 1 := hj
    have hk : k = 2 * j := by omega
    rw [hk, pow_succ, pow_mul, sq, hε, one_pow, one_mul] at hεk
    exact hεk
  apply Subtype.ext
  rw [← hA, hAeq, hN0, hε1]
  simp

end Trace

section Inv

variable {K : Type} [Field K] [Finite K]

theorem pRank_le_one_of_equiv_sl2_ne {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    [NeZero (p : K)] (e : X ≃* SpecialLinearGroup (Fin 2) K) : CFSG.pRank p X ≤ 1 := by
  refine CFSG.LieType.SteinbergBR.pRank_le_of_card_le hp.one_lt fun A hA => ?_
  have hpow : ∀ x : A, x ^ p = 1 := fun x =>
    Subtype.ext (CFSG.elemPow_eq_one_of_isElementaryAbelian (x : X) x.2)
  let A' : Subgroup (SpecialLinearGroup (Fin 2) K) := A.map e.toMonoidHom
  have hcomm : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show e x * e y = e y * e x
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hA.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hpow' : ∀ x ∈ A', x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show e x ^ p = 1
    have h1 : x ^ p = 1 := by simpa using congrArg Subtype.val (hpow ⟨x, hx⟩)
    rw [← map_pow, h1, map_one]
  have hcyc : IsCyclic A' := K133.isCyclic_of_commuting_pow_eq_one_sl2 hp A' hcomm hpow'
  have hexp : Monoid.exponent A' ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hpow' x x.2)
  have hcard : Nat.card A' ≤ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd hp.pos hexp
  rw [pow_one]
  calc Nat.card A = Nat.card A' := (Subgroup.card_map_of_injective e.injective).symm
    _ ≤ p := hcard

theorem exists_inv_of_isPGroup_sl2_odd (h2 : (2 : K) ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : (p : K) ≠ 0) {E : Subgroup (SpecialLinearGroup (Fin 2) K)} (hE : IsPGroup p E) :
    ∃ w : SpecialLinearGroup (Fin 2) K, ∀ y ∈ E, w * y * w⁻¹ = y⁻¹ := by
  have : NeZero (p : K) := ⟨hpK⟩
  have hcyc : IsCyclic E :=
    isCyclic_of_pRank_le_one hp hp2 (le_top : E ≤ ⊤) hE
      (pRank_le_one_of_equiv_sl2_ne hp Subgroup.topEquiv)
  obtain ⟨z, hz⟩ := hcyc.exists_generator
  by_cases hz1 : (z : SpecialLinearGroup (Fin 2) K) = 1
  · refine ⟨1, fun y hy => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hz ⟨y, hy⟩)
    have : y = 1 := by simpa [hz1] using (congrArg Subtype.val hk).symm
    simp [this]
  · obtain ⟨n, hn⟩ := hE z
    have hzn : (z : SpecialLinearGroup (Fin 2) K) ^ (p ^ n) = 1 := by
      simpa using congrArg Subtype.val hn
    have hpodd : Odd (p ^ n) := (hp.odd_of_ne_two hp2).pow
    have hpnK : ((p ^ n : ℕ) : K) ≠ 0 := by
      rw [Nat.cast_pow]
      exact pow_ne_zero _ hpK
    have ht : ((z : Matrix (Fin 2) (Fin 2) K) 0 0 + (z : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2 ≠ 4 :=
      fun h => hz1 (eq_one_of_trace_sq_eq_four h2 (z : SpecialLinearGroup (Fin 2) K) hpodd hpnK
        hzn h)
    obtain ⟨w, hw⟩ := exists_inv_conj_sl2_odd h2 (z : SpecialLinearGroup (Fin 2) K) ht
    refine ⟨w, fun y hy => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hz ⟨y, hy⟩)
    have hyk : y = (z : SpecialLinearGroup (Fin 2) K) ^ k := by
      simpa using (congrArg Subtype.val hk).symm
    rw [hyk]
    calc w * (z : SpecialLinearGroup (Fin 2) K) ^ k * w⁻¹
        = (w * (z : SpecialLinearGroup (Fin 2) K) * w⁻¹) ^ k := by
          rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
      _ = ((z : SpecialLinearGroup (Fin 2) K) ^ k)⁻¹ := by rw [hw, _root_.inv_zpow]

theorem exists_inv_of_isPGroup_prod_odd (h2 : (2 : K) ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : (p : K) ≠ 0)
    {E : Subgroup (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K)}
    (hE : IsPGroup p E) :
    ∃ w : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K,
      ∀ y ∈ E, w * y * w⁻¹ = y⁻¹ := by
  obtain ⟨w₁, h₁⟩ := exists_inv_of_isPGroup_sl2_odd h2 hp hp2 hpK
    (E := E.map (MonoidHom.fst _ _)) (hE.map _)
  obtain ⟨w₂, h₂⟩ := exists_inv_of_isPGroup_sl2_odd h2 hp hp2 hpK
    (E := E.map (MonoidHom.snd _ _)) (hE.map _)
  refine ⟨(w₁, w₂), fun y hy => Prod.ext ?_ ?_⟩
  · exact h₁ y.1 (Subgroup.mem_map_of_mem (MonoidHom.fst _ _) hy)
  · exact h₂ y.2 (Subgroup.mem_map_of_mem (MonoidHom.snd _ _) hy)

theorem exists_inv_of_prod_sl2_odd (h2 : (2 : K) ≠ 0) {C : Type} [Group C] [Finite C]
    (μ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K →* C)
    (hμ : ∀ x, μ x = 1 → x ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hord : (Nat.card C).factorization p =
      2 * (Nat.card (SpecialLinearGroup (Fin 2) K)).factorization p)
    {E : Subgroup C} (hE : IsPGroup p E) : ∃ g : C, ∀ e ∈ E, g * e * g⁻¹ = e⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain PH : Sylow p (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) := default
  have hdis : Disjoint (PH : Subgroup (SpecialLinearGroup (Fin 2) K ×
      SpecialLinearGroup (Fin 2) K)) μ.ker := by
    rw [Subgroup.disjoint_def]
    intro x hxP hxk
    obtain ⟨n, hn⟩ := PH.isPGroup' ⟨x, hxP⟩
    have h1 : x ^ (p ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have h2' : x ^ 2 = 1 := hμ x (MonoidHom.mem_ker.1 hxk)
    have hcop : Nat.Coprime (p ^ n) 2 :=
      Nat.Coprime.pow_left n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have hdvd : orderOf x ∣ Nat.gcd (p ^ n) 2 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2')
    rw [hcop] at hdvd
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd)
  have hP₀card : Nat.card ((PH : Subgroup _).map μ) = p ^ (Nat.card C).factorization p := by
    rw [CFSG.RankThree.PartOne.N143.card_map_of_disjoint_ker μ hdis, Sylow.card_eq_multiplicity PH,
      Nat.card_prod, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      hord]
    ring_nf
  have hPH : IsPGroup p (PH : Subgroup (SpecialLinearGroup (Fin 2) K ×
      SpecialLinearGroup (Fin 2) K)) := PH.isPGroup'
  obtain ⟨w, hw⟩ := exists_inv_of_isPGroup_prod_odd h2 hp hp2 hpK hPH
  refine exists_inv_of_sylow (Sylow.ofCard _ hP₀card) (g₀ := μ w) (fun y hy => ?_) hE
  rw [Sylow.coe_ofCard] at hy
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
  calc μ w * μ y' * (μ w)⁻¹ = μ (w * y' * w⁻¹) := by simp [map_mul, map_inv]
    _ = μ y'⁻¹ := by rw [hw y' hy']
    _ = (μ y')⁻¹ := map_inv μ y'

end Inv

end CFSG.RankThree.PartOne.Q1327F
