module

public import CFSG.RankThree.PartOne.KC.UnitaryRegularUnipotentLift

public section

namespace CFSG.RankThree.PartOne.KCUnitaryRegular

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K) {C : GL (Fin n) K}

include h in
theorem conj_map_eq_of_exp_eq (hn : 1 ≤ n) (hnp : n ≤ p) {M M' : Matrix (Fin n) (Fin n) K}
    (hM : M ^ n = 0) (hM' : M' ^ n = 0) (A : GL (Fin n) K) (σ : K ≃+* K)
    (he : (A : Matrix (Fin n) (Fin n) K) * (truncExp n M).map σ *
      (↑(A⁻¹) : Matrix (Fin n) (Fin n) K) = truncExp n M') :
    (A : Matrix (Fin n) (Fin n) K) * M.map σ * (↑(A⁻¹) : Matrix (Fin n) (Fin n) K) = M' := by
  have hK := KCUnitaryLog.hK_of_le h hnp
  have hMσ : (M.map σ) ^ n = 0 := by
    have h1 : (M.map σ) ^ n = (M ^ n).map σ := (map_pow (σ : K →+* K).mapMatrix M n).symm
    rw [h1, hM, Matrix.map_zero _ (map_zero σ)]
  have hconj : ((A : Matrix (Fin n) (Fin n) K) * M.map σ *
      (↑(A⁻¹) : Matrix (Fin n) (Fin n) K)) ^ n = 0 := by
    rw [Units.conj_pow, hMσ, mul_zero, zero_mul]
  have h1 : truncExp n ((A : Matrix (Fin n) (Fin n) K) * M.map σ *
      (↑(A⁻¹) : Matrix (Fin n) (Fin n) K)) = truncExp n M' := by
    have hmap : truncExp n (M.map σ) = (truncExp n M).map σ := truncExp_map (σ : K →+* K) M
    rw [truncExp_conj A (M.map σ), hmap]
    exact he
  have h2 := congrArg (truncLog n) h1
  rwa [truncLog_truncExp hn hK hconj, truncLog_truncExp hn hK hM'] at h2

variable (hC : IsPrimeFormGram C)

include hC in
theorem fix_exact (hn : 1 ≤ n) (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K))
    (σ : K ≃+* K) {v : gramSU h (C : Matrix (Fin n) (Fin n) K)} (hvp : v ^ p = 1)
    (hfix : (primeFormConjHom h _ A * primeFormFieldHom h hC σ)
        (v : primeFormP h (C : Matrix (Fin n) (Fin n) K)) =
      (v : primeFormP h (C : Matrix (Fin n) (Fin n) K))) :
    (A : GL (Fin n) K) * glAut σ (v : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ =
      (v : GL (Fin n) K) := by
  set v' : gramSU h (C : Matrix (Fin n) (Fin n) K) :=
    ⟨(A : GL (Fin n) K) * glAut σ (v : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹,
      conj_mem_gramSU h _ A.2 (glAut_mem_gramSU h hC σ v.2)⟩ with hv'
  have hπ : (v' : primeFormP h (C : Matrix (Fin n) (Fin n) K)) =
      (v : primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by
    rw [MulAut.mul_apply] at hfix
    change primeFormConjHom h _ A (primeFormFieldAut h hC σ
      (v : primeFormP h (C : Matrix (Fin n) (Fin n) K))) = _ at hfix
    rw [primeFormFieldAut_mk, primeFormConjHom_mk] at hfix
    exact hfix
  have hv'p : v' ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change ((A : GL (Fin n) K) * glAut σ (v : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹) ^ p = 1
    have hvp' : (v : GL (Fin n) K) ^ p = 1 := by
      have := congrArg (fun y : gramSU h (C : Matrix (Fin n) (Fin n) K) => (y : GL (Fin n) K)) hvp
      simpa using this
    rw [conj_pow, ← map_pow, hvp', map_one, mul_one, mul_inv_cancel]
  exact congrArg (fun y : gramSU h (C : Matrix (Fin n) (Fin n) K) => (y : GL (Fin n) K))
    (eq_of_mk_eq_of_pow_eq_one h hn _ hv'p hvp hπ)

include hC in
theorem exists_conj_of_forall_fix (hp3 : 3 < p) (hn3 : 3 ≤ n) (hnp : n ≤ p)
    {N : Matrix (Fin n) (Fin n) K} (hNskew : unitaryAdjoint h C N = -N) (hNn : N ^ n = 0)
    (hNreg : N ^ (n - 1) ≠ 0) (α : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)))
    (hα : ∀ y ∈ Subgroup.centralizer ({(unitaryExp h hn3 hnp hNn hNskew :
      primeFormP h (C : Matrix (Fin n) (Fin n) K))} :
        Set (primeFormP h (C : Matrix (Fin n) (Fin n) K))), α y = y) :
    ∃ y ∈ Subgroup.centralizer ({(unitaryExp h hn3 hnp hNn hNskew :
      primeFormP h (C : Matrix (Fin n) (Fin n) K))} :
        Set (primeFormP h (C : Matrix (Fin n) (Fin n) K))), α = MulAut.conj y := by
  have hp2 : p ≠ 2 := by omega
  have hn1 : 1 ≤ n := by omega
  have hq : ¬(n = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, h2⟩
    have := Nat.le_self_pow (show f ≠ 0 by have := h.one_le; omega) p
    omega
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  obtain ⟨-, -, -, -, hex, -⟩ := unitary_prime_form_full_semilinear_realization h hC hn3 hq
  obtain ⟨σ, ⟨A, hαA⟩, -⟩ := hex α
  obtain ⟨c1, -, -, -, -, -, -, -, -, c7, -, c12⟩ :=
    unitary_small_unipotent_logarithm_calculus h hp3 hn3 hnp hC
  set u := unitaryExp h hn3 hnp hNn hNskew with hu
  set x : primeFormP h (C : Matrix (Fin n) (Fin n) K) :=
    (u : primeFormP h (C : Matrix (Fin n) (Fin n) K)) with hx
  have hN0 : IsNilpotent N := ⟨n, hNn⟩
  have hN_ne : N ≠ 0 := by
    intro h0
    apply hNreg
    rw [h0]
    exact zero_pow (by omega)
  have hfixM : ∀ (M : Matrix (Fin n) (Fin n) K) (hMn : M ^ n = 0)
      (hMs : unitaryAdjoint h C M = -M), M * N = N * M →
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M.map σ *
        (↑((A : GL (Fin n) K)⁻¹) : Matrix (Fin n) (Fin n) K) = M := by
    intro M hMn hMs hMN
    set v := unitaryExp h hn3 hnp hMn hMs with hv
    have hMnil : IsNilpotent M := ⟨n, hMn⟩
    have hvm : ((v : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = truncExp n M := rfl
    have hvp : v ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact c12 _ v.2 (by rw [hvm]; exact (c1 M hMnil).1)
    have hcommN : Commute (truncExp n M) N :=
      Commute.sum_left _ _ _ fun j _ =>
        ((Commute.pow_left (show Commute M N from hMN) j).smul_left _)
    have hvu : (v : primeFormP h (C : Matrix (Fin n) (Fin n) K)) * x =
        x * (v : primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by
      rw [hx, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      apply Units.ext
      have h1 : Commute ((v : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (truncExp n N) :=
        (c7 N hN0 (v : GL (Fin n) K)).mpr (by rw [hvm]; exact hcommN)
      exact h1.eq
    have hfix := hα _ (Subgroup.mem_centralizer_singleton_iff.mpr hvu)
    rw [hαA] at hfix
    have h1 := fix_exact h hC hn1 A σ hvp hfix
    have h2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h1
    simp only [Units.val_mul, coe_glAut] at h2
    exact conj_map_eq_of_exp_eq h hn1 hnp hMn hMn _ σ (by rw [← hvm]; exact h2)
  have hAN1 := hfixM N hNn hNskew rfl
  have hσF : ∀ c : K, h.bar c = c → σ c = c := by
    intro c hc
    have hMn : (c • N) ^ n = 0 := by rw [smul_pow, hNn, smul_zero]
    have hMs : unitaryAdjoint h C (c • N) = -(c • N) := by
      rw [KCUnitaryLog.unitaryAdjoint_smul, hNskew, hc, smul_neg]
    have hMN : (c • N) * N = N * (c • N) := by rw [Matrix.smul_mul, Matrix.mul_smul]
    have h1 := hfixM (c • N) hMn hMs hMN
    rw [Matrix.map_smul' _ c N (map_mul σ), Matrix.mul_smul, Matrix.smul_mul, hAN1] at h1
    have h2 : (σ c - c) • N = 0 := by rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hN_ne
  rcases ringEquiv_eq_one_or_eq_bar h σ hσF with hσ1 | hσbar
  ·
    have hσ' : σ = 1 := RingEquiv.ext hσ1
    have hAN : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N =
        N * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      have hNσ : N.map σ = N := Matrix.ext fun i j => hσ1 _
      rw [hNσ] at hAN1
      have hAiA : (↑((A : GL (Fin n) K)⁻¹) : Matrix (Fin n) (Fin n) K) *
          ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      calc ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N =
            ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N * (↑((A : GL (Fin n) K)⁻¹) *
              ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw [hAiA, mul_one]
        _ = N * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
            rw [← mul_assoc, hAN1]
    obtain ⟨z, u₀, hu₀N, hAz⟩ :=
      exists_scalar_mul_of_mem_primeFormUnitary h hn3 hNn hNreg A.2 hAN
    refine ⟨(u₀ : primeFormP h (C : Matrix (Fin n) (Fin n) K)), ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff, hx, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      apply Units.ext
      exact ((c7 N hN0 (u₀ : GL (Fin n) K)).mpr hu₀N).eq
    · have hAconj : primeFormConjHom h _ A =
          primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) ⟨(u₀ : GL (Fin n) K), u₀.2.1⟩ := by
        refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun g => ?_
        rw [primeFormConjHom_mk, primeFormConjHom_mk]
        congr 1
        apply Subtype.ext
        change (A : GL (Fin n) K) * (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ =
          (u₀ : GL (Fin n) K) * (g : GL (Fin n) K) * (u₀ : GL (Fin n) K)⁻¹
        rw [hAz]
        calc GeneralLinearGroup.scalar (Fin n) z * (u₀ : GL (Fin n) K) * (g : GL (Fin n) K) *
              (GeneralLinearGroup.scalar (Fin n) z * (u₀ : GL (Fin n) K))⁻¹ =
            GeneralLinearGroup.scalar (Fin n) z * ((u₀ : GL (Fin n) K) * (g : GL (Fin n) K) *
              (u₀ : GL (Fin n) K)⁻¹) * (GeneralLinearGroup.scalar (Fin n) z)⁻¹ := by group
          _ = (u₀ : GL (Fin n) K) * (g : GL (Fin n) K) * (u₀ : GL (Fin n) K)⁻¹ := by
              rw [← (commute_scalar z ((u₀ : GL (Fin n) K) * (g : GL (Fin n) K) *
                (u₀ : GL (Fin n) K)⁻¹)).eq]
              group
      rw [hαA, hσ', map_one, mul_one, hAconj]
      exact primeFormConjHom_eq_conj h _ u₀
  ·
    exfalso
    obtain ⟨η, hη, hη0⟩ := h.exists_mem_traceZero_ne_zero
    have hηbar : h.bar η = -η := by
      have := h.mem_traceZero.mp hη
      unfold UnitaryFieldData.trace at this
      linear_combination this
    have hMn : (η • N ^ 2) ^ n = 0 := by
      rw [smul_pow, ← pow_mul, pow_eq_zero_of_le hNn (by omega), smul_zero]
    have hMs : unitaryAdjoint h C (η • N ^ 2) = -(η • N ^ 2) := by
      rw [KCUnitaryLog.unitaryAdjoint_smul, KCUnitaryLog.unitaryAdjoint_pow, hNskew, hηbar,
        neg_sq, neg_smul]
    have hMN : (η • N ^ 2) * N = N * (η • N ^ 2) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, ← pow_succ, ← pow_succ']
    have h1 := hfixM _ hMn hMs hMN
    have hσf : (⇑σ : K → K) = ⇑h.bar := funext hσbar
    rw [hσf] at h1 hAN1
    have hmap : (η • N ^ 2).map h.bar = h.bar η • (N.map h.bar) ^ 2 := by
      rw [Matrix.map_smul' _ η _ (map_mul h.bar)]
      congr 1
      exact map_pow (h.bar : K →+* K).mapMatrix N 2
    rw [hmap, Matrix.mul_smul, Matrix.smul_mul] at h1
    have hconj2 : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (N.map h.bar) ^ 2 *
        (↑((A : GL (Fin n) K)⁻¹) : Matrix (Fin n) (Fin n) K) = N ^ 2 := by
      rw [← Units.conj_pow, hAN1]
    rw [hconj2, hηbar] at h1
    have hN2 : N ^ 2 ≠ 0 := by
      intro h0
      apply hNreg
      rw [show n - 1 = (n - 3) + 2 by omega, pow_add, h0, mul_zero]
    have h2 : (2 * η) • N ^ 2 = 0 := by
      rw [neg_smul] at h1
      rw [two_mul, add_smul]
      exact add_eq_zero_iff_eq_neg.mpr h1.symm
    have h2K : (2 : K) ≠ 0 := by
      intro h0
      have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp this)
    rcases smul_eq_zero.mp h2 with h3 | h3
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact h2K h4
      · exact hη0 h4
    · exact hN2 h3

end CFSG.RankThree.PartOne.KCUnitaryRegular

namespace CFSG.RankThree.PartOne

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.KCUnitaryRegular

theorem unitary_regular_unipotent_centralizer_normal_prime_complements_trivial {p f n : ℕ}
    {K : Type} [Field K] (h : UnitaryFieldData p f K) (hp3 : 3 < p) (hn3 : 3 ≤ n) (hnp : n ≤ p)
    {C : GL (Fin n) K} (hC : IsPrimeFormGram C) {N : Matrix (Fin n) (Fin n) K}
    (hNskew : unitaryAdjoint h C N = -N) (hNn : N ^ n = 0) (hNreg : N ^ (n - 1) ≠ 0)
    (B : Subgroup (MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))))
    (hB : (MulAut.conj : primeFormP h (C : Matrix (Fin n) (Fin n) K) →*
      MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))).range ≤ B)
    (S : Subgroup (MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))))
    (hSC : S ≤ B ⊓ Subgroup.centralizer {MulAut.conj (unitaryExp h hn3 hnp hNn hNskew :
      primeFormP h (C : Matrix (Fin n) (Fin n) K))})
    (hSn : (S.subgroupOf (B ⊓ Subgroup.centralizer {MulAut.conj (unitaryExp h hn3 hnp hNn hNskew :
      primeFormP h (C : Matrix (Fin n) (Fin n) K))})).Normal)
    (hSp : ¬ p ∣ Nat.card S) : S = ⊥ := by
  have hn1 : 1 ≤ n := by omega
  have hq : ¬(n = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, h2⟩
    have := Nat.le_self_pow (show f ≠ 0 by have := h.one_le; omega) p
    omega
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  have hN0 : IsNilpotent N := ⟨n, hNn⟩
  obtain ⟨c1, -, -, -, -, -, -, -, -, c7, -, c12⟩ :=
    unitary_small_unipotent_logarithm_calculus h hp3 hn3 hnp hC
  set u := unitaryExp h hn3 hnp hNn hNskew with hu
  have hum : ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = truncExp n N := rfl
  have hup : u ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact c12 _ u.2 (by rw [hum]; exact (c1 N hN0).1)
  refine eq_bot_of_pointwise_centralizer (conj_injective_primeFormP h hC hn3 hq) h.prime ?_ ?_ B hB
    S hSC hSn hSp
  ·
    intro y hy
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have hy' : (g : primeFormP h (C : Matrix (Fin n) (Fin n) K)) *
        (u : primeFormP h (C : Matrix (Fin n) (Fin n) K)) =
        (u : primeFormP h (C : Matrix (Fin n) (Fin n) K)) *
          (g : primeFormP h (C : Matrix (Fin n) (Fin n) K)) :=
      Subgroup.mem_centralizer_singleton_iff.1 hy
    have hconjp : (g * u * g⁻¹) ^ p = 1 := by rw [conj_pow, hup, mul_one, mul_inv_cancel]
    have hconjπ : ((g * u * g⁻¹ : gramSU h (C : Matrix (Fin n) (Fin n) K)) :
        primeFormP h (C : Matrix (Fin n) (Fin n) K)) =
        (u : primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy', mul_assoc,
        mul_inv_cancel, mul_one]
    have hconj : g * u * g⁻¹ = u := eq_of_mk_eq_of_pow_eq_one h hn1 _ hconjp hup hconjπ
    have hgu : (g : GL (Fin n) K) * (u : GL (Fin n) K) =
        (u : GL (Fin n) K) * (g : GL (Fin n) K) := by
      have := congrArg (fun z : gramSU h (C : Matrix (Fin n) (Fin n) K) => z * g) hconj
      simp only [inv_mul_cancel_right] at this
      exact congrArg (fun z : gramSU h (C : Matrix (Fin n) (Fin n) K) => (z : GL (Fin n) K)) this
    have hcomm : Commute ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (truncExp n N) := by
      have h1 : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * truncExp n N =
          truncExp n N * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        have := congrArg (fun z : GL (Fin n) K => (z : Matrix (Fin n) (Fin n) K)) hgu
        simpa [Units.val_mul, hum] using this
      exact h1
    have hgN := (c7 N hN0 (g : GL (Fin n) K)).mp hcomm
    have hmem := pow_mem_normOneScalars_of_commute h hn3 hnp hNn hNreg hgN
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hmem
  · intro α hα
    exact exists_conj_of_forall_fix h hC hp3 hn3 hnp hNskew hNn hNreg α hα

end CFSG.RankThree.PartOne
