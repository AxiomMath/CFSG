module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpHeis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (formJ)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {r : ℕ} {K : Type} [Field K]

private theorem formJ_mul_formJ (r : ℕ) : formJ r K * formJ r K = -1 := by
  rw [show formJ r K = -Matrix.J (Fin r) K by
      rw [formJ, Matrix.J, Matrix.fromBlocks_neg]; simp,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.J_squared]

theorem exists_spForm_sep {S : Set (Fin r ⊕ Fin r → K)} {c : Fin r ⊕ Fin r → K}
    (hc : c ∉ Submodule.span K S) :
    ∃ f : Fin r ⊕ Fin r → K, (∀ a ∈ S, spForm a f = 0) ∧ spForm c f = 1 := by
  classical
  obtain ⟨φ₀, hφ₀c, hφ₀S⟩ := Submodule.exists_le_ker_of_notMem (K := K) hc
  let φ : (Fin r ⊕ Fin r → K) →ₗ[K] K := (φ₀ c)⁻¹ • φ₀
  let w : Fin r ⊕ Fin r → K := fun i => φ (fun j => if i = j then 1 else 0)
  have hφc : φ c = 1 := by
    simp only [φ, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hφ₀c
  have hφS : ∀ a ∈ S, φ a = 0 := by
    intro a ha
    have h0 : φ₀ a = 0 := LinearMap.mem_ker.mp (hφ₀S (Submodule.subset_span ha))
    simp [φ, h0]
  have hdot : ∀ y, φ y = y ⬝ᵥ w := by
    intro y
    rw [LinearMap.pi_apply_eq_sum_univ φ y]
    simp [w, dotProduct, smul_eq_mul]
  have hJf : formJ r K *ᵥ (-(formJ r K *ᵥ w)) = w := by
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, formJ_mul_formJ, Matrix.neg_mulVec,
      Matrix.one_mulVec, neg_neg]
  have hvalue : ∀ y, spForm y (-(formJ r K *ᵥ w)) = φ y := by
    intro y
    rw [spForm, hJf]
    exact (hdot y).symm
  exact ⟨-(formJ r K *ᵥ w), fun a ha => by rw [hvalue a, hφS a ha],
    by rw [hvalue c, hφc]⟩

private theorem spT_smul_left (c : K) (a b : Fin r ⊕ Fin r → K) :
    spT (c • a) b = c • spT a b := by
  simp only [spT, Matrix.mulVec_smul, Matrix.vecMulVec_smul]

private theorem spT_smul_right (c : K) (a b : Fin r ⊕ Fin r → K) :
    spT b (c • a) = c • spT b a := by
  simp only [spT, Matrix.smul_vecMulVec]

private theorem spN_smul_self (κ : K) (v : Fin r ⊕ Fin r → K) :
    spN v (κ • v) = (2 * κ) • spT v v := by
  rw [spN, spT_smul_left, spT_smul_right, ← add_smul, ← two_mul]

private theorem spT_self_mul_spN_of_orth {v c : Fin r ⊕ Fin r → K} (hvc : spForm v c = 0) :
    spT v v * spN v c = 0 := by
  rw [spN, Matrix.mul_add, spT_mul_spT, spT_mul_spT, spForm_self, spForm_swap v c, hvc,
    neg_zero]
  simp

private theorem spN_mul_spN_of_orth {v c c' : Fin r ⊕ Fin r → K} (hvc : spForm v c = 0)
    (hvc' : spForm v c' = 0) : spN v c * spN v c' = spForm c' c • spT v v := by
  rw [spN, spN, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [spT_mul_spT, hvc, spForm_self, spForm_swap v c', hvc', neg_zero, zero_smul,
    zero_add, add_zero]

private theorem spN_mul_spN_of_orth' {v c c' : Fin r ⊕ Fin r → K} (hvc : spForm v c = 0)
    (hvc' : spForm v c' = 0) : spN v c' * spN v c = spForm c c' • spT v v :=
  spN_mul_spN_of_orth hvc' hvc

private theorem spT_self_ne_zero {v : Fin r ⊕ Fin r → K} (hv : v ≠ 0) : spT v v ≠ 0 := by
  obtain ⟨y, hy⟩ : ∃ y, spForm y v ≠ 0 := by
    obtain ⟨y, -, hy⟩ := exists_spForm_sep (S := (∅ : Set (Fin r ⊕ Fin r → K))) (c := v)
      (by simpa using hv)
    exact ⟨y, by rw [spForm_swap, hy]; norm_num⟩
  intro h
  have h2 : spT v v *ᵥ y = 0 := by rw [h, Matrix.zero_mulVec]
  rw [spT_mulVec] at h2
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact hy h3
  · exact hv h3

private theorem spN_mul_spN_neg {v c f : Fin r ⊕ Fin r → K} (hvc : spForm v c = 0)
    (hvf : spForm v f = 0) (hcf : spForm c f = 1) : spN v c * spN v f = -spT v v := by
  rw [spN_mul_spN_of_orth hvc hvf, spForm_swap c f, hcf, neg_one_smul]

private theorem spN_mul_spN_pos {v c f : Fin r ⊕ Fin r → K} (hvc : spForm v c = 0)
    (hvf : spForm v f = 0) (hcf : spForm c f = 1) : spN v f * spN v c = spT v v := by
  rw [spN_mul_spN_of_orth' hvc hvf, hcf, one_smul]

private theorem heis_hyps {v c f : Fin r ⊕ Fin r → K} (hv : v ≠ 0) (hvc : spForm v c = 0)
    (hvf : spForm v f = 0) (hcf : spForm c f = 1) (h2 : (2 : K) ≠ 0) :
    spN v c * spN v f * spN v c = 0 ∧ spN v f * spN v c * spN v f = 0 ∧
      spN v c * spN v f ≠ 0 ∧ spN v c * spN v f ≠ spN v f * spN v c := by
  have hT : spT v v ≠ 0 := spT_self_ne_zero hv
  have h12 := spN_mul_spN_neg hvc hvf hcf
  have h21 := spN_mul_spN_pos hvc hvf hcf
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h12, Matrix.neg_mul, spT_self_mul_spN_of_orth hvc, neg_zero]
  · rw [h21, spT_self_mul_spN_of_orth hvf]
  · rw [h12]
    exact neg_ne_zero.mpr hT
  · rw [h12, h21]
    intro h
    have hz : (2 : K) • spT v v = 0 := by
      rw [two_smul]
      exact neg_eq_iff_add_eq_zero.mp h
    rcases smul_eq_zero.mp hz with h0 | h0
    · exact absurd h0 h2
    · exact hT h0

private theorem exists_orth_notMem_span (hr : 2 ≤ r) {v : Fin r ⊕ Fin r → K} (hv : v ≠ 0) :
    ∃ e : Fin r ⊕ Fin r → K, spForm v e = 0 ∧ e ∉ Submodule.span K {v} := by
  classical
  obtain ⟨y, -, hy⟩ := exists_spForm_sep (S := (∅ : Set (Fin r ⊕ Fin r → K))) (c := v)
    (by simpa using hv)
  let φ : (Fin r ⊕ Fin r → K) →ₗ[K] K :=
    { toFun := fun z => spForm v z
      map_add' := by intro a b; simp [spForm, Matrix.mulVec_add, dotProduct_add]
      map_smul' := by
        intro c a
        simp [spForm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] }
  have hφ : ∀ z, φ z = spForm v z := fun _ => rfl
  have hφy : φ y = 1 := by rw [hφ]; exact hy
  have hφne : φ ≠ 0 := fun h0 => by rw [h0] at hφy; exact one_ne_zero hφy.symm
  have hfin : Module.finrank K (LinearMap.ker φ) + 1 = Module.finrank K (Fin r ⊕ Fin r → K) :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hφne
  have hV : Module.finrank K (Fin r ⊕ Fin r → K) = 2 * r := by
    rw [Module.finrank_pi, Fintype.card_sum, Fintype.card_fin]
    omega
  have hle : Submodule.span K {v} ≤ LinearMap.ker φ := by
    rw [Submodule.span_le]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha, SetLike.mem_coe, LinearMap.mem_ker, hφ]
    exact spForm_self v
  have hlt : Module.finrank K (Submodule.span K {v}) < Module.finrank K (LinearMap.ker φ) := by
    rw [finrank_span_singleton hv]
    omega
  obtain ⟨-, e, he1, he2⟩ :=
    SetLike.lt_iff_le_and_exists.mp (Submodule.lt_of_le_of_finrank_lt_finrank hle hlt)
  exact ⟨e, by rw [← hφ]; exact LinearMap.mem_ker.mp he1, he2⟩

theorem unipSp_congr {N N' : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (h : N = N')
    (hs : Nᵀ * formJ r K + formJ r K * N = 0) (hN : N * N = 0)
    (hs' : N'ᵀ * formJ r K + formJ r K * N' = 0) (hN' : N' * N' = 0) :
    unipSp N hs hN = unipSp N' hs' hN' := by
  subst h
  rfl

theorem good_unipSp_spN [Finite K] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p]
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) (hr : 2 ≤ r)
    {v u : Fin r ⊕ Fin r → K} (hv : v ≠ 0) (hu : u ≠ 0) (hvu : spForm v u = 0) :
    orderOf (proj r K (unipSp (spN v u) (isSp_spN v u) (spN_mul_self hvu))) = p ∧
      IsSpecialGood p (proj r K (unipSp (spN v u) (isSp_spN v u) (spN_mul_self hvu))) := by
  classical
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := hp.two_le
    omega
  by_cases hin : u ∈ Submodule.span K {v}
  ·
    obtain ⟨κ, hκ⟩ := Submodule.mem_span_singleton.mp hin
    have hκ0 : κ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hκ
      exact hu hκ.symm
    obtain ⟨e, hve, hespan⟩ := exists_orth_notMem_span hr hv
    obtain ⟨f, hf1, hf2⟩ := exists_spForm_sep (S := {v}) (c := e) hespan
    have hvf : spForm v f = 0 := hf1 v (Set.mem_singleton v)
    obtain ⟨h121, h212, h12, hPQ⟩ := heis_hyps hv hve hvf hf2 h2
    have hEq : (-κ) • (spN v e * spN v f - spN v f * spN v e) = spN v u := by
      rw [spN_mul_spN_neg hve hvf hf2, spN_mul_spN_pos hve hvf hf2, ← hκ, spN_smul_self]
      module
    have hs' : ((-κ) • (spN v e * spN v f - spN v f * spN v e))ᵀ * formJ r K +
        formJ r K * ((-κ) • (spN v e * spN v f - spN v f * spN v e)) = 0 := by
      rw [hEq]
      exact isSp_spN v u
    have hN' : ((-κ) • (spN v e * spN v f - spN v f * spN v e)) *
        ((-κ) • (spN v e * spN v f - spN v f * spN v e)) = 0 := by
      rw [hEq]
      exact spN_mul_self hvu
    have key := good_unipSp_center hp hp2 hK h3 (by omega) (isSp_spN v e) (isSp_spN v f)
      (spN_mul_self hve) (spN_mul_self hvf) h121 h212 h12 hPQ (neg_ne_zero.mpr hκ0) hs' hN'
    have hcongr := unipSp_congr hEq hs' hN' (isSp_spN v u) (spN_mul_self hvu)
    exact ⟨by rw [← hcongr]; exact key.1, by rw [← hcongr]; exact key.2⟩
  ·
    obtain ⟨f, hf1, hf2⟩ := exists_spForm_sep (S := {v}) (c := u) hin
    have hvf : spForm v f = 0 := hf1 v (Set.mem_singleton v)
    obtain ⟨h121, h212, h12, hPQ⟩ := heis_hyps hv hvu hvf hf2 h2
    exact good_unipSp hp hp2 hK h3 (by omega) (isSp_spN v u) (isSp_spN v f)
      (spN_mul_self hvu) (spN_mul_self hvf) h121 h212 h12 hPQ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
