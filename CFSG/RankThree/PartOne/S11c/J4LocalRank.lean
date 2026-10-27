module

public import CFSG.RankThree.PartOne.S11c.J4Abstract

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LinearAlgebra Module Subgroup Matrix
open scoped commutatorElement Matrix

section Minor

theorem finrank_ker_vecMul_add_le_of_minor {K : Type*} [Field K] {n k : ℕ}
    (N : Matrix (Fin n) (Fin n) K) (ps qs : Fin k → Fin n) (B : Matrix (Fin k) (Fin k) K)
    (hB : N.submatrix ps qs * B = 1) :
    finrank K (LinearMap.ker (Matrix.vecMulLinear N)) + k ≤ n := by
  set f : (Fin n → K) →ₗ[K] (Fin n → K) := Matrix.vecMulLinear N with hf
  set v : Fin k → (Fin n → K) := fun a => f (Pi.single (ps a) 1) with hv
  have hli : LinearIndependent K v := by
    refine Fintype.linearIndependent_iff.mpr ?_
    intro c hc a
    have h1 : ∀ b : Fin k, ∑ a', c a' * N (ps a') (qs b) = 0 := by
      intro b
      have := congrFun hc (qs b)
      simp only [hv, hf, Matrix.vecMulLinear_apply, Matrix.single_vecMul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, one_mul, Pi.zero_apply] at this
      exact this
    have h2 : c ᵥ* (N.submatrix ps qs) = 0 := by
      funext b
      simpa [Matrix.vecMul, dotProduct, Matrix.submatrix_apply] using h1 b
    have h3 : c = 0 := by
      calc c = c ᵥ* (N.submatrix ps qs * B) := by rw [hB, Matrix.vecMul_one]
        _ = (c ᵥ* (N.submatrix ps qs)) ᵥ* B := by rw [Matrix.vecMul_vecMul]
        _ = 0 := by rw [h2, Matrix.zero_vecMul]
    exact congrFun h3 a
  have hspan : Submodule.span K (Set.range v) ≤ LinearMap.range f := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨_, rfl⟩
  have h4 : k ≤ finrank K (LinearMap.range f) := by
    have := Submodule.finrank_mono hspan
    rwa [finrank_span_eq_card hli, Fintype.card_fin] at this
  have h5 := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at h5
  omega

end Minor

section Local

variable {J : Type*} [Group J] [Finite J] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

omit [Finite J] [FiniteDimensional (ZMod 2) V] in
theorem centralFixed_conj (ρ : Representation (ZMod 2) J V) (g c : J) :
    centralFixed ρ (c * g * c⁻¹) = (centralFixed ρ g).map (repEquiv ρ c : V →ₗ[ZMod 2] V) := by
  ext v
  simp only [centralFixed, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
    sub_eq_zero, Submodule.mem_map]
  constructor
  · intro h
    refine ⟨ρ c⁻¹ v, ?_, ?_⟩
    · have h1 := congrArg (ρ c⁻¹) h
      rw [← Module.End.mul_apply, ← map_mul] at h1
      have e : c⁻¹ * (c * g * c⁻¹) = g * c⁻¹ := by group
      rw [e, map_mul, Module.End.mul_apply] at h1
      exact h1
    · change ρ c (ρ c⁻¹ v) = v
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  · rintro ⟨w, hw, rfl⟩
    change ρ (c * g * c⁻¹) (ρ c w) = ρ c w
    rw [← Module.End.mul_apply, ← map_mul]
    have : c * g * c⁻¹ * c = c * g := by group
    rw [this, map_mul, Module.End.mul_apply, hw]

omit [Finite J] [FiniteDimensional (ZMod 2) V] in
theorem finrank_centralFixed_conj (ρ : Representation (ZMod 2) J V) (g c : J) :
    finrank (ZMod 2) (centralFixed ρ (c * g * c⁻¹)) = finrank (ZMod 2) (centralFixed ρ g) := by
  rw [centralFixed_conj]
  exact LinearEquiv.finrank_map_eq (repEquiv ρ c) _

omit [Finite J] in
theorem two_mul_finrank_centralFixed_le (ρ : Representation (ZMod 2) J V) (g n : J) :
    2 * finrank (ZMod 2) (centralFixed ρ g) ≤
      finrank (ZMod 2) (centralFixed ρ (g * n * g⁻¹ * n⁻¹)) + finrank (ZMod 2) V := by
  set F := centralFixed ρ g with hF
  set F' := F.map (repEquiv ρ n : V →ₗ[ZMod 2] V) with hF'
  have hX : F ⊓ F' ≤ centralFixed ρ (g * n * g⁻¹ * n⁻¹) := by
    intro v hv
    obtain ⟨hv1, w, hw, hwv⟩ := Submodule.mem_inf.mp hv
    have hv1' : ρ g v = v := by
      simpa [hF, centralFixed, sub_eq_zero] using hv1
    have hw' : ρ g w = w := by
      simpa [hF, centralFixed, sub_eq_zero] using hw
    have hwv' : ρ n w = v := hwv
    have hw'' : ρ g⁻¹ w = w := by
      have := congrArg (ρ g⁻¹) hw'
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
      exact this.symm
    simp only [centralFixed, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero]
    have e1 : ρ n⁻¹ v = w := by
      rw [← hwv', ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    rw [map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      Module.End.mul_apply, e1, hw'', hwv', hv1']
  have h1 := Submodule.finrank_mono hX
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq F F'
  have h3 : finrank (ZMod 2) ↥(F ⊔ F') ≤ finrank (ZMod 2) V := Submodule.finrank_le _
  have h4 : finrank (ZMod 2) F' = finrank (ZMod 2) F := LinearEquiv.finrank_map_eq _ _
  omega

variable (ρ : Representation (ZMod 2) J V) (hV : finrank (ZMod 2) V = 112)
  (H N S0 : Subgroup J) (hNH : N ≤ H)
  (hNnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
  (hCN : ∀ h ∈ H, (∀ n ∈ N, h * n = n * h) → h ∈ N) (n₁ n₂ : J)
  (hcov : ∀ n ∈ N, n ≠ 1 → ∃ h ∈ H, n = h * n₁ * h⁻¹ ∨ n = h * n₂ * h⁻¹)
  (hr₁ : finrank (ZMod 2) (centralFixed ρ n₁) ≤ 86)
  (hr₂ : finrank (ZMod 2) (centralFixed ρ n₂) ≤ 86)
include hV hNnorm hCN hcov hr₁ hr₂

omit [Finite J] in
theorem finrank_centralFixed_le_ninety_nine {g : J} (hgH : g ∈ H) (hg : g ≠ 1) :
    finrank (ZMod 2) (centralFixed ρ g) ≤ 99 := by
  have hN86 : ∀ n ∈ N, n ≠ 1 → finrank (ZMod 2) (centralFixed ρ n) ≤ 86 := by
    intro n hn hn1
    obtain ⟨h, -, hh⟩ := hcov n hn hn1
    rcases hh with rfl | rfl
    · rw [finrank_centralFixed_conj]; exact hr₁
    · rw [finrank_centralFixed_conj]; exact hr₂
  by_cases hgN : g ∈ N
  · have := hN86 g hgN hg
    omega
  · have hnc : ¬ ∀ n ∈ N, g * n = n * g := fun h => hgN (hCN g hgH h)
    push Not at hnc
    obtain ⟨n, hn, hgn⟩ := hnc
    have hk : g * n * g⁻¹ * n⁻¹ ∈ N := mul_mem (hNnorm g hgH n hn) (inv_mem hn)
    have hk1 : g * n * g⁻¹ * n⁻¹ ≠ 1 := by
      intro h
      apply hgn
      have h' : g * n * g⁻¹ = n := by
        simpa using congrArg (· * n) h
      calc g * n = g * n * g⁻¹ * g := by group
        _ = n * g := by rw [h']
    have := hN86 _ hk hk1
    have h2 := two_mul_finrank_centralFixed_le ρ g n
    omega

theorem hrank_of_local (S0 : Subgroup J) (hS0p : IsPGroup 2 S0) (hS0idx : ¬ 2 ∣ S0.index)
    (hS0H : S0 ≤ H) (g : J) (hg : g ≠ 1) (hpg : IsPGroup 2 (Subgroup.zpowers g)) :
    finrank (ZMod 2) (centralFixed ρ g) ≤ 99 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_conj_map_le_of_isPGroup (p := 2) S0 hS0p hS0idx (Subgroup.zpowers g) hpg
  have hmem : c * g * c⁻¹ ∈ S0 :=
    hc ⟨g, Subgroup.mem_zpowers g, by simp [MulAut.conj_apply]⟩
  have hne : c * g * c⁻¹ ≠ 1 := by
    intro h
    apply hg
    have : g = c⁻¹ * (c * g * c⁻¹) * c := by group
    rw [this, h]
    group
  have h1 := finrank_centralFixed_le_ninety_nine ρ hV H N hNnorm hCN n₁ n₂ hcov hr₁ hr₂
    (hS0H hmem) hne
  rwa [finrank_centralFixed_conj] at h1

end Local

end CFSG.RankThree.PartOne
