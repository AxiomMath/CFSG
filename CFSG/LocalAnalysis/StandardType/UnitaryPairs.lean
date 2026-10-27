module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSUFrame
public import CFSG.LocalAnalysis.StandardType.UnitaryCenterScalar
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.RankThree.PartOne.S15K.CentralCover

public section

namespace CFSG.StandardType

namespace UnitaryPairs

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits InnerDiagSU UFusion

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ} {G : Type*} [Group G]

theorem exists_scalar_of_mem_suInducedPairs_one (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n)) {B : GL (Fin n) F}
    (h : ((1 : G), B) ∈ suInducedPairs ψ) :
    ∃ c : Fˣ, B = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  obtain ⟨hB, hconj⟩ := h
  have hperf : Group.IsPerfect (SU (unitaryInvolution F 2 f) n) :=
    (isQuasisimple_SU (p := 2) (f := f) hF hn hnq).1
  have hmap : ∀ u : SU (unitaryInvolution F 2 f) n,
      ψ (conjSU B hB u) = ψ ((MonoidHom.id (SU (unitaryInvolution F 2 f) n)) u) := by
    intro u
    have h1 := hconj u
    rw [one_mul, inv_one, mul_one] at h1
    simpa using h1.symm
  have hEq := CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq ψ hker hperf
    (conjSU B hB) (MonoidHom.id (SU (unitaryInvolution F 2 f) n)) hmap
  have hcomm : ∀ u : SU (unitaryInvolution F 2 f) n,
      B * (u : GL (Fin n) F) = (u : GL (Fin n) F) * B := by
    intro u
    have h1 : B * (u : GL (Fin n) F) * B⁻¹ = (u : GL (Fin n) F) := by
      have := congrArg (fun v : SU (unitaryInvolution F 2 f) n => (v : GL (Fin n) F)) (hEq u)
      rwa [coe_conjSU] at this
    calc B * (u : GL (Fin n) F) = B * (u : GL (Fin n) F) * B⁻¹ * B := by group
      _ = (u : GL (Fin n) F) * B := by rw [h1]
  exact UnitaryCenter.exists_scalar_of_commute_SU hF hf hn hcomm

theorem exists_scalar_pow_of_mem_suInducedPairs (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n)) {y : G} {A : GL (Fin n) F}
    (h : (y, A) ∈ suInducedPairs ψ) {k : ℕ} (hk : y ^ k = 1) :
    ∃ c : Fˣ, A ^ k = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  have hmem : ((1 : G), A ^ k) ∈ suInducedPairs ψ := by
    have h' := (suInducedPairs ψ).pow_mem h k
    simpa only [Prod.pow_mk, hk] using h'
  exact exists_scalar_of_mem_suInducedPairs_one hF hf hn hnq hker hmem

theorem exists_scalar_commutator_of_mem_suInducedPairs (hF : Nat.card F = (2 ^ f) ^ 2)
    (hf : 1 ≤ f) (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2))
    {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n)) {y₁ y₂ : G}
    {A₁ A₂ : GL (Fin n) F} (h₁ : (y₁, A₁) ∈ suInducedPairs ψ) (h₂ : (y₂, A₂) ∈ suInducedPairs ψ)
    (hy : y₁ * y₂ = y₂ * y₁) :
    ∃ c : Fˣ, A₁ * A₂ * A₁⁻¹ * A₂⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  have hmem := (suInducedPairs ψ).mul_mem
    ((suInducedPairs ψ).mul_mem ((suInducedPairs ψ).mul_mem h₁ h₂)
      ((suInducedPairs ψ).inv_mem h₁)) ((suInducedPairs ψ).inv_mem h₂)
  have h1comp : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ = 1 := by
    rw [hy, mul_inv_cancel_right, mul_inv_cancel]
  have hmem' : ((1 : G), A₁ * A₂ * A₁⁻¹ * A₂⁻¹) ∈ suInducedPairs ψ := by
    simpa only [Prod.mk_mul_mk, Prod.inv_mk, h1comp] using hmem
  exact exists_scalar_of_mem_suInducedPairs_one hF hf hn hnq hker hmem'

theorem mem_centralizer_of_mem_suInducedPairs_scalar {ψ : SU (unitaryInvolution F 2 f) n →* G}
    {y : G} {c : Fˣ} (h : (y, Matrix.GeneralLinearGroup.scalar (Fin n) c) ∈ suInducedPairs ψ) :
    y ∈ Subgroup.centralizer (ψ.range : Set G) := by
  obtain ⟨hA, hconj⟩ := h
  have hcu : ∀ u, conjSU (Matrix.GeneralLinearGroup.scalar (Fin n) c) hA u = u := by
    intro u
    apply Subtype.ext
    rw [coe_conjSU, Matrix.GeneralLinearGroup.scalar_commute]
    group
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨u, rfl⟩
  have h2 := hconj u
  rw [hcu u] at h2
  calc ψ u * y = y * ψ u * y⁻¹ * y := by rw [h2]
    _ = y * ψ u := by group

theorem norm_eq_one_of_isJUnitary_scalar (hn : 1 ≤ n) {c : Fˣ}
    (h : IsJUnitary (unitaryInvolution F 2 f) (Matrix.GeneralLinearGroup.scalar (Fin n) c)) :
    c ^ (2 ^ f + 1) = 1 := by
  unfold IsJUnitary at h
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, conjTr,
    Matrix.diagonal_map (map_zero (unitaryInvolution F 2 f)), Matrix.diagonal_transpose] at h
  let i : Fin n := ⟨0, by omega⟩
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) F => M i (Fin.rev i)) h
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, antidiag, Matrix.of_apply, Fin.rev_rev,
    ↓reduceIte, mul_one] at hentry
  have hσc : unitaryInvolution F 2 f (c : F) * (c : F) = 1 := hentry
  have hpow : (c : F) ^ (2 ^ f + 1) = 1 := by
    calc (c : F) ^ (2 ^ f + 1) = (c : F) ^ (2 ^ f) * (c : F) := by rw [pow_succ]
      _ = unitaryInvolution F 2 f (c : F) * (c : F) := by rw [unitaryInvolution_apply]
      _ = 1 := hσc
  exact Units.ext (by simpa using hpow)

theorem one_scalar_mem_suInducedPairs (ψ : SU (unitaryInvolution F 2 f) n →* G) {c : Fˣ}
    (hc : c ^ (2 ^ f + 1) = 1) :
    ((1 : G), Matrix.GeneralLinearGroup.scalar (Fin n) c) ∈ suInducedPairs ψ := by
  rw [mem_suInducedPairs]
  have hσc : unitaryInvolution F 2 f (c : F) * (c : F) = 1 := by
    calc unitaryInvolution F 2 f (c : F) * (c : F) = (c : F) ^ (2 ^ f) * (c : F) := by
          rw [unitaryInvolution_apply]
      _ = (c : F) ^ (2 ^ f + 1) := by rw [pow_succ]
      _ = 1 := by
          have := congrArg (fun u : Fˣ => (u : F)) hc
          simpa using this
  have hA : IsJUnitary (unitaryInvolution F 2 f) (Matrix.GeneralLinearGroup.scalar (Fin n) c) := by
    unfold IsJUnitary
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, conjTr,
      Matrix.diagonal_map (map_zero (unitaryInvolution F 2 f)), Matrix.diagonal_transpose]
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [mul_assoc, mul_comm (antidiag n i j) (c : F), ← mul_assoc, hσc, one_mul]
  refine ⟨hA, ?_⟩
  intro u
  have hcu : conjSU (Matrix.GeneralLinearGroup.scalar (Fin n) c) hA u = u := by
    apply Subtype.ext
    rw [coe_conjSU, Matrix.GeneralLinearGroup.scalar_commute]
    group
  rw [hcu]
  simp

theorem not_three_dvd_two_pow_add_one_of_even {f : ℕ} (hf : Even f) : ¬ 3 ∣ 2 ^ f + 1 := by
  obtain ⟨k, rfl⟩ := hf
  have h : 4 ^ k ≡ 1 [MOD 3] := by
    simpa using (Nat.ModEq.pow k (show 4 ≡ 1 [MOD 3] by decide))
  have h2 : 2 ^ (k + k) = 4 ^ k := by rw [← two_mul, pow_mul]; norm_num
  rw [h2]
  intro hd
  have h0 : 4 ^ k + 1 ≡ 0 [MOD 3] := Nat.modEq_zero_iff_dvd.2 hd
  have h3 : 4 ^ k + 1 ≡ 1 + 1 [MOD 3] := Nat.ModEq.add_right 1 h
  have h4 : (0 : ℕ) ≡ 1 + 1 [MOD 3] := h0.symm.trans h3
  revert h4
  decide

theorem exists_cube_root_norm_one (hfe : Even f) {c : Fˣ} (hc : c ^ (2 ^ f + 1) = 1) :
    ∃ d : Fˣ, d ^ 3 = c ∧ d ^ (2 ^ f + 1) = 1 := by
  have hnot : ¬ 3 ∣ 2 ^ f + 1 := not_three_dvd_two_pow_add_one_of_even hfe
  have hcop : Nat.Coprime 3 (2 ^ f + 1) := (Nat.prime_three.coprime_iff_not_dvd).mpr hnot
  obtain ⟨m, _hm_lt, hm⟩ :=
    Nat.exists_mul_mod_eq_one_of_coprime hcop (by have := Nat.one_le_two_pow (n := f); omega)
  refine ⟨c ^ m, ?_, ?_⟩
  · have h3m : 3 * m = (2 ^ f + 1) * (3 * m / (2 ^ f + 1)) + 1 := by
      have h := Nat.div_add_mod (3 * m) (2 ^ f + 1)
      rw [hm] at h
      omega
    calc (c ^ m) ^ 3 = c ^ (3 * m) := by rw [← pow_mul, mul_comm m 3]
      _ = c ^ ((2 ^ f + 1) * (3 * m / (2 ^ f + 1)) + 1) := by
          nth_rewrite 1 [h3m]
          rfl
      _ = (c ^ (2 ^ f + 1)) ^ (3 * m / (2 ^ f + 1)) * c := by rw [pow_add, pow_one, pow_mul]
      _ = c := by rw [hc, one_pow, one_mul]
  · rw [← pow_mul, mul_comm m (2 ^ f + 1), pow_mul, hc, one_pow]

theorem commute_of_mem_suInducedPairs_of_perfect {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n))
    {Γ : Subgroup (SU (unitaryInvolution F 2 f) n)} (hperf : commutator ↥Γ = ⊤) {y : G}
    {A : GL (Fin n) F} (hA : (y, A) ∈ suInducedPairs ψ) (hy : ∀ γ ∈ Γ, y * ψ γ = ψ γ * y) :
    ∀ γ ∈ Γ, A * (γ : GL (Fin n) F) = (γ : GL (Fin n) F) * A := by
  obtain ⟨hAJ, hconj⟩ := hA
  have hΓ : Group.IsPerfect ↥Γ := ⟨hperf⟩
  let τ₁ : ↥Γ →* SU (unitaryInvolution F 2 f) n :=
    (conjSU A hAJ).comp (Subgroup.subtype Γ)
  have hmap : ∀ γ : ↥Γ, ψ (τ₁ γ) = ψ ((Subgroup.subtype Γ) γ) := by
    intro γ
    have h1 := hconj (γ : SU (unitaryInvolution F 2 f) n)
    have h2 := hy (γ : SU (unitaryInvolution F 2 f) n) γ.2
    rw [h2, mul_assoc, mul_inv_cancel, mul_one] at h1
    exact h1.symm
  have hEq := CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq ψ hker hΓ τ₁
    (Subgroup.subtype Γ) hmap
  intro γ hγ
  have h1 : A * (γ : GL (Fin n) F) * A⁻¹ = (γ : GL (Fin n) F) := by
    have h := congrArg (fun v : SU (unitaryInvolution F 2 f) n => (v : GL (Fin n) F))
      (hEq ⟨γ, hγ⟩)
    change (conjSU A hAJ γ : GL (Fin n) F) = (γ : GL (Fin n) F) at h
    rwa [coe_conjSU] at h
  calc A * (γ : GL (Fin n) F) = A * (γ : GL (Fin n) F) * A⁻¹ * A := by group
    _ = (γ : GL (Fin n) F) * A := by rw [h1]

end UnitaryPairs

end CFSG.StandardType
