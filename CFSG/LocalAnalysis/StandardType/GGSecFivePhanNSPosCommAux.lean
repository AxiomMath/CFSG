module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.UnitaryCenterScalar
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.LieType.Steinberg.CentralExt.SUThree
import CFSG.RankThree.PartOne.S15K.CentralCover
import CFSG.GroupTheory.ElemAbelianClosure
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg
  CFSG.ClassicalGroups.Unitary CFSG.RankThree.PartOne.S15K

open scoped MatrixGroups

@[expose] def ggNSPosPF_commutator {K : Type} [Field K] {n : ℕ} (g₁ g₂ : GL (Fin n) K) :
    GL (Fin n) K :=
  g₁ * g₂ * g₁⁻¹ * g₂⁻¹

theorem ggNSPosPF_commutator_eq_one_iff {K : Type} [Field K] {n : ℕ} (g₁ g₂ : GL (Fin n) K) :
    ggNSPosPF_commutator g₁ g₂ = 1 ↔ g₁ * g₂ = g₂ * g₁ := by
  rw [ggNSPosPF_commutator]
  constructor
  · intro h
    have := congrArg (· * (g₂ * g₁)) h
    simpa [mul_assoc] using this
  · intro h
    rw [h]
    simp [mul_assoc]

theorem ggNSPosPF_mul_comm_of_commutator_eq_one {K : Type} [Field K] {n : ℕ}
    (g₁ g₂ : GL (Fin n) K) (h : ggNSPosPF_commutator g₁ g₂ = 1) : g₁ * g₂ = g₂ * g₁ :=
  (ggNSPosPF_commutator_eq_one_iff g₁ g₂).mp h

theorem ggNSPosPF_exists_scalar_of_commute_SUid {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} (hF : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hn : 3 ≤ n) {N : GL (Fin n) K}
    (hN : ∀ u : Su K 2 f n, N * (u : GL (Fin n) K) = (u : GL (Fin n) K) * N) :
    ∃ c : Kˣ, N = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  have hUFD : UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hSUeq : unitarySU 2 f K n = SUid (unitaryInvolution K 2 f) n := by
    rw [SUid_eq_statedSU (p := 2) (f := f) hF n]
  have hcomm : ∀ g ∈ unitarySU 2 f K n, N * g = g * N := by
    intro g hg
    exact hN ⟨g, by rwa [hSUeq] at hg⟩
  obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd (show 2 ^ f + 1 ≠ 1 by
    have := Nat.one_le_two_pow (n := f); omega)
  have hNmem := TableBUE.mem_scalars_of_commute (n := f) (d := n) (p := q) hUFD hqprime hqdvd hcomm
  rw [CFSG.Assembly.largeEvenScalars_def] at hNmem
  obtain ⟨c, hc⟩ := hNmem
  exact ⟨c, hc.symm⟩

private theorem ggNSPosPF_one_le_f {K : Type} [Field K] [Finite K] {f : ℕ}
    (hF : Nat.card K = (2 ^ f) ^ 2) : 1 ≤ f := by
  rcases Nat.eq_zero_or_pos f with hf | hf
  · exfalso
    subst hf
    have h1 : Nat.card K = 1 := by simpa using hF
    have := Finite.one_lt_card (α := K)
    omega
  · exact hf

private theorem ggNSPosPF_conjTr_inv {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}
    (g : GL (Fin n) K) :
    conjTr σ (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      (conjTr σ ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))⁻¹ := by
  have h : conjTr σ (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
      conjTr σ ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← conjTr_mul]
    have h1 : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h1, conjTr_one]
  exact (Matrix.inv_eq_left_inv h).symm

private theorem ggNSPosPF_ggIsUnitaryMat_mul {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} {g₁ g₂ : GL (Fin n) K}
    (h₁ : ggIsUnitaryMat (p := 2) (f := f) g₁) (h₂ : ggIsUnitaryMat (p := 2) (f := f) g₂) :
    ggIsUnitaryMat (p := 2) (f := f) (g₁ * g₂) := by
  unfold ggIsUnitaryMat at h₁ h₂ ⊢
  rw [Units.val_mul, conjTr_mul]
  calc conjTr (unitaryInvolution K 2 f) (g₂ : Matrix (Fin n) (Fin n) K) *
        conjTr (unitaryInvolution K 2 f) (g₁ : Matrix (Fin n) (Fin n) K) *
          ((g₁ : Matrix (Fin n) (Fin n) K) * (g₂ : Matrix (Fin n) (Fin n) K))
      = conjTr (unitaryInvolution K 2 f) (g₂ : Matrix (Fin n) (Fin n) K) *
          (conjTr (unitaryInvolution K 2 f) (g₁ : Matrix (Fin n) (Fin n) K) *
            (g₁ : Matrix (Fin n) (Fin n) K)) *
          (g₂ : Matrix (Fin n) (Fin n) K) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h₁, Matrix.mul_one, h₂]

private theorem ggNSPosPF_ggIsUnitaryMat_inv {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} {g : GL (Fin n) K} (hg : ggIsUnitaryMat (p := 2) (f := f) g) :
    ggIsUnitaryMat (p := 2) (f := f) g⁻¹ := by
  unfold ggIsUnitaryMat at hg ⊢
  rw [Matrix.coe_units_inv]
  have h1 : conjTr (unitaryInvolution K 2 f) (g : Matrix (Fin n) (Fin n) K) =
      ((g : Matrix (Fin n) (Fin n) K))⁻¹ := by
    have hgg : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc conjTr (unitaryInvolution K 2 f) (g : Matrix (Fin n) (Fin n) K)
        = conjTr (unitaryInvolution K 2 f) (g : Matrix (Fin n) (Fin n) K) *
            ((g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
          rw [hgg, Matrix.mul_one]
      _ = (conjTr (unitaryInvolution K 2 f) (g : Matrix (Fin n) (Fin n) K) *
            (g : Matrix (Fin n) (Fin n) K)) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [Matrix.mul_assoc]
      _ = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hg, Matrix.one_mul]
      _ = ((g : Matrix (Fin n) (Fin n) K))⁻¹ := by rw [Matrix.coe_units_inv]
  have h2 : conjTr (unitaryInvolution K 2 f)
        (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
      conjTr (unitaryInvolution K 2 f) ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← conjTr_mul]
    have h3 : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h3, conjTr_one]
  rw [h1] at h2
  rw [Matrix.coe_units_inv] at h2
  exact h2

private theorem ggNSPosPF_ggIsUnitaryMat_pow {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} {g : GL (Fin n) K} (hg : ggIsUnitaryMat (p := 2) (f := f) g) (k : ℕ) :
    ggIsUnitaryMat (p := 2) (f := f) (g ^ k) := by
  induction k with
  | zero =>
      unfold ggIsUnitaryMat
      rw [pow_zero, Units.val_one, conjTr_one, Matrix.one_mul]
  | succ k ih => rw [pow_succ]; exact ggNSPosPF_ggIsUnitaryMat_mul ih hg

private noncomputable def ggNSPosPF_conjSUid {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} (hF : Nat.card K = (2 ^ f) ^ 2) {z : GL (Fin n) K}
    (hz : ggIsUnitaryMat (p := 2) (f := f) z) : Su K 2 f n →* Su K 2 f n where
  toFun x := ⟨z * (x : GL (Fin n) K) * z⁻¹,
    conj_mem_SUid (isUnitaryInvolution_unitaryInvolution hF).invol hz x.2⟩
  map_one' := by
    apply Subtype.ext
    show z * (1 : GL (Fin n) K) * z⁻¹ = 1
    group
  map_mul' x y := by
    apply Subtype.ext
    show z * ((x * y : Su K 2 f n) : GL (Fin n) K) * z⁻¹ =
      (z * (x : GL (Fin n) K) * z⁻¹) * (z * (y : GL (Fin n) K) * z⁻¹)
    rw [Subgroup.coe_mul]
    group

private theorem ggNSPosPF_scalar_of_conj_psi_trivial {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} {G : Type} [Group G] {ψ : Su K 2 f n →* G}
    (hF : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hn : 4 ≤ n)
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n)) {z : GL (Fin n) K}
    (hz : ggIsUnitaryMat (p := 2) (f := f) z)
    (h : ∀ x : Su K 2 f n, ψ (ggNSPosPF_conjSUid hF hz x) = ψ x) :
    ∃ c : Kˣ, z = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  have hperf : Group.IsPerfect (Su K 2 f n) :=
    isPerfect_SUid (isUnitaryInvolution_unitaryInvolution hF) (by omega)
      (fun h3 => absurd h3 (by omega))
  have heq := eq_of_perfect_of_map_eq ψ hker hperf (ggNSPosPF_conjSUid hF hz) (MonoidHom.id _) h
  have hcomm : ∀ u : Su K 2 f n, z * (u : GL (Fin n) K) = (u : GL (Fin n) K) * z := by
    intro u
    have h1 : (ggNSPosPF_conjSUid hF hz u : GL (Fin n) K) = (u : GL (Fin n) K) :=
      congrArg (fun v : Su K 2 f n => (v : GL (Fin n) K)) (heq u)
    have h1' : z * (u : GL (Fin n) K) * z⁻¹ = (u : GL (Fin n) K) := h1
    calc z * (u : GL (Fin n) K) = z * (u : GL (Fin n) K) * z⁻¹ * z := by group
      _ = (u : GL (Fin n) K) * z := by rw [h1']
  exact ggNSPosPF_exists_scalar_of_commute_SUid hF hf (by omega) hcomm

private theorem ggNSPosPF_commutator_commute_SU_aux {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ) {b₁ b₂ : G}
    (hb₁ : b₁ ∈ Bs) (hb₂ : b₂ ∈ Bs) {g₁ g₂ : GL (Fin n) K}
    (h₁ : GGInducesUnitary (p := 2) (f := f) ψ b₁ g₁)
    (h₂ : GGInducesUnitary (p := 2) (f := f) ψ b₂ g₂) :
    ∀ u : Su K 2 f n,
      ggNSPosPF_commutator g₁ g₂ * (u : GL (Fin n) K) = (u : GL (Fin n) K) * ggNSPosPF_commutator g₁ g₂ := by
  have hf : 1 ≤ f := ggNSPosPF_one_le_f (K := K) h.card
  have hn : 4 ≤ n := h.four_le
  have hc_uni : ggIsUnitaryMat (p := 2) (f := f) (ggNSPosPF_commutator g₁ g₂) := by
    have h12 := ggNSPosPF_ggIsUnitaryMat_mul h₁.1 h₂.1
    have hA := ggNSPosPF_ggIsUnitaryMat_mul h12 (ggNSPosPF_ggIsUnitaryMat_inv h₁.1)
    have hB := ggNSPosPF_ggIsUnitaryMat_mul hA (ggNSPosPF_ggIsUnitaryMat_inv h₂.1)
    simpa [ggNSPosPF_commutator] using hB
  have hb : b₁ * b₂ = b₂ * b₁ := CFSG.Open.IsElemAbelian.comm (h.bstar.2.1) hb₁ hb₂
  have hpsi : ∀ z : Su K 2 f n, ψ (ggNSPosPF_conjSUid h.card hc_uni z) = ψ z := by
    intro z
    have hB : ggIsUnitaryMat (p := 2) (f := f) (g₂ * g₁) := ggNSPosPF_ggIsUnitaryMat_mul h₂.1 h₁.1
    have hBinv : ggIsUnitaryMat (p := 2) (f := f) (g₂ * g₁)⁻¹ := ggNSPosPF_ggIsUnitaryMat_inv hB
    let x : Su K 2 f n := ⟨(g₂ * g₁)⁻¹ * (z : GL (Fin n) K) * (g₂ * g₁),
      conj_mem_SUid (isUnitaryInvolution_unitaryInvolution h.card).invol hBinv z.2⟩
    have hx : (x : GL (Fin n) K) = (g₂ * g₁)⁻¹ * (z : GL (Fin n) K) * (g₂ * g₁) := rfl
    obtain ⟨y₁, hy₁eq, hy₁ψ⟩ := h₁.2 x
    obtain ⟨y₂, hy₂eq, hy₂ψ⟩ := h₂.2 x
    obtain ⟨y₃, hy₃eq, hy₃ψ⟩ := h₁.2 y₂
    obtain ⟨y₄, hy₄eq, hy₄ψ⟩ := h₂.2 y₁
    have hψeq : ψ y₃ = ψ y₄ := by
      have h3 : ψ y₃ = (b₁ * b₂) * ψ x * (b₁ * b₂)⁻¹ := by
        rw [← hy₃ψ, ← hy₂ψ]; group
      have h4 : ψ y₄ = (b₂ * b₁) * ψ x * (b₂ * b₁)⁻¹ := by
        rw [← hy₄ψ, ← hy₁ψ]; group
      rw [h3, h4, hb]
    have hy₄z : (y₄ : GL (Fin n) K) = (z : GL (Fin n) K) := by
      rw [hy₄eq, hy₁eq, hx]
      group
    have hy₃c : (y₃ : GL (Fin n) K) =
        ggNSPosPF_commutator g₁ g₂ * (z : GL (Fin n) K) * (ggNSPosPF_commutator g₁ g₂)⁻¹ := by
      rw [hy₃eq, hy₂eq, hx]
      unfold ggNSPosPF_commutator
      group
    have hy3eq' : ggNSPosPF_conjSUid h.card hc_uni z = y₃ := Subtype.ext hy₃c.symm
    rw [hy3eq', hψeq, show y₄ = z from Subtype.ext hy₄z]
  obtain ⟨c, hc⟩ := ggNSPosPF_scalar_of_conj_psi_trivial h.card hf hn h.ker hc_uni hpsi
  intro u
  rw [hc, Matrix.GeneralLinearGroup.scalar_commute]

theorem ggNSPosPF_commutator_scalar {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) {b₁ b₂ : G}
    (hb₁ : b₁ ∈ Bs) (hb₂ : b₂ ∈ Bs) {g₁ g₂ : GL (Fin n) K}
    (h₁ : GGInducesUnitary (p := 2) (f := f) ψ b₁ g₁)
    (h₂ : GGInducesUnitary (p := 2) (f := f) ψ b₂ g₂) :
    ∃ z : K, ((ggNSPosPF_commutator g₁ g₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = z • 1 := by
  have hn : 3 ≤ n := by have := h.four_le; omega
  have hf : 1 ≤ f := ggNSPosPF_one_le_f (K := K) h.card
  obtain ⟨c, hc⟩ := ggNSPosPF_exists_scalar_of_commute_SUid (K := K) (f := f) (n := n) h.card hf hn
    (ggNSPosPF_commutator_commute_SU_aux h hb₁ hb₂ h₁ h₂)
  refine ⟨(c : K), ?_⟩
  rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply]

private theorem ggNSPosPF_smul_one_pow {K : Type} [Semiring K] {n : ℕ} (z : K) (k : ℕ) :
    (z • (1 : Matrix (Fin n) (Fin n) K)) ^ k = z ^ k • 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, Matrix.smul_mul, Matrix.one_mul, smul_smul, pow_succ]

private theorem ggNSPosPF_scalar_pow_eq_one {K : Type} [Field K] {n : ℕ} {p : ℕ} (hn : 0 < n) {z : K}
    (h : (z • (1 : Matrix (Fin n) (Fin n) K)) ^ p = 1) : z ^ p = 1 := by
  have h' : z ^ p • (1 : Matrix (Fin n) (Fin n) K) = 1 := by
    rwa [ggNSPosPF_smul_one_pow] at h
  have h00 := congrFun (congrFun h' ⟨0, hn⟩) ⟨0, hn⟩
  simpa using h00

private theorem ggNSPosPF_pow_conj_psi {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} {ψ : Su K 2 f n →* G} {b : G} {g : GL (Fin n) K}
    (h : GGInducesUnitary (p := 2) (f := f) ψ b g) (k : ℕ) (x : Su K 2 f n) :
    ∃ y : Su K 2 f n, (y : GL (Fin n) K) = g ^ k * (x : GL (Fin n) K) * (g ^ k)⁻¹ ∧
      ψ y = b ^ k * ψ x * (b ^ k)⁻¹ := by
  induction k with
  | zero => exact ⟨x, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨y, hy_eq, hy_psi⟩ := ih
    obtain ⟨y', hy'_eq, hy'_psi⟩ := h.2 y
    refine ⟨y', ?_, ?_⟩
    · calc (y' : GL (Fin n) K) = g * (y : GL (Fin n) K) * g⁻¹ := hy'_eq
        _ = g * (g ^ k * (x : GL (Fin n) K) * (g ^ k)⁻¹) * g⁻¹ := by rw [hy_eq]
        _ = g ^ (k + 1) * (x : GL (Fin n) K) * (g ^ (k + 1))⁻¹ := by group
    · calc ψ y' = b * ψ y * b⁻¹ := hy'_psi.symm
        _ = b * (b ^ k * ψ x * (b ^ k)⁻¹) * b⁻¹ := by rw [hy_psi]
        _ = b ^ (k + 1) * ψ x * (b ^ (k + 1))⁻¹ := by group

theorem ggNSPosPF_commutator_pow_prime_aux {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ) {b₁ b₂ : G}
    (hb₁ : b₁ ∈ Bs) (hb₂ : b₂ ∈ Bs) {g₁ g₂ : GL (Fin n) K}
    (h₁ : GGInducesUnitary (p := 2) (f := f) ψ b₁ g₁)
    (h₂ : GGInducesUnitary (p := 2) (f := f) ψ b₂ g₂) {z : K}
    (hz : ((ggNSPosPF_commutator g₁ g₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = z • 1) :
    z ^ p = 1 := by
  have hf : 1 ≤ f := ggNSPosPF_one_le_f (K := K) h.card
  have hn4 : 4 ≤ n := h.four_le
  have hb1p : b₁ ^ p = 1 := h.bstar.2.1.2 b₁ hb₁
  have hg1p : ggIsUnitaryMat (p := 2) (f := f) (g₁ ^ p) := ggNSPosPF_ggIsUnitaryMat_pow h₁.1 p
  have hψ : ∀ x : Su K 2 f n, ψ (ggNSPosPF_conjSUid h.card hg1p x) = ψ x := by
    intro x
    obtain ⟨y, hy_eq, hy_psi⟩ := ggNSPosPF_pow_conj_psi h₁ p x
    have hy : y = ggNSPosPF_conjSUid h.card hg1p x := by
      apply Subtype.ext
      rw [hy_eq]
      rfl
    rw [← hy, hy_psi, hb1p]
    simp
  obtain ⟨c, hc⟩ := ggNSPosPF_scalar_of_conj_psi_trivial h.card hf hn4 h.ker hg1p hψ
  have hz_central : ∀ u : GL (Fin n) K,
      ggNSPosPF_commutator g₁ g₂ * u = u * ggNSPosPF_commutator g₁ g₂ := by
    intro u
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hz]
    simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  have hg1p_central : ∀ u : GL (Fin n) K, g₁ ^ p * u = u * g₁ ^ p := by
    intro u
    rw [hc]
    rw [Matrix.GeneralLinearGroup.scalar_commute]
  have hg1g2 : g₁ * g₂ = ggNSPosPF_commutator g₁ g₂ * g₂ * g₁ := by
    unfold ggNSPosPF_commutator
    group
  have hpow : ∀ k : ℕ, g₁ ^ k * g₂ = (ggNSPosPF_commutator g₁ g₂) ^ k * g₂ * g₁ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc g₁ ^ (k + 1) * g₂ = g₁ ^ k * (g₁ * g₂) := by group
        _ = g₁ ^ k * (ggNSPosPF_commutator g₁ g₂ * g₂ * g₁) := by rw [hg1g2]
        _ = ggNSPosPF_commutator g₁ g₂ * (g₁ ^ k * g₂) * g₁ := by
          simp only [← mul_assoc]
          rw [← hz_central (g₁ ^ k)]
        _ = ggNSPosPF_commutator g₁ g₂ * ((ggNSPosPF_commutator g₁ g₂) ^ k * g₂ * g₁ ^ k) * g₁ := by
          rw [ih]
        _ = (ggNSPosPF_commutator g₁ g₂) ^ (k + 1) * g₂ * g₁ ^ (k + 1) := by
          rw [pow_succ]
          group
  have hzp : (ggNSPosPF_commutator g₁ g₂) ^ p = 1 := by
    have h1 : (1 : GL (Fin n) K) * (g₂ * g₁ ^ p) =
        (ggNSPosPF_commutator g₁ g₂) ^ p * (g₂ * g₁ ^ p) := by
      rw [one_mul]
      calc g₂ * g₁ ^ p = g₁ ^ p * g₂ := (hg1p_central g₂).symm
        _ = (ggNSPosPF_commutator g₁ g₂) ^ p * g₂ * g₁ ^ p := hpow p
        _ = (ggNSPosPF_commutator g₁ g₂) ^ p * (g₂ * g₁ ^ p) := by group
    exact (mul_right_cancel h1).symm
  have hmat : (z • (1 : Matrix (Fin n) (Fin n) K)) ^ p = 1 := by
    rw [ggNSPosPF_smul_one_pow]
    have h1 : ((ggNSPosPF_commutator g₁ g₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hzp, Units.val_one]
    rw [hz, ggNSPosPF_smul_one_pow] at h1
    exact h1
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn4
  exact ggNSPosPF_scalar_pow_eq_one hnpos hmat

theorem ggNSPosPF_commutator_pow_n_aux {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ) {b₁ b₂ : G}
    (hb₁ : b₁ ∈ Bs) (hb₂ : b₂ ∈ Bs) {g₁ g₂ : GL (Fin n) K}
    (h₁ : GGInducesUnitary (p := 2) (f := f) ψ b₁ g₁)
    (h₂ : GGInducesUnitary (p := 2) (f := f) ψ b₂ g₂) {z : K}
    (hz : ((ggNSPosPF_commutator g₁ g₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = z • 1) :
    z ^ n = 1 := by
  have hdetU : Matrix.GeneralLinearGroup.det (ggNSPosPF_commutator g₁ g₂) = 1 := by
    rw [ggNSPosPF_commutator]
    simp only [map_mul, map_inv, map_one]
    have h1 : Matrix.GeneralLinearGroup.det g₁ * Matrix.GeneralLinearGroup.det g₂ *
        (Matrix.GeneralLinearGroup.det g₁)⁻¹ * (Matrix.GeneralLinearGroup.det g₂)⁻¹ =
        (Matrix.GeneralLinearGroup.det g₁ * Matrix.GeneralLinearGroup.det g₂) *
          (Matrix.GeneralLinearGroup.det g₂ * Matrix.GeneralLinearGroup.det g₁)⁻¹ := by
      rw [_root_.mul_inv_rev]; simp only [mul_assoc]
    rw [h1]
    exact mul_inv_eq_one.mpr (mul_comm _ _)
  have hdet : ((ggNSPosPF_commutator g₁ g₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdetU, Units.val_one]
  have h1 := congrArg Matrix.det hz
  rw [hdet, Matrix.det_smul] at h1
  simpa using h1.symm

end CFSG.StandardType

end
