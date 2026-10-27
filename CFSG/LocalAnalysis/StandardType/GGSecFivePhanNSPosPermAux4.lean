module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux3
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
  CFSG.LocalAnalysis.ComponentInitial

open scoped MatrixGroups

theorem exists_scalar_of_su_conj_trivial
    {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 4 ≤ n)
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n)) {z : GL (Fin n) K}
    (hzU : ggIsUnitaryMat (p := 2) (f := f) z)
    (hzt : ∀ x : Su K 2 f n,
      ψ ⟨z * (x : GL (Fin n) K) * z⁻¹, InnerDiagSU.conj_mem_SUid hzU x.2⟩ = ψ x) :
    ∃ c : K, (z : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) c := by
  classical
  have hσ : ClassicalGroups.Unitary.IsUnitaryInvolution (unitaryInvolution K 2 f) :=
    ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK
  have : Group.IsPerfect (Su K 2 f n) :=
    ClassicalGroups.Unitary.isPerfect_SUid hσ (by omega) (fun h3 => absurd h3 (by omega))
  have hzN : z ∈ Subgroup.normalizer
      ((SUid (unitaryInvolution K 2 f) n : Subgroup (GL (Fin n) K)) : Set (GL (Fin n) K)) :=
    InnerDiagSU.mem_normalizer_SUid hzU
  have hX : ∀ x : ↥(SUid (unitaryInvolution K 2 f) n),
      z * (x : GL (Fin n) K) * z⁻¹ * (x : GL (Fin n) K)⁻¹ ∈ LargeEvenScalars (Fin n) K := by
    intro x
    let x' : Su K 2 f n :=
      ⟨z * (x : GL (Fin n) K) * z⁻¹, InnerDiagSU.conj_mem_SUid hzU x.2⟩
    have hmem : x' * x⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hzt x, mul_inv_cancel]
    have hsc := su_coe_mem_largeEvenScalars_of_mem_center hK hn (hker hmem)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, x'] using hsc
  have hcomm := ggNSPosPA_commute_of_scalar_commutator (H := SUid (unitaryInvolution K 2 f) n)
    inferInstance ⟨z, hzN⟩ hX
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with hf0 | hfpos
    · exfalso
      have hK2 : 2 ≤ Nat.card K := by
        have : Fintype K := Fintype.ofFinite K
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card
      have hcard := hK
      rw [hf0] at hcard
      simp at hcard
      omega
    · exact hfpos
  have hc : ∀ g ∈ LargeEvenSUGroup (Fin n) K (2 ^ f), Commute z g := by
    intro g hg
    have hg' : g ∈ SUid (unitaryInvolution K 2 f) n := by
      rw [largeEvenSUGroup_eq_statedSU] at hg
      rwa [← SUid_eq_statedSU hK n] at hg
    exact hcomm g hg'
  have hscalar := GGL45TG.SU.mem_scalars_of_commute_su
    (TableBU.unitaryFieldData_of_card hK hf) (by omega) z hc
  rw [largeEvenScalars_def, MonoidHom.mem_range] at hscalar
  obtain ⟨c, hc⟩ := hscalar
  refine ⟨(c : K), ?_⟩
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]

theorem ggNSPosPA_scalar_of_conj_trivial
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) {z : GL (Fin n) K}
    (hzU : ggIsUnitaryMat (p := 2) (f := f) z)
    (hzt : ∀ x : Su K 2 f n,
      ψ ⟨z * (x : GL (Fin n) K) * z⁻¹, InnerDiagSU.conj_mem_SUid hzU x.2⟩ = ψ x) :
    ∃ c : K, (z : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) c :=
  exists_scalar_of_su_conj_trivial h.card h.four_le h.ker hzU hzt

open TauCeti in
theorem ggNSPosPA_permSU_conj_mem
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    (τ : Equiv.Perm (Fin n)) {b : G} (hb : b ∈ Bs) :
    ψ (ggPermSU (K := K) (f := f) τ) * b * (ψ (ggPermSU (K := K) (f := f) τ))⁻¹ ∈ Bs := by
  classical
  set P : Su K 2 f n := ggPermSU (K := K) (f := f) τ with hPdef
  obtain ⟨g, hgdiag, hgind⟩ := hd b hb
  obtain ⟨d, hd_eq⟩ := hgdiag
  have hne : ∀ i, d i ≠ 0 := by
    intro i hdi
    have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i i)
      (show (((g : GL (Fin n) K) * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 by
        rw [mul_inv_cancel, Units.val_one])
    rw [Units.val_mul, hd_eq, Matrix.mul_apply] at h2
    simp [Matrix.diagonal_apply, hdi, Matrix.one_apply_eq] at h2
  let du : Fin n → Kˣ := fun i => Units.mk0 (d i) (hne i)
  have hdu : ∀ i, ((du i : Kˣ) : K) = d i := fun i => Units.val_mk0 (hne i)
  have hg_eq : (g : GL (Fin n) K) = TauCeti.diagGL du := by
    ext i j
    rw [hd_eq, TauCeti.diagGL_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp [hdu]
    · simp [hij]
  have hunit_one : ggIsUnitaryMat (p := 2) (f := f) (1 : GL (Fin n) K) := by
    unfold ggIsUnitaryMat
    rw [Units.val_one, conjTr_one (σ := unitaryInvolution K 2 f), Matrix.mul_one]
  have hunit_mul : ∀ A B : GL (Fin n) K,
      ggIsUnitaryMat (p := 2) (f := f) A → ggIsUnitaryMat (p := 2) (f := f) B →
      ggIsUnitaryMat (p := 2) (f := f) (A * B) := by
    intro A B hA hB
    unfold ggIsUnitaryMat at hA hB ⊢
    rw [Units.val_mul, conjTr_mul]
    calc conjTr (unitaryInvolution K 2 f) (B : Matrix (Fin n) (Fin n) K) *
          conjTr (unitaryInvolution K 2 f) (A : Matrix (Fin n) (Fin n) K) *
          ((A : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K))
        = conjTr (unitaryInvolution K 2 f) (B : Matrix (Fin n) (Fin n) K) *
            (conjTr (unitaryInvolution K 2 f) (A : Matrix (Fin n) (Fin n) K) *
              (A : Matrix (Fin n) (Fin n) K)) *
            (B : Matrix (Fin n) (Fin n) K) := by noncomm_ring
      _ = conjTr (unitaryInvolution K 2 f) (B : Matrix (Fin n) (Fin n) K) *
            (B : Matrix (Fin n) (Fin n) K) := by rw [hA, Matrix.mul_one]
      _ = 1 := hB
  have hgunit : ∀ k : ℕ, ggIsUnitaryMat (p := 2) (f := f) ((g : GL (Fin n) K) ^ k) := by
    intro k
    induction k with
    | zero => simpa using hunit_one
    | succ k ih => rw [pow_succ]; exact hunit_mul _ _ ih hgind.1
  let c : Su K 2 f n → Su K 2 f n := fun x =>
    ⟨(g : GL (Fin n) K) * (x : GL (Fin n) K) * (g : GL (Fin n) K)⁻¹,
      InnerDiagSU.conj_mem_SUid (show InnerDiagSU.IsIdUnitary (unitaryInvolution K 2 f) g from hgind.1) x.2⟩
  have hcψ : ∀ x : Su K 2 f n, b * ψ x * b⁻¹ = ψ (c x) := by
    intro x
    obtain ⟨y, hy, hby⟩ := hgind.2 x
    have hyx : c x = y := Subtype.ext (by
      change (g : GL (Fin n) K) * (x : GL (Fin n) K) * (g : GL (Fin n) K)⁻¹ = (y : GL (Fin n) K)
      rw [hy])
    rw [hyx, hby]
  have hciter : ∀ k : ℕ, ∀ x : Su K 2 f n, b ^ k * ψ x * (b ^ k)⁻¹ = ψ ((c^[k]) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ]
      rw [show b ^ k * b * ψ x * (b ^ k * b)⁻¹ = b * (b ^ k * ψ x * (b ^ k)⁻¹) * b⁻¹ by group]
      rw [ih x, hcψ]
      congr 1
      rw [Function.iterate_succ_apply']
  have hciter_coe : ∀ k : ℕ, ∀ x : Su K 2 f n,
      (((c^[k]) x : Su K 2 f n) : GL (Fin n) K) =
        (g : GL (Fin n) K) ^ k * (x : GL (Fin n) K) * ((g : GL (Fin n) K) ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply']
      change (g : GL (Fin n) K) * (((c^[k]) x : Su K 2 f n) : GL (Fin n) K) *
          (g : GL (Fin n) K)⁻¹ =
        (g : GL (Fin n) K) ^ (k + 1) * (x : GL (Fin n) K) * ((g : GL (Fin n) K) ^ (k + 1))⁻¹
      rw [ih x, pow_succ]
      group
  have hbp : b ^ p = 1 := h.bstar.2.1.2 b hb
  have hzt : ∀ x : Su K 2 f n,
      ψ ⟨(g : GL (Fin n) K) ^ p * (x : GL (Fin n) K) * ((g : GL (Fin n) K) ^ p)⁻¹,
        InnerDiagSU.conj_mem_SUid (hgunit p) x.2⟩ = ψ x := by
    intro x
    have h1 := hciter p x
    rw [hbp, one_mul, inv_one, mul_one] at h1
    have h2 : (c^[p]) x = ⟨(g : GL (Fin n) K) ^ p * (x : GL (Fin n) K) *
        ((g : GL (Fin n) K) ^ p)⁻¹, InnerDiagSU.conj_mem_SUid (hgunit p) x.2⟩ :=
      Subtype.ext (hciter_coe p x)
    rw [h2] at h1
    exact h1.symm
  obtain ⟨lam, hlam⟩ := ggNSPosPA_scalar_of_conj_trivial h (hgunit p) hzt
  have hdp : ∀ i, d i ^ p = lam := by
    intro i
    have h1 : ((Matrix.diagonal d) ^ p) i i = lam := by
      have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i i) hlam
      rw [show (((g : GL (Fin n) K) ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          ((g : Matrix (Fin n) (Fin n) K)) ^ p by rw [Units.val_pow_eq_pow_val],
        hd_eq] at h2
      simpa [Matrix.scalar_apply] using h2
    rwa [Matrix.diagonal_pow, Matrix.diagonal_apply_eq] at h1
  obtain ⟨y, hy, hby⟩ := hgind.2 P⁻¹
  let w : Su K 2 f n := P * y
  have hwGL : (w : GL (Fin n) K) = (P : GL (Fin n) K) * (g : GL (Fin n) K) *
      (P : GL (Fin n) K)⁻¹ * (g : GL (Fin n) K)⁻¹ := by
    rw [Subgroup.coe_mul, hy, Subgroup.coe_inv]
    group
  have hP_perm : (P : GL (Fin n) K) = TauCeti.permutationGL τ⁻¹ := by
    apply Units.ext
    rw [TauCeti.permutationGL_coe, inv_inv]
    rfl
  have hw_diagGL : (w : GL (Fin n) K) =
      TauCeti.diagGL (fun i => du (τ i) * (du i)⁻¹) := by
    rw [hwGL, hg_eq, hP_perm, TauCeti.permutationGL_mul_diagGL_mul_inv]
    rw [inv_inv, ← map_inv, ← map_mul]
    rfl
  have hw_diag : ∃ d' : Fin n → K,
      (w : GL (Fin n) K) = Matrix.diagonal d' ∧ ∀ i, d' i ^ p = 1 := by
    refine ⟨fun i => d (τ i) * (d i)⁻¹, ?_, ?_⟩
    · rw [hw_diagGL]
      ext i j
      rw [TauCeti.diagGL_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp [hdu]
      · simp [hij]
    · intro i
      rw [mul_pow, inv_pow, hdp (τ i), hdp i]
      exact mul_inv_cancel₀ (by rw [← hdp i]; exact pow_ne_zero p (hne i))
  have hwbs : ψ w ∈ Bs := ggNSDiag_torus_le h hd w hw_diag
  have hb' : ψ P * b * (ψ P)⁻¹ = ψ w * b := by
    calc ψ P * b * (ψ P)⁻¹ = ψ P * (b * ψ (P⁻¹) * b⁻¹) * b := by rw [map_inv]; group
      _ = ψ P * ψ y * b := by rw [hby]
      _ = ψ (P * y) * b := by rw [← map_mul]
      _ = ψ w * b := rfl
  rw [hb']
  exact Bs.mul_mem hwbs hb

theorem ggNSPosPA_permSU_mem_normalizer
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    (σ : Equiv.Perm (Fin n)) :
    ψ (ggPermSU (K := K) (f := f) σ) ∈ Subgroup.normalizer (Bs : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact ggNSPosPA_permSU_conj_mem h hd σ hx
  · intro hx
    have hone : ggPermSU (K := K) (f := f) (1 : Equiv.Perm (Fin n)) = 1 := by
      apply Subtype.ext
      apply Units.ext
      show ((1 : Equiv.Perm (Fin n)).permMatrix K) = (1 : Matrix (Fin n) (Fin n) K)
      simp
    have hP_inv : ggPermSU (K := K) (f := f) σ⁻¹ =
        (ggPermSU (K := K) (f := f) σ)⁻¹ := by
      have h := ggNSPosPA_permSU_mul_anti' (K := K) (f := f) σ σ⁻¹
      rw [mul_inv_cancel, hone] at h
      exact eq_inv_of_mul_eq_one_left h.symm
    have hf := ggNSPosPA_permSU_conj_mem h hd σ⁻¹ hx
    rw [hP_inv, map_inv] at hf
    convert hf using 1
    group

end CFSG.StandardType

end
