module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux4
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux2

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
  CFSG.LocalAnalysis.ComponentInitial

open scoped MatrixGroups

theorem ggNSPosPA_ggIsUnitaryMat_mul {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {A B : GL (Fin n) K} (hA : ggIsUnitaryMat (p := 2) (f := f) A)
    (hB : ggIsUnitaryMat (p := 2) (f := f) B) :
    ggIsUnitaryMat (p := 2) (f := f) (A * B) := by
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

theorem ggNSPosPA_ggIsUnitaryMat_inv {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {A : GL (Fin n) K} (hA : ggIsUnitaryMat (p := 2) (f := f) A) :
    ggIsUnitaryMat (p := 2) (f := f) A⁻¹ :=
  InnerDiagSU.IsIdUnitary.inv (show InnerDiagSU.IsIdUnitary (unitaryInvolution K 2 f) A from hA)

theorem ggNSPosPA_induces_self {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (s : Su K 2 f n) :
    GGInducesUnitary (p := 2) (f := f) ψ (ψ s) (s : GL (Fin n) K) := by
  have hsU : (s : GL (Fin n) K) ∈ SUid (unitaryInvolution K 2 f) n := s.2
  refine ⟨(mem_SUid.mp hsU).2, fun u => ?_⟩
  refine ⟨s * u * s⁻¹, ?_, ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  · rw [map_mul, map_mul, map_inv]

theorem ggNSPosPA_conj_inv_mul_of_same_action {G : Type} [Group G]
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G} {b : G}
    {h1 h2 : GL (Fin n) K} (hind1 : GGInducesUnitary (p := 2) (f := f) ψ b h1)
    (hind2 : GGInducesUnitary (p := 2) (f := f) ψ b h2) :
    ∀ u : Su K 2 f n,
      ψ ⟨h1⁻¹ * h2 * (u : GL (Fin n) K) * (h1⁻¹ * h2)⁻¹,
        InnerDiagSU.conj_mem_SUid
          (ggNSPosPA_ggIsUnitaryMat_mul (ggNSPosPA_ggIsUnitaryMat_inv hind1.1) hind2.1) u.2⟩ = ψ u := by
  intro u
  let w2 : Su K 2 f n :=
    ⟨h2 * (u : GL (Fin n) K) * h2⁻¹, InnerDiagSU.conj_mem_SUid hind2.1 u.2⟩
  obtain ⟨y2, hy2, hby2⟩ := hind2.2 u
  have hy2w : y2 = w2 := Subtype.ext (by rw [hy2])
  have hw2ψ : ψ w2 = b * ψ u * b⁻¹ := by rw [← hy2w]; exact hby2.symm
  let w : Su K 2 f n :=
    ⟨h1⁻¹ * (w2 : GL (Fin n) K) * h1,
      InnerDiagSU.conj_mem_SUid (ggNSPosPA_ggIsUnitaryMat_inv hind1.1) w2.2⟩
  obtain ⟨y1, hy1, hby1⟩ := hind1.2 w
  have hy1w : y1 = w2 := Subtype.ext (by
    rw [hy1]
    change h1 * (h1⁻¹ * (w2 : GL (Fin n) K) * h1) * h1⁻¹ = (w2 : GL (Fin n) K)
    group)
  have hwψ : ψ w = ψ u := by
    have h1' : b * ψ w * b⁻¹ = b * ψ u * b⁻¹ := by rw [hby1, hy1w, hw2ψ]
    exact mul_left_cancel (mul_right_cancel h1')
  have hw_eq : w = ⟨h1⁻¹ * h2 * (u : GL (Fin n) K) * (h1⁻¹ * h2)⁻¹,
      InnerDiagSU.conj_mem_SUid
        (ggNSPosPA_ggIsUnitaryMat_mul (ggNSPosPA_ggIsUnitaryMat_inv hind1.1) hind2.1) u.2⟩ :=
    Subtype.ext (by
      change h1⁻¹ * (w2 : GL (Fin n) K) * h1 =
        h1⁻¹ * h2 * (u : GL (Fin n) K) * (h1⁻¹ * h2)⁻¹
      rw [show (w2 : GL (Fin n) K) = h2 * (u : GL (Fin n) K) * h2⁻¹ from rfl]
      group)
  rw [← hw_eq]
  exact hwψ

theorem ggNSPosPA_diag_mem_SUid {K : Type} [Field K] [Finite K] [CharP K 2] {p f n : ℕ}
    {ζ : Kˣ} (hζp : ζ ^ p = 1) (hζq : ζ ^ (2 ^ f + 1) = 1)
    {v : Fin n → ℕ} (hv : p ∣ ∑ i, v i) :
    TauCeti.diagGL (fun i => ζ ^ (v i)) ∈ SUid (unitaryInvolution K 2 f) n := by
  have hζpK : ((ζ : K)) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζp, Units.val_one]
  have hζqK : ((ζ : K)) ^ (2 ^ f + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζq, Units.val_one]
  have hcoe : ((TauCeti.diagGL (fun i => ζ ^ (v i)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = Matrix.diagonal (fun i => (ζ : K) ^ (v i)) := by
    ext i j
    rw [TauCeti.diagGL_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp [Units.val_pow_eq_pow_val]
    · simp [hij]
  rw [mem_SUid]
  refine ⟨?_, ?_⟩
  · rw [hcoe, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
    obtain ⟨k, hk⟩ := hv
    rw [hk, pow_mul, hζpK, one_pow]
  · rw [hcoe]
    have hconj : conjTr (unitaryInvolution K 2 f) (Matrix.diagonal (fun i => (ζ : K) ^ (v i))) =
        Matrix.diagonal (fun i => unitaryInvolution K 2 f ((ζ : K) ^ (v i))) := by
      ext i j
      rw [conjTr, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply,
        Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    rw [hconj, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => unitaryInvolution K 2 f ((ζ : K) ^ (v i)) * (ζ : K) ^ (v i)) =
        fun _ => (1 : K) by
      funext i
      rw [unitaryInvolution_apply, ← pow_mul, ← pow_add,
        show v i * 2 ^ f + v i = (2 ^ f + 1) * v i by ring, pow_mul, hζqK, one_pow]]
    exact Matrix.diagonal_one

theorem ggNSPosPA_exists_zeta {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) :
    ∃ ζ : Kˣ, orderOf ζ = p ∧ ζ ^ (2 ^ f + 1) = 1 := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hpK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card]
    have e : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      have := Nat.sq_sub_sq (2 ^ f) 1
      rwa [one_pow] at this
    rw [e]
    exact Dvd.dvd.mul_right h.dvd _
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hpK
  refine ⟨ζ, hζ, ?_⟩
  obtain ⟨k, hk⟩ := h.dvd
  rw [hk, pow_mul, ← hζ, pow_orderOf_eq_one, one_pow]


theorem ggNSPosPA_coe_diagGL {K : Type} [Field K] {n : ℕ} (t : Fin n → Kˣ) :
    ((TauCeti.diagGL t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun i => (t i : K)) := by
  ext i j
  rw [TauCeti.diagGL_apply, Matrix.diagonal_apply]

theorem ggNSPosPA_monomial_of_mem_normalizer {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) {x : Su K 2 f n}
    (hxN : ψ x ∈ Subgroup.normalizer (Bs : Set G)) :
    ∃ (d : Fin n → Kˣ) (σ : Equiv.Perm (Fin n)),
      (x : GL (Fin n) K) = TauCeti.diagGL d * TauCeti.permutationGL σ := by
  classical
  obtain ⟨ζ, hζ, hζq⟩ := ggNSPosPA_exists_zeta h
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hn : 2 ≤ n := by have h4 := h.four_le; omega
  refine ggNSPosPA_monomial_of_conj_torus h.prime h.odd hn ζ hζ x ?_
  intro v hv
  let t : Su K 2 f n :=
    ⟨TauCeti.diagGL (fun i => ζ ^ (v i)), ggNSPosPA_diag_mem_SUid hζp hζq hv⟩
  have ht_coe : (t : GL (Fin n) K) = TauCeti.diagGL (fun i => ζ ^ (v i)) := rfl
  have ht_diag : ∃ d : Fin n → K, (t : GL (Fin n) K) = Matrix.diagonal d ∧ ∀ i, d i ^ p = 1 := by
    refine ⟨fun i => (ζ : K) ^ (v i), ?_, ?_⟩
    · rw [ht_coe]
      ext i j
      rw [TauCeti.diagGL_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp [Units.val_pow_eq_pow_val]
      · simp [hij]
    · intro i
      rw [← pow_mul, mul_comm, pow_mul]
      rw [show ((ζ : K) ^ p) = 1 by
        rw [← Units.val_pow_eq_pow_val, hζp, Units.val_one]]
      exact one_pow _
  have htBs : ψ t ∈ Bs := ggNSDiag_torus_le h hd t ht_diag
  have hmem : ψ (x * t * x⁻¹) ∈ Bs := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hxN (ψ t)).mp htBs
  obtain ⟨hh, hhdiag, hhind⟩ := hd (ψ (x * t * x⁻¹)) hmem
  obtain ⟨dh, hdh_eq⟩ := hhdiag
  let z : GL (Fin n) K := (hh : GL (Fin n) K)⁻¹ * ((x * t * x⁻¹ : Su K 2 f n) : GL (Fin n) K)
  have hxz_coe : ((x * t * x⁻¹ : Su K 2 f n) : GL (Fin n) K) =
      (x : GL (Fin n) K) * (t : GL (Fin n) K) * (x : GL (Fin n) K)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have hzU : ggIsUnitaryMat (p := 2) (f := f) z :=
    ggNSPosPA_ggIsUnitaryMat_mul (ggNSPosPA_ggIsUnitaryMat_inv hhind.1)
      (show ggIsUnitaryMat (p := 2) (f := f) ((x * t * x⁻¹ : Su K 2 f n) : GL (Fin n) K) from
        (mem_SUid.mp (x * t * x⁻¹).2).2)
  have hzt := ggNSPosPA_conj_inv_mul_of_same_action (ψ := ψ) hhind
    (ggNSPosPA_induces_self (ψ := ψ) (x * t * x⁻¹))
  obtain ⟨c, hc⟩ := ggNSPosPA_scalar_of_conj_trivial h hzU (fun u => hzt u)
  have hzx : (x : GL (Fin n) K) * (t : GL (Fin n) K) * (x : GL (Fin n) K)⁻¹ =
      (hh : GL (Fin n) K) * z := by
    rw [show z = (hh : GL (Fin n) K)⁻¹ * ((x * t * x⁻¹ : Su K 2 f n) : GL (Fin n) K) from rfl]
    rw [hxz_coe]
    group
  refine ⟨fun i => dh i * c, ?_⟩
  have hmat : (((hh : GL (Fin n) K) * z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun i => dh i * c) := by
    rw [Units.val_mul, hdh_eq, hc]
    rw [show Matrix.scalar (Fin n) c = Matrix.diagonal (fun _ => c) by
      ext a b; rw [Matrix.scalar_apply, Matrix.diagonal_apply]]
    rw [Matrix.diagonal_mul_diagonal]
  have hstep : (((x : GL (Fin n) K) * (t : GL (Fin n) K) * (x : GL (Fin n) K)⁻¹ :
      GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        Matrix.diagonal (fun i => (ζ : K) ^ (v i)) *
        ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Units.val_mul, Units.val_mul, ht_coe, ggNSPosPA_coe_diagGL]
    simp only [Units.val_pow_eq_pow_val]
  rw [← hstep, hzx, hmat]

end CFSG.StandardType

end
