module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux8

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
  CFSG.LocalAnalysis.ComponentInitial

open scoped MatrixGroups

theorem ggNSPosPA7_ggIsUnitaryMat_pow {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {A : GL (Fin n) K} (hA : ggIsUnitaryMat (p := 2) (f := f) A) (k : ℕ) :
    ggIsUnitaryMat (p := 2) (f := f) (A ^ k) := by
  induction k with
  | zero =>
      rw [pow_zero]
      unfold ggIsUnitaryMat
      rw [Units.val_one, conjTr_one (σ := unitaryInvolution K 2 f), Matrix.mul_one]
  | succ k ih =>
      rw [pow_succ]
      exact ggNSPosPA_ggIsUnitaryMat_mul ih hA

theorem ggNSPosPA7_induces_mul {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} {ψ : Su K 2 f n →* G} {b c : G} {g h : GL (Fin n) K}
    (hb : GGInducesUnitary (p := 2) (f := f) ψ b g)
    (hc : GGInducesUnitary (p := 2) (f := f) ψ c h) :
    GGInducesUnitary (p := 2) (f := f) ψ (b * c) (g * h) := by
  refine ⟨ggNSPosPA_ggIsUnitaryMat_mul hb.1 hc.1, fun x => ?_⟩
  obtain ⟨y, hy, hby⟩ := hc.2 x
  obtain ⟨z, hz, hbz⟩ := hb.2 y
  refine ⟨z, ?_, ?_⟩
  · rw [hz, hy]
    group
  · rw [show b * c * ψ x * (b * c)⁻¹ = b * (c * ψ x * c⁻¹) * b⁻¹ by group, hby, hbz]

theorem ggNSPosPA7_induces_pow {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} {ψ : Su K 2 f n →* G} {b : G} {g : GL (Fin n) K}
    (hind : GGInducesUnitary (p := 2) (f := f) ψ b g) (k : ℕ) :
    GGInducesUnitary (p := 2) (f := f) ψ (b ^ k) (g ^ k) := by
  induction k with
  | zero =>
      rw [pow_zero, pow_zero]
      refine ⟨?_, fun x => ⟨x, by simp, by simp⟩⟩
      unfold ggIsUnitaryMat
      rw [Units.val_one, conjTr_one (σ := unitaryInvolution K 2 f), Matrix.mul_one]
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact ggNSPosPA7_induces_mul ih hind

theorem ggNSPosPA7_lift_pow_eq_scalar {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    (s : ↥Bs) :
    ∃ c : K, (((ggNSPosPA_lift hd s : GL (Fin n) K) ^ p : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) c := by
  have hind := ggNSPosPA_lift_induces hd s
  have hbp : (s : G) ^ p = 1 := h.bstar.2.1.2 s s.2
  have hzU : ggIsUnitaryMat (p := 2) (f := f) ((ggNSPosPA_lift hd s) ^ p) :=
    ggNSPosPA7_ggIsUnitaryMat_pow hind.1 p
  have hzt : ∀ x : Su K 2 f n,
      ψ ⟨(ggNSPosPA_lift hd s) ^ p * (x : GL (Fin n) K) *
          ((ggNSPosPA_lift hd s) ^ p)⁻¹, InnerDiagSU.conj_mem_SUid hzU x.2⟩ = ψ x := by
    intro x
    obtain ⟨y, hy, hby⟩ := (ggNSPosPA7_induces_pow hind p).2 x
    have hyψ : ψ y = ψ x := by
      rw [← hby, hbp, one_mul, inv_one, mul_one]
    have hy' : y = ⟨(ggNSPosPA_lift hd s) ^ p * (x : GL (Fin n) K) *
        ((ggNSPosPA_lift hd s) ^ p)⁻¹, InnerDiagSU.conj_mem_SUid hzU x.2⟩ :=
      Subtype.ext hy
    rw [← hy', hyψ]
  exact ggNSPosPA_scalar_of_conj_trivial h hzU hzt

theorem ggNSPosPA7_liftUnits_pow_eq_scalar {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) (s : ↥Bs) :
    ∃ c : K, ∀ i, (((ggNSPosPA_liftUnits hd s i : Kˣ) : K)) ^ p = c := by
  obtain ⟨c, hc⟩ := ggNSPosPA7_lift_pow_eq_scalar h hd s
  refine ⟨c, fun i => ?_⟩
  have hmat : (((ggNSPosPA_lift hd s : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun i => ((ggNSPosPA_liftUnits hd s i : Kˣ) : K)) := by
    rw [← ggNSPosPA_diagGL_liftUnits hd s, ggNSPosPA_coe_diagGL]
  have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i i) hc
  rw [show (((ggNSPosPA_lift hd s) ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((((ggNSPosPA_lift hd s : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)) ^ p by
        rw [Units.val_pow_eq_pow_val]] at h2
  rw [hmat, Matrix.diagonal_pow] at h2
  simpa only [Matrix.diagonal_apply_eq, Matrix.scalar_apply, Pi.pow_apply] using h2

theorem ggNSPosPA7_ratio_pow {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    (s : ↥Bs) (a b : Fin n) :
    (ggNSPosPA_ratioOfUnits (ggNSPosPA_liftUnits hd s) a b) ^ p = 1 := by
  obtain ⟨c, hc⟩ := ggNSPosPA7_liftUnits_pow_eq_scalar h hd s
  have hcne : c ≠ 0 := by
    rw [← hc a]
    exact pow_ne_zero p (Units.ne_zero (ggNSPosPA_liftUnits hd s a))
  have hua : (ggNSPosPA_liftUnits hd s a) ^ p = Units.mk0 c hcne := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hc a, Units.val_mk0]
  have hub : (ggNSPosPA_liftUnits hd s b) ^ p = Units.mk0 c hcne := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hc b, Units.val_mk0]
  unfold ggNSPosPA_ratioOfUnits
  rw [mul_pow, inv_pow, hua, hub, mul_inv_cancel]

theorem ggNSPosPA7_diagUnits_mul {K : Type} [Field K] {n : ℕ} {g1 g2 : GL (Fin n) K}
    (h1 : g1 ∈ TauCeti.diagonalTorus K n) (h2 : g2 ∈ TauCeti.diagonalTorus K n)
    (h12 : g1 * g2 ∈ TauCeti.diagonalTorus K n) :
    ggNSPosPA_diagUnits h12 = ggNSPosPA_diagUnits h1 * ggNSPosPA_diagUnits h2 := by
  apply TauCeti.diagGL_injective
  rw [ggNSPosPA_diagGL_diagUnits, map_mul, ggNSPosPA_diagGL_diagUnits, ggNSPosPA_diagGL_diagUnits]

theorem ggNSPosPA7_diagUnits_one {K : Type} [Field K] {n : ℕ}
    (h1 : (1 : GL (Fin n) K) ∈ TauCeti.diagonalTorus K n) :
    ggNSPosPA_diagUnits h1 = 1 := by
  apply TauCeti.diagGL_injective
  rw [ggNSPosPA_diagGL_diagUnits, map_one]

@[expose] noncomputable def ggNSPosPA7_ratioHom {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) (a b : Fin n) : ↥Bs →* Kˣ where
  toFun s := ggNSPosPA_ratioOfUnits (ggNSPosPA_liftUnits hd s) a b
  map_one' := by
    have hdiag1 : ggIsDiagMat (1 : GL (Fin n) K) :=
      ⟨fun _ => 1, by rw [Units.val_one, Matrix.diagonal_one]⟩
    have hindu1 : GGInducesUnitary (p := 2) (f := f) ψ (((1 : ↥Bs) : G))
        (1 : GL (Fin n) K) := by
      simpa using ggNSPosPA_induces_self (ψ := ψ) (1 : Su K 2 f n)
    have hwd := ggNSPosPA_ratio_wd (h := h) (s := (1 : ↥Bs))
      (g1 := ggNSPosPA_lift hd 1) (ggNSPosPA_lift_diag hd 1) (ggNSPosPA_lift_induces hd 1)
      hdiag1 hindu1 a b
    change ggNSPosPA_ratioOfUnits
        (ggNSPosPA_diagUnits (ggNSPosPA_mem_diagonalTorus_of_isDiag
          (ggNSPosPA_lift_diag hd 1))) a b = 1
    rw [hwd, ggNSPosPA7_diagUnits_one (ggNSPosPA_mem_diagonalTorus_of_isDiag hdiag1)]
    simp [ggNSPosPA_ratioOfUnits]
  map_mul' s t := by
    have hprod_diag : ggIsDiagMat (ggNSPosPA_lift hd s * ggNSPosPA_lift hd t) := by
      obtain ⟨d1, hd1⟩ := ggNSPosPA_lift_diag hd s
      obtain ⟨d2, hd2⟩ := ggNSPosPA_lift_diag hd t
      exact ⟨fun i => d1 i * d2 i, by
        rw [Units.val_mul, hd1, hd2, Matrix.diagonal_mul_diagonal]⟩
    have hprod_ind : GGInducesUnitary (p := 2) (f := f) ψ (((s * t : ↥Bs) : G))
        (ggNSPosPA_lift hd s * ggNSPosPA_lift hd t) := by
      have hh := ggNSPosPA7_induces_mul (ψ := ψ)
        (ggNSPosPA_lift_induces hd s) (ggNSPosPA_lift_induces hd t)
      simpa only [Subgroup.coe_mul] using hh
    have hunits : ggNSPosPA_diagUnits (ggNSPosPA_mem_diagonalTorus_of_isDiag hprod_diag) =
        ggNSPosPA_diagUnits (ggNSPosPA_mem_diagonalTorus_of_isDiag
          (ggNSPosPA_lift_diag hd s)) *
        ggNSPosPA_diagUnits (ggNSPosPA_mem_diagonalTorus_of_isDiag
          (ggNSPosPA_lift_diag hd t)) :=
      ggNSPosPA7_diagUnits_mul _ _ _
    have hwd := ggNSPosPA_ratio_wd (h := h) (s := s * t)
      (g1 := ggNSPosPA_lift hd (s * t)) (ggNSPosPA_lift_diag hd (s * t))
      (ggNSPosPA_lift_induces hd (s * t)) hprod_diag hprod_ind a b
    change ggNSPosPA_ratioOfUnits
        (ggNSPosPA_diagUnits (ggNSPosPA_mem_diagonalTorus_of_isDiag
          (ggNSPosPA_lift_diag hd (s * t)))) a b =
      ggNSPosPA_ratioOfUnits
        (ggNSPosPA_diagUnits (ggNSPosPA_mem_diagonalTorus_of_isDiag
          (ggNSPosPA_lift_diag hd s))) a b *
      ggNSPosPA_ratioOfUnits
        (ggNSPosPA_diagUnits (ggNSPosPA_mem_diagonalTorus_of_isDiag
          (ggNSPosPA_lift_diag hd t))) a b
    rw [hwd, hunits, ggNSPosPA_ratioOfUnits_mul]

theorem ggNSPosPA7_ratioHom_apply {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    (a b : Fin n) (s : ↥Bs) :
    ggNSPosPA7_ratioHom h hd a b s =
      ggNSPosPA_ratioOfUnits (ggNSPosPA_liftUnits hd s) a b :=
  rfl

theorem ggNSPosPA7_ratioHom_pow {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    (a b : Fin n) (s : ↥Bs) :
    (ggNSPosPA7_ratioHom h hd a b s) ^ p = 1 := by
  rw [ggNSPosPA7_ratioHom_apply]
  exact ggNSPosPA7_ratio_pow h hd s a b

theorem ggNSPosPA7_ratio_lift_wd {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    (s : ↥Bs) {g : GL (Fin n) K} (hg : ggIsDiagMat g)
    (hi : GGInducesUnitary (p := 2) (f := f) ψ (s : G) g) (a b : Fin n) :
    ggNSPosPA_ratioOfUnits (ggNSPosPA_liftUnits hd s) a b =
      ggNSPosPA_ratioOfUnits
        (ggNSPosPA_diagUnits (ggNSPosPA_mem_diagonalTorus_of_isDiag hg)) a b :=
  ggNSPosPA_ratio_wd (h := h) (s := s) (ggNSPosPA_lift_diag hd s)
    (ggNSPosPA_lift_induces hd s) hg hi a b

theorem ggNSPosPA7_conj_formula {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
    [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G} {Bs : Subgroup G}
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) (π : Equiv.Perm (Fin n)) (s : ↥Bs) :
    ∃ w : Su K 2 f n,
      (w : GL (Fin n) K) = (ggPermSU (K := K) (f := f) π : GL (Fin n) K) *
          (ggNSPosPA_lift hd s : GL (Fin n) K) *
          ((ggPermSU (K := K) (f := f) π : GL (Fin n) K))⁻¹ *
          (ggNSPosPA_lift hd s : GL (Fin n) K)⁻¹ ∧
      ψ (ggPermSU (K := K) (f := f) π) * (s : G) *
          (ψ (ggPermSU (K := K) (f := f) π))⁻¹ = ψ w * (s : G) := by
  classical
  set g : GL (Fin n) K := ggNSPosPA_lift hd s with hgdef
  have hgdiag : ggIsDiagMat g := by rw [hgdef]; exact ggNSPosPA_lift_diag hd s
  have hgind : GGInducesUnitary (p := 2) (f := f) ψ (s : G) g := by
    rw [hgdef]; exact ggNSPosPA_lift_induces hd s
  set P : Su K 2 f n := ggPermSU (K := K) (f := f) π with hPdef
  obtain ⟨y, hy, hby⟩ := hgind.2 P⁻¹
  refine ⟨P * y, ?_, ?_⟩
  · rw [Subgroup.coe_mul, hy, Subgroup.coe_inv, hgdef, hPdef]
    group
  · calc ψ P * (s : G) * (ψ P)⁻¹
        = ψ P * ((s : G) * ψ (P⁻¹) * (s : G)⁻¹) * (s : G) := by
          rw [map_inv]; group
      _ = ψ P * ψ y * (s : G) := by rw [hby]
      _ = ψ (P * y) * (s : G) := by rw [← map_mul]

theorem ggNSPosPA7_fixed_iff_conj {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    (τ : Equiv.Perm (Fin n)) (s : ↥Bs) :
    (((ggNSPosPA_permAutEquiv h hd τ : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) s = s) ↔
      ψ (ggPermSU (K := K) (f := f) τ⁻¹) * (s : G) *
          (ψ (ggPermSU (K := K) (f := f) τ⁻¹))⁻¹ = (s : G) := by
  constructor
  · intro hfix
    have h2 := congrArg Subtype.val hfix
    rwa [ggNSPosPA_permAutEquiv_apply h hd τ s] at h2
  · intro hconj
    apply Subtype.ext
    rw [ggNSPosPA_permAutEquiv_apply h hd τ s, hconj]

theorem ggNSPosPA7_fixed_iff {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    {a b : Fin n} (hab : a ≠ b) (s : ↥Bs) :
    (((ggNSPosPA_permAutEquiv h hd (Equiv.swap a b) :
      ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) s = s) ↔
      ggNSPosPA7_ratioHom h hd a b s = 1 := by
  classical
  set τ : Equiv.Perm (Fin n) := Equiv.swap a b with hτdef
  have hτinv : τ⁻¹ = Equiv.swap a b := by
    rw [hτdef]
    exact (inv_eq_of_mul_eq_one_right (Equiv.swap_mul_self a b)).symm
  obtain ⟨w, hwGL, hconj⟩ := ggNSPosPA7_conj_formula (ψ := ψ) hd τ⁻¹ s
  let d : Fin n → Kˣ := ggNSPosPA_liftUnits hd s
  let u : Fin n → Kˣ := fun i => d (τ⁻¹ i) * (d i)⁻¹
  have hw_diag : (w : GL (Fin n) K) = TauCeti.diagGL u := by
    rw [hwGL, ← ggNSPosPA_diagGL_liftUnits hd s,
      ggNSPosPA_permSU_inv_eq_permutationGL τ,
      TauCeti.permutationGL_mul_diagGL_mul_inv]
    rw [← map_inv, ← map_mul]
    rfl
  rw [ggNSPosPA7_fixed_iff_conj h hd τ s]
  constructor
  · intro hc
    have hwψ : ψ w = 1 := by
      have h1 : ψ w * (s : G) = 1 * (s : G) := by rw [← hconj, hc, one_mul]
      exact mul_right_cancel h1
    have hwker : w ∈ ψ.ker := MonoidHom.mem_ker.mpr hwψ
    have hwcenter : w ∈ Subgroup.center (Su K 2 f n) := h.ker hwker
    have hwscal := ggNSPosPA_scalar_of_mem_center h hwcenter
    rw [largeEvenScalars_def, MonoidHom.mem_range] at hwscal
    obtain ⟨c, hc'⟩ := hwscal
    have hui : ∀ i, (u i : K) = (c : K) := by
      intro i
      have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i i)
        (congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) hc')
      rw [Matrix.GeneralLinearGroup.coe_scalar, hw_diag, ggNSPosPA_coe_diagGL] at h2
      simpa using h2.symm
    have hcard : ({a, b} : Finset (Fin n)).card ≤ 2 := by
      calc ({a, b} : Finset (Fin n)).card ≤ ({b} : Finset (Fin n)).card + 1 :=
            Finset.card_insert_le a {b}
        _ = 2 := by simp
    have hlt : ({a, b} : Finset (Fin n)).card < Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      have h4 := h.four_le
      omega
    obtain ⟨i0, hi0⟩ : ∃ i0, i0 ∉ ({a, b} : Finset (Fin n)) := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset (Fin n)) ⊆ ({a, b} : Finset (Fin n)) :=
        fun i _ => hcon i
      have := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at this
      have h4 := h.four_le
      omega
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi0
    obtain ⟨hia, hib⟩ := hi0
    have hua : (u a : Kˣ) = (ggNSPosPA_ratioOfUnits d a b)⁻¹ := by
      unfold ggNSPosPA_ratioOfUnits
      show d (τ⁻¹ a) * (d a)⁻¹ = (d a * (d b)⁻¹)⁻¹
      rw [hτinv, Equiv.swap_apply_left]
      group
    have hui0 : (u i0 : Kˣ) = 1 := by
      show d (τ⁻¹ i0) * (d i0)⁻¹ = 1
      rw [hτinv, Equiv.swap_apply_of_ne_of_ne hia hib]
      group
    have hratio_inv : (ggNSPosPA_ratioOfUnits d a b)⁻¹ = 1 := by
      rw [← hua, ← hui0]
      apply Units.ext
      rw [hui a, hui i0]
    have hratio : ggNSPosPA_ratioOfUnits d a b = 1 := inv_eq_one.mp hratio_inv
    exact hratio
  · intro hr
    have hda : d a = d b := by
      have h1 : d a * (d b)⁻¹ = 1 := by
        have h2 := hr
        rw [ggNSPosPA7_ratioHom_apply] at h2
        unfold ggNSPosPA_ratioOfUnits at h2
        exact h2
      exact mul_inv_eq_one.mp h1
    have hu1 : u = 1 := by
      funext i
      show d (τ⁻¹ i) * (d i)⁻¹ = 1
      by_cases hia : i = a
      · subst hia
        rw [hτinv, Equiv.swap_apply_left, hda]
        group
      · by_cases hib : i = b
        · subst hib
          rw [hτinv, Equiv.swap_apply_right, hda]
          group
        · rw [hτinv, Equiv.swap_apply_of_ne_of_ne hia hib]
          group
    have hw1 : w = 1 := by
      apply Subtype.ext
      rw [hw_diag, hu1, map_one]
      simp
    have hwψ : ψ w = 1 := by rw [hw1, map_one]
    rw [hconj, hwψ, one_mul]

theorem ggNSPosPA7_ratioHom_range_card {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    (a b : Fin n) (hab : a ≠ b) :
    Nat.card (ggNSPosPA7_ratioHom h hd a b).range = p := by
  classical
  set ρ : ↥Bs →* Kˣ := ggNSPosPA7_ratioHom h hd a b with hρdef
  have hle : ρ.range ≤ rootsOfUnity p K := by
    rintro z ⟨s, rfl⟩
    rw [mem_rootsOfUnity]
    exact ggNSPosPA7_ratioHom_pow h hd a b s
  haveI : NeZero p := ⟨h.prime.ne_zero⟩
  have hcard_le : Nat.card ρ.range ≤ p :=
    le_trans (Subgroup.card_le_of_le hle) (card_rootsOfUnity K p)
  obtain ⟨ζ, hζ, hζq⟩ := ggNSPosPA_exists_zeta h
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  let v : Fin n → ℕ := fun i => (if i = a then 1 else 0) + (if i = b then p - 1 else 0)
  have hv : p ∣ ∑ i, v i := by
    have hsum : ∑ i, v i = p := by
      have h1 : ∑ i, (if i = a then (1 : ℕ) else 0) = 1 := by
        rw [Finset.sum_ite_eq' Finset.univ a (fun _ => 1)]; simp
      have h2 : ∑ i, (if i = b then (p - 1 : ℕ) else 0) = p - 1 := by
        rw [Finset.sum_ite_eq' Finset.univ b (fun _ => p - 1)]; simp
      simp only [v, Finset.sum_add_distrib, h1, h2]
      have hp2 := h.prime.two_le
      omega
    rw [hsum]
  let t : Su K 2 f n :=
    ⟨TauCeti.diagGL (fun i => ζ ^ (v i)), ggNSPosPA_diag_mem_SUid hζp hζq hv⟩
  have ht_coe : (t : GL (Fin n) K) = TauCeti.diagGL (fun i => ζ ^ (v i)) := rfl
  have ht_diag : ∃ d : Fin n → K, (t : GL (Fin n) K) = Matrix.diagonal d ∧ ∀ i, d i ^ p = 1 := by
    refine ⟨fun i => (ζ : K) ^ (v i), ?_, ?_⟩
    · rw [ht_coe, ggNSPosPA_coe_diagGL]
      simp only [Units.val_pow_eq_pow_val]
    · intro i
      rw [← pow_mul, mul_comm, pow_mul,
        show ((ζ : K) ^ p) = 1 by rw [← Units.val_pow_eq_pow_val, hζp, Units.val_one], one_pow]
  have htBs : ψ t ∈ Bs := ggNSDiag_torus_le h hd t ht_diag
  obtain ⟨hdt, hdtp⟩ := ht_diag
  have h2diag : ggIsDiagMat (t : GL (Fin n) K) := ⟨hdt, hdtp.1⟩
  have ht_ind : GGInducesUnitary (p := 2) (f := f) ψ (ψ t) (t : GL (Fin n) K) :=
    ggNSPosPA_induces_self (ψ := ψ) t
  have hwd := ggNSPosPA7_ratio_lift_wd (h := h) (hd := hd) (⟨ψ t, htBs⟩ : ↥Bs) h2diag
    (by simpa using ht_ind) a b
  have hunits : ggNSPosPA_diagUnits (ggNSPosPA_mem_diagonalTorus_of_isDiag h2diag) =
      (fun i : Fin n => ζ ^ (v i)) := by
    apply TauCeti.diagGL_injective
    rw [ggNSPosPA_diagGL_diagUnits]
  have hratio2 : ggNSPosPA_ratioOfUnits (fun i : Fin n => ζ ^ (v i)) a b = ζ ^ 2 := by
    unfold ggNSPosPA_ratioOfUnits
    have hva : v a = 1 := by simp [v, hab]
    have hvb : v b = p - 1 := by simp [v, Ne.symm hab]
    show ζ ^ (v a) * (ζ ^ (v b))⁻¹ = ζ ^ 2
    rw [hva, hvb]
    have hζpred : ζ ^ (p - 1) = ζ⁻¹ := by
      have h1 : ζ ^ (p - 1) * ζ = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel h.prime.one_le, hζp]
      have h2 : ζ⁻¹ * ζ = 1 := inv_mul_cancel ζ
      exact mul_right_cancel (h1.trans h2.symm)
    rw [hζpred]
    group
  have hratio : ρ ⟨ψ t, htBs⟩ = ζ ^ 2 := by
    rw [hρdef, ggNSPosPA7_ratioHom_apply, hwd, hunits, hratio2]
  have hmem : ζ ^ 2 ∈ ρ.range := ⟨⟨ψ t, htBs⟩, hratio⟩
  have hord : orderOf (ζ ^ 2) = p := by
    haveI : Fact p.Prime := ⟨h.prime⟩
    apply orderOf_eq_prime
    · rw [← pow_mul, mul_comm, pow_mul, hζp, one_pow]
    · intro hc
      have hdvd : p ∣ 2 := by
        have h2 := (orderOf_dvd_iff_pow_eq_one (x := ζ) (n := 2)).mpr hc
        rwa [hζ] at h2
      exact h.odd ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp hdvd)
  have hcard_ge : p ≤ Nat.card ρ.range := by
    have hsub : Subgroup.zpowers (ζ ^ 2) ≤ ρ.range := Subgroup.zpowers_le.mpr hmem
    have hc := Subgroup.card_le_of_le hsub
    rwa [Nat.card_zpowers, hord] at hc
  exact le_antisymm hcard_le hcard_ge

end CFSG.StandardType

end
