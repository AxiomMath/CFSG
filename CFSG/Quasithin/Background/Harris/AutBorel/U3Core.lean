module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismHyperbolic
public import CFSG.Quasithin.H13.A6S13820AutBorel

public section

namespace CFSG.Quasithin.Background.Harris.AutBorel

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

variable {p f : ℕ} {K : Type} [Field K]

section Eigen

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem pow_mulVec_of_eq_smul {M : Matrix ι ι K} {v : ι → K} {x : K} (hv : M *ᵥ v = x • v)
    (n : ℕ) : (M ^ n) *ᵥ v = x ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv, smul_smul, pow_succ]

theorem inv_mulVec_of_eq_smul (g : GL ι K) {v : ι → K} {x : K} (hx : x ≠ 0)
    (hv : (g : Matrix ι ι K) *ᵥ v = x • v) :
    ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v = x⁻¹ • v := by
  have h1 : ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [hv, Matrix.mulVec_smul] at h1
  calc ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v
      = x⁻¹ • (x • (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)) := by
        rw [smul_smul, inv_mul_cancel₀ hx, one_smul]
    _ = x⁻¹ • v := by rw [h1]

end Eigen

@[expose] noncomputable def eOne (K : Type) [Field K] : HypIndex 1 1 → K :=
  Pi.single (.inl 0) 1

theorem eOne_ne_zero : eOne K ≠ 0 := by
  intro h0
  have := congrFun h0 (.inl 0)
  simp [eOne] at this

theorem eOne_apply_inl : eOne K (.inl 0) = 1 := by simp [eOne]

theorem comp_eOne (σ : K ≃+* K) : (σ : K →+* K) ∘ eOne K = eOne K := by
  funext j
  simp only [Function.comp_apply, eOne, Pi.single_apply]
  split_ifs <;> simp

theorem glAut_mulVec_eOne (σ : K ≃+* K) (g : GL (HypIndex 1 1) K) {x : K}
    (hg : (g : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ eOne K = x • eOne K) :
    ((glAut σ g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ eOne K =
      σ x • eOne K := by
  rw [coe_glAut]
  funext i
  have h1 := RingHom.map_mulVec (σ : K →+* K) (g : Matrix (HypIndex 1 1) (HypIndex 1 1) K)
    (eOne K) i
  rw [comp_eOne, hg] at h1
  change ((g : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map (σ : K →+* K) *ᵥ eOne K) i =
    (σ x • eOne K) i
  rw [← h1, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  congr 1
  exact congrFun (comp_eOne σ) i

variable (h : UnitaryFieldData p f K)

theorem fix_unitriangular_iff (v : HypIndex 1 1 → K) :
    (∀ u ∈ hypUnitriangular h 1 1,
      ((u : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ v = v) ↔
      ∃ c : K, v = c • eOne K := by
  obtain ⟨hF1, hfix, -⟩ := unitriangular_invariant_isotropic_subspaces h le_rfl le_rfl
  rw [hfix v, hF1, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩

theorem unitriangular_mulVec_eOne {u : hypSU h 1 1} (hu : u ∈ hypUnitriangular h 1 1) :
    ((u : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ eOne K = eOne K :=
  (fix_unitriangular_iff h (eOne K)).mpr ⟨1, (one_smul K _).symm⟩ u hu

theorem exists_eq_mul_of_proj_mem {w : hypSU h 1 1}
    (hw : hypProj h 1 1 w ∈ hypProjUnitriangular h 1 1) :
    ∃ u ∈ hypUnitriangular h 1 1, ∃ z ∈ hypScalars h 1 1, w = u * z := by
  obtain ⟨u, hu, hue⟩ := hw
  refine ⟨u, hu, u⁻¹ * w, ?_, by group⟩
  have h1 : hypProj h 1 1 (u⁻¹ * w) = 1 := by
    rw [map_mul, map_inv, hue, inv_mul_cancel]
  rwa [← MonoidHom.mem_ker, ker_hypProj] at h1

theorem exists_torus_mulVec_eOne (a : Kˣ) :
    ∃ t ∈ hypBorel h 1 1,
      ((t : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ eOne K =
        (a : K) • eOne K := by
  have hbar0 : h.bar (a : K) ≠ 0 := (map_ne_zero h.bar).mpr a.ne_zero
  set d0 : Kˣ := Units.mk0 (h.bar (a : K) / a) (div_ne_zero hbar0 a.ne_zero) with hd0
  have hnorm : h.norm (d0 : K) = 1 := by
    rw [hd0, Units.val_mk0, UnitaryFieldData.norm, map_div₀, h.bar_bar]
    field_simp
  have hratio : torusRatio h (fun _ : Fin 1 => a) (fun _ : Fin 1 => d0) = 1 := by
    rw [torusRatio, Fin.prod_univ_one, Fin.prod_univ_one, hd0, Units.val_mk0]
    field_simp
  obtain ⟨t, ht, htm⟩ := torusMat_mem_hypSU h (fun _ : Fin 1 => a) (fun _ => hnorm) hratio
  refine ⟨t, hypTorus_le_hypBorel h ht, ?_⟩
  rw [htm, eOne, diagonal_mulVec_single, mul_one]
  funext i
  simp [torusEntries, Pi.single_apply]

theorem pow_three_mem {G : Type*} [Group G] {N C : Subgroup G}
    (hn : (C.subgroupOf N).Normal) (hidx : C.relIndex N ∣ 3) {s : G} (hs : s ∈ N) :
    s ^ 3 ∈ C := by
  have hcard : Nat.card (↥N ⧸ C.subgroupOf N) ∣ 3 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hfin : Finite (↥N ⧸ C.subgroupOf N) := by
    refine Nat.finite_of_card_ne_zero ?_
    intro h0
    rw [h0] at hcard
    norm_num at hcard
  have h1 : ((⟨s, hs⟩ : ↥N) : ↥N ⧸ C.subgroupOf N) ^ 3 = 1 := by
    obtain ⟨m, hm⟩ := hcard
    rw [hm, pow_mul, pow_card_eq_one', one_pow]
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem card_hypUnitriangular_two (h : UnitaryFieldData 2 f K) :
    Nat.card (hypUnitriangular h 1 1) = 2 ^ (3 * f) := by
  rw [(unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl).1, ← pow_mul]
  congr 1
  norm_num
  ring

theorem exists_smul_eOne (h : UnitaryFieldData 2 f K) {α : MulAut (hypPSU h 1 1)}
    (hαS : (hypProjUnitriangular h 1 1).map α.toMonoidHom = hypProjUnitriangular h 1 1)
    {σ : K ≃+* K} {B : GL (HypIndex 1 1) K}
    (hα : ∀ g : hypSU h 1 1, ∃ hg : B * glAut σ (g : GL (HypIndex 1 1) K) * B⁻¹ ∈ hypSU h 1 1,
      α (hypProj h 1 1 g) = hypProj h 1 1 ⟨_, hg⟩) :
    ∃ c : K, c ≠ 0 ∧
      (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ eOne K = c • eOne K := by
  have := h.finite
  have hfix : ∀ u' ∈ hypUnitriangular h 1 1,
      ((u' : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
        ((B : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ eOne K) =
        (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ eOne K := by
    intro u' hu'
    have hmem : hypProj h 1 1 u' ∈ (hypProjUnitriangular h 1 1).map α.toMonoidHom := by
      rw [hαS]
      exact ⟨u', hu', rfl⟩
    obtain ⟨x, ⟨u, hu, rfl⟩, hxu⟩ := hmem
    obtain ⟨hg, hαu⟩ := hα u
    set w : hypSU h 1 1 := ⟨_, hg⟩ with hw
    have hpw : hypProj h 1 1 w = hypProj h 1 1 u' := by
      rw [← hαu]
      exact hxu
    have hz : u'⁻¹ * w ∈ hypScalars h 1 1 := by
      rw [← ker_hypProj, MonoidHom.mem_ker, map_mul, map_inv, hpw, inv_mul_cancel]
    have hz1 : u'⁻¹ * w = 1 := by
      set N := Nat.card (hypUnitriangular h 1 1) with hN
      have hu'N : u' ^ N = 1 := by
        have h1 : (⟨u', hu'⟩ : hypUnitriangular h 1 1) ^ N = 1 := pow_card_eq_one'
        have h2 := congrArg (fun x : hypUnitriangular h 1 1 => (x : hypSU h 1 1)) h1
        simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
        exact h2
      have huN : u ^ N = 1 := by
        have h1 : (⟨u, hu⟩ : hypUnitriangular h 1 1) ^ N = 1 := pow_card_eq_one'
        have h2 := congrArg (fun x : hypUnitriangular h 1 1 => (x : hypSU h 1 1)) h1
        simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
        exact h2
      have hwN : w ^ N = 1 := by
        apply Subtype.ext
        rw [SubmonoidClass.coe_pow, hw]
        change (B * glAut σ (u : GL (HypIndex 1 1) K) * B⁻¹) ^ N = 1
        rw [conj_pow, ← map_pow, ← SubmonoidClass.coe_pow, huN]
        simp
      have hcen := normOneScalars_le_center h (hypSU h 1 1) (2 * 1 + 1) hz
      have hcomm : Commute u' (u'⁻¹ * w) := (Subgroup.mem_center_iff.mp hcen u')
      have hzN : (u'⁻¹ * w) ^ N = 1 := by
        have hweq : w = u' * (u'⁻¹ * w) := by group
        rw [hweq, hcomm.mul_pow, hu'N, one_mul] at hwN
        exact hwN
      obtain ⟨c, -, hc3, hcz⟩ := mem_normOneScalars.mp hz
      have hz3 : (u'⁻¹ * w) ^ 3 = 1 := by
        apply Subtype.ext
        rw [SubmonoidClass.coe_pow, hcz, ← map_pow]
        have hc3' : c ^ 3 = 1 := hc3
        rw [hc3', map_one]
        rfl
      have hcop : Nat.Coprime N 3 := by
        rw [hN, card_hypUnitriangular_two h]
        exact Nat.Coprime.pow_left _ (by norm_num)
      exact (pow_eq_one_iff_of_coprime hcop).mp ⟨hzN, hz3⟩
    have hwu : w = u' := (inv_mul_eq_one.mp hz1).symm
    have hue := unitriangular_mulVec_eOne h hu
    have hσu := glAut_mulVec_eOne σ (u : GL (HypIndex 1 1) K) (x := 1) (by rw [one_smul]; exact hue)
    rw [map_one, one_smul] at hσu
    rw [← hwu, hw]
    change ((B * glAut σ (u : GL (HypIndex 1 1) K) * B⁻¹ : GL (HypIndex 1 1) K) :
        Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
        ((B : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ eOne K) =
      (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ eOne K
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul,
      ← Matrix.mulVec_mulVec, hσu]
  obtain ⟨c, hc⟩ := (fix_unitriangular_iff h _).mp hfix
  refine ⟨c, ?_, hc⟩
  rintro rfl
  rw [zero_smul] at hc
  have h1 : ((B⁻¹ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
      ((B : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ eOne K) = eOne K := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [hc, Matrix.mulVec_zero] at h1
  exact eOne_ne_zero h1.symm

theorem fix_pow_nine (h : UnitaryFieldData 2 f K) {C : Subgroup (hypPSU h 1 1)}
    {α : MulAut (hypPSU h 1 1)}
    (hBor : H13.A6.BorelAut13820 (hypProjUnitriangular h 1 1) C α)
    {σ : K ≃+* K} {B : GL (HypIndex 1 1) K}
    (hα : ∀ g : hypSU h 1 1, ∃ hg : B * glAut σ (g : GL (HypIndex 1 1) K) * B⁻¹ ∈ hypSU h 1 1,
      α (hypProj h 1 1 g) = hypProj h 1 1 ⟨_, hg⟩) (a : Kˣ) :
    σ ((a : K) ^ 9) = (a : K) ^ 9 := by
  obtain ⟨-, -, -, hCn, hidx, -, hαS, hcomm⟩ := hBor
  obtain ⟨c, hc0, hBe⟩ := exists_smul_eOne h hαS hα
  obtain ⟨t, htB, hte⟩ := exists_torus_mulVec_eOne h a
  have htN : hypProj h 1 1 t ∈
      Subgroup.normalizer (hypProjUnitriangular h 1 1 : Set (hypPSU h 1 1)) := by
    rw [normalizer_hypProjUnitriangular h le_rfl le_rfl]
    exact ⟨t, htB, rfl⟩
  have hmem := hcomm _ (pow_three_mem hCn hidx htN)
  rw [← map_pow] at hmem
  obtain ⟨hg, hαt⟩ := hα (t ^ 3)
  rw [hαt, ← map_inv, ← map_mul] at hmem
  obtain ⟨u, hu, z, hz, hw⟩ := exists_eq_mul_of_proj_mem h hmem
  obtain ⟨l, -, hl3, hlz⟩ := mem_normOneScalars.mp hz
  have key := congrArg (fun g : hypSU h 1 1 =>
    ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ eOne K) hw
  have ha0 : (a : K) ^ 3 ≠ 0 := pow_ne_zero _ a.ne_zero
  have ht3 : (((t ^ 3 : hypSU h 1 1) : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ eOne K = (a : K) ^ 3 • eOne K := by
    rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val]
    exact pow_mulVec_of_eq_smul hte 3
  have hσt3 := glAut_mulVec_eOne σ ((t ^ 3 : hypSU h 1 1) : GL (HypIndex 1 1) K) ht3
  have hBinv := inv_mulVec_of_eq_smul B hc0 hBe
  have ht3inv := inv_mulVec_of_eq_smul ((t ^ 3 : hypSU h 1 1) : GL (HypIndex 1 1) K) ha0 ht3
  have hlhs : ((((t ^ 3)⁻¹ * ⟨_, hg⟩ : hypSU h 1 1) : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ eOne K =
      (((a : K) ^ 3)⁻¹ * σ ((a : K) ^ 3)) • eOne K := by
    change (((((t ^ 3 : hypSU h 1 1) : GL (HypIndex 1 1) K))⁻¹ *
        (B * glAut σ ((t ^ 3 : hypSU h 1 1) : GL (HypIndex 1 1) K) * B⁻¹) :
          GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ eOne K = _
    rw [Units.val_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBinv]
    simp only [Matrix.mulVec_smul, hσt3, hBe, ht3inv, smul_smul]
    congr 1
    field_simp
  have hrhs : (((u * z : hypSU h 1 1) : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ eOne K = (l : K) • eOne K := by
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hlz,
      GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← smul_one_eq_diagonal,
      Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul, unitriangular_mulVec_eOne h hu]
  rw [hlhs, hrhs] at key
  have hcoord := congrFun key (.inl 0)
  rw [Pi.smul_apply, Pi.smul_apply, eOne_apply_inl, smul_eq_mul, smul_eq_mul, mul_one,
    mul_one] at hcoord
  have hσ3 : σ ((a : K) ^ 3) = (l : K) * (a : K) ^ 3 := by
    rw [← hcoord]
    field_simp
  have hl3' : (l : K) ^ 3 = 1 := by
    have := congrArg Units.val hl3
    simpa using this
  calc σ ((a : K) ^ 9) = σ ((a : K) ^ 3) ^ 3 := by rw [← map_pow, ← pow_mul]
    _ = (l : K) ^ 3 * (a : K) ^ 9 := by rw [hσ3, mul_pow, ← pow_mul]
    _ = (a : K) ^ 9 := by rw [hl3', one_mul]

theorem isometry_mul (h : UnitaryFieldData p f K) {X Y : Matrix (HypIndex 1 1) (HypIndex 1 1) K}
    (hX : (X.map h.bar)ᵀ * hypGram 1 1 K * X = hypGram 1 1 K)
    (hY : (Y.map h.bar)ᵀ * hypGram 1 1 K * Y = hypGram 1 1 K) :
    ((X * Y).map h.bar)ᵀ * hypGram 1 1 K * (X * Y) = hypGram 1 1 K := by
  rw [Matrix.map_mul, Matrix.transpose_mul]
  calc (Y.map h.bar)ᵀ * (X.map h.bar)ᵀ * hypGram 1 1 K * (X * Y)
      = (Y.map h.bar)ᵀ * ((X.map h.bar)ᵀ * hypGram 1 1 K * X) * Y := by
        simp only [Matrix.mul_assoc]
    _ = hypGram 1 1 K := by rw [hX, hY]

theorem norm_det_eq_one (h : UnitaryFieldData p f K) {X : Matrix (HypIndex 1 1) (HypIndex 1 1) K}
    (hX : (X.map h.bar)ᵀ * hypGram 1 1 K * X = hypGram 1 1 K) : h.norm X.det = 1 := by
  have h1 := congrArg Matrix.det hX
  have hdet : (X.map h.bar).det = h.bar X.det := (RingHom.map_det h.bar X).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet] at h1
  have hJ : (hypGram 1 1 K).det ≠ 0 := by
    have h2 := congrArg Matrix.det (hypGram_mul_self (r := 1) (ε := 1) (K := K))
    rw [Matrix.det_mul, Matrix.det_one] at h2
    intro h0
    rw [h0, zero_mul] at h2
    exact zero_ne_one h2
  have h3 : (h.bar X.det * X.det) * (hypGram 1 1 K).det = 1 * (hypGram 1 1 K).det := by
    linear_combination h1
  rw [UnitaryFieldData.norm, mul_comm]
  exact mul_right_cancel₀ hJ h3

theorem inner_of_conj (h : UnitaryFieldData p f K) {α : MulAut (hypPSU h 1 1)} {k : ℕ}
    (hk : α ^ 2 ^ k = 1) {B : GL (HypIndex 1 1) K}
    (hB : ((B : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map h.bar)ᵀ * hypGram 1 1 K *
      (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = hypGram 1 1 K)
    (hα : ∀ g : hypSU h 1 1, ∃ hg : B * (g : GL (HypIndex 1 1) K) * B⁻¹ ∈ hypSU h 1 1,
      α (hypProj h 1 1 g) = hypProj h 1 1 ⟨_, hg⟩) :
    ∃ y : hypPSU h 1 1, α = MulAut.conj y := by
  set d : Kˣ := Matrix.GeneralLinearGroup.det B with hd
  have hB3 : (((B ^ 3 : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map
      h.bar)ᵀ * hypGram 1 1 K * ((B ^ 3 : GL (HypIndex 1 1) K) :
        Matrix (HypIndex 1 1) (HypIndex 1 1) K) = (1 : K) • hypGram 1 1 K := by
    rw [one_smul, pow_succ, pow_succ, pow_one, Units.val_mul, Units.val_mul]
    exact isometry_mul h (isometry_mul h hB hB) hB
  have hnd : h.norm (d : K) = 1 := norm_det_eq_one h hB
  have hiso := scalar_mul_isometry h hB3 (c := d⁻¹) (by
    rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hnd, inv_one, mul_one])
  have hdetM : ((Matrix.GeneralLinearGroup.scalar (HypIndex 1 1) d⁻¹ * B ^ 3 :
      GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det = 1 := by
    have hBdet : (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    have hcard : Fintype.card (HypIndex 1 1) = 3 := by simp
    rw [Units.val_mul, Matrix.det_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, hcard, Units.val_pow_eq_pow_val,
      Matrix.det_pow, ← mul_pow, Units.val_inv_eq_inv_val, hd,
      Matrix.GeneralLinearGroup.val_det_apply, inv_mul_cancel₀ hBdet, one_pow]
  set M : hypSU h 1 1 := ⟨_, mem_hypSU.mpr ⟨hiso, hdetM⟩⟩ with hM
  choose hg hαg using hα
  have h3 : α ^ 3 = MulAut.conj (hypProj h 1 1 M) := by
    ext x
    obtain ⟨g, rfl⟩ := hypProj_surjective h 1 1 x
    rw [MulAut.conj_apply, pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, hαg,
      hαg, hαg, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change B * (B * (B * (g : GL (HypIndex 1 1) K) * B⁻¹) * B⁻¹) * B⁻¹ =
      (Matrix.GeneralLinearGroup.scalar (HypIndex 1 1) d⁻¹ * B ^ 3) * (g : GL (HypIndex 1 1) K) *
        (Matrix.GeneralLinearGroup.scalar (HypIndex 1 1) d⁻¹ * B ^ 3)⁻¹
    have hc := (commute_scalar d⁻¹ (B ^ 3 * (g : GL (HypIndex 1 1) K) * (B ^ 3)⁻¹)).eq
    calc B * (B * (B * (g : GL (HypIndex 1 1) K) * B⁻¹) * B⁻¹) * B⁻¹
        = B ^ 3 * (g : GL (HypIndex 1 1) K) * (B ^ 3)⁻¹ := by
          rw [show B ^ 3 = B * B * B by rw [pow_succ, pow_succ, pow_one]]
          group
      _ = (Matrix.GeneralLinearGroup.scalar (HypIndex 1 1) d⁻¹ * B ^ 3) *
            (g : GL (HypIndex 1 1) K) *
            (Matrix.GeneralLinearGroup.scalar (HypIndex 1 1) d⁻¹ * B ^ 3)⁻¹ := by
          have hre : (Matrix.GeneralLinearGroup.scalar (HypIndex 1 1) d⁻¹ * B ^ 3) *
              (g : GL (HypIndex 1 1) K) *
              (Matrix.GeneralLinearGroup.scalar (HypIndex 1 1) d⁻¹ * B ^ 3)⁻¹ =
              Matrix.GeneralLinearGroup.scalar (HypIndex 1 1) d⁻¹ *
                (B ^ 3 * (g : GL (HypIndex 1 1) K) * (B ^ 3)⁻¹) *
                (Matrix.GeneralLinearGroup.scalar (HypIndex 1 1) d⁻¹)⁻¹ := by group
          rw [hre, ← hc, mul_inv_cancel_right]
  have hk' : α ^ 2 ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hk, one_pow]
  have hcop : Nat.Coprime 3 (2 ^ (k + 1)) := Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop
    (Nat.one_lt_two_pow (Nat.succ_ne_zero k))
  refine ⟨hypProj h 1 1 M ^ m, ?_⟩
  calc α = α ^ (3 * m % 2 ^ (k + 1)) := by rw [hm, pow_one]
    _ = α ^ (3 * m) := (pow_eq_pow_mod _ hk').symm
    _ = MulAut.conj (hypProj h 1 1 M ^ m) := by rw [pow_mul, h3, map_pow]

theorem autBorel_hypPSU (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (hfield : ∀ σ : K ≃+* K, (∀ a : Kˣ, σ ((a : K) ^ 9) = (a : K) ^ 9) → σ = 1 ∨ f = 3)
    {C : Subgroup (hypPSU h 1 1)} {α : MulAut (hypPSU h 1 1)}
    (hBor : H13.A6.BorelAut13820 (hypProjUnitriangular h 1 1) C α) :
    (∃ g, α = MulAut.conj g) ∨ f = 3 := by
  have hq : 2 < 2 ^ f := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨σ, B, hB, hα⟩ := exists_isometry_hypPSU h hq α
  rcases hfield σ (fix_pow_nine h hBor hα) with rfl | h3
  · left
    obtain ⟨k, hk⟩ := hBor.2.2.2.2.2.1
    refine inner_of_conj h hk hB fun g => ?_
    obtain ⟨hg, hαg⟩ := hα g
    have h1 : glAut (1 : K ≃+* K) (g : GL (HypIndex 1 1) K) = g := by
      rw [map_one]
      rfl
    have hg' : B * (g : GL (HypIndex 1 1) K) * B⁻¹ ∈ hypSU h 1 1 := h1 ▸ hg
    refine ⟨hg', ?_⟩
    rw [hαg]
    congr 1
  · exact Or.inr h3

end CFSG.Quasithin.Background.Harris.AutBorel
