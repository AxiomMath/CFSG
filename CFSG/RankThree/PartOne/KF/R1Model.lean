module

public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KF.CentralQuot
public import CFSG.RankThree.PartOne.KF.R9Perm

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne

variable {n p : ℕ} {K : Type} [Field K]

theorem mem_statedSL_iff {A : GL (Fin n) K} :
    A ∈ StatedSL n K ↔ (A : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

theorem torusSU_le_statedSL : torusSU p n K ≤ StatedSL n K := by
  intro x hx
  obtain ⟨d, -, hd2, rfl⟩ := mem_torusSU_iff.mp hx
  rw [mem_statedSL_iff, det_diagU, ← Units.coe_prod, hd2, Units.val_one]

theorem permGL_mem_statedSL [CharP K 2] (σ : Equiv.Perm (Fin n)) :
    (permGL σ : GL (Fin n) K) ∈ StatedSL n K :=
  mem_statedSL_iff.mpr (det_permGL σ)

theorem exists_conj_torus_statedSL [Finite K] (hp : p.Prime)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (X : Subgroup ↥(StatedSL 3 K)) (hexp : ∀ x ∈ X, x ^ p = 1)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    ∃ g : ↥(StatedSL 3 K), ∀ x ∈ X, g * x * g⁻¹ ∈
      (torusSU p 3 K).subgroupOf (StatedSL 3 K) := by
  classical
  obtain ⟨ζ, hζ⟩ := hζ
  have : NeZero p := ⟨hp.ne_zero⟩
  let e := specialLinearGroupEquivStatedSL 3 K
  let E₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) := X.comap e.toMonoidHom
  have hE₀mem : ∀ s, s ∈ E₀ ↔ e s ∈ X := fun s => Iff.rfl
  obtain ⟨A, hA⟩ := exists_conj_diagonal_of_commuting_pow_eq_one
    (IsPrimitiveRoot.coe_units_iff.mpr hζ) E₀
    (fun x hx y hy => e.injective (by rw [map_mul, map_mul]; exact hcomm _ hx _ hy))
    (fun x hx => e.injective (by rw [map_pow, map_one]; exact hexp _ hx))
  let δ : Kˣ := Matrix.GeneralLinearGroup.det A
  let D : GL (Fin 3) K := diagU (Function.update (1 : Fin 3 → Kˣ) 0 δ⁻¹)
  have hDdet : ((D : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = (δ⁻¹ : Kˣ) := by
    rw [det_diagU]
    simp [Fin.prod_univ_succ, Function.update_apply]
  have hgdet : ((D * A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hDdet]
    have : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = (δ : K) := rfl
    rw [this, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨⟨D * A, mem_statedSL_iff.mpr hgdet⟩, fun x hx => ?_⟩
  have hxdet : Matrix.GeneralLinearGroup.det (x : GL (Fin 3) K) = 1 :=
    Units.ext (mem_statedSL_iff.mp x.2)
  have h1 : ((e.symm x : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    conv_rhs => rw [← e.apply_symm_apply x]
    exact (specialLinearGroupEquivStatedSL_coe 3 K _).symm
  have hdiag : ((A * (x : GL (Fin 3) K) * A⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).IsDiag := by
    intro i j hij
    have h2 := hA (e.symm x) (by rw [hE₀mem, MulEquiv.apply_symm_apply]; exact hx) i j hij
    rw [h1] at h2
    rw [Units.val_mul, Units.val_mul]
    exact h2
  obtain ⟨d, hd⟩ := exists_diagU_of_isDiag hdiag
  have hxp : (x : GL (Fin 3) K) ^ p = 1 := by
    have := congrArg (fun y : ↥(StatedSL 3 K) => (y : GL (Fin 3) K)) (hexp x hx)
    simpa using this
  have hdp : d ^ p = 1 := by
    apply diagU_injective (K := K)
    rw [← diagU_pow, hd, conj_pow, hxp, mul_one, mul_inv_cancel, diagU_one]
  have hdprod : ∏ i, d i = 1 := by
    have h2 : Matrix.GeneralLinearGroup.det (diagU d : GL (Fin 3) K) = 1 := by
      rw [hd, map_mul, map_mul, map_inv, hxdet, mul_one, mul_inv_cancel]
    have h3 := congrArg (fun u : Kˣ => (u : K)) h2
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h3
    rw [det_diagU] at h3
    exact Units.ext (by rw [Units.coe_prod]; exact h3)
  have hxmem : (diagU d : GL (Fin 3) K) ∈ torusSU p 3 K :=
    mem_torusSU_iff.mpr ⟨d, fun i => by simpa using congrFun hdp i, hdprod, rfl⟩
  show ((D * A : GL (Fin 3) K) * (x : GL (Fin 3) K) * (D * A : GL (Fin 3) K)⁻¹) ∈ torusSU p 3 K
  have h4 : (D * A : GL (Fin 3) K) * (x : GL (Fin 3) K) * (D * A : GL (Fin 3) K)⁻¹ =
      D * (A * (x : GL (Fin 3) K) * A⁻¹) * D⁻¹ := by group
  rw [h4, ← hd]
  have h5 : D * diagU d * D⁻¹ = diagU d := by
    obtain ⟨v, hv⟩ : ∃ v : Fin 3 → Kˣ, D = diagU v := ⟨_, rfl⟩
    rw [hv, ← diagU_inv, diagU_mul, diagU_mul]
    congr 1
    rw [mul_comm v d, mul_inv_cancel_right]
  rw [h5]
  exact hxmem

theorem statedScalars_eq_center : StatedScalars (Fin n) K = Subgroup.center (GL (Fin n) K) :=
  Matrix.GeneralLinearGroup.center_eq_range_scalar.symm

theorem scalar_pow_three {z : GL (Fin 3) K} (hz : z ∈ StatedScalars (Fin 3) K)
    (hdet : (z : Matrix (Fin 3) (Fin 3) K).det = 1) : z ^ 3 = 1 := by
  obtain ⟨c, rfl⟩ := hz
  have h1 : ((c : Kˣ) : K) ^ 3 = 1 := by
    have : ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).det = (c : K) ^ 3 := by
      simp [Matrix.GeneralLinearGroup.scalar]
    rw [← this]
    exact hdet
  rw [← map_pow]
  have : c ^ 3 = 1 := Units.ext (by simpa using h1)
  rw [this, map_one]

theorem isCentralPQuot_statedSL [Finite K] (hp : p.Prime) (h5 : 5 ≤ p) :
    IsCentralPQuot p (QuotientGroup.mk'
      ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K))) := by
  refine ⟨QuotientGroup.mk'_surjective _, ?_, ?_⟩
  · intro z hz
    rw [QuotientGroup.ker_mk'] at hz
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hzc : (z : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
      rw [← statedScalars_eq_center]
      exact hz
    exact Subgroup.mem_center_iff.mp hzc g
  · rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hxk : (x : ↥(StatedSL 3 K)) ∈ (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) :=
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp x.2)
    have hx3 : x ^ 3 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      have := scalar_pow_three (z := ((x : ↥(StatedSL 3 K)) : GL (Fin 3) K)) hxk
        (mem_statedSL_iff.mp (x : ↥(StatedSL 3 K)).2)
      simpa using this
    have h3 := orderOf_dvd_of_pow_eq_one hx3
    rw [hx] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega

theorem isCentralPQuot_center {L P : Type} [Group L] [Group P] (e : L ⧸ Subgroup.center L ≃* P)
    (hcop : Nat.Coprime p (Nat.card (Subgroup.center L))) :
    IsCentralPQuot p (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) := by
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))).ker =
      Subgroup.center L := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (x : L ⧸ Subgroup.center L) = 1 ↔ x ∈ Subgroup.center L
    rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff]
  refine ⟨e.surjective.comp (QuotientGroup.mk'_surjective _), hker.le, ?_⟩
  rw [hker]
  exact hcop

end CFSG.RankThree.PartOne.KFU
