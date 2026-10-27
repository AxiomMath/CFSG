module

public import CFSG.RankThree.PartOne.K133.OddChar4
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import CFSG.RankThree.PartOne.LIT.RankPSL3

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.RankThree.GroupTheory CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
  Module Matrix

theorem exists_primitiveRoot_of_dvd_card_sub_one {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card K - 1) : ∃ ζ : K, IsPrimitiveRoot ζ p := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : p ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h1
  refine ⟨(x : K), IsPrimitiveRoot.coe_units_iff.2 ?_⟩
  have := IsPrimitiveRoot.orderOf x
  rwa [hx] at this

theorem exists_eigenbasis_gl {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {p : ℕ} [NeZero p]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (E : Subgroup (GL ι K)) [Finite E]
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ p = 1) :
    ∃ (b : Basis ι K (ι → K)) (μ : E → ι → K),
      ∀ (g : E) (j : ι), ((g : GL ι K) : Matrix ι ι K) *ᵥ (b j) = μ g j • b j := by
  classical
  let f : E → Module.End K (ι → K) := fun g => Matrix.toLinAlgEquiv' ((g : GL ι K) : Matrix ι ι K)
  have hcomm' : ∀ x y, Commute (f x) (f y) := fun x y => by
    show f x * f y = f y * f x
    simp only [f, ← map_mul]
    congr 1
    have := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) (hcomm x x.2 y y.2)
    simpa using this
  have hpow : ∀ x, f x ^ p = 1 := fun x => by
    simp only [f, ← map_pow]
    have := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) (hexp x x.2)
    have h2 : ((x : GL ι K) : Matrix ι ι K) ^ p = 1 := by simpa using this
    rw [h2, map_one]
  obtain ⟨b, μ, hb⟩ := exists_basis_common_eigenvectors_of_pow_eq_one hζ f hcomm' hpow
  let e : ι ≃ Fin (finrank K (ι → K)) :=
    (Fintype.equivFin ι).trans (finCongr (Module.finrank_fintype_fun_eq_card K).symm)
  refine ⟨b.reindex e.symm, fun g j => μ g (e j), fun g j => ?_⟩
  have := hb g (e j)
  simpa [f, Basis.reindex_apply] using this

theorem exists_conj_isDiag_gl {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {p : ℕ} [NeZero p]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (E : Subgroup (GL ι K)) [Finite E]
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ p = 1) :
    ∃ P : GL ι K, ∀ g ∈ E, ((P⁻¹ * g * P : GL ι K) : Matrix ι ι K).IsDiag := by
  classical
  obtain ⟨b', μ, hb'⟩ := exists_eigenbasis_gl hζ E hcomm hexp
  let P : Matrix ι ι K := (Pi.basisFun K ι).toMatrix b'
  have hPi : Invertible P := Basis.invertibleToMatrix (Pi.basisFun K ι) b'
  let Pu : GL ι K := unitOfInvertible P
  refine ⟨Pu, fun g hg => ?_⟩
  have hxP : ((g : GL ι K) : Matrix ι ι K) * P = P * Matrix.diagonal (fun j => μ ⟨g, hg⟩ j) := by
    ext a j
    have h := congrFun (hb' ⟨g, hg⟩ j) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_diagonal]
    simp only [P, Matrix.mul_apply, Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [h, mul_comm]
  have h1 : ((Pu⁻¹ : GL ι K) : Matrix ι ι K) = ⅟P := rfl
  have h2 : ((Pu : GL ι K) : Matrix ι ι K) = P := rfl
  have h3 : ((Pu⁻¹ * g * Pu : GL ι K) : Matrix ι ι K) = Matrix.diagonal (fun j => μ ⟨g, hg⟩ j) := by
    rw [Units.val_mul, Units.val_mul, h1, h2, Matrix.mul_assoc, hxP, ← Matrix.mul_assoc, invOf_mul_self,
      Matrix.one_mul]
  rw [h3]
  exact Matrix.isDiag_diagonal _

theorem exists_involution_centralizing_four {K : Type} [Field K] [Finite K] {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (h2 : (2 : K) ≠ 0) (E : Subgroup (GL (Fin 4) K))
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ p = 1) :
    ∃ τ : GL (Fin 4) K, τ ^ 2 = 1 ∧ (τ : Matrix (Fin 4) (Fin 4) K).det = 1 ∧
      (∀ μ : Kˣ, τ ≠ Matrix.GeneralLinearGroup.scalar (Fin 4) μ) ∧ ∀ g ∈ E, g * τ = τ * g := by
  classical
  obtain ⟨P, hP⟩ := exists_conj_isDiag_gl hζ E hcomm hexp
  let d : Fin 4 → K := fun i => if (i : ℕ) < 2 then 1 else -1
  let D : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal d
  have hDD : D * D = 1 := by
    simp only [D, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    ext i
    simp only [d]
    split_ifs <;> simp
  let Dg : GL (Fin 4) K := ⟨D, D, hDD, hDD⟩
  have hDg2 : Dg * Dg = 1 := Units.ext hDD
  have hdetD : D.det = 1 := by
    simp only [D, Matrix.det_diagonal, Fin.prod_univ_four, d]
    norm_num
  have hPP : (P : Matrix (Fin 4) (Fin 4) K).det * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  refine ⟨P * Dg * P⁻¹, ?_, ?_, ?_, ?_⟩
  · calc (P * Dg * P⁻¹) ^ 2 = P * (Dg * Dg) * P⁻¹ := by rw [pow_two]; group
      _ = 1 := by rw [hDg2]; group
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
    have : ((Dg : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = D := rfl
    rw [this, hdetD]
    calc (P : Matrix (Fin 4) (Fin 4) K).det * 1 * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det
        = (P : Matrix (Fin 4) (Fin 4) K).det * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det := by ring
      _ = 1 := hPP
  · intro μ hμ
    have hc : Matrix.GeneralLinearGroup.scalar (Fin 4) μ ∈ Subgroup.center (GL (Fin 4) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨μ, rfl⟩
    have hD' : Dg = Matrix.GeneralLinearGroup.scalar (Fin 4) μ := by
      calc Dg = P⁻¹ * (P * Dg * P⁻¹) * P := by group
        _ = P⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 4) μ) * P := by rw [hμ]
        _ = P⁻¹ * (P * Matrix.GeneralLinearGroup.scalar (Fin 4) μ) := by
          rw [mul_assoc, ← Subgroup.mem_center_iff.1 hc P]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 4) μ := by group
    have hmat := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) hD'
    simp only [Matrix.GeneralLinearGroup.coe_scalar] at hmat
    have h00 := congrFun (congrFun hmat 0) 0
    have h22 := congrFun (congrFun hmat 2) 2
    simp [Dg, D, d, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h00 h22
    apply h2
    linear_combination h00 - h22
  · intro g hg
    have hΔ : Dg * (P⁻¹ * g * P) = (P⁻¹ * g * P) * Dg := by
      have hdiag := hP g hg
      obtain ⟨δ, hδ⟩ : ∃ δ : Fin 4 → K,
          ((P⁻¹ * g * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal δ :=
        ⟨_, hdiag.diagonal_diag.symm⟩
      apply Units.ext
      have e1 : ((Dg * (P⁻¹ * g * P) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          D * ((P⁻¹ * g * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := Units.val_mul _ _
      have e2 : (((P⁻¹ * g * P) * Dg : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          ((P⁻¹ * g * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * D := Units.val_mul _ _
      rw [e1, e2, hδ]
      simp only [D, Matrix.diagonal_mul_diagonal]
      congr 1
      ext i
      exact mul_comm _ _
    calc g * (P * Dg * P⁻¹) = P * ((P⁻¹ * g * P) * Dg) * P⁻¹ := by group
      _ = P * (Dg * (P⁻¹ * g * P)) * P⁻¹ := by rw [hΔ]
      _ = (P * Dg * P⁻¹) * g := by group

theorem mem_normalizer_of_forall_commute {G : Type*} [Group G] (H : Subgroup G) (h : G)
    (hc : ∀ x ∈ H, h * x = x * h) : h ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    have := hc n hn
    rw [this, mul_assoc, mul_inv_cancel, mul_one]
    exact hn
  · intro hn
    generalize hx : h * n * h⁻¹ = x at hn
    have hxc := hc x hn
    have e1 : h⁻¹ * x * h = n := by rw [← hx]; group
    have e2 : h⁻¹ * x * h = x := by
      rw [mul_assoc, ← hxc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [← e1, e2]
    exact hn

theorem dead_statedProj_sl_four {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hdvd : p ∣ Nat.card K - 1) (h2 : (2 : K) ≠ 0)
    (hZ : Subgroup.center (StatedProj (StatedSL 4 K)) = ⊥)
    (hOut : ∀ E : Subgroup (MulAut (StatedProj (StatedSL 4 K))), IsElementaryAbelian p E →
      E ≤ inner (StatedProj (StatedSL 4 K))) :
    Dead p (StatedProj (StatedSL 4 K)) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd_card_sub_one hp hdvd
  refine dead_of_inner_el hp hZ hOut ?_
  intro A hA _
  have hZN : ∀ z : StatedSL 4 K, (z : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K → z ^ 4 = 1 :=
    fun z hz => statedSL_scalar_pow z hz
  have hp4 : ¬ p ∣ 4 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  obtain ⟨E, hEmap, hEcomm, hEexp⟩ := exists_lift_elemAb_statedProj hp hp4 (StatedSL 4 K) hZN A hA
  obtain ⟨τ, hτ2, hτdet, hτns, hτc⟩ := exists_involution_centralizing_four hζ h2
    (E.map (StatedSL 4 K).subtype)
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simpa using congrArg (StatedSL 4 K).subtype (hEcomm a ha b hb))
    (by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hEexp a ha, map_one])
  have hτM : τ ∈ StatedSL 4 K := by
    rw [LIT.statedSL_eq_det_ker, MonoidHom.mem_ker]
    apply Units.ext
    simpa using hτdet
  let t : StatedProj (StatedSL 4 K) :=
    QuotientGroup.mk (s := (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K)) (⟨τ, hτM⟩ : StatedSL 4 K)
  have ht2 : t ^ 2 = 1 := by
    have : (⟨τ, hτM⟩ : StatedSL 4 K) ^ 2 = 1 := Subtype.ext (by simpa using hτ2)
    show (QuotientGroup.mk (⟨τ, hτM⟩ : StatedSL 4 K) :
      StatedProj (StatedSL 4 K)) ^ 2 = 1
    rw [← QuotientGroup.mk_pow, this]
    rfl
  refine ⟨Subgroup.zpowers t, ?_, ?_, ?_⟩
  · intro hbot
    have hmem : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : (⟨τ, hτM⟩ : StatedSL 4 K) ∈ (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K) :=
      (QuotientGroup.eq_one_iff _).1 hmem
    obtain ⟨μ, hμ⟩ := Subgroup.mem_subgroupOf.1 h1
    exact hτns μ hμ.symm
  · intro y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 y.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hk]
    calc (t ^ k) ^ 2 = (t ^ 2) ^ k := by group
      _ = 1 := by rw [ht2, _root_.one_zpow]
  · intro a ha
    rw [← hEmap] at ha
    obtain ⟨g, hg, rfl⟩ := ha
    refine mem_normalizer_of_forall_commute _ _ ?_
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hgt : QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K)) g * t =
        t * QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K)) g := by
      show (QuotientGroup.mk g : StatedProj (StatedSL 4 K)) * QuotientGroup.mk (⟨τ, hτM⟩ : StatedSL 4 K) =
        QuotientGroup.mk (⟨τ, hτM⟩ : StatedSL 4 K) * (QuotientGroup.mk g : StatedProj (StatedSL 4 K))
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact hτc (g : GL (Fin 4) K) ⟨g, hg, rfl⟩
    exact (Commute.zpow_right (show Commute _ t from hgt) k).eq

end CFSG.RankThree.PartOne.K133
