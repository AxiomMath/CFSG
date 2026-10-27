module

public import CFSG.RankThree.PartOne.KC.SymplecticDefiningCriterion
public import CFSG.RankThree.PartOne.KC.SymplecticFourTransvectionPointwise
public import CFSG.RankThree.PartOne.KC.SymplecticFourTransvectionTransport

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

namespace KCSymplecticFour

variable {K : Type} [Field K]

@[expose] def radicalStd (K : Type) [Field K] : Subgroup (StatedSp 2 K) :=
  (radical K).map (spEquiv K).toMonoidHom

theorem conjAut_eq_conj_of_eq_scalar_mul {r : ℕ} (A : gsp r K) (z : Kˣ) (y : StatedSp r K)
    (hA : (A : GL (Fin r ⊕ Fin r) K) =
      GeneralLinearGroup.scalar (Fin r ⊕ Fin r) z * (y : GL (Fin r ⊕ Fin r) K)) :
    conjAut r K A = MulAut.conj (proj r K y) := by
  have hz : GeneralLinearGroup.scalar (Fin r ⊕ Fin r) z ∈
      Subgroup.center (GL (Fin r ⊕ Fin r) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  ext t
  obtain ⟨g, rfl⟩ := SymplecticHigher.proj_surjective t
  rw [conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coe_conjSp, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hA]
  set z' := GeneralLinearGroup.scalar (Fin r ⊕ Fin r) z
  set u := (y : GL (Fin r ⊕ Fin r) K)
  have hzc := Subgroup.mem_center_iff.mp hz (u * (g : GL (Fin r ⊕ Fin r) K) * u⁻¹)
  calc z' * u * (g : GL (Fin r ⊕ Fin r) K) * (z' * u)⁻¹ =
        u * (g : GL (Fin r ⊕ Fin r) K) * u⁻¹ * z' * z'⁻¹ := by
        rw [hzc]
        group
    _ = u * (g : GL (Fin r ⊕ Fin r) K) * u⁻¹ := by group

theorem exists_eq_conj_of_forall_fix_radicalStd (h2 : (2 : K) ≠ 0) (A : gsp 2 K) (σ : K ≃+* K)
    (hexact : ∀ y ∈ radicalStd K, conjSp 2 K A (fieldSp 2 K σ y) = y) :
    ∃ y' ∈ radicalStd K, conjAut 2 K A * fieldAut 2 K σ = MulAut.conj (proj 2 K y') := by
  obtain ⟨μ, hμ⟩ := A.2
  set A₀ : GL (Fin 4) K := (coordGL K).symm (A : GL (Fin 2 ⊕ Fin 2) K) with hA₀
  have hρA₀ : coordAlg K (A₀ : Matrix (Fin 4) (Fin 4) K) =
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [← coe_coordGL, hA₀, MulEquiv.apply_symm_apply]
  have hA₀μ : (A₀ : Matrix (Fin 4) (Fin 4) K)ᵀ * symplecticFourGram K * A₀ =
      (μ : K) • symplecticFourGram K := by
    apply (coordAlg K).injective
    rw [← coordAlg_conj_gram, map_smul, coordAlg_gram, hρA₀]
    exact hμ
  have hfix : ∀ s t b : K, (A₀ : Matrix (Fin 4) (Fin 4) K) * uMat (σ s) (σ t) (σ b) =
      uMat s t b * A₀ := by
    intro s t b
    have hy := hexact (spEquiv K (uElt s t b)) ⟨uElt s t b, uElt_mem_radical s t b, rfl⟩
    have hy' := congrArg (fun z : StatedSp 2 K => ((z : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hy
    simp only [coe_conjSp, Units.val_mul, coe_fieldSp, coe_spEquiv, coe_coordGL, coe_uElt] at hy'
    have hAinv : (((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 :=
      Units.inv_mul _
    have hcomm : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (coordAlg K (uMat s t b)).map σ = coordAlg K (uMat s t b) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      calc _ = ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
            (coordAlg K (uMat s t b)).map σ *
            ((((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
              ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
            rw [hAinv, Matrix.mul_one]
        _ = (((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
            (coordAlg K (uMat s t b)).map σ *
            (((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
            ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hy']
    apply (coordAlg K).injective
    rw [map_mul, map_mul, hρA₀, ← uMat_map, ← coordAlg_map]
    exact hcomm
  obtain ⟨hσ, a, d, ha, hAd⟩ := eq_scalar_add_of_fix h2 μ.ne_zero hA₀μ σ hfix
  subst hσ
  refine ⟨spEquiv K (uElt 0 0 (d / a)), ⟨uElt 0 0 (d / a), uElt_mem_radical 0 0 (d / a), rfl⟩, ?_⟩
  rw [map_one, mul_one]
  refine conjAut_eq_conj_of_eq_scalar_mul A (Units.mk0 a ha) _ ?_
  apply Units.ext
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mk0, coe_spEquiv, coe_coordGL,
    coe_uElt, uMat_zero_zero, ← hρA₀, hAd, map_add, map_add, map_smul, map_smul, map_one,
    coordAlg_E14, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, map_smul, coordAlg_E14,
    smul_add, smul_smul, mul_div_cancel₀ _ ha]

end KCSymplecticFour

open KCSymplecticFour

@[expose] def symplecticStdTransvection (K : Type) [Field K] (c : K) : StatedSp 2 K :=
  spEquiv K (symplecticFourTransvection K c)

theorem coe_symplecticStdTransvection {K : Type} [Field K] (c : K) :
    (((symplecticStdTransvection K c : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      1 + Matrix.single (Sum.inl 0) (Sum.inr 0) c :=
  coe_spEquiv_transvection c

theorem symplectic_transvection_std_normalPrimeComplementsTrivial {p f : ℕ} {K : Type} [Field K]
    (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) {c : K} (hc : c ≠ 0)
    (u : StatedSp 2 K)
    (hu : ((u : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      1 + Matrix.single (Sum.inl 0) (Sum.inr 0) c) :
    NormalPrimeComplementsTrivial p (MulAut.conj (proj 2 K u)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hp.ne_zero)
  have := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) ((CharP.cast_eq_zero_iff K p 2).mp h')
    omega
  have hu' : u = symplecticStdTransvection K c := by
    apply Subtype.ext
    apply Units.ext
    rw [hu, coe_symplecticStdTransvection]
  subst hu'
  have htv : symplecticFourTransvection K c ∈ radical K :=
    ⟨0, 0, c, by rw [coe_symplecticFourTransvection, uMat_zero_zero]⟩
  refine KCSymplectic.symplectic_normalPrimeComplementsTrivial_of_radical_data hp hp3 hf
    (le_refl 2) hK _ ?_ (Matrix.single (Sum.inl 0) (Sum.inr 0) c) ?_ (radicalStd K) ?_ ?_ ?_ ?_
  · rw [symplecticStdTransvection, ← map_pow, pow_char_eq_one_of_mem_radical htv, map_one]
  · intro g hg
    have h1 := congrArg (fun z : StatedSp 2 K => ((z : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hg
    simp only [Subgroup.coe_mul, Units.val_mul, coe_symplecticStdTransvection] at h1
    rw [mul_add, add_mul, mul_one, one_mul] at h1
    exact add_left_cancel h1
  · rintro _ ⟨y₀, hy₀, rfl⟩
    change spEquiv K y₀ * spEquiv K (symplecticFourTransvection K c) =
      spEquiv K (symplecticFourTransvection K c) * spEquiv K y₀
    rw [← map_mul, ← map_mul, radical_comm_transvection hy₀ c]
  · rintro _ ⟨y₀, hy₀, rfl⟩
    change (spEquiv K y₀) ^ p = 1
    rw [← map_pow, pow_char_eq_one_of_mem_radical hy₀, map_one]
  · intro g hg y hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    set g₀ : symplecticFourS K := (spEquiv K).symm g with hg₀
    have hgρ : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        coordAlg K ((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      rw [← coe_coordGL, ← coe_spEquiv, hg₀, MulEquiv.apply_symm_apply]
    have hNρ : Matrix.single (Sum.inl 0) (Sum.inr 0) c =
        coordAlg K (c • symplecticFourE14 K) := by
      rw [map_smul, coordAlg_E14, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hgρ, hNρ, ← map_mul, ← map_mul] at hg
    have hg' := (coordAlg K).injective hg
    rw [Matrix.mul_smul, Matrix.smul_mul] at hg'
    have hcomm := smul_right_injective _ hc hg'
    refine ⟨g₀ * y₀ * g₀⁻¹, conj_mem_radical_of_commute hcomm hy₀, ?_⟩
    change spEquiv K (g₀ * y₀ * g₀⁻¹) = g * spEquiv K y₀ * g⁻¹
    rw [map_mul, map_mul, map_inv, hg₀, MulEquiv.apply_symm_apply]
  · intro A σ hex
    exact exists_eq_conj_of_forall_fix_radicalStd h2 A σ hex

end CFSG.RankThree.PartOne
