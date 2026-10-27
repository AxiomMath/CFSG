module

public import CFSG.LieType.BorelTits.LeviOrder
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalC3Part2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.NativePinFinalPart1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.RationalA1

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Open Multiplicative

open scoped Matrix

theorem map_uSL_a1 {K L : Type} [Field K] [Field L] (f : K →+* L) (t : K) :
    Matrix.SpecialLinearGroup.map f (uSL t) = uSL (f t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL]

theorem map_vSL_a1 {K L : Type} [Field K] [Field L] (f : K →+* L) (t : K) :
    Matrix.SpecialLinearGroup.map f (vSL t) = vSL (f t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vSL]

theorem SL2_map_algebraMap_range_eq_eqLocus {k Ω : Type} [Field k] [Finite k] [Field Ω]
    [Algebra k Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ Nat.card k) :
    (Matrix.SpecialLinearGroup.map (algebraMap k Ω) :
        Matrix.SpecialLinearGroup (Fin 2) k →*
          Matrix.SpecialLinearGroup (Fin 2) Ω).range =
      (Matrix.SpecialLinearGroup.map Fr :
        Matrix.SpecialLinearGroup (Fin 2) Ω →*
          Matrix.SpecialLinearGroup (Fin 2) Ω).eqLocus (MonoidHom.id _) := by
  apply le_antisymm
  · rintro x ⟨g, rfl⟩
    apply Subtype.ext
    ext i j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, MonoidHom.id_apply]
    exact DFunLike.congr_fun (CFSG.LieType.Chevalley.frobenius_comp_algebraMap Fr hFr)
      ((g : Matrix (Fin 2) (Fin 2) k) i j)
  · intro X hX
    have hent : ∀ i j, (X : Matrix (Fin 2) (Fin 2) Ω) i j ∈ Set.range (algebraMap k Ω) := by
      intro i j
      apply CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq
      have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) Ω =>
        (A : Matrix (Fin 2) (Fin 2) Ω) i j) hX
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply, MonoidHom.id_apply] at h
      exact (hFr ((X : Matrix (Fin 2) (Fin 2) Ω) i j)).symm.trans h
    obtain ⟨Y, hY⟩ :=
      CFSG.RankThree.Classical2.exists_map_eq_of_forall_mem_range
        (n := 2) (algebraMap k Ω).injective X hent
    exact ⟨Y, hY⟩

theorem rootSL2_range_eq_sup
    {Ω : Type} [Field Ω] {γ : Fin Tag.F4.rank → ℤ}
    (hγ : IsRoot Tag.F4 γ) :
    (rootSL2 Tag.F4 Ω γ).range =
      rootSubgroup Tag.F4 Ω γ ⊔ rootSubgroup Tag.F4 Ω (-γ) :=
  range_rootSL2_of_isRoot hγ

noncomputable def phiA1
    {Ω k : Type} [Field Ω] [Field k] [Algebra k Ω]
    (z : ModGL Tag.F4 Ω) (γ : Fin Tag.F4.rank → ℤ) :
    Matrix.SpecialLinearGroup (Fin 2) k →* ModGL Tag.F4 Ω :=
  ((MulAut.conj z).toMonoidHom.comp (rootSL2 Tag.F4 Ω γ)).comp
    (Matrix.SpecialLinearGroup.map (algebraMap k Ω))

theorem phiA1_injective
    {Ω k : Type} [Field Ω] [CharP Ω 2] [Field k] [Algebra k Ω]
    (z : ModGL Tag.F4 Ω) (γ : Fin Tag.F4.rank → ℤ) :
    Function.Injective (phiA1 (k := k) z γ) :=
  ((MulAut.conj z).injective.comp
      (CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_injective_of_two
        (CharP.cast_eq_zero Ω 2) γ)).comp
    (CFSG.RankThree.Classical2.specialLinearGroup_map_injective (algebraMap k Ω).injective)

theorem phiA1_range
    {Ω k : Type} [Field Ω] [CharP Ω 2] [Field k] [Finite k] [Algebra k Ω]
    (D : LangDatum Tag.F4 Ω) (σ : Ω ≃+* Ω) (hσ : ∀ c, σ c = c ^ Nat.card k)
    (z : ModGL Tag.F4 Ω) (γ : Fin Tag.F4.rank → ℤ) (hγ : IsRoot Tag.F4 γ)
    (hzF : ∀ g ∈ (rootSL2 Tag.F4 Ω γ).range,
      D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹) :
    (phiA1 (k := k) z γ).range =
      MonoidHom.range ((MulAut.conj z).toMonoidHom.comp (rootSL2 Tag.F4 Ω γ)) ⊓
        D.step.eqLocus (MonoidHom.id _) := by
  change MonoidHom.range
    (((MulAut.conj z).toMonoidHom.comp (rootSL2 Tag.F4 Ω γ)).comp
      (Matrix.SpecialLinearGroup.map (algebraMap k Ω))) = _
  have hi : Function.Injective
      ((MulAut.conj z).toMonoidHom.comp (rootSL2 Tag.F4 Ω γ)) :=
    (MulAut.conj z).injective.comp
      (CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_injective_of_two
        (CharP.cast_eq_zero Ω 2) γ)
  have hs : MonoidHom.range (Matrix.SpecialLinearGroup.map (algebraMap k Ω) :
        Matrix.SpecialLinearGroup (Fin 2) k →*
          Matrix.SpecialLinearGroup (Fin 2) Ω) =
      (Matrix.SpecialLinearGroup.map σ.toRingHom : Matrix.SpecialLinearGroup (Fin 2) Ω →*
          Matrix.SpecialLinearGroup (Fin 2) Ω).eqLocus (MonoidHom.id _) :=
    SL2_map_algebraMap_range_eq_eqLocus σ.toRingHom hσ
  have hβF : ∀ A : Matrix.SpecialLinearGroup (Fin 2) Ω,
      ((MulAut.conj z).toMonoidHom.comp (rootSL2 Tag.F4 Ω γ))
        (Matrix.SpecialLinearGroup.map σ.toRingHom A) =
      D.step (((MulAut.conj z).toMonoidHom.comp (rootSL2 Tag.F4 Ω γ)) A) := by
    intro A
    change z * rootSL2 Tag.F4 Ω γ (Matrix.SpecialLinearGroup.map σ.toRingHom A) * z⁻¹ =
      D.step (z * rootSL2 Tag.F4 Ω γ A * z⁻¹)
    rw [hzF (rootSL2 Tag.F4 Ω γ A) (MonoidHom.mem_range.mpr ⟨A, rfl⟩)]
    rw [CFSG.StandardType.F4ExplicitPos.NativePinFinal.frobGL_rootSL2_native σ hγ A]
  exact CFSG.StandardType.F4ExplicitPos.RationalC3.range_comp_eq_inf_eqLocus
    ((MulAut.conj z).toMonoidHom.comp (rootSL2 Tag.F4 Ω γ))
    (Matrix.SpecialLinearGroup.map σ.toRingHom) D.step
    (Matrix.SpecialLinearGroup.map (algebraMap k Ω)) hi hβF hs

theorem phiA1_range_of_normalizes
    {Ω k : Type} [Field Ω] [CharP Ω 2] [Field k] [Finite k]
    [Algebra k Ω] (D : LangDatum Tag.F4 Ω) (σ : Ω ≃+* Ω) (hσ : ∀ c, σ c = c ^ Nat.card k)
    (z : ModGL Tag.F4 Ω) (γ : Fin Tag.F4.rank → ℤ) (hγ : IsRoot Tag.F4 γ)
    (hzH : ∀ g, g ∈ (rootSL2 Tag.F4 Ω γ).range ↔
      z * g * z⁻¹ ∈ (rootSL2 Tag.F4 Ω γ).range)
    (hzF : ∀ g ∈ (rootSL2 Tag.F4 Ω γ).range,
      D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹) :
    (phiA1 (k := k) z γ).range = (rootSL2 Tag.F4 Ω γ).range ⊓ D.model := by
  rw [phiA1_range D σ hσ z γ hγ hzF]
  have hran_i : MonoidHom.range
      ((MulAut.conj z).toMonoidHom.comp (rootSL2 Tag.F4 Ω γ)) =
      MonoidHom.range (rootSL2 Tag.F4 Ω γ) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (hzH (rootSL2 Tag.F4 Ω γ g)).mp (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    · intro hx
      have hx' : z⁻¹ * x * z ∈ MonoidHom.range (rootSL2 Tag.F4 Ω γ) := by
        refine (hzH (z⁻¹ * x * z)).mpr ?_
        have hconj : z * (z⁻¹ * x * z) * z⁻¹ = x := by group
        rw [hconj]; exact hx
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hx'
      refine ⟨g, ?_⟩
      change z * rootSL2 Tag.F4 Ω γ g * z⁻¹ = x
      rw [hg]; group
  have hH_adj : (rootSL2 Tag.F4 Ω γ).range ≤ adjointGroup Tag.F4 Ω := by
    rw [rootSL2_range_eq_sup hγ]
    exact sup_le (rootSubgroup_le_adjointGroup γ) (rootSubgroup_le_adjointGroup (-γ))
  rw [hran_i]
  rw [show D.model = adjointGroup Tag.F4 Ω ⊓ D.step.eqLocus (MonoidHom.id _) from rfl,
    ← inf_assoc, inf_eq_left.mpr hH_adj]

theorem isSolvable_SL2_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (Matrix.SpecialLinearGroup (Fin 2) K) := Fintype.ofFinite _
  have hcard : Fintype.card (Matrix.SpecialLinearGroup (Fin 2) K) = 2 ^ 1 * 3 ^ 1 := by
    rw [← Nat.card_eq_fintype_card,
      CFSG.LieType.BorelTits.card_specialLinearGroup_fin_two (K := K) hK]
    norm_num
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    Nat.prime_two Nat.prime_three (by norm_num) hcard

theorem isQuasisimple_range_phiA1
    {Ω k : Type} [Field Ω] [CharP Ω 2] [Field k] [Finite k]
    [Algebra k Ω] (z : ModGL Tag.F4 Ω) (γ : Fin Tag.F4.rank → ℤ) (h4 : 4 ≤ Nat.card k) :
    CFSG.IsQuasisimple ↥(phiA1 (k := k) z γ).range :=
  CFSG.IsQuasisimple.of_mulEquiv
    (MonoidHom.ofInjective (phiA1_injective (Ω := Ω) (k := k) z γ)).symm
    (CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le (K := k) h4)

end CFSG.StandardType.F4ExplicitPos.RationalA1
end

end
