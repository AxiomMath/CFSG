module

public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveEigen

public section

namespace CFSG.RankThree.PartOne

open Matrix Polynomial CFSG.LocalAnalysis.ComponentInitial

theorem exists_fifth_root_of_invariant {K : Type} [Field K] {A : GL (Fin 5) K} {c : Kˣ}
    (hA : A ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) c) {W : Submodule K (Fin 5 → K)}
    (hW0 : W ≠ ⊥) (hWtop : W ≠ ⊤)
    (hinv : ∀ w ∈ W, ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ w ∈ W) :
    ∃ μ : Kˣ, μ ^ 5 = c := by
  by_contra hno
  push Not at hno
  have hb : ∀ b : K, b ^ 5 ≠ (c : K) := fun b hb => by
    have hb0 : b ≠ 0 := by
      rintro rfl
      simp at hb
      exact c.ne_zero hb.symm
    exact hno (Units.mk0 b hb0) (Units.ext (by simpa using hb))
  have hirr : Irreducible (X ^ 5 - C (c : K)) := X_pow_sub_C_irreducible_of_prime Nat.prime_five hb
  let E : Module.End K (Fin 5 → K) := Matrix.toLin' (A : Matrix (Fin 5) (Fin 5) K)
  have hEW : ∀ w ∈ W, E w ∈ W := fun w hw => by
    rw [Matrix.toLin'_apply]
    exact hinv w hw
  have hE5 : E ^ 5 = (c : K) • (1 : Module.End K (Fin 5 → K)) := by
    have h1 : E ^ 5 = Matrix.toLin' ((A : Matrix (Fin 5) (Fin 5) K) ^ 5) :=
      (map_pow (Matrix.toLinAlgEquiv' : Matrix (Fin 5) (Fin 5) K ≃ₐ[K] _) _ 5).symm
    rw [h1, ← Units.val_pow_eq_pow_val, hA, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply]
    ext v i
    simp [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  have hE'5 : (E.restrict hEW) ^ 5 = (c : K) • (1 : Module.End K W) := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    have h1 := congrArg (fun F : Module.End K W => ((F w : W) : Fin 5 → K))
      (Module.End.pow_restrict (f' := E) (p := W) 5 hEW)
    simp only [LinearMap.restrict_apply] at h1
    simp only [LinearMap.smul_apply, Module.End.one_apply, SetLike.val_smul]
    rw [h1, hE5]
    simp
  have hroot : aeval (E.restrict hEW) (X ^ 5 - C (c : K)) = 0 := by
    simp [hE'5, Algebra.algebraMap_eq_smul_one]
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  have hmin : X ^ 5 - C (c : K) = minpoly K (E.restrict hEW) :=
    minpoly.eq_of_irreducible_of_monic hirr hroot (monic_X_pow_sub_C _ (by norm_num))
  have hle := Polynomial.natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly (E.restrict hEW))
    (LinearMap.charpoly_monic (E.restrict hEW)).ne_zero
  rw [← hmin, natDegree_X_pow_sub_C, LinearMap.charpoly_natDegree] at hle
  have hlt : Module.finrank K W < 5 := by
    have := Submodule.finrank_lt hWtop
    rwa [Module.finrank_fin_fun] at this
  omega

theorem norm_eq_one_of_norm_pow_five_eq_one {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {μ : K} (hμ : h.norm (μ ^ 5) = 1) :
    h.norm μ = 1 := by
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp [UnitaryFieldData.norm] at hμ
  refine (mul_comm _ _).trans (KCEvenUnitaryFive.bar_mul_eq_one_of_pow_five h h5
    (c := Units.mk0 (μ ^ 5) (pow_ne_zero 5 hμ0)) ?_ rfl)
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, ← hμ, UnitaryFieldData.norm,
    UnitaryFieldData.bar_apply, pow_succ']

theorem prod_eq_one_of_injective_pow_five {K : Type} [Field K]
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5) {d : Fin 5 → Kˣ} (hd5 : ∀ k, d k ^ 5 = 1)
    (hinj : Function.Injective d) : ∏ k, d k = 1 := by
  classical
  obtain ⟨ζ, hζ⟩ := hζ
  have : NeZero 5 := ⟨by norm_num⟩
  have hcard : Nat.card (rootsOfUnity 5 K) = 5 :=
    IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.coe_units_iff.mpr hζ)
  let e : Fin 5 → rootsOfUnity 5 K := fun k => ⟨d k, (mem_rootsOfUnity 5 _).mpr (hd5 k)⟩
  have he : Function.Injective e := fun a b hab => hinj (congrArg Subtype.val hab)
  have : Fintype (rootsOfUnity 5 K) := Fintype.ofFinite _
  have hbij : Function.Bijective e := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨he, ?_⟩
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, hcard]
  have h1 : ∏ k, e k = ∏ u : rootsOfUnity 5 K, u :=
    Fintype.prod_bijective e hbij _ _ fun _ => rfl
  set Pr : rootsOfUnity 5 K := ∏ u : rootsOfUnity 5 K, u with hPr
  have h2 : Pr = Pr⁻¹ := by
    rw [hPr, ← Finset.prod_inv_distrib]
    exact (Fintype.prod_equiv (Equiv.inv _) _ _ fun u => rfl).symm
  have h3 : Pr ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [h2]
    exact inv_mul_cancel Pr
  have h4 : Pr ^ 5 = 1 := by
    have := pow_card_eq_one' (G := rootsOfUnity 5 K) (x := Pr)
    rwa [hcard] at this
  have h5 : Pr = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h4, h3⟩
    simpa using this
  have h6 : ((∏ k, e k : rootsOfUnity 5 K) : Kˣ) = ∏ k, d k :=
    map_prod (rootsOfUnity 5 K).subtype e Finset.univ
  rw [← h6, h1, h5]
  rfl

end CFSG.RankThree.PartOne
