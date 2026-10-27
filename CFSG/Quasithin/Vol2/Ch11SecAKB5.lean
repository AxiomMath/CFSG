module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.KGNatComm
public import CFSG.Quasithin.Vol2.KGNatPointT

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix
open CFSG.Assembly.LowTwoRank (StatedSL)

namespace PointStab

variable {K : Type} [Field K]

theorem semilinear_eq_mulVec {σ : K →+* K} {T : (Fin 3 → K) →+ (Fin 3 → K)}
    (hT : ∀ (c : K) (x : Fin 3 → K), T (c • x) = σ c • T x) (x : Fin 3 → K) :
    T x = Matrix.of (fun i j => T (Pi.single j 1) i) *ᵥ (σ ∘ x) := by
  conv_lhs => rw [← sum_single_eq x]
  rw [map_sum]
  funext i
  rw [Finset.sum_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Function.comp_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_single_one j (x j), hT, Pi.smul_apply, smul_eq_mul, mul_comm]

end PointStab

open PointStab in
theorem factNoGraphSL3_holds : Ch11.SecA.FactNoGraphSL3 := by
  intro K _ _ _ _ _ W _ _ _ H π hπ Tb hTb t ht
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  have hinj : ∀ a b : W, f a = f b → a = b := fun a b h =>
    mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff a b).mp h))
  have ht' : ∀ h ∈ H, t⁻¹ * h * t ∈ H := fun h hh => by
    have := hTb t⁻¹ (Tb.inv_mem ht) h hh
    rwa [inv_inv] at this
  have he0 : (![1, 0, 0] : Fin 3 → K) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_statedSL (by norm_num) T hT)
    he0 t (bot_maps t) (bot_maps t⁻¹) ht'
  set T := hf.autMap t (bot_maps t) with hTdef
  have hTf : ∀ w, T (f w) = f (t w) := hf.autMap_apply t (bot_maps t)
  set σ' : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩ with hσ'
  set A : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => T (Pi.single j 1) i with hA
  have hTA : ∀ x, T x = A *ᵥ (σ ∘ x) := semilinear_eq_mulVec hσ
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    obtain ⟨w, hw⟩ := hf.surj (fun i => σ'.symm (v i))
    apply hv0
    have h1 : f (t w) = 0 := by
      rw [← hTf, hTA, hw]
      convert hAv using 2
      funext i
      exact σ'.apply_symm_apply (v i)
    have h3 : w = 1 := (MulEquiv.map_eq_one_iff t).mp (Subgroup.mem_bot.mp ((hf.ker _).mp h1))
    funext i
    have h4 := congrFun hw i
    rw [h3, hf.map_one] at h4
    simpa using h4.symm
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet, σ', fun g hg => ?_⟩
  have hAA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hdet)
  have hσv : ∀ w, σ ∘ f (t⁻¹ w) = A⁻¹ *ᵥ f w := by
    intro w
    have h1 : A *ᵥ (σ ∘ f (t⁻¹ w)) = f w := by
      rw [← hTA, hTf, MulAut.apply_inv_self]
    rw [← h1, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  have hM : (((⟨_, hg⟩ : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      A * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ * A⁻¹ := by
    show ((Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet *
      Matrix.GeneralLinearGroup.map σ'.toRingHom (g : GL (Fin 3) K) *
        (Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet)⁻¹ : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) = _
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    rfl
  have hact : ∀ (γ : ↥(StatedSL 3 K)) (u : W), f (((π γ : ↥H) : MulAut W) u) =
      ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f u := fun γ u =>
    (hf.act γ u).trans (linModelNat_lin _ _ _)
  refine MulEquiv.ext fun w => hinj _ _ ?_
  have hmv : σ ∘ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f (t⁻¹ w)) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ *ᵥ (σ ∘ f (t⁻¹ w)) :=
    funext fun i => RingHom.map_mulVec σ _ _ i
  rw [hact, MulAut.mul_apply, MulAut.mul_apply, ← hTf, hact, hTA, hmv, hσv,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]

end CFSG.Quasithin.Vol2.KGNat
