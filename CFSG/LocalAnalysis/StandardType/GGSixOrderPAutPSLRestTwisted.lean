module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestOutdiag

public section

namespace CFSG.StandardType

open Matrix Polynomial CFSG.Timmesfeld

namespace OrdPRest

theorem ggTwistedPPDInput_holds : GGTwistedPPDInput := by
  intro K _ _ f n p r hK hf hn hp A c hc hcμ hr
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr.prime⟩
  set P : K[X] := X ^ p - C (c : K) with hP
  have hPirr : Irreducible P := X_pow_sub_C_irreducible_of_prime hp fun b hb => by
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hb
      exact c.ne_zero hb.symm
    exact hcμ (Units.mk0 b hb0) (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hb]))
  have : Fact (Irreducible P) := ⟨hPirr⟩
  have hP0 : P ≠ 0 := hPirr.ne_zero
  set xA : Module.End K (Fin n → K) := Matrix.toLinAlgEquiv' (A : Matrix (Fin n) (Fin n) K)
    with hxA
  have haeval : aeval xA P = 0 := by
    have h1 : xA ^ p = algebraMap K (Module.End K (Fin n → K)) (c : K) := by
      rw [hxA, ← map_pow, ← Units.val_pow_eq_pow_val, hc, GeneralLinearGroup.coe_scalar,
        ← AlgEquiv.commutes Matrix.toLinAlgEquiv' (c : K)]
      rfl
    rw [hP, map_sub, aeval_X_pow, aeval_C, h1, sub_self]
  set φ : AdjoinRoot P →ₐ[K] Module.End K (Fin n → K) :=
    Ideal.Quotient.liftₐ (Ideal.span {P}) (aeval xA) (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, haeval, mul_zero]) with hφ
  have hφroot : φ (AdjoinRoot.root P) = xA := by
    rw [← AdjoinRoot.mk_X]
    exact aeval_X xA
  let : Module (AdjoinRoot P) (Fin n → K) := Module.compHom (Fin n → K) φ.toRingHom
  have hsmul : ∀ (l : AdjoinRoot P) (v : Fin n → K), l • v = φ l v := fun _ _ => rfl
  have : IsScalarTower K (AdjoinRoot P) (Fin n → K) := ⟨fun a l v => by
    rw [hsmul, hsmul, map_smul, LinearMap.smul_apply]⟩
  have : Module.Finite K (AdjoinRoot P) := (AdjoinRoot.powerBasis hP0).finite
  have : Finite (AdjoinRoot P) := Module.finite_of_finite K
  let : Fintype (AdjoinRoot P) := Fintype.ofFinite _
  have : Module.Finite (AdjoinRoot P) (Fin n → K) :=
    Module.Finite.of_restrictScalars_finite K (AdjoinRoot P) (Fin n → K)
  have hdimL : Module.finrank K (AdjoinRoot P) = p := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis hP0), AdjoinRoot.powerBasis_dim hP0,
      natDegree_X_pow_sub_C]
  set k := Module.finrank (AdjoinRoot P) (Fin n → K) with hk
  have hdim : p * k = n := by
    rw [hk, ← hdimL, Module.finrank_mul_finrank K (AdjoinRoot P) (Fin n → K),
      Module.finrank_fin_fun]
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, mul_zero] at hdim
      omega
    · exact h0
  have hn2 : 2 ≤ n := by
    rw [← hdim]
    exact le_trans hp.two_le (Nat.le_mul_of_pos_right p hk0)
  have hcardL : Fintype.card (AdjoinRoot P) = 2 ^ (f * p) := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := K), hdimL,
      Nat.card_eq_fintype_card, hK, ← pow_mul]
  have hrdvd : r ∣ Nat.card (GL (Fin k) (AdjoinRoot P)) := by
    rw [Matrix.card_GL_field, hcardL]
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨0, hk0⟩ : Fin k)))
    simp only [pow_zero]
    rw [← pow_mul, show f * p * k = f * n by rw [mul_assoc, hdim]]
    exact hr.dvd
  obtain ⟨g₀, hg₀⟩ := exists_prime_orderOf_dvd_card' r hrdvd
  let b := Module.finBasisOfFinrankEq (AdjoinRoot P) (Fin n → K) hk.symm
  let e₁ : GL (Fin k) (AdjoinRoot P) ≃* (Module.End (AdjoinRoot P) (Fin n → K))ˣ :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).symm.toMulEquiv
  let R : Module.End (AdjoinRoot P) (Fin n → K) →* Module.End K (Fin n → K) :=
    { toFun := fun g => g.restrictScalars K, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hR : Function.Injective R := LinearMap.restrictScalars_injective K
  let e₃ : (Module.End K (Fin n → K))ˣ ≃* GL (Fin n) K :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv' :
      Module.End K (Fin n → K) ≃ₐ[K] Matrix (Fin n) (Fin n) K).toMulEquiv
  set g₃ : GL (Fin n) K := e₃ (Units.map R (e₁ g₀)) with hg₃def
  have hg₃ : orderOf g₃ = r := by
    rw [hg₃def, MulEquiv.orderOf_eq, orderOf_injective _ (Units.map_injective hR),
      MulEquiv.orderOf_eq, hg₀]
  have hcomm : g₃ * A = A * g₃ := by
    apply Units.ext
    have hA' : (A : Matrix (Fin n) (Fin n) K) = LinearMap.toMatrixAlgEquiv' xA := by
      rw [hxA, LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv']
    rw [Units.val_mul, Units.val_mul, hA']
    change LinearMap.toMatrixAlgEquiv' (R (e₁ g₀ : Module.End (AdjoinRoot P) (Fin n → K))) * _ =
      _ * LinearMap.toMatrixAlgEquiv' (R (e₁ g₀ : Module.End (AdjoinRoot P) (Fin n → K)))
    rw [← map_mul, ← map_mul]
    congr 1
    refine LinearMap.ext fun v => ?_
    change (e₁ g₀ : Module.End (AdjoinRoot P) (Fin n → K)) (xA v) =
      xA ((e₁ g₀ : Module.End (AdjoinRoot P) (Fin n → K)) v)
    have hx : ∀ w : Fin n → K, xA w = AdjoinRoot.root P • w := fun w => by
      rw [hsmul, hφroot]
    rw [hx, hx, LinearMap.map_smul]
  have hdet : GeneralLinearGroup.det g₃ = 1 := by
    have h1 : (GeneralLinearGroup.det g₃) ^ r = 1 := by
      rw [← map_pow, ← hg₃, pow_orderOf_eq_one, map_one]
    have h2 : orderOf (GeneralLinearGroup.det g₃) ∣ Nat.card Kˣ := orderOf_dvd_natCard _
    rw [Nat.card_units, Nat.card_eq_fintype_card, hK] at h2
    rcases (Nat.dvd_prime hr.prime).mp (orderOf_dvd_of_pow_eq_one h1) with h4 | h4
    · exact orderOf_eq_one_iff.mp h4
    · exfalso
      rw [h4] at h2
      exact not_dvd_two_pow_sub_one hr hf (j := 1) one_pos (by omega) (by rwa [mul_one])
  have hdet' : (g₃ : Matrix (Fin n) (Fin n) K).det = 1 := by
    have h := congrArg (fun u : Kˣ => (u : K)) hdet
    simpa only [GeneralLinearGroup.val_det_apply, Units.val_one] using h
  let g : SpecialLinearGroup (Fin n) K := ⟨(g₃ : Matrix (Fin n) (Fin n) K), hdet'⟩
  have hto : SpecialLinearGroup.toGL g = g₃ := Units.ext rfl
  refine ⟨g, ?_, ?_⟩
  · rw [← orderOf_injective _ SpecialLinearGroup.toGL_injective g, hto, hg₃]
  · rw [hto]
    exact hcomm

end OrdPRest

section Family

theorem ggOrdPOutdiagAt_PSL : GGOrdPOutdiagAt .PSL :=
  ggOrdPOutdiagAt_PSL_of_twisted OrdPRest.ggTwistedPPDInput_holds

end Family

end CFSG.StandardType
