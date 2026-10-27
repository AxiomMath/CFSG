module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXThetaQ
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXThetaH

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KGD

private lemma units_map_algebraMap_comp {k K L : Type} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] (u : kˣ) :
    Units.map (algebraMap K L).toMonoidHom (Units.map (algebraMap k K).toMonoidHom u) =
      Units.map (algebraMap k L).toMonoidHom u := by
  refine Units.ext ?_
  change algebraMap K L (algebraMap k K (u : k)) = algebraMap k L (u : k)
  exact (IsScalarTower.algebraMap_apply k K L (u : k)).symm

private noncomputable def thetaTuple {K : Type} [Field K] (σ : K →+* K) (a B : Kˣ) :
    Fin Tag.D4.rank → Kˣ :=
  ![a ^ 2 * B⁻¹, (Units.map σ.toMonoidHom a) ^ 2 * B⁻¹,
    (a * Units.map σ.toMonoidHom a * Units.map σ.toMonoidHom (Units.map σ.toMonoidHom a))⁻¹
      * B ^ 2, (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom a)) ^ 2 * B⁻¹]

private lemma thetaTuple_apply_zero {K : Type} [Field K] (σ : K →+* K) (a B : Kˣ) :
    thetaTuple σ a B 0 = a ^ 2 * B⁻¹ := rfl

private lemma thetaTuple_apply_one {K : Type} [Field K] (σ : K →+* K) (a B : Kˣ) :
    thetaTuple σ a B 1 = (Units.map σ.toMonoidHom a) ^ 2 * B⁻¹ := rfl

private lemma thetaTuple_apply_two {K : Type} [Field K] (σ : K →+* K) (a B : Kˣ) :
    thetaTuple σ a B 2 =
      (a * Units.map σ.toMonoidHom a * Units.map σ.toMonoidHom (Units.map σ.toMonoidHom a))⁻¹
        * B ^ 2 := rfl

private lemma thetaTuple_apply_three {K : Type} [Field K] (σ : K →+* K) (a B : Kˣ) :
    thetaTuple σ a B 3 = (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom a)) ^ 2 * B⁻¹ := rfl

theorem triD4LineTheta_agree
    {n : ℕ} (K : Type) [Field K] (hK : Nat.card K = (2 ^ n) ^ 3)
    (σ : K ≃+* K) (k : Type) [Field k] [Algebra k K]
    (τ : K ≃ₐ[k] K) (hτ : ∀ c, τ c = σ c)
    (hdeg : Module.finrank k K = 3) (hτo : orderOf τ = 3)
    (L : Type) [Field L] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    (y : ↥(triD4LineH1 K σ))
    (hy : (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∈ triD4LineNR K σ L)
    (a : Kˣ) (b : (trialityFixedField K σ.toRingHom)ˣ) (c : kˣ)
    (hyT : ((y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
      trialityTorusHom σ (a, b))
    (hbc : trialityFixedUnit K σ b = Units.map (algebraMap k K).toMonoidHom c)
    (g : GL (Fin 3) k)
    (hg : (g : Matrix (Fin 3) (Fin 3) k) =
      Matrix.diagonal ![(c : k) ^ 2, Algebra.norm k (a : K), (c : k)])
    (hdet : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K))
      (Units.map (algebraMap k K).toMonoidHom c * a)) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 3) k,
      (d4A2QvEquiv (K := L) triD4LineV ⟨triEmb K σ L y, hy⟩ :
          Matrix.SpecialLinearGroup (Fin 3) L) =
        Matrix.SpecialLinearGroup.map (algebraMap k L) s ∧
      triD4LineSL3 k K s =
        triD4LineMk k K g (Units.map (algebraMap k K).toMonoidHom c * a) hdet := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  let B : Kˣ := Units.map (algebraMap k K).toMonoidHom c
  let bL : Fin Tag.D4.rank → Lˣ := fun i => Units.map (algebraMap K L) (thetaTuple σ a B i)
  have htri : triEmb K σ L y = rootDiagUnit Tag.D4 bL := by
    change triEmb K σ L y = rootDiagUnit Tag.D4
      (fun i => Units.map (algebraMap K L) (thetaTuple σ a B i))
    rw [triEmb_apply, hyT, trialityTorusHom_apply, trialityOuter_mul_middle_eq, hbc]
    rw [baseChangeGL_rootDiagUnit]
    rfl
  have hQ : rootDiagUnit Tag.D4 bL ∈ d4A2Qv L triD4LineV := by
    rw [← htri]
    exact hy
  have hmem := (triD4Line_rootDiagUnit_mem_Qv_iff L bL).1 hQ
  have hinj : Function.Injective (Units.map (algebraMap K L : K →* L)) :=
    Units.map_injective (f := (algebraMap K L : K →* L)) (algebraMap K L).injective
  have h1eq : thetaTuple σ a B 1 = thetaTuple σ a B 0 := hinj hmem.1
  have hsqU : (Units.map ((σ : K →+* K).toMonoidHom) a) ^ 2 = a ^ 2 := by
    have h := h1eq
    rw [thetaTuple_apply_one, thetaTuple_apply_zero] at h
    exact mul_right_cancel_iff.1 h
  have hσa : σ (a : K) = (a : K) := by
    have hsqK : (σ (a : K)) ^ 2 = (a : K) ^ 2 := by
      simpa using congrArg (fun u : Kˣ => (u : K)) hsqU
    rcases (sq_eq_sq_iff_eq_or_eq_neg).1 hsqK with h | h
    · exact h
    · rwa [CharTwo.neg_eq] at h
  have hσua : Units.map ((σ : K →+* K).toMonoidHom) a = a := Units.ext hσa
  have hσ2ua : Units.map ((σ : K →+* K).toMonoidHom)
      (Units.map ((σ : K →+* K).toMonoidHom) a) = a := by rw [hσua, hσua]
  obtain ⟨a', ha'⟩ := triD4Line_exists_algebraMap_of_sigma_eq k K hdeg τ hτo (a : K)
    (by rw [hτ, hσa])
  have ha'0 : a' ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ha'
    exact a.ne_zero ha'.symm
  let a'u : kˣ := Units.mk0 a' ha'0
  have hua : Units.map (algebraMap k K).toMonoidHom a'u = a := Units.ext ha'
  have hnorm : Algebra.norm k (a : K) = (a'u : k) ^ 3 := by
    rw [← ha', Algebra.norm_algebraMap, hdeg]
    rfl
  have hsKeq : a ^ 2 * B⁻¹ =
      Units.map (algebraMap k K).toMonoidHom (a'u ^ 2 * c⁻¹) := by
    rw [← hua, show B = Units.map (algebraMap k K).toMonoidHom c from rfl]
    simp only [← map_mul, ← map_pow, ← map_inv]
  have htKeq : (a * a * a)⁻¹ * B ^ 2 =
      Units.map (algebraMap k K).toMonoidHom ((a'u * a'u * a'u)⁻¹ * c ^ 2) := by
    rw [← hua, show B = Units.map (algebraMap k K).toMonoidHom c from rfl]
    simp only [← map_mul, ← map_pow, ← map_inv]
  let sL : Lˣ := Units.map (algebraMap k L).toMonoidHom (a'u ^ 2 * c⁻¹)
  let tL : Lˣ := Units.map (algebraMap k L).toMonoidHom ((a'u * a'u * a'u)⁻¹ * c ^ 2)
  have htuple : (fun i => Units.map (algebraMap K L) (thetaTuple σ a B i)) =
      ![sL, sL, tL, sL] := by
    funext i
    fin_cases i
    · change Units.map (algebraMap K L) (thetaTuple σ a B 0) = sL
      rw [thetaTuple_apply_zero, hsKeq]
      exact units_map_algebraMap_comp _
    · change Units.map (algebraMap K L) (thetaTuple σ a B 1) = sL
      rw [thetaTuple_apply_one, hσua, hsKeq]
      exact units_map_algebraMap_comp _
    · change Units.map (algebraMap K L) (thetaTuple σ a B 2) = tL
      rw [thetaTuple_apply_two, hσ2ua, hσua, htKeq]
      exact units_map_algebraMap_comp _
    · change Units.map (algebraMap K L) (thetaTuple σ a B 3) = sL
      rw [thetaTuple_apply_three, hσ2ua, hsKeq]
      exact units_map_algebraMap_comp _
  have htri2 : triEmb K σ L y = rootDiagUnit Tag.D4 ![sL, sL, tL, sL] := by
    rw [htri]
    change rootDiagUnit Tag.D4 (fun i => Units.map (algebraMap K L) (thetaTuple σ a B i)) =
      rootDiagUnit Tag.D4 ![sL, sL, tL, sL]
    rw [htuple]
  have hQ2 : rootDiagUnit Tag.D4 ![sL, sL, tL, sL] ∈ d4A2Qv L triD4LineV := by
    rw [← htri2]
    exact hy
  have hsLt : (sL * tL : Lˣ) = Units.map (algebraMap k L).toMonoidHom (c * a'u⁻¹) := by
    rw [← map_mul]
    congr 1
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
  have hsLt_val : ((sL * tL : Lˣ) : L) = algebraMap k L ((c : k) * (a'u : k)⁻¹) := by
    rw [hsLt]
    simp
  have hsL_val : (sL : L) = algebraMap k L ((a'u : k) ^ 2 * (c : k)⁻¹) := by
    change (Units.map (algebraMap k L).toMonoidHom (a'u ^ 2 * c⁻¹) : L) = _
    simp
  have hst_val : (((sL ^ 2 * tL)⁻¹ : Lˣ) : L) = algebraMap k L ((a'u : k)⁻¹) := by
    have h : (sL ^ 2 * tL : Lˣ) = Units.map (algebraMap k L).toMonoidHom a'u := by
      rw [← map_pow, ← map_mul]
      congr 1
      refine Units.ext ?_
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
      field_simp
    rw [h, ← map_inv]
    simp
  have hΨ' : ((d4A2QvEquiv (K := L) triD4LineV ⟨triEmb K σ L y, hy⟩ :
      Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal ![((sL * tL : Lˣ) : L), (sL : L), (((sL ^ 2 * tL)⁻¹ : Lˣ) : L)] := by
    have hsub : (⟨triEmb K σ L y, hy⟩ : ↥(d4A2Qv L triD4LineV)) =
        ⟨rootDiagUnit Tag.D4 ![sL, sL, tL, sL], hQ2⟩ := Subtype.ext htri2
    rw [hsub]
    exact triD4Line_d4A2QvEquiv_rootDiagUnit L sL tL hQ2
  have hdet_s : (Matrix.diagonal
      ![(c : k) * (a'u : k)⁻¹, (a'u : k) ^ 2 * (c : k)⁻¹, (a'u : k)⁻¹] :
        Matrix (Fin 3) (Fin 3) k).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    field_simp
  let s₀ : Matrix.SpecialLinearGroup (Fin 3) k :=
    ⟨Matrix.diagonal ![(c : k) * (a'u : k)⁻¹, (a'u : k) ^ 2 * (c : k)⁻¹,
      (a'u : k)⁻¹], hdet_s⟩
  refine ⟨s₀, ?_, ?_⟩
  · apply Subtype.ext
    have hs₀ : (s₀ : Matrix (Fin 3) (Fin 3) k) =
        Matrix.diagonal ![(c : k) * (a'u : k)⁻¹, (a'u : k) ^ 2 * (c : k)⁻¹,
          (a'u : k)⁻¹] := rfl
    rw [hΨ', Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hs₀]
    rw [show (Matrix.diagonal ![(c : k) * (a'u : k)⁻¹, (a'u : k) ^ 2 * (c : k)⁻¹,
        (a'u : k)⁻¹] : Matrix (Fin 3) (Fin 3) k).map (algebraMap k L) =
        Matrix.diagonal ![(algebraMap k L) ((c : k) * (a'u : k)⁻¹),
          (algebraMap k L) ((a'u : k) ^ 2 * (c : k)⁻¹),
          (algebraMap k L) ((a'u : k)⁻¹)] by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne]]
    congr 1
    funext i
    fin_cases i <;> simp only [hsLt_val, hsL_val, hst_val]
  · have h1 : Matrix.SpecialLinearGroup.toGL s₀ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) ((c * a'u)⁻¹) * g := by
      refine Units.ext ?_
      have htoGL : ((Matrix.SpecialLinearGroup.toGL s₀ : GL (Fin 3) k) :
          Matrix (Fin 3) (Fin 3) k) =
          Matrix.diagonal ![(c : k) * (a'u : k)⁻¹, (a'u : k) ^ 2 * (c : k)⁻¹,
            (a'u : k)⁻¹] := rfl
      rw [htoGL, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hg, hnorm,
        Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      fin_cases i <;>
        simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons, Units.val_inv_eq_inv_val, Units.val_mul] <;>
        field_simp
    have h2 : (1 : Kˣ) = Units.map (algebraMap k K).toMonoidHom ((c * a'u)⁻¹) * (B * a) := by
      rw [← hua, show B = Units.map (algebraMap k K).toMonoidHom c from rfl, ← map_mul, ← map_mul,
        show (c * a'u)⁻¹ * (c * a'u) = 1 from inv_mul_cancel _, map_one]
    have hSL3 : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL s₀) =
        Units.map (Algebra.norm k (S := K)) 1 := by
      rw [map_one]
      exact Matrix.SpecialLinearGroup.coeToGL_det _
    rw [triD4LineSL3_apply k K s₀ hSL3]
    exact ((triD4LineMk_eq_mk_iff k K g (Matrix.SpecialLinearGroup.toGL s₀) (B * a) 1 hdet
      hSL3).2 ⟨(c * a'u)⁻¹, h1, h2⟩).symm

end CFSG.StandardType
