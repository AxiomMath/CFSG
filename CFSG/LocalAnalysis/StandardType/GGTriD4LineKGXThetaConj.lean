module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXThetaQ
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXThetaH
import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXSL3

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KGD

private noncomputable def thetaConjTuple {K : Type} [Field K] (σ : K →+* K) (a B : Kˣ) :
    Fin Tag.D4.rank → Kˣ :=
  ![a ^ 2 * B⁻¹, (Units.map σ.toMonoidHom a) ^ 2 * B⁻¹,
    (a * Units.map σ.toMonoidHom a * Units.map σ.toMonoidHom (Units.map σ.toMonoidHom a))⁻¹
      * B ^ 2,
    (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom a)) ^ 2 * B⁻¹]

private def d4LongVec (a c : ℤ) : Fin Tag.D4.rank → ℤ :=
  a • Pi.single 0 1 + a • Pi.single 1 1 + c • Pi.single 2 1 + a • Pi.single 3 1

private lemma rootChar_d4LongVec {K : Type} [Field K] (b : Fin Tag.D4.rank → Kˣ) (a c : ℤ) :
    rootChar b (d4LongVec a c) = b 0 ^ a * b 1 ^ a * b 2 ^ c * b 3 ^ a := by
  rw [d4LongVec, rootChar_add, rootChar_add, rootChar_add, rootChar_zsmul, rootChar_zsmul,
    rootChar_zsmul, rootChar_zsmul, rootChar_single_D4, rootChar_single_D4,
    rootChar_single_D4, rootChar_single_D4]

private lemma rootChar_thetaConjTuple_1121 {K : Type} [Field K] (σ : K →+* K) (a B : Kˣ) :
    rootChar (thetaConjTuple σ a B) (d4LongVec 1 2) = B := by
  rw [rootChar_d4LongVec]
  rw [show thetaConjTuple σ a B 0 = a ^ 2 * B⁻¹ from rfl,
    show thetaConjTuple σ a B 1 = (Units.map σ.toMonoidHom a) ^ 2 * B⁻¹ from rfl,
    show thetaConjTuple σ a B 2 =
      (a * Units.map σ.toMonoidHom a *
        Units.map σ.toMonoidHom (Units.map σ.toMonoidHom a))⁻¹ * B ^ 2 from rfl,
    show thetaConjTuple σ a B 3 =
      (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom a)) ^ 2 * B⁻¹ from rfl]
  simp only [zpow_one, zpow_ofNat]
  refine Units.ext ?_
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  field_simp

private lemma rootChar_thetaConjTuple_1111 {K : Type} [Field K] (σ : K →+* K) (a B : Kˣ) :
    rootChar (thetaConjTuple σ a B) (d4LongVec 1 1) =
      a * Units.map σ.toMonoidHom a *
        Units.map σ.toMonoidHom (Units.map σ.toMonoidHom a) * B⁻¹ := by
  rw [rootChar_d4LongVec]
  rw [show thetaConjTuple σ a B 0 = a ^ 2 * B⁻¹ from rfl,
    show thetaConjTuple σ a B 1 = (Units.map σ.toMonoidHom a) ^ 2 * B⁻¹ from rfl,
    show thetaConjTuple σ a B 2 =
      (a * Units.map σ.toMonoidHom a *
        Units.map σ.toMonoidHom (Units.map σ.toMonoidHom a))⁻¹ * B ^ 2 from rfl,
    show thetaConjTuple σ a B 3 =
      (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom a)) ^ 2 * B⁻¹ from rfl]
  simp only [zpow_one, zpow_ofNat]
  refine Units.ext ?_
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  field_simp

private lemma thetaConj_norm_units {K k : Type} [Field K] [Field k] [Algebra k K] [Finite K]
    (hdeg : Module.finrank k K = 3) (τ : K ≃ₐ[k] K) (hτo : orderOf τ = 3)
    (σ : K →+* K) (hτ : ∀ c, τ c = σ c) (a : Kˣ) :
    a * Units.map σ.toMonoidHom a *
        Units.map σ.toMonoidHom (Units.map σ.toMonoidHom a) =
      Units.map (algebraMap k K).toMonoidHom (Units.map (Algebra.norm k) a) := by
  refine Units.ext ?_
  simp only [Units.val_mul, Units.coe_map]
  change (a : K) * σ (a : K) * σ (σ (a : K)) =
    (algebraMap k K) (Algebra.norm k (a : K))
  rw [triD4Line_algebraMap_norm k K hdeg τ hτo (a : K)]
  simp only [hτ, pow_two, AlgEquiv.mul_apply]

private lemma thetaConj_triEmb {K L : Type} [Field K] [Field L] [Algebra K L]
    (σ : K ≃+* K) (a : Kˣ) (b : (trialityFixedField K σ.toRingHom)ˣ) (B : Kˣ)
    (hB : trialityFixedUnit K σ b = B)
    (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hyT : (y : ModGL TwistTag.D4.tag K) = trialityTorusHom σ (a, b)) :
    triEmb K σ L y =
      rootDiagUnit Tag.D4
        (fun i => Units.map (algebraMap K L) (thetaConjTuple σ a B i)) := by
  rw [triEmb_apply, hyT, trialityTorusHom_apply, trialityOuter_mul_middle_eq, hB]
  rw [baseChangeGL_rootDiagUnit]
  rfl

theorem triD4LineTheta_conj
    {n : ℕ} (K : Type) [Field K] (hK : Nat.card K = (2 ^ n) ^ 3)
    (σ : K ≃+* K) (k : Type) [Field k] [Algebra k K]
    (τ : K ≃ₐ[k] K) (hτ : ∀ c, τ c = σ c)
    (hdeg : Module.finrank k K = 3) (hτo : orderOf τ = 3)
    (L : Type) [Field L] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    (y : ↥(triD4LineH1 K σ)) (a : Kˣ) (b : (trialityFixedField K σ.toRingHom)ˣ) (c : kˣ)
    (hyT : ((y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
      trialityTorusHom σ (a, b))
    (hbc : trialityFixedUnit K σ b = Units.map (algebraMap k K).toMonoidHom c)
    (g : GL (Fin 3) k)
    (hg : (g : Matrix (Fin 3) (Fin 3) k) =
      Matrix.diagonal ![(c : k) ^ 2, Algebra.norm k (a : K), (c : k)])
    (hdet : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K))
      (Units.map (algebraMap k K).toMonoidHom c * a))
    (m m' : ↥(triD4LineNR K σ L))
    (hm' : (m' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) *
        (m : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) *
        (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)⁻¹)
    (s s' : Matrix.SpecialLinearGroup (Fin 3) k)
    (hs : (d4A2QvEquiv (K := L) triD4LineV ⟨triEmb K σ L m, m.2⟩ :
        Matrix.SpecialLinearGroup (Fin 3) L) =
      Matrix.SpecialLinearGroup.map (algebraMap k L) s)
    (hs' : (d4A2QvEquiv (K := L) triD4LineV ⟨triEmb K σ L m', m'.2⟩ :
        Matrix.SpecialLinearGroup (Fin 3) L) =
      Matrix.SpecialLinearGroup.map (algebraMap k L) s') :
    triD4LineMk k K g (Units.map (algebraMap k K).toMonoidHom c * a) hdet *
        triD4LineSL3 k K s *
        (triD4LineMk k K g (Units.map (algebraMap k K).toMonoidHom c * a) hdet)⁻¹ =
      triD4LineSL3 k K s' := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  let B : Kˣ := Units.map (algebraMap k K).toMonoidHom c
  let bL : Fin Tag.D4.rank → Lˣ :=
    fun i => Units.map (algebraMap K L) (thetaConjTuple σ a B i)
  let P : Matrix.SpecialLinearGroup (Fin 3) L :=
    d4A2QvEquiv (K := L) triD4LineV ⟨triEmb K σ L m, m.2⟩
  let P' : Matrix.SpecialLinearGroup (Fin 3) L :=
    d4A2QvEquiv (K := L) triD4LineV ⟨triEmb K σ L m', m'.2⟩
  let χ1 : Lˣ := rootChar bL ![1, 1, 2, 1]
  let χ2 : Lˣ := rootChar bL ![1, 1, 1, 1]
  let A : Matrix (Fin 3) (Fin 3) L := Matrix.diagonal ![↑χ1, ↑χ2, 1]
  let Ainv : Matrix (Fin 3) (Fin 3) L := Matrix.diagonal ![↑(χ1⁻¹), ↑(χ2⁻¹), 1]
  let Dmat : Matrix (Fin 3) (Fin 3) k :=
    Matrix.diagonal ![(c : k), Algebra.norm k (a : K) * (c : k)⁻¹, 1]
  have hB : trialityFixedUnit K σ b = B := hbc
  have htri : triEmb K σ L (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      rootDiagUnit Tag.D4 bL := by
    exact thetaConj_triEmb σ a b B hB y hyT
  have hιm' : triEmb K σ L (m' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      triEmb K σ L (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) *
        triEmb K σ L (m : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) *
        (triEmb K σ L (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁻¹ := by
    rw [hm']
    simp only [map_mul, map_inv]
  let q : ModGL Tag.D4 L := triEmb K σ L m
  have hq : q ∈ d4A2Qv L triD4LineV := m.2
  obtain ⟨hq', hconj⟩ := triD4Line_d4A2QvEquiv_conj (L := L) bL q hq
  have hsub : (⟨triEmb K σ L m', m'.2⟩ : d4A2Qv L triD4LineV) =
      ⟨rootDiagUnit Tag.D4 bL * q * (rootDiagUnit Tag.D4 bL)⁻¹, hq'⟩ := by
    apply Subtype.ext
    change triEmb K σ L (m' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      rootDiagUnit Tag.D4 bL * q * (rootDiagUnit Tag.D4 bL)⁻¹
    rw [hιm', htri]
    rfl
  have hP'eq : P' = (d4A2QvEquiv (K := L) triD4LineV
      ⟨rootDiagUnit Tag.D4 bL * q * (rootDiagUnit Tag.D4 bL)⁻¹, hq'⟩) := by
    change d4A2QvEquiv (K := L) triD4LineV ⟨triEmb K σ L m', m'.2⟩ = _
    rw [hsub]
  have hconjM : (P' : Matrix (Fin 3) (Fin 3) L) = A * (P : Matrix (Fin 3) (Fin 3) L) * Ainv := by
    rw [hP'eq]
    exact hconj
  have hχ1 : χ1 = Units.map (algebraMap k L).toMonoidHom c := by
    change rootChar (fun i => Units.map (algebraMap K L).toMonoidHom
      (thetaConjTuple σ a B i)) (d4LongVec 1 2) = Units.map (algebraMap k L).toMonoidHom c
    rw [CFSG.RankThree.PartOne.KE.rootChar_map_tuple, rootChar_thetaConjTuple_1121]
    refine Units.ext ?_
    simp only [Units.coe_map, B]
    exact (IsScalarTower.algebraMap_apply k K L (c : k)).symm
  have hχ2 : (χ2 : L) = algebraMap k L (Algebra.norm k (a : K) * (c : k)⁻¹) := by
    change (rootChar (fun i => Units.map (algebraMap K L).toMonoidHom
      (thetaConjTuple σ a B i)) (d4LongVec 1 1) : L) = _
    rw [CFSG.RankThree.PartOne.KE.rootChar_map_tuple, rootChar_thetaConjTuple_1111]
    rw [thetaConj_norm_units hdeg τ hτo σ hτ a]
    simp only [Units.coe_map, Units.val_mul, Units.val_inv_eq_inv_val, B, map_mul, map_inv,
      IsScalarTower.algebraMap_apply k K L]
    rw [map_inv₀ (algebraMap k K) (c : k), map_inv₀ (algebraMap K L) (algebraMap k K (c : k))]
    rfl
  have hA : A = Dmat.map (algebraMap k L) := by
    rw [show A = Matrix.diagonal ![↑χ1, ↑χ2, 1] from rfl,
      show Dmat = Matrix.diagonal ![(c : k), Algebra.norm k (a : K) * (c : k)⁻¹, 1] from rfl,
      Matrix.diagonal_map (map_zero (algebraMap k L))]
    congr 1
    funext i
    fin_cases i
    · simpa [hχ1]
    · simpa using hχ2
    · simp
  have hAinvA : Ainv * A = 1 := by
    rw [show Ainv = Matrix.diagonal ![↑(χ1⁻¹), ↑(χ2⁻¹), 1] from rfl,
      show A = Matrix.diagonal ![↑χ1, ↑χ2, 1] from rfl,
      Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one using 2
    funext i
    fin_cases i <;> simp
  have h1 : (P' : Matrix (Fin 3) (Fin 3) L) * A = A * (P : Matrix (Fin 3) (Fin 3) L) := by
    rw [hconjM, mul_assoc, mul_assoc, hAinvA, mul_one]
  have hsM : (P : Matrix (Fin 3) (Fin 3) L) =
      (s : Matrix (Fin 3) (Fin 3) k).map (algebraMap k L) := by
    change ((d4A2QvEquiv (K := L) triD4LineV ⟨triEmb K σ L m, m.2⟩ :
      Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = _
    rw [hs, Matrix.SpecialLinearGroup.map_apply_coe]
    rfl
  have hsM' : (P' : Matrix (Fin 3) (Fin 3) L) =
      (s' : Matrix (Fin 3) (Fin 3) k).map (algebraMap k L) := by
    change ((d4A2QvEquiv (K := L) triD4LineV ⟨triEmb K σ L m', m'.2⟩ :
      Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = _
    rw [hs', Matrix.SpecialLinearGroup.map_apply_coe]
    rfl
  have hmap : (algebraMap k L).mapMatrix ((s' : Matrix (Fin 3) (Fin 3) k) * Dmat) =
      (algebraMap k L).mapMatrix (Dmat * (s : Matrix (Fin 3) (Fin 3) k)) := by
    rw [hsM', hsM, hA] at h1
    rw [map_mul, map_mul]
    exact h1
  have h3 : (s' : Matrix (Fin 3) (Fin 3) k) * Dmat =
      Dmat * (s : Matrix (Fin 3) (Fin 3) k) :=
    Matrix.map_injective (algebraMap k L).injective hmap
  have hG : (g : Matrix (Fin 3) (Fin 3) k) = Matrix.scalar (Fin 3) (c : k) * Dmat := by
    rw [hg, show Dmat = Matrix.diagonal ![(c : k), Algebra.norm k (a : K) * (c : k)⁻¹, 1]
      from rfl, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i
    · simp [pow_two]
    · change Algebra.norm k (a : K) = (c : k) * (Algebra.norm k (a : K) * (c : k)⁻¹)
      field_simp
    · simp
  have hcomm := Matrix.scalar_commute (n := Fin 3) (c : k) (fun r' => mul_comm _ _)
    (s' : Matrix (Fin 3) (Fin 3) k)
  have h4 : (s' : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k) =
      (g : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k) := by
    calc (s' : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k)
        = (s' : Matrix (Fin 3) (Fin 3) k) *
            (Matrix.scalar (Fin 3) (c : k) * Dmat) := by rw [hG]
      _ = ((s' : Matrix (Fin 3) (Fin 3) k) * Matrix.scalar (Fin 3) (c : k)) * Dmat := by
            rw [mul_assoc]
      _ = (Matrix.scalar (Fin 3) (c : k) * (s' : Matrix (Fin 3) (Fin 3) k)) * Dmat := by
            rw [hcomm.eq]
      _ = Matrix.scalar (Fin 3) (c : k) *
            ((s' : Matrix (Fin 3) (Fin 3) k) * Dmat) := by rw [mul_assoc]
      _ = Matrix.scalar (Fin 3) (c : k) *
            (Dmat * (s : Matrix (Fin 3) (Fin 3) k)) := by rw [h3]
      _ = (Matrix.scalar (Fin 3) (c : k) * Dmat) *
            (s : Matrix (Fin 3) (Fin 3) k) := by rw [mul_assoc]
      _ = (g : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k) := by rw [hG]
  have hGL : Matrix.SpecialLinearGroup.toGL s' * g =
      g * Matrix.SpecialLinearGroup.toGL s := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
    exact h4
  have htoGL : Matrix.SpecialLinearGroup.toGL s' =
      g * Matrix.SpecialLinearGroup.toGL s * g⁻¹ := by
    rw [← hGL]
    group
  exact triD4LineMk_mul_SL3_mul_inv k K g (Units.map (algebraMap k K).toMonoidHom c * a) hdet
    s s' htoGL

end CFSG.StandardType
