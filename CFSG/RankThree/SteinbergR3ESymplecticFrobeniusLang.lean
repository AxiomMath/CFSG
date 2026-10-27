module

public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.RankThree.Literature.AlternatingPencil
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical

public section

namespace CFSG.RankThree.SymplecticLang

open Matrix CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup
  mem_matrixIsometryGroup)
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry (exists_form_isometry)
open CFSG.RankThree.Literature.Beisiegel (isAlt_toBilin')

theorem exists_transpose_mul_mul_eq {K : Type*} [Field K] {m : ℕ}
    (B J : Matrix (Fin m) (Fin m) K) (hB : (Matrix.toBilin' B).IsAlt) (hBd : B.det ≠ 0)
    (hJ : (Matrix.toBilin' J).IsAlt) (hJd : J.det ≠ 0) :
    ∃ R : GL (Fin m) K, (R : Matrix (Fin m) (Fin m) K)ᵀ * B * R = J := by
  obtain ⟨e⟩ := exists_form_isometry (Matrix.toBilin' J) (Matrix.toBilin' B) hJ
    (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hJd) hB
    (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hBd) rfl
  set e' : (Fin m → K) ≃ₗ[K] (Fin m → K) := e.toLinearEquiv with he'
  set R : GL (Fin m) K :=
    Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv e') with hRdef
  have hR : Matrix.toLin' (R : Matrix (Fin m) (Fin m) K) =
      (e' : (Fin m → K) →ₗ[K] (Fin m → K)) := by
    refine LinearMap.ext fun x => ?_
    calc Matrix.toLin' (R : Matrix (Fin m) (Fin m) K) x =
          (Matrix.GeneralLinearGroup.toLin R : (Fin m → K) → Fin m → K) x := rfl
      _ = e' x := by
          rw [hRdef, MulEquiv.apply_symm_apply]
          rfl
  refine ⟨R, Matrix.toBilin'.injective ?_⟩
  rw [← Matrix.toBilin'_comp, hR]
  refine LinearMap.ext₂ fun x y => ?_
  rw [LinearMap.BilinForm.comp_apply]
  exact e.map_app y x

theorem symplectic_matrix_frobenius_lang_and_exact_fixed_group {K : Type} [Field K] [Finite K]
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {n : ℕ} (hn : 1 ≤ n)
    (J : GL (Fin (2 * n)) K)
    (hdiag : ∀ j, (J : Matrix (Fin (2 * n)) (Fin (2 * n)) K) j j = 0)
    (hskew : ∀ j l, (J : Matrix (Fin (2 * n)) (Fin (2 * n)) K) l j =
      -(J : Matrix (Fin (2 * n)) (Fin (2 * n)) K) j l)
    (A : GL (Fin (2 * n)) Ω)
    (hA : A ∈ matrixIsometryGroup
      ((J : Matrix (Fin (2 * n)) (Fin (2 * n)) K).map (algebraMap K Ω))) :
    ∃ P ∈ matrixIsometryGroup ((J : Matrix (Fin (2 * n)) (Fin (2 * n)) K).map (algebraMap K Ω)),
      (A : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω) =
          P * ((P : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω).map (· ^ Nat.card K))⁻¹ ∧
        {X : GL (Fin (2 * n)) Ω | X ∈ matrixIsometryGroup
            ((J : Matrix (Fin (2 * n)) (Fin (2 * n)) K).map (algebraMap K Ω)) ∧
          (A : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω) *
              (X : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω).map (· ^ Nat.card K) *
            (↑A⁻¹ : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω) = X} =
          (fun Y => P * GeneralLinearGroup.map (algebraMap K Ω) Y * P⁻¹) ''
            (matrixIsometryGroup (J : Matrix (Fin (2 * n)) (Fin (2 * n)) K) :
              Set (GL (Fin (2 * n)) K)) ∧
        ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧
          ∀ i j, (P : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω) i j ∈ L := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ℓ, hchar, f', hℓ, hcard⟩ := FiniteField.card' K
  set f : ℕ := (f' : ℕ) with hfdef
  have hf : 1 ≤ f := f'.pos
  have hK : Nat.card K = ℓ ^ f := by rw [Nat.card_eq_fintype_card, hcard]
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  set φ : Ω →+* Ω := iterateFrobenius Ω ℓ f with hφdef
  have hφ' : ∀ c, φ c = c ^ ℓ ^ f := fun c => iterateFrobenius_def ℓ f c
  have hφfun : (fun c : Ω => c ^ Nat.card K) = ⇑φ := funext fun c => by rw [hK, hφ']
  rw [hφfun]
  have hfixK : ∀ a : K, φ (algebraMap K Ω a) = algebraMap K Ω a := fun a => by
    rw [hφ']
    exact (mem_range_algebraMap_iff hℓ hf hK _).mp ⟨a, rfl⟩
  have hfix : ∀ c : Ω, φ c = c → c ∈ Set.range (algebraMap K Ω) := fun c hc =>
    (mem_range_algebraMap_iff hℓ hf hK c).mpr (by rw [← hφ']; exact hc)
  set J' : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω :=
    (J : Matrix (Fin (2 * n)) (Fin (2 * n)) K).map (algebraMap K Ω) with hJ'
  have hφJ' : J'.map φ = J' := by
    ext i j
    rw [Matrix.map_apply, hJ', Matrix.map_apply, hfixK]
  have hGval : ∀ (ψ : Ω →+* Ω) (X : GL (Fin (2 * n)) Ω),
      ((GeneralLinearGroup.map ψ X : GL (Fin (2 * n)) Ω) : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω) =
        (X : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω).map ψ := fun _ _ => rfl
  have hιfix : ∀ Y : GL (Fin (2 * n)) K,
      GeneralLinearGroup.map φ (GeneralLinearGroup.map (algebraMap K Ω) Y) =
        GeneralLinearGroup.map (algebraMap K Ω) Y := fun Y => by
    ext i j
    simp only [GeneralLinearGroup.map_apply, hfixK]
  have hιSp : ∀ Y : GL (Fin (2 * n)) K, GeneralLinearGroup.map (algebraMap K Ω) Y ∈
      matrixIsometryGroup J' ↔
        Y ∈ matrixIsometryGroup (J : Matrix (Fin (2 * n)) (Fin (2 * n)) K) := by
    intro Y
    rw [mem_matrixIsometryGroup, mem_matrixIsometryGroup]
    change ((Y : Matrix (Fin (2 * n)) (Fin (2 * n)) K).map (algebraMap K Ω))ᵀ * J' *
      (Y : Matrix (Fin (2 * n)) (Fin (2 * n)) K).map (algebraMap K Ω) = J' ↔ _
    rw [hJ', ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
    exact (Matrix.map_injective (algebraMap K Ω).injective).eq_iff
  obtain ⟨⟨H, hH⟩, -⟩ := matrix_frobenius_lang hℓ hf hK (by omega : 1 ≤ 2 * n) A
  have hAH : A = H⁻¹ * GeneralLinearGroup.map φ H := by
    apply Units.ext
    rw [hH, Units.val_mul, hGval, ← hφfun, hK]
  set c : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω := ((H⁻¹ : GL (Fin (2 * n)) Ω) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) Ω) with hcdef
  have hsc : ((GeneralLinearGroup.map φ H : GL (Fin (2 * n)) Ω) :
      Matrix (Fin (2 * n)) (Fin (2 * n)) Ω) * c.map φ = 1 := by
    rw [hcdef, ← hGval, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hB'fix : (cᵀ * J' * c).map φ = cᵀ * J' * c := by
    have hA' : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω)ᵀ * J' * A = J' := hA
    have e1 : (c.map φ)ᵀ * ((A : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω)ᵀ * J' * A) * c.map φ =
        cᵀ * J' * c := by
      rw [hAH, Units.val_mul, Matrix.transpose_mul]
      calc (c.map φ)ᵀ * (((GeneralLinearGroup.map φ H : GL (Fin (2 * n)) Ω) :
              Matrix (Fin (2 * n)) (Fin (2 * n)) Ω)ᵀ * cᵀ * J' *
            (c * ((GeneralLinearGroup.map φ H : GL (Fin (2 * n)) Ω) :
              Matrix (Fin (2 * n)) (Fin (2 * n)) Ω))) * c.map φ =
          (((GeneralLinearGroup.map φ H : GL (Fin (2 * n)) Ω) :
              Matrix (Fin (2 * n)) (Fin (2 * n)) Ω) * c.map φ)ᵀ * (cᵀ * J' * c) *
            (((GeneralLinearGroup.map φ H : GL (Fin (2 * n)) Ω) :
              Matrix (Fin (2 * n)) (Fin (2 * n)) Ω) * c.map φ) := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = cᵀ * J' * c := by rw [hsc, transpose_one, Matrix.one_mul, Matrix.mul_one]
    rw [hA'] at e1
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hφJ']
    exact e1
  obtain ⟨B, hBmap⟩ : ∃ B : Matrix (Fin (2 * n)) (Fin (2 * n)) K,
      B.map (algebraMap K Ω) = cᵀ * J' * c := by
    have hent : ∀ i j, (cᵀ * J' * c) i j ∈ Set.range (algebraMap K Ω) := fun i j =>
      hfix _ (by
        have := congrFun (congrFun hB'fix i) j
        rwa [Matrix.map_apply] at this)
    choose b hb using hent
    exact ⟨Matrix.of b, by ext i j; exact hb i j⟩
  have hJ'alt : (Matrix.toBilin' J').IsAlt := isAlt_toBilin' J'
    (fun j => by simp [J', hdiag]) (fun j l => by simp [J', hskew j l])
  have hB'alt : ∀ w : Fin (2 * n) → Ω, w ⬝ᵥ ((cᵀ * J' * c) *ᵥ w) = 0 := by
    intro w
    have h := hJ'alt (c *ᵥ w)
    rw [Matrix.toBilin'_apply'] at h
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
    exact h
  have hBalt : (Matrix.toBilin' B).IsAlt := by
    intro v
    rw [Matrix.toBilin'_apply']
    apply (algebraMap K Ω).injective
    have hv : (algebraMap K Ω) ∘ (B *ᵥ v) = B.map (algebraMap K Ω) *ᵥ ((algebraMap K Ω) ∘ v) :=
      funext fun i => RingHom.map_mulVec _ _ _ i
    rw [map_zero, RingHom.map_dotProduct, hv, hBmap]
    exact hB'alt _
  have hJ'det : J'.det ≠ 0 := by
    rw [hJ', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).mpr (GeneralLinearGroup.det_ne_zero J)
  have hBdet : B.det ≠ 0 := by
    intro h0
    have h1 := congrArg (algebraMap K Ω) h0
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hBmap, map_zero, Matrix.det_mul,
      Matrix.det_mul, Matrix.det_transpose] at h1
    have hc0 : c.det ≠ 0 := GeneralLinearGroup.det_ne_zero H⁻¹
    exact mul_ne_zero (mul_ne_zero hc0 hJ'det) hc0 h1
  have hJalt : (Matrix.toBilin' (J : Matrix (Fin (2 * n)) (Fin (2 * n)) K)).IsAlt :=
    isAlt_toBilin' _ hdiag hskew
  obtain ⟨R, hR⟩ :=
    exists_transpose_mul_mul_eq B _ hBalt hBdet hJalt (GeneralLinearGroup.det_ne_zero J)
  obtain ⟨R', hR'def⟩ : ∃ R' : GL (Fin (2 * n)) Ω, R' = GeneralLinearGroup.map (algebraMap K Ω) R :=
    ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : GL (Fin (2 * n)) Ω, P = H⁻¹ * R' := ⟨_, rfl⟩
  have hPSp : P ∈ matrixIsometryGroup J' := by
    rw [mem_matrixIsometryGroup, hPdef, Units.val_mul, Matrix.transpose_mul]
    calc (R' : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω)ᵀ * cᵀ * J' * (c * R') =
          (R' : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω)ᵀ * (cᵀ * J' * c) * R' := by
          simp only [Matrix.mul_assoc]
      _ = J' := by
          rw [← hBmap, hR'def]
          change ((R : Matrix (Fin (2 * n)) (Fin (2 * n)) K).map (algebraMap K Ω))ᵀ *
            B.map (algebraMap K Ω) * (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K).map
              (algebraMap K Ω) = J'
          rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hR]
  have hAP : A = P * (GeneralLinearGroup.map φ P)⁻¹ := by
    rw [hAH, hPdef, map_mul, map_inv, hR'def, hιfix, _root_.mul_inv_rev, inv_inv]
    group
  refine ⟨P, hPSp, ?_, ?_, ?_⟩
  ·
    have h := congrArg (fun Z : GL (Fin (2 * n)) Ω => (Z : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω))
      hAP
    simp only [Units.val_mul, Matrix.coe_units_inv] at h
    rw [h, hGval]
  ·
    have hfixGL : ∀ X : GL (Fin (2 * n)) Ω,
        (A : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω) *
            (X : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω).map φ *
          (↑A⁻¹ : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω) = X ↔
        A * GeneralLinearGroup.map φ X * A⁻¹ = X := by
      intro X
      rw [← hGval, ← Units.val_mul, ← Units.val_mul]
      exact Units.val_inj
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe]
    rw [hfixGL]
    constructor
    · rintro ⟨hXSp, hXfix⟩
      set Z := P⁻¹ * X * P with hZdef
      have hZfix : GeneralLinearGroup.map φ Z = Z := by
        have hσX : GeneralLinearGroup.map φ X = A⁻¹ * X * A := by
          calc GeneralLinearGroup.map φ X = A⁻¹ * (A * GeneralLinearGroup.map φ X * A⁻¹) * A := by
                group
            _ = A⁻¹ * X * A := by rw [hXfix]
        rw [hZdef]
        simp only [map_mul, map_inv]
        rw [hσX, hAP]
        group
      obtain ⟨Ym, hYm⟩ : ∃ Ym : Matrix (Fin (2 * n)) (Fin (2 * n)) K,
          Ym.map (algebraMap K Ω) = (Z : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω) := by
        have hent : ∀ i j, (Z : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω) i j ∈
            Set.range (algebraMap K Ω) := fun i j => hfix _ (by
          have := congrFun (congrFun (congrArg (fun W : GL (Fin (2 * n)) Ω =>
            (W : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω)) hZfix) i) j
          simpa only [hGval, Matrix.map_apply] using this)
        choose b hb using hent
        exact ⟨Matrix.of b, by ext i j; exact hb i j⟩
      have hYdet : Ym.det ≠ 0 := by
        intro h0
        have h1 := congrArg (algebraMap K Ω) h0
        rw [RingHom.map_det, RingHom.mapMatrix_apply, hYm, map_zero] at h1
        exact GeneralLinearGroup.det_ne_zero Z h1
      set Y : GL (Fin (2 * n)) K := GeneralLinearGroup.mkOfDetNeZero Ym hYdet with hYdef
      have hYZ : GeneralLinearGroup.map (algebraMap K Ω) Y = Z := Units.ext hYm
      have hZSp : Z ∈ matrixIsometryGroup J' :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hPSp) hXSp) hPSp
      refine ⟨Y, (hιSp Y).mp (by rw [hYZ]; exact hZSp), ?_⟩
      rw [hYZ, hZdef]
      group
    · rintro ⟨Y, hY, rfl⟩
      refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hPSp ((hιSp Y).mpr hY))
        (Subgroup.inv_mem _ hPSp), ?_⟩
      rw [hAP]
      simp only [map_mul, map_inv, hιfix]
      group
  ·
    set S : Set Ω := Set.range fun x : Fin (2 * n) × Fin (2 * n) =>
      (P : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω) x.1 x.2
    have : Finite S := Set.finite_range _ |>.to_subtype
    have : Algebra.IsIntegral K Ω := (IsAlgClosure.isAlgebraic (R := K) (K := Ω)).isIntegral
    exact ⟨IntermediateField.adjoin K S,
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x,
      fun i j => IntermediateField.subset_adjoin K S ⟨(i, j), rfl⟩⟩

end CFSG.RankThree.SymplecticLang
