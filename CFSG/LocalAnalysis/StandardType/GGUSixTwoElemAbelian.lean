module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoF4Transport
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeF4CubeScalar
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeF4Torus
public import CFSG.Fischer.Unitary
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoElemAbelianAux
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.KF.UnitaryModel

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly Matrix
open scoped commutatorElement

variable {K : Type} [Field K]

theorem eq_one_of_det_eq_one_of_pow_three_eq_scalar [Finite K] (hK : Nat.card K = 4)
    {s : Matrix (Fin 6) (Fin 6) K} (hs : s.det = 1) {c : K}
    (h : s ^ 3 = Matrix.scalar (Fin 6) c) : c = 1 := by
  classical
  let e : K ≃+* CFSG.Fischer.F4 := ringEquivF4 hK
  have hdet : (s.map (e : K →+* CFSG.Fischer.F4)).det = 1 := by
    have h1 := RingHom.map_det (e : K →+* CFSG.Fischer.F4) s
    rw [hs, map_one] at h1
    exact h1.symm
  have hpow : (s.map (e : K →+* CFSG.Fischer.F4)) ^ 3 = Matrix.scalar (Fin 6) (e c) := by
    rw [← Matrix.map_pow (f := (e : K →+* CFSG.Fischer.F4)) (a := 3), h, Matrix.scalar_apply,
      Matrix.scalar_apply, Matrix.diagonal_map (f := (e : K →+* CFSG.Fischer.F4)) (map_zero e)]
    rfl
  exact e.injective (by
    rw [CFSG.GGQ2Prime.eq_one_of_det_eq_one_of_pow_three_eq_scalar hdet hpow, map_one])

section F4Transport

open CFSG.Fischer
open CFSG.RankThree.PartOne.KFU (torusSU diagU diagU_val mem_torusSU_iff isDiag_diagU)

theorem isIsom_iff_map_sq_transpose_mul {A : Matrix (Fin 6) (Fin 6) F4} :
    IsIsom A ↔ (A.map (· ^ 2))ᵀ * A = 1 := by
  let h4 : Nat.card F4 = 4 := by rw [Nat.card_eq_fintype_card, F4.card]
  let h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F4 := fieldDataFour h4
  have hbar : ⇑h.bar = fun x : F4 => x ^ 2 := funext (fieldDataFour_bar h4)
  have hgf : ∀ x y : Fin 6 → F4,
      CFSG.ClassicalGroups.UnitaryFlag.gramForm h (1 : Matrix (Fin 6) (Fin 6) F4) x y =
        herm y x := by
    intro x y
    rw [CFSG.ClassicalGroups.UnitaryFlag.gramForm_apply, herm_eq]
    simp only [hbar, Matrix.one_mulVec, dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hiso : IsIsom A ↔ ∀ x y : Fin 6 → F4,
      CFSG.ClassicalGroups.UnitaryFlag.gramForm h (1 : Matrix (Fin 6) (Fin 6) F4)
        (A *ᵥ x) (A *ᵥ y) =
      CFSG.ClassicalGroups.UnitaryFlag.gramForm h (1 : Matrix (Fin 6) (Fin 6) F4) x y := by
    constructor
    · intro hA x y
      rw [hgf, hgf]
      exact hA y x
    · intro hA x y
      have h' := hA y x
      rwa [hgf, hgf] at h'
  rw [hiso, CFSG.ClassicalGroups.UnitaryFlag.gramForm_isometry_iff, hbar]
  simp

theorem map_sq_transpose_mul_self_mul [CharP K 2] {A B : Matrix (Fin 6) (Fin 6) K}
    (hA : (A.map (· ^ 2))ᵀ * A = 1) (hB : (B.map (· ^ 2))ᵀ * B = 1) :
    ((A * B).map (· ^ 2))ᵀ * (A * B) = 1 := by
  have hsq : (fun x : K => x ^ 2) = ⇑(frobenius K 2) := by
    funext x
    rw [frobenius_def]
  rw [hsq] at hA hB ⊢
  have hstep : ∀ M N : Matrix (Fin 6) (Fin 6) K,
      (Nᵀ * Mᵀ) * (A * B) = Nᵀ * (Mᵀ * A) * B := by
    intro M N
    noncomm_ring
  rw [Matrix.map_mul (f := frobenius K 2), Matrix.transpose_mul, hstep, hA]
  simp [hB]

theorem map_sq_transpose_mul_self_map {L : Type} [Field L] (e : K ≃+* L)
    {A : Matrix (Fin 6) (Fin 6) K} (hA : (A.map (· ^ 2))ᵀ * A = 1) :
    ((A.map (e : K → L)).map (· ^ 2))ᵀ * A.map (e : K → L) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h1 : (∑ k, e (A k i) ^ 2 * e (A k j)) = e (∑ k, A k i ^ 2 * A k j) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul, map_pow]
  rw [h1]
  have h2 : (∑ k, A k i ^ 2 * A k j) = ((A.map (· ^ 2))ᵀ * A) i j := by
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [h2, hA, Matrix.one_apply, Matrix.one_apply]
  split_ifs with h
  · rw [map_one]
  · rw [map_zero]

theorem inv_mul_mul_eq_of_isDiag {t Y : GL (Fin 6) K}
    (ht : ((t : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag)
    (hY : ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag) :
    t⁻¹ * Y * t = Y := by
  have hcomm : t * Y = Y * t := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ← ht.diagonal_diag, ← hY.diagonal_diag,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem exists_conj_le_torSU [Finite K] (hK : Nat.card K = 4)
    {E : Subgroup ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h3 : ∀ a ∈ E, a ^ 3 = 1) :
    ∃ g : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)), E.map (MulAut.conj g).toMonoidHom ≤ torSU K := by
  classical
  haveI : CharP K 2 := charP_two_of_card_four hK
  let SUK : Subgroup (GL (Fin 6) K) := LargeEvenSUGroup (Fin 6) K (2 ^ 1)
  let e : K ≃+* F4 := ringEquivF4 hK
  let hom : ↥SUK →* GL (Fin 6) F4 :=
    (Matrix.GeneralLinearGroup.map (e : K →+* F4)).comp SUK.subtype
  let E' : Subgroup (GL (Fin 6) F4) := E.map hom
  have hbar : ⇑(fieldDataFour hK).bar = fun x : K => x ^ 2 := funext (fieldDataFour_bar hK)
  have hE'SU : E' ≤ SU0 := by
    rintro x ⟨a, ha, rfl⟩
    have hmem : ((a : ↥SUK) : GL (Fin 6) K) ∈ SUK := a.2
    rw [mem_SU_iff (fieldDataFour hK), hbar] at hmem
    obtain ⟨hdet, huni⟩ := hmem
    have hdetu : Matrix.GeneralLinearGroup.det ((a : ↥SUK) : GL (Fin 6) K) = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
    have hdet' : Matrix.GeneralLinearGroup.det (hom a) = 1 := by
      have h : Matrix.GeneralLinearGroup.det (hom a) =
          Units.map (e : K →* F4) (Matrix.GeneralLinearGroup.det ((a : ↥SUK) : GL (Fin 6) K)) :=
        Matrix.GeneralLinearGroup.map_det (e : K →+* F4) ((a : ↥SUK) : GL (Fin 6) K)
      rw [h, hdetu, map_one]
    have hisom : IsIsom ((hom a : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := by
      refine isIsom_iff_map_sq_transpose_mul.mpr ?_
      have h := map_sq_transpose_mul_self_map (e := e) huni
      simpa [hom, Matrix.GeneralLinearGroup.val_map_apply] using h
    exact Subgroup.subset_closure ⟨hdet', hisom⟩
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    simpa [hom, map_mul] using congrArg hom (hcomm a ha b hb)
  have hE'3 : ∀ a ∈ E', a ^ 3 = 1 := by
    rintro x ⟨a, ha, rfl⟩
    simpa [hom, map_pow] using congrArg hom (h3 a ha)
  obtain ⟨y, hyGU, hyconj⟩ := CFSG.GGQ2Prime.exists_conj_le_torusSU hE'SU hE'comm hE'3
  have hyu : ((y : Matrix (Fin 6) (Fin 6) F4).map (· ^ 2))ᵀ * y = 1 :=
    isIsom_iff_map_sq_transpose_mul.mp hyGU
  let yK : GL (Fin 6) K := Matrix.GeneralLinearGroup.map (e.symm : F4 →+* K) y
  have hyKu : (((yK : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map (· ^ 2))ᵀ *
      ((yK : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
    have h := map_sq_transpose_mul_self_map (e := e.symm) (A := (y : Matrix (Fin 6) (Fin 6) F4)) hyu
    simpa [yK, Matrix.GeneralLinearGroup.val_map_apply] using h
  let μ : Kˣ := (Matrix.GeneralLinearGroup.det yK)⁻¹
  let t : GL (Fin 6) K := diagU (Pi.mulSingle (0 : Fin 6) μ)
  have hμ : (μ : K) ^ 2 * μ = 1 := by
    have h := congrArg Units.val (cube_unit_eq_one hK μ)
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h
    calc (μ : K) ^ 2 * μ = (μ : K) ^ 3 := by ring
      _ = 1 := h
  have ht_det : Matrix.GeneralLinearGroup.det t = μ := by
    have ht : t = diagU (Pi.mulSingle (0 : Fin 6) μ) := rfl
    apply Units.ext
    rw [ht, Matrix.GeneralLinearGroup.val_det_apply, diagU_val, Matrix.det_diagonal]
    rw [Finset.prod_eq_single (0 : Fin 6)]
    · rw [Pi.mulSingle_eq_same]
    · intro j _ hj
      rw [Pi.mulSingle_eq_of_ne hj]
      rfl
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin 6)) h
  have ht_unitary : (((t : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map (· ^ 2))ᵀ *
      ((t : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
    have ht : t = diagU (Pi.mulSingle (0 : Fin 6) μ) := rfl
    rw [ht, diagU_val, Matrix.diagonal_map (by norm_num), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
    funext k
    by_cases hk : k = 0
    · subst hk
      simp [Pi.mulSingle_eq_same, hμ]
    · simp [Pi.mulSingle_eq_of_ne hk]
  have hg0 : yK * t ∈ SUK := by
    rw [show SUK = LargeEvenSUGroup (Fin 6) K (2 ^ 1) from rfl,
      mem_SU_iff (fieldDataFour hK), hbar]
    refine ⟨?_, ?_⟩
    · have hd : Matrix.GeneralLinearGroup.det (yK * t) = 1 := by
        rw [map_mul, ht_det]
        exact mul_inv_cancel _
      have := congrArg Units.val hd
      rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this
    · have hyt : (((yK * t : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K) =
          (yK : Matrix (Fin 6) (Fin 6) K) * (t : Matrix (Fin 6) (Fin 6) K) := rfl
      rw [hyt]
      exact map_sq_transpose_mul_self_mul hyKu ht_unitary
  let g : ↥SUK := ⟨yK * t, hg0⟩⁻¹
  refine ⟨g, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have hconj_a : y⁻¹ * hom a * y ∈ torusSU 3 6 F4 := by
    have h1 : (MulAut.conj y⁻¹) (hom a) ∈ E'.map (MulAut.conj y⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem ((MulAut.conj y⁻¹).toMonoidHom)
        (Subgroup.mem_map_of_mem hom ha)
    have h2 := hyconj h1
    simpa [MulAut.conj_apply] using h2
  obtain ⟨u, -, -, hu⟩ := mem_torusSU_iff.mp hconj_a
  have hmap_hom : Matrix.GeneralLinearGroup.map (e.symm : F4 →+* K) (hom a) =
      ((a : ↥SUK) : GL (Fin 6) K) := by
    have hhom : hom a =
        Matrix.GeneralLinearGroup.map (e : K →+* F4) ((a : ↥SUK) : GL (Fin 6) K) := rfl
    rw [hhom, glMap_symm_glMap]
  have hYdiag : (((yK⁻¹ * ((a : ↥SUK) : GL (Fin 6) K) * yK : GL (Fin 6) K)) :
      Matrix (Fin 6) (Fin 6) K).IsDiag := by
    have heq : (yK⁻¹ * ((a : ↥SUK) : GL (Fin 6) K) * yK : GL (Fin 6) K) =
        Matrix.GeneralLinearGroup.map (e.symm : F4 →+* K) (y⁻¹ * hom a * y) := by
      rw [map_mul, map_mul, map_inv, hmap_hom]
    rw [heq, ← hu, map_diagU]
    exact isDiag_diagU _
  have ht_diag : ((t : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag := isDiag_diagU _
  rw [torSU, Subgroup.mem_comap, TauCeti.mem_diagonalTorus_iff]
  show ((((MulAut.conj g) a : ↥SUK) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag
  have hco : (((MulAut.conj g) a : ↥SUK) : GL (Fin 6) K) =
      t⁻¹ * (yK⁻¹ * ((a : ↥SUK) : GL (Fin 6) K) * yK) * t := by
    rw [MulAut.conj_apply]
    change (g : GL (Fin 6) K) * ((a : ↥SUK) : GL (Fin 6) K) * (g : GL (Fin 6) K)⁻¹ = _
    rw [show (g : GL (Fin 6) K) = (yK * t)⁻¹ from rfl]
    group
  rw [hco, inv_mul_mul_eq_of_isDiag ht_diag hYdiag]
  exact hYdiag

end F4Transport

theorem card_le_nine_of_le_centralizer [Finite K] (hK : Nat.card K = 4)
    {a c : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))} (ha : a ^ 3 = 1) (hac : a * c ≠ c * a)
    (hs : c * a * c⁻¹ * a⁻¹ ∈
      (LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    {R : Subgroup ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))} (hR : IsPGroup 3 R)
    (hRa : R ≤ Subgroup.centralizer {a, c}) : Nat.card R ≤ 9 := by
  classical
  let SU := LargeEvenSUGroup (Fin 6) K (2 ^ 1)
  let M : Matrix (Fin 6) (Fin 6) K := (a : GL (Fin 6) K)
  let C : Matrix (Fin 6) (Fin 6) K := (c : GL (Fin 6) K)
  have hM3 : M ^ 3 = 1 := by
    have h : (((a ^ 3 : SU) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
      rw [ha]; rfl
    simpa [M, Subgroup.coe_pow] using h
  have hs' : ((c * a * c⁻¹ * a⁻¹ : SU) : GL (Fin 6) K) ∈ LargeEvenScalars (Fin 6) K := by
    simpa [SU, Subgroup.mem_subgroupOf] using hs
  rw [largeEvenScalars_def, MonoidHom.mem_range] at hs'
  obtain ⟨lam, hlam⟩ := hs'
  let S : GL (Fin 6) K := Matrix.GeneralLinearGroup.scalar (Fin 6) lam
  have hCM_GL : (c : GL (Fin 6) K) * (a : GL (Fin 6) K) =
      S * (a : GL (Fin 6) K) * (c : GL (Fin 6) K) := by
    dsimp [S]
    rw [hlam]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hMC_GL : (a : GL (Fin 6) K) * (c : GL (Fin 6) K) =
      S⁻¹ * (c : GL (Fin 6) K) * (a : GL (Fin 6) K) := by
    calc
      (a : GL (Fin 6) K) * (c : GL (Fin 6) K) = S⁻¹ * (S * (a : GL (Fin 6) K) *
          (c : GL (Fin 6) K)) := by group
      _ = S⁻¹ * ((c : GL (Fin 6) K) * (a : GL (Fin 6) K)) := by rw [← hCM_GL]
      _ = S⁻¹ * (c : GL (Fin 6) K) * (a : GL (Fin 6) K) := by group
  have hrel_GL : (a : GL (Fin 6) K) * (c : GL (Fin 6) K) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) lam⁻¹ * (c : GL (Fin 6) K) *
        (a : GL (Fin 6) K) := by
    rw [hMC_GL]
    rw [show S = Matrix.GeneralLinearGroup.scalar (Fin 6) lam from rfl, map_inv]
  have hrel : M * C = Matrix.scalar (Fin 6) (((lam⁻¹ : Kˣ) : K)) * C * M := by
    have h := congrArg (fun u : GL (Fin 6) K => ((u : Matrix (Fin 6) (Fin 6) K))) hMC_GL
    have hSinv : ((S⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        Matrix.scalar (Fin 6) (((lam⁻¹ : Kˣ) : K)) := by
      change (((Matrix.GeneralLinearGroup.scalar (Fin 6) lam)⁻¹ : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) = Matrix.scalar (Fin 6) (((lam⁻¹ : Kˣ) : K))
      rw [show (Matrix.GeneralLinearGroup.scalar (Fin 6) lam)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 6) lam⁻¹ from
          (map_inv (Matrix.GeneralLinearGroup.scalar (Fin 6)) lam).symm]
      rw [Matrix.GeneralLinearGroup.coe_scalar]
    simpa [M, C, hSinv] using h
  have hlamne : lam ≠ 1 := by
    intro h
    apply hac
    have hca : (c : GL (Fin 6) K) * (a : GL (Fin 6) K) =
        (a : GL (Fin 6) K) * (c : GL (Fin 6) K) := by
      have h' := hCM_GL
      dsimp [S] at h'
      rw [h, map_one] at h'
      simpa using h'
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hca.symm
  have hlam3 : lam ^ 3 = 1 := cube_unit_eq_one hK lam
  have hCdet : IsUnit C.det := by
    have h := (mem_SU_iff (fieldDataFour hK)).mp c.2 |>.1
    change ((c : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 at h
    rw [show C = ((c : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) from rfl, h]
    exact isUnit_one
  let R' : Subgroup (GL (Fin 6) K) := R.map (Subgroup.subtype SU)
  have hR' : IsPGroup 3 R' := hR.map (Subgroup.subtype SU)
  have hcardR' : Nat.card R' = Nat.card R := by
    dsimp [R']
    exact Subgroup.card_map_of_injective (Subgroup.subtype_injective SU)
  have hcomm' : ∀ y ∈ R', ((y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * M =
        M * ((y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ∧
      ((y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * C =
        C * ((y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hy
    have ha_ctr := (Subgroup.mem_centralizer_iff.mp (hRa hr)) a (by simp)
    have hc_ctr := (Subgroup.mem_centralizer_iff.mp (hRa hr)) c (by simp)
    constructor
    · have h := congrArg (fun x : SU => ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) ha_ctr
      simpa [M, Subgroup.coe_mul] using h.symm
    · have h := congrArg (fun x : SU => ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) hc_ctr
      simpa [C, Subgroup.coe_mul] using h.symm
  have hmain := card_le_nine_of_matrix_data hK hM3 hlam3 hlamne hrel hCdet hR' hcomm'
  rw [hcardR'] at hmain
  exact hmain

theorem exists_conj_eq_torU [Finite K] (hK : Nat.card K = 4)
    {E : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 4) :
    ∃ g : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)),
      E.map (MulAut.conj g).toMonoidHom = torU K := by
  classical
  let H := LargeEvenSUGroup (Fin 6) K (2 ^ 1)
  let U := LargeEvenProj H
  let π : H →* U := LargeEvenProjMk H
  let Z : Subgroup H := (LargeEvenScalars (Fin 6) K).subgroupOf H
  let Ehat : Subgroup H := E.comap π
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Z := by
    dsimp [π, Z, LargeEvenProjMk]
    rw [QuotientGroup.ker_mk']
  have hZcard : Nat.card Z = 3 := by
    dsimp [Z]
    exact card_scalars_subgroupOf_SU hK
  have hEhatcard : Nat.card Ehat = 3 ^ 5 := by
    have hmapE : Ehat.map π = E := by
      dsimp [Ehat]
      exact Subgroup.map_comap_eq_self_of_surjective hπsurj E
    have hr := Subgroup.card_ker_mul_card_range (π.domRestrict Ehat)
    have hrange : (π.domRestrict Ehat).range = E := by
      rw [MonoidHom.domRestrict_range]
      exact hmapE
    have hkerdom : (π.domRestrict Ehat).ker = Z.subgroupOf Ehat := by
      rw [MonoidHom.ker_domRestrict, hker]
    have hkerz : Nat.card (Z.subgroupOf Ehat) = 3 := by
      have hle : Z ≤ Ehat := by
        rw [← hker]
        exact MonoidHom.ker_le_comap π E
      have hcard := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
      rw [hcard, hZcard]
    rw [hrange, hkerdom, hkerz, hc] at hr
    norm_num at hr ⊢
    omega
  have hE3 : ∀ x ∈ Ehat, x ^ 3 = 1 := by
    intro x hx
    have hxE : π x ∈ E := hx
    have hx3ker : x ^ 3 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hE.2 (π x) hxE
    have hx3Z : x ^ 3 ∈ Z := by
      rwa [hker] at hx3ker
    have hx3scal : ((x ^ 3 : H) : GL (Fin 6) K) ∈ LargeEvenScalars (Fin 6) K :=
      Subgroup.mem_subgroupOf.mp hx3Z
    rw [largeEvenScalars_def, MonoidHom.mem_range] at hx3scal
    obtain ⟨c, hcscal⟩ := hx3scal
    have hxdet : (((x : H) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
      (mem_SU_iff (fieldDataFour hK)).mp x.2 |>.1
    have hpow : (((x : H) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ^ 3 =
        Matrix.scalar (Fin 6) (c : K) := by
      have h := congrArg (fun u : GL (Fin 6) K => ((u : Matrix (Fin 6) (Fin 6) K))) hcscal
      rw [Subgroup.coe_pow] at h
      simpa [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar] using h.symm
    have hc1 : (c : K) = 1 :=
      eq_one_of_det_eq_one_of_pow_three_eq_scalar hK hxdet hpow
    apply Subtype.ext
    apply Units.ext
    have hmat : (((x : H) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ^ 3 = 1 := by
      rw [hpow, hc1]
      ext i j
      simp [Matrix.scalar_apply, Matrix.one_apply]
    simpa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using hmat
  have hcommKer : ∀ x ∈ Ehat, ∀ y ∈ Ehat, x * y * x⁻¹ * y⁻¹ ∈ Z := by
    intro x hx y hy
    rw [← hker, MonoidHom.mem_ker]
    have hxE : π x ∈ E := hx
    have hyE : π y ∈ E := hy
    have hcomm : π x * π y = π y * π x :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨π x, hxE⟩ ⟨π y, hyE⟩)
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  have hEhatP : IsPGroup 3 Ehat := by
    have hExp : Monoid.exponent Ehat ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one (by
        intro x
        apply Subtype.ext
        simpa using hE3 (x : H) x.2)
    exact IsPGroup.of_exponent_dvd_pow (n := 1) (by simpa using hExp)
  by_cases hEc : IsMulCommutative Ehat
  · have hcommE : ∀ a ∈ Ehat, ∀ b ∈ Ehat, a * b = b * a :=
      fun a ha b hb => congrArg Subtype.val (hEc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    obtain ⟨g, hgle⟩ := exists_conj_le_torSU hK hcommE hE3
    have hmap_le : E.map (MulAut.conj (π g)).toMonoidHom ≤ torU K := by
      intro e he
      obtain ⟨x, hxE, rfl⟩ := Subgroup.mem_map.mp he
      obtain ⟨y, rfl⟩ := hπsurj x
      have hy : y ∈ Ehat := hxE
      have hgy : (MulAut.conj g).toMonoidHom y ∈ torSU K :=
        hgle (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
      refine Subgroup.mem_map.mpr ⟨(MulAut.conj g).toMonoidHom y, hgy, ?_⟩
      dsimp [π]
      simp only [MulAut.conj_apply, map_mul, map_inv]
      rfl
    refine ⟨π g, le_antisymm hmap_le ?_⟩
    have hcardmap : Nat.card (E.map (MulAut.conj (π g)).toMonoidHom) = 3 ^ 4 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj (π g)).injective]
      exact hc
    have hcardT : Nat.card (torU K) = 3 ^ 4 := card_torU hK
    have hEq : E.map (MulAut.conj (π g)).toMonoidHom = torU K :=
      Subgroup.eq_of_le_of_card_ge hmap_le (by rw [hcardT, hcardmap])
    exact hEq.ge
  · have hnotcomm : ∃ a c : Ehat, a * c ≠ c * a := by
      by_contra h
      push Not at h
      exact hEc (IsMulCommutative.of_comm h)
    obtain ⟨a, c, hac⟩ := hnotcomm
    have ha3 : ((a : H) ^ 3) = 1 := hE3 a a.2
    have hacH : (a : H) * (c : H) ≠ (c : H) * (a : H) := by
      intro h
      exact hac (Subtype.ext h)
    have hs : (c : H) * (a : H) * (c : H)⁻¹ * (a : H)⁻¹ ∈ Z :=
      hcommKer c c.2 a a.2
    let R : Subgroup H := Ehat ⊓ Subgroup.centralizer ({(a : H), (c : H)} : Set H)
    have hRle : R ≤ Ehat := inf_le_left
    have hRpg : IsPGroup 3 R := by
      have hExp : Monoid.exponent R ∣ 3 :=
        Monoid.exponent_dvd_of_forall_pow_eq_one (by
          intro x
          apply Subtype.ext
          simpa using hE3 (x : H) x.2.1)
      exact IsPGroup.of_exponent_dvd_pow (n := 1) (by simpa using hExp)
    have hRa : R ≤ Subgroup.centralizer ({(a : H), (c : H)} : Set H) := inf_le_right
    have hR9 : Nat.card R ≤ 9 :=
      card_le_nine_of_le_centralizer hK ha3 hacH hs hRpg hRa
    let Ca : Subgroup H := Subgroup.centralizer ({(a : H)} : Set H)
    let Cc : Subgroup H := Subgroup.centralizer ({(c : H)} : Set H)
    have hcent_pair : Subgroup.centralizer ({(a : H), (c : H)} : Set H) = Ca ⊓ Cc := by
      ext x
      simp only [Subgroup.mem_inf, Ca, Cc, Subgroup.mem_centralizer_iff,
        Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    have hR_eq : R = (Ehat ⊓ Ca) ⊓ (Ehat ⊓ Cc) := by
      dsimp [R]
      rw [hcent_pair]
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    have hZhatcard : Nat.card (Z.subgroupOf Ehat) = 3 := by
      have hle : Z ≤ Ehat := by
        rw [← hker]
        exact MonoidHom.ker_le_comap π E
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hZcard]
    have hrel_a : (Ehat ⊓ Ca).relIndex Ehat ≤ 3 := by
      have hcentE : Subgroup.centralizer ({(a : Ehat)} : Set Ehat) =
          (Ehat ⊓ Ca).subgroupOf Ehat := by
        ext x
        constructor
        · intro h
          have h' := Subgroup.mem_centralizer_iff.mp h a (by simp)
          refine ⟨x.2, ?_⟩
          apply Subgroup.mem_centralizer_iff.mpr
          intro z hz
          have hz' : z = (a : H) := by simpa using hz
          subst hz'
          simpa [Subgroup.coe_mul] using congrArg Subtype.val h'
        · intro h
          apply Subgroup.mem_centralizer_iff.mpr
          intro y hy
          have hy' : y = a := by simpa using hy
          subst y
          have hxca : (a : H) * (x : H) = (x : H) * (a : H) :=
            Subgroup.mem_centralizer_iff.mp h.2 a (by simp)
          apply Subtype.ext
          simpa [Subgroup.coe_mul] using hxca
      have hIndex : (Subgroup.centralizer ({(a : Ehat)} : Set Ehat)).index ≤ 3 := by
        rw [Subgroup.index_centralizer_eq_ncard]
        have hsub : conjugatesOf a ⊆
            (fun z : Z.subgroupOf Ehat => ((z : Ehat) * a)) '' Set.univ := by
          intro b hb
          rw [conjugatesOf, Set.mem_setOf_eq, isConj_iff] at hb
          obtain ⟨x, rfl⟩ := hb
          have hz : ⁅x, a⁆ ∈ Z.subgroupOf Ehat := hcommKer x x.2 a a.2
          exact ⟨⟨⁅x, a⁆, hz⟩, Set.mem_univ _, by
            exact (conj_eq_commutatorElement_mul (g₁ := x) (g₂ := a)).symm⟩
        calc (conjugatesOf a).ncard ≤
              ((fun z : Z.subgroupOf Ehat => ((z : Ehat) * a)) '' Set.univ).ncard :=
                Set.ncard_le_ncard hsub
          _ ≤ (Set.univ : Set (Z.subgroupOf Ehat)).ncard := Set.ncard_image_le
          _ = Nat.card (Z.subgroupOf Ehat) := by simp
          _ = 3 := hZhatcard
      rw [hcentE] at hIndex
      have hconv : (Ehat ⊓ Ca).relIndex Ehat = ((Ehat ⊓ Ca).subgroupOf Ehat).index := rfl
      rw [hconv]
      exact hIndex
    have hrel_c : (Ehat ⊓ Cc).relIndex Ehat ≤ 3 := by
      have hcentE : Subgroup.centralizer ({(c : Ehat)} : Set Ehat) =
          (Ehat ⊓ Cc).subgroupOf Ehat := by
        ext x
        constructor
        · intro h
          have h' := Subgroup.mem_centralizer_iff.mp h c (by simp)
          refine ⟨x.2, ?_⟩
          apply Subgroup.mem_centralizer_iff.mpr
          intro z hz
          have hz' : z = (c : H) := by simpa using hz
          subst hz'
          simpa [Subgroup.coe_mul] using congrArg Subtype.val h'
        · intro h
          apply Subgroup.mem_centralizer_iff.mpr
          intro y hy
          have hy' : y = c := by simpa using hy
          subst y
          have hxca : (c : H) * (x : H) = (x : H) * (c : H) :=
            Subgroup.mem_centralizer_iff.mp h.2 c (by simp)
          apply Subtype.ext
          simpa [Subgroup.coe_mul] using hxca
      have hIndex : (Subgroup.centralizer ({(c : Ehat)} : Set Ehat)).index ≤ 3 := by
        rw [Subgroup.index_centralizer_eq_ncard]
        have hsub : conjugatesOf c ⊆
            (fun z : Z.subgroupOf Ehat => ((z : Ehat) * c)) '' Set.univ := by
          intro b hb
          rw [conjugatesOf, Set.mem_setOf_eq, isConj_iff] at hb
          obtain ⟨x, rfl⟩ := hb
          have hz : ⁅x, c⁆ ∈ Z.subgroupOf Ehat := hcommKer x x.2 c c.2
          exact ⟨⟨⁅x, c⁆, hz⟩, Set.mem_univ _, by
            exact (conj_eq_commutatorElement_mul (g₁ := x) (g₂ := c)).symm⟩
        calc (conjugatesOf c).ncard ≤
              ((fun z : Z.subgroupOf Ehat => ((z : Ehat) * c)) '' Set.univ).ncard :=
                Set.ncard_le_ncard hsub
          _ ≤ (Set.univ : Set (Z.subgroupOf Ehat)).ncard := Set.ncard_image_le
          _ = Nat.card (Z.subgroupOf Ehat) := by simp
          _ = 3 := hZhatcard
      rw [hcentE] at hIndex
      have hconv : (Ehat ⊓ Cc).relIndex Ehat = ((Ehat ⊓ Cc).subgroupOf Ehat).index := rfl
      rw [hconv]
      exact hIndex
    have hRrel : R.relIndex Ehat ≤ 9 := by
      rw [hR_eq]
      calc ((Ehat ⊓ Ca) ⊓ (Ehat ⊓ Cc)).relIndex Ehat
          ≤ (Ehat ⊓ Ca).relIndex Ehat * (Ehat ⊓ Cc).relIndex Ehat :=
            Subgroup.relIndex_inf_le (H := Ehat ⊓ Ca) (K := Ehat ⊓ Cc) (L := Ehat)
        _ ≤ 3 * 3 := Nat.mul_le_mul hrel_a hrel_c
        _ = 9 := by norm_num
    have hRm : R.relIndex Ehat * Nat.card R = Nat.card Ehat := by
      have h := Subgroup.relIndex_mul_card (H := R) (K := Ehat)
      rwa [inf_eq_left.mpr hRle] at h
    have hprod : R.relIndex Ehat * Nat.card R ≤ 9 * 9 :=
      Nat.mul_le_mul hRrel hR9
    rw [hRm, hEhatcard] at hprod
    norm_num at hprod

theorem card_le_of_isElemAbelian [Finite K] (hK : Nat.card K = 4)
    {E : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 4 := by
  classical
  by_contra hlt
  push Not at hlt
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 (x : _) x.2)⟩
  obtain ⟨F, hFcard⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card (G := ↥E) (n := 4)
    Nat.prime_three hEp hlt.le
  have hFE : F.map E.subtype ≤ E := Subgroup.map_subtype_le F
  have hF : IsElemAbelian 3 (F.map E.subtype) := by
    refine ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, fun y hy => hE.2 y (hFE hy)⟩
    have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨u, hFE u.2⟩ ⟨v, hFE v.2⟩)
    exact h
  have hFcard' : Nat.card (F.map E.subtype) = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective E.subtype_injective, hFcard]
  obtain ⟨g, hg⟩ := exists_conj_eq_torU hK hF hFcard'
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ torU K := by
    rw [← centralizer_torU hK]
    rintro _ ⟨u, hu, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [← hg] at ht
    obtain ⟨_, ⟨v, -, rfl⟩, rfl⟩ := ht
    have hcomm : (v : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * u =
        u * (v : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
      congrArg Subtype.val (hE.1.is_comm.comm v ⟨u, hu⟩)
    simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype, MulAut.conj_apply]
    rw [show g * ↑v * g⁻¹ * (g * u * g⁻¹) = g * (↑v * u) * g⁻¹ by group, hcomm]
    group
  have hcard := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_torU hK] at hcard
  omega

end CFSG.StandardType.USixTwo

end
