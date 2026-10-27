module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18U54InvRankData
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.U54InvRank

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.KGroups
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.U5K.Hyp
open CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.F431.Un CFSG.Quasithin.H13.Sec53F.Unit
open CFSG.Blueprint (LieModel)

@[expose] def eprod5 {M : Type*} [Group M] (e : Fin 3 → M) (c : Fin 3 → ZMod 5) : M :=
  e 0 ^ (c 0).val * e 1 ^ (c 1).val * e 2 ^ (c 2).val

theorem pow_add_zmod5 {M : Type*} [Group M] (x : M) (hx : x ^ 5 = 1) (a b : ZMod 5) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  have hord : orderOf x ∣ 5 := orderOf_dvd_of_pow_eq_one hx
  have hmod : a.val + b.val ≡ (a + b).val [MOD 5] := by
    rw [ZMod.val_add]
    exact (Nat.mod_modEq (a.val + b.val) 5).symm
  rw [← pow_add, pow_eq_pow_iff_modEq.mpr (Nat.ModEq.of_dvd hord hmod.symm)]

theorem eprod5_add {M : Type*} [Group M] (e : Fin 3 → M)
    (hcomm : ∀ i j, e i * e j = e j * e i) (h5 : ∀ i, e i ^ 5 = 1) (c c' : Fin 3 → ZMod 5) :
    eprod5 e (c + c') = eprod5 e c * eprod5 e c' := by
  unfold eprod5
  simp only [Pi.add_apply]
  rw [pow_add_zmod5 (e 0) (h5 0), pow_add_zmod5 (e 1) (h5 1), pow_add_zmod5 (e 2) (h5 2)]
  have hpc : ∀ i j, e i ^ (c i).val * e j ^ (c' j).val = e j ^ (c' j).val * e i ^ (c i).val :=
    fun i j => ((show Commute (e i) (e j) from hcomm i j).pow_left (c i).val).pow_right (c' j).val
  grind

@[expose] def eprod5Hom {M : Type*} [Group M] (e : Fin 3 → M)
    (hcomm : ∀ i j, e i * e j = e j * e i) (h5 : ∀ i, e i ^ 5 = 1) :
    Multiplicative (Fin 3 → ZMod 5) →* M where
  toFun c := eprod5 e (Multiplicative.toAdd c)
  map_one' := by simp [eprod5]
  map_mul' c c' := eprod5_add e hcomm h5 _ _

theorem eprod5_single {M : Type*} [Group M] (e : Fin 3 → M) (j : Fin 3) :
    eprod5 e (Pi.single j 1) = e j := by
  have hv1 : (1 : ZMod 5).val = 1 := rfl
  fin_cases j <;> simp [eprod5, Pi.single_apply, hv1]

theorem amap_add (i : Fin 4) (c c' : Fin 3 → ZMod 5) :
    Amap i (c + c') = Amap i c + Amap i c' := by
  funext j
  fin_cases i <;> fin_cases j <;> simp [Amap] <;> ring

theorem amap_nsmul (i : Fin 4) (n : ℕ) (c : Fin 3 → ZMod 5) :
    Amap i (n • c) = n • Amap i c := by
  funext j
  fin_cases i <;> fin_cases j <;> simp [Amap, nsmul_eq_mul] <;> ring

theorem decomp5 (c : Fin 3 → ZMod 5) :
    c = (c 0).val • Pi.single 0 1 + (c 1).val • Pi.single 1 1 + (c 2).val • Pi.single 2 1 := by
  funext j
  fin_cases j <;> simp [Pi.single_apply, nsmul_eq_mul, -ZMod.natCast_val, ZMod.natCast_zmod_val]

theorem conj_eq_of_single {M : Type*} [Group M] (φ : Multiplicative (Fin 3 → ZMod 5) →* M)
    (x : M) (i : Fin 4)
    (hx : ∀ j, x * φ (.ofAdd (Pi.single j 1)) * x⁻¹ = φ (.ofAdd (Amap i (Pi.single j 1))))
    (c : Fin 3 → ZMod 5) : x * φ (.ofAdd c) * x⁻¹ = φ (.ofAdd (Amap i c)) := by
  have h1 : ∀ v : Fin 3 → ZMod 5, x * φ (.ofAdd v) * x⁻¹ = MulAut.conj x (φ (.ofAdd v)) :=
    fun v => rfl
  rw [h1, decomp5 c]
  simp only [ofAdd_add, ofAdd_nsmul, map_mul, map_pow, amap_add, amap_nsmul]
  rw [← h1, ← h1, ← h1, hx, hx, hx]

section Transport

variable {K : Type} [Field K] (h : UnitaryFieldData 2 2 K) (ψ : K ≃+* GF16)

@[expose] noncomputable def tr16 :
    Matrix (HypIndex 2 1) (HypIndex 2 1) GF16 ≃+* Matrix (HypIndex 2 1) (HypIndex 2 1) K :=
  RingEquiv.mapMatrix ψ.symm

theorem tr16_apply (M : Matrix (HypIndex 2 1) (HypIndex 2 1) GF16) (a b : HypIndex 2 1) :
    tr16 ψ M a b = ψ.symm (M a b) := rfl

theorem tr16_transpose (M : Matrix (HypIndex 2 1) (HypIndex 2 1) GF16) :
    tr16 ψ Mᵀ = (tr16 ψ M)ᵀ := rfl

theorem tr16_bar (M : Matrix (HypIndex 2 1) (HypIndex 2 1) GF16) :
    (tr16 ψ M).map h.bar = tr16 ψ (M.map bar16) := by
  ext a b
  simp [tr16_apply, h.bar_apply, bar16, map_pow]

theorem tr16_gram : tr16 ψ (hypGram 2 1 GF16) = hypGram 2 1 K := by
  ext a b
  rw [tr16_apply, hypGram_apply, hypGram_apply]
  split_ifs <;> simp

theorem tr16_det (M : Matrix (HypIndex 2 1) (HypIndex 2 1) GF16) :
    (tr16 ψ M).det = ψ.symm M.det :=
  (RingHom.map_det (ψ.symm : GF16 →+* K) M).symm

theorem tr16_scalar (c : GF16) :
    tr16 ψ (Matrix.scalar (HypIndex 2 1) c) = Matrix.scalar (HypIndex 2 1) (ψ.symm c) := by
  ext a b
  by_cases hab : a = b
  · subst hab; simp [tr16_apply]
  · simp [tr16_apply, Matrix.scalar_apply, Matrix.diagonal, hab]

theorem tr16_single (a b : HypIndex 2 1) :
    tr16 ψ (Matrix.single a b 1) = Matrix.single a b (1 : K) := by
  ext x y
  simp [tr16_apply, Matrix.single_apply]

@[expose] noncomputable def su16 (M : Matrix (HypIndex 2 1) (HypIndex 2 1) GF16)
    (hu : (M.map bar16)ᵀ * hypGram 2 1 GF16 * M = hypGram 2 1 GF16) (hd : M.det = 1) :
    hypSU h 2 1 :=
  mkHypSU h (tr16 ψ M)
    (by rw [tr16_bar, ← tr16_transpose, ← tr16_gram ψ, ← map_mul, ← map_mul, hu])
    (by rw [tr16_det, hd, map_one])

theorem mat_su16 (M : Matrix (HypIndex 2 1) (HypIndex 2 1) GF16)
    (hu : (M.map bar16)ᵀ * hypGram 2 1 GF16 * M = hypGram 2 1 GF16) (hd : M.det = 1) :
    mat (su16 h ψ M hu hd) = tr16 ψ M := rfl

theorem mat_pow' (x : hypSU h 2 1) (n : ℕ) : mat (x ^ n) = mat x ^ n := by
  simp [mat, Subgroup.coe_pow, Units.val_pow_eq_pow_val]

end Transport

theorem exists_torusPackage_hyp {K : Type} [Field K] (h : UnitaryFieldData 2 2 K) :
    ∃ (φ : Multiplicative (Fin 3 → ZMod 5) →* hypPSU h 2 1) (g : Fin 4 → hypPSU h 2 1),
      (∀ i c, g i * φ (.ofAdd c) * (g i)⁻¹ = φ (.ofAdd (Amap i c))) ∧ φ (.ofAdd cS) ≠ 1 ∧
      ∀ l : hypPSU h 2 1, orderOf l = 2 → ∃ x : hypPSU h 2 1,
        l * (x * φ (.ofAdd cS) * x⁻¹) * l⁻¹ = (x * φ (.ofAdd cS) * x⁻¹)⁻¹ := by
  classical
  haveI : Finite K := h.finite
  letI : Fintype K := Fintype.ofFinite K
  have hK16 : Fintype.card K = 16 := by
    rw [Fintype.card_eq_nat_card, h.card]
    norm_num
  have hG16 : Fintype.card GF16 = 16 := by decide +kernel
  let ψ : K ≃+* GF16 := FiniteField.ringEquivOfCardEq (hK16.trans hG16.symm)
  let dSU : Fin 3 → hypSU h 2 1 := fun j => su16 h ψ (D16 j) (D16_unitary j) (D16_det j)
  let gSU : Fin 4 → hypSU h 2 1 := fun i => su16 h ψ (G16 i) (G16_unitary i) (G16_det i)
  let d : Fin 3 → hypPSU h 2 1 := fun j => hypProj h 2 1 (dSU j)
  let g : Fin 4 → hypPSU h 2 1 := fun i => hypProj h 2 1 (gSU i)
  have hmatd : ∀ j, mat (dSU j) = tr16 ψ (D16 j) := fun j => rfl
  have hmatg : ∀ i, mat (gSU i) = tr16 ψ (G16 i) := fun i => rfl
  have hdcommSU : ∀ j j', dSU j * dSU j' = dSU j' * dSU j := fun j j' =>
    mat_injective (by rw [mat_mul, mat_mul, hmatd, hmatd, ← map_mul, ← map_mul, D16_comm])
  have hd5SU : ∀ j, dSU j ^ 5 = 1 := fun j =>
    mat_injective (by rw [mat_pow', hmatd, ← map_pow, D16_pow_five, map_one, mat_one])
  have hgg : ∀ i, gSU i * gSU i = 1 := fun i =>
    mat_injective (by rw [mat_mul, hmatg, ← map_mul, G16_mul_self, map_one, mat_one])
  have hdcomm : ∀ j j', d j * d j' = d j' * d j := fun j j' => by
    simp only [d, ← map_mul, hdcommSU]
  have hd5 : ∀ j, d j ^ 5 = 1 := fun j => by
    simp only [d, ← map_pow, hd5SU, map_one]
  let φ := eprod5Hom d hdcomm hd5
  have hφapp : ∀ c, φ (.ofAdd c) = hypProj h 2 1 (eprod5 dSU c) := fun c => by
    simp [φ, eprod5Hom, eprod5, d, map_mul, map_pow]
  have hmat_eprod : ∀ c, mat (eprod5 dSU c) = tr16 ψ (Dprod16 c) := fun c => by
    simp only [eprod5, mat_mul, mat_pow', hmatd, Dprod16, map_mul, map_pow]
  have hscal : ∀ i, ∃ z ∈ hypScalars h 2 1,
      mat z = Matrix.scalar (HypIndex 2 1) (ψ.symm (mu16 i)) := by
    intro i
    have hne : ψ.symm (mu16 i) ≠ 0 := by
      intro h0
      have := congrArg ψ h0
      rw [RingEquiv.apply_symm_apply, map_zero] at this
      exact mu16_ne_zero i this
    let c : Kˣ := Units.mk0 _ hne
    refine ⟨su16 h ψ (Matrix.scalar _ (mu16 i)) (scal16_unitary i) (scal16_det i), ?_,
      by rw [mat_su16, tr16_scalar]⟩
    rw [mem_normOneScalars]
    refine ⟨c, ?_, ?_, ?_⟩
    · apply ψ.injective
      change ψ ((c : K) * h.bar (c : K)) = ψ 1
      rw [map_mul, map_one, h.bar_apply, map_pow]
      simp only [c, Units.val_mk0, RingEquiv.apply_symm_apply]
      have := mu16_norm i
      rw [bar16] at this
      simpa using this
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      apply ψ.injective
      rw [map_pow, map_one]
      simp only [c, Units.val_mk0, RingEquiv.apply_symm_apply]
      exact mu16_pow_five i
    · apply Units.ext
      change tr16 ψ (Matrix.scalar _ (mu16 i)) = _
      rw [tr16_scalar, Matrix.GeneralLinearGroup.coe_scalar]
      rfl
  have hginv : ∀ i, (g i)⁻¹ = g i := fun i =>
    inv_eq_of_mul_eq_one_right (by simp only [g, ← map_mul, hgg, map_one])
  have hgen : ∀ i j, g i * φ (.ofAdd (Pi.single j 1)) * (g i)⁻¹ =
      φ (.ofAdd (Amap i (Pi.single j 1))) := by
    intro i j
    obtain ⟨z, hz, hzmat⟩ := hscal i
    have hSU : gSU i * dSU j * gSU i = z * eprod5 dSU (Amap i (Pi.single j 1)) :=
      mat_injective (by
        rw [mat_mul, mat_mul, mat_mul, hmatg, hmatd, hzmat, hmat_eprod, ← map_mul, ← map_mul,
          G16_conj, map_mul, tr16_scalar])
    have hz1 : hypProj h 2 1 z = 1 := by
      rw [← MonoidHom.mem_ker, ker_hypProj]
      exact hz
    rw [hginv, hφapp, hφapp, eprod5_single]
    show hypProj h 2 1 (gSU i) * hypProj h 2 1 (dSU j) * hypProj h 2 1 (gSU i) = _
    rw [← map_mul, ← map_mul, hSU, map_mul, hz1, one_mul]
  have hrel : ∀ i c, g i * φ (.ofAdd c) * (g i)⁻¹ = φ (.ofAdd (Amap i c)) := fun i c =>
    conj_eq_of_single φ (g i) i (hgen i) c
  have hs1 : φ (.ofAdd cS) ≠ 1 := by
    rw [hφapp]
    intro h1
    have hmem : eprod5 dSU cS ∈ hypScalars h 2 1 := by
      rw [← ker_hypProj, MonoidHom.mem_ker]
      exact h1
    obtain ⟨c', -, -, hc'⟩ := (mem_normOneScalars (h := h) (H := hypSU h 2 1)
      (m := 2 * 2 + 1)).mp hmem
    have h2 : mat (eprod5 dSU cS) = Matrix.scalar (HypIndex 2 1) (c' : K) := by
      rw [show mat (eprod5 dSU cS) = (((eprod5 dSU cS : hypSU h 2 1) : GL (HypIndex 2 1) K) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) K) from rfl, hc',
        Matrix.GeneralLinearGroup.coe_scalar]
    have h3 := congrFun (congrFun h2 (.inl 0)) (.inr (.inr 0))
    rw [hmat_eprod, tr16_apply] at h3
    simp [Matrix.scalar_apply, Matrix.diagonal] at h3
    exact Dprod16_cS_entry h3
  have hz5 : g 0 = z5Y h := by
    show hypProj h 2 1 (gSU 0) = hypProj h 2 1 (z₁SU h)
    congr 1
    apply mat_injective
    rw [hmatg, G16_zero, map_add, map_one, tr16_single, mat_z₁SU_eq]
  have hherm1 : IsHerm h (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) := by
    have := h.charP
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]
  have hw₂ : hypProj h 2 1 (vSU h !![1, 0; 0, 1] hherm1) = g 0 * g 3 := by
    show hypProj h 2 1 (vSU h !![1, 0; 0, 1] hherm1) =
      hypProj h 2 1 (gSU 0) * hypProj h 2 1 (gSU 3)
    rw [← map_mul]
    congr 1
    apply mat_injective
    rw [mat_mul, hmatg, hmatg, ← map_mul, G16_zero_mul_three, map_add, map_one, map_add,
      tr16_single, tr16_single, mat_vSU]
    ext a b
    rcases hypIndex_cases a with rfl | rfl | rfl | rfl | rfl <;>
      rcases hypIndex_cases b with rfl | rfl | rfl | rfl | rfl <;>
      simp [oddUni, ιe₁, ιe₂, ιz, ιf₁, ιf₂]
  have ht5 : IsConj (t5Y h) (g 0 * g 3) := by
    obtain ⟨A, hA, hconj⟩ := exists_lev_conj_of_det_ne_zero (h := h)
      (vSU_mem_Vsub (isHerm_swap h)) (vSU_mem_Vsub hherm1)
      (by rw [Yof_eq (mat_vSU (isHerm_swap h))]; simp [Matrix.det_fin_two])
      (by rw [Yof_eq (mat_vSU hherm1)]; simp [Matrix.det_fin_two])
    rw [isConj_iff]
    refine ⟨hypProj h 2 1 (lev (hK := h) A hA), ?_⟩
    rw [← hw₂, ← hconj, map_mul, map_mul, map_inv]
    rfl
  have hinvS : ∀ v : Fin 3 → ZMod 5, φ (.ofAdd (-v)) = (φ (.ofAdd v))⁻¹ := fun v => by
    rw [ofAdd_neg, map_inv]
  have hA0 : Amap 0 cS = -cS := by decide
  have hA30 : Amap 0 (Amap 3 cS) = -cS := by decide
  have hy0 : g 0 * φ (.ofAdd cS) * (g 0)⁻¹ = (φ (.ofAdd cS))⁻¹ := by
    rw [hrel, hA0, hinvS]
  have hy03 : (g 0 * g 3) * φ (.ofAdd cS) * (g 0 * g 3)⁻¹ = (φ (.ofAdd cS))⁻¹ := by
    rw [show (g 0 * g 3) * φ (.ofAdd cS) * (g 0 * g 3)⁻¹ =
      g 0 * (g 3 * φ (.ofAdd cS) * (g 3)⁻¹) * (g 0)⁻¹ by group, hrel, hrel, hA30, hinvS]
  have key : ∀ y : hypPSU h 2 1, y * φ (.ofAdd cS) * y⁻¹ = (φ (.ofAdd cS))⁻¹ →
      ∀ l, IsConj y l → ∃ x, l * (x * φ (.ofAdd cS) * x⁻¹) * l⁻¹ = (x * φ (.ofAdd cS) * x⁻¹)⁻¹ := by
    intro y hy l hl
    obtain ⟨c, rfl⟩ := isConj_iff.1 hl
    refine ⟨c, ?_⟩
    calc c * y * c⁻¹ * (c * φ (.ofAdd cS) * c⁻¹) * (c * y * c⁻¹)⁻¹ =
        c * (y * φ (.ofAdd cS) * y⁻¹) * c⁻¹ := by group
      _ = (c * φ (.ofAdd cS) * c⁻¹)⁻¹ := by rw [hy]; group
  refine ⟨φ, g, hrel, hs1, fun l hl => ?_⟩
  rcases cls_Y (h := h) (by norm_num) hl with hz | ht
  · exact key (g 0) hy0 l (hz5 ▸ hz)
  · exact key (g 0 * g 3) hy03 l (ht5.symm.trans ht)

theorem exists_hypPSU_equiv_of_lieModel {S : Type} [Group S]
    (hS : LieModel S .PSU 5 2 2) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 2 K),
      Nonempty (hypPSU h 2 1 ≃* S) := by
  rcases hS with ⟨-, hcl⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
  · obtain ⟨-, K, hfield, hfinite, hcard, ⟨e⟩⟩ := hcl
    letI := hfield
    letI := hfinite
    have h : UnitaryFieldData 2 2 K :=
      ⟨Nat.prime_two, by norm_num, by rw [hcard, ← pow_mul, mul_comm]⟩
    obtain ⟨R, hR⟩ := exists_isHypTransport (h := h) (r := 2) (ε := 1)
    let e₁ := hypPSUEquivStatedProj h hR (by norm_num : 1 ≤ 2 * 2 + 1)
    exact ⟨K, hfield, h, ⟨e₁.trans e.symm⟩⟩
  all_goals omega

theorem exists_torusPackage {S : Type} [Group S] (hS : LieModel S .PSU 5 2 2) :
    ∃ (φ : Multiplicative (Fin 3 → ZMod 5) →* S) (g : Fin 4 → S),
      (∀ i c, g i * φ (.ofAdd c) * (g i)⁻¹ = φ (.ofAdd (Amap i c))) ∧ φ (.ofAdd cS) ≠ 1 ∧
      ∀ l : S, orderOf l = 2 → ∃ x : S,
        l * (x * φ (.ofAdd cS) * x⁻¹) * l⁻¹ = (x * φ (.ofAdd cS) * x⁻¹)⁻¹ := by
  obtain ⟨K, hfield, h, ⟨e⟩⟩ := exists_hypPSU_equiv_of_lieModel hS
  letI := hfield
  obtain ⟨φ, g, hrel, hs1, hinv⟩ := exists_torusPackage_hyp h
  refine ⟨e.toMonoidHom.comp φ, fun i => e (g i), fun i c => ?_, ?_, fun l hl => ?_⟩
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_inv, ← map_mul, hrel]
  · simpa using hs1
  · obtain ⟨x, hx⟩ := hinv (e.symm l) (by rw [MulEquiv.orderOf_eq]; exact hl)
    refine ⟨e x, ?_⟩
    have := congrArg e hx
    simpa [map_mul, map_inv] using this

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.U54InvRank
