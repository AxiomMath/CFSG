module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34ParAut
public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverMatrices
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.Ch9.L34T

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter

variable {k : Type} [Field k]

theorem map_conjAut_diagGL [Finite k] (x : kˣ) :
    (projUnitriangular 3 k).map (LinearFlag.conjAut 3 k (diagGL x)).toMonoidHom =
      projUnitriangular 3 k := by
  refine Subgroup.eq_of_le_of_card_ge ?_ (Subgroup.card_map_of_injective (MulEquiv.injective _)).ge
  rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  refine ⟨CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k (diagGL x) u,
    ⟨fun i j hij => ?_, fun i => ?_⟩, (conjAut_proj _ _).symm⟩
  · rw [coe_slConjugation, coe_diagGL, coe_diagGL_inv, mul_diagonal, diagonal_mul, hu.1 i j hij]
    simp
  · rw [coe_slConjugation, coe_diagGL, coe_diagGL_inv, mul_diagonal, diagonal_mul, hu.2 i]
    fin_cases i <;> simp

theorem isUpperTriangular_of_map_conjAut (hk : Nat.card k = 4) {A : GL (Fin 3) k}
    (hA : (projUnitriangular 3 k).map (LinearFlag.conjAut 3 k A).toMonoidHom =
      projUnitriangular 3 k) :
    (A : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : GL (Fin 3) k := diagGL (GeneralLinearGroup.det A) with hD
  set A' : GL (Fin 3) k := A * D⁻¹ with hA'
  have hdet : GeneralLinearGroup.det A' = 1 := by
    rw [hA', map_mul, map_inv, hD, det_diagGL, mul_inv_cancel]
  let g : Matrix.SpecialLinearGroup (Fin 3) k :=
    ⟨(A' : Matrix (Fin 3) (Fin 3) k), by
      rw [← GeneralLinearGroup.val_det_apply, hdet, Units.val_one]⟩
  have hg : LinearFlag.conjAut 3 k A' = MulAut.conj (proj 3 k g) := by
    rw [← conjAut_toGL]
    congr 1
    exact Units.ext rfl
  have hcA : LinearFlag.conjAut 3 k A = LinearFlag.conjAut 3 k A' * LinearFlag.conjAut 3 k D := by
    rw [← map_mul, hA', inv_mul_cancel_right]
  have h1 : (projUnitriangular 3 k).map (LinearFlag.conjAut 3 k A).toMonoidHom =
      ((projUnitriangular 3 k).map (LinearFlag.conjAut 3 k D).toMonoidHom).map
        (LinearFlag.conjAut 3 k A').toMonoidHom := by
    rw [hcA, Subgroup.map_map]
    rfl
  rw [hD, map_conjAut_diagGL, hA, hg] at h1
  have hgN : proj 3 k g ∈ Subgroup.normalizer (projUnitriangular 3 k : Set (projectiveSL 3 k)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1.symm
  rw [normalizer_projUnitriangular 2] at hgN
  obtain ⟨b, hb, hbg⟩ := hgN
  have hz : b⁻¹ * g ∈ scalars 3 k := by
    rw [← proj_eq_one_iff, map_mul, map_inv, hbg, inv_mul_cancel]
  have hgU : g ∈ upperTriangular 3 k := by
    have e : g = b * (b⁻¹ * g) := by group
    rw [e]
    exact mul_mem hb (scalars_le_upperTriangular 3 k hz)
  have hAeq : A = A' * D := by rw [hA', inv_mul_cancel_right]
  rw [hAeq, Units.val_mul, hD, coe_diagGL]
  exact Matrix.BlockTriangular.mul (mem_upperTriangular_iff_isUpperTriangular.mp hgU)
    (Matrix.blockTriangular_diagonal _)

theorem twist_w0GL (σ : k ≃+* k) (a b : ZMod 2) :
    twistF σ a (twistD b (KGL34P.w0GL : GL (Fin 3) k)) = KGL34P.w0GL := by
  have hD : twistD b (KGL34P.w0GL : GL (Fin 3) k) = KGL34P.w0GL := by
    rcases zmod_two_cases b with rfl | rfl
    · simp [twistD]
    · simp only [twistD, one_ne_zero, ite_false]
      refine Units.ext ?_
      rw [GeneralLinearGroup.coe_inverseTranspose]
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
  rw [hD]
  rcases zmod_two_cases a with rfl | rfl
  · simp [twistF]
  · simp only [twistF, one_ne_zero, ite_false]
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [KGL34P.w0GL, KGL34P.w0M]

theorem map_nf_w0 [Finite k] (σ : k ≃+* k) (a : ZMod 2) :
    (projUnitriangular 3 k).map (nf σ KGL34P.w0GL a 1).toMonoidHom = projUnitriangular 3 k := by
  refine KGL34P.map_projUnitriangular_eq fun x hx => ?_
  rcases zmod_two_cases a with rfl | rfl
  · have e : nf σ (KGL34P.w0GL : GL (Fin 3) k) 0 1 = nf (1 : k ≃+* k) KGL34P.w0GL 1 1 := by
      simp [nf, val_one_two]
    rw [e]
    exact KGL34P.alpha0_mem_projUnitriangular hx
  · exact KGL34P.alpha0_mem_projUnitriangular hx

theorem isUpperTriangular_inv {A : GL (Fin 3) k}
    (hA : (A : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular) :
    ((A⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular := by
  rw [Matrix.coe_units_inv]
  have := A.invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular hA

theorem conj_unipOne_matrix {M M' : Matrix (Fin 3) (Fin 3) k} (hMM' : M * M' = 1)
    (hM : M.IsUpperTriangular) (hM' : M'.IsUpperTriangular) (a c : k) :
    M * (FieldFourCover.unipU k a 0 c : Matrix (Fin 3) (Fin 3) k) * M' =
      (FieldFourCover.unipU k (M 0 0 * a * M' 1 1)
        0 ((M * (FieldFourCover.unipU k a 0 c : Matrix (Fin 3) (Fin 3) k) * M') 0 2) :
        Matrix (Fin 3) (Fin 3) k) := by
  have r : ∀ i j, (M * M') i j = (1 : Matrix (Fin 3) (Fin 3) k) i j := fun i j => by rw [hMM']
  have z10 : M 1 0 = 0 := hM (by decide)
  have z20 : M 2 0 = 0 := hM (by decide)
  have z21 : M 2 1 = 0 := hM (by decide)
  have z10' : M' 1 0 = 0 := hM' (by decide)
  have z20' : M' 2 0 = 0 := hM' (by decide)
  have z21' : M' 2 1 = 0 := hM' (by decide)
  have e00 : M 0 0 * M' 0 0 = 1 := by
    have h := r 0 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three, z10', z20'] using h
  have e11 : M 1 1 * M' 1 1 = 1 := by
    have h := r 1 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, z10, z21'] using h
  have e22 : M 2 2 * M' 2 2 = 1 := by
    have h := r 2 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three, z20, z21] using h
  have e01 : M 0 0 * M' 0 1 + M 0 1 * M' 1 1 = 0 := by
    have h := r 0 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, z21'] using h
  have e12 : M 1 1 * M' 1 2 + M 1 2 * M' 2 2 = 0 := by
    have h := r 1 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three, z10] using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, FieldFourCover.coe_unipU, z10, z20, z21, z10', z20',
      z21']
  all_goals first | exact e00 | exact e11 | exact e22 | exact e12 | linear_combination e01

theorem slConj_mem_unipOne {A : GL (Fin 3) k}
    (hA : (A : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular) {g : SpecialLinearGroup (Fin 3) k}
    (hg : g ∈ FieldFourCover.unipOne k) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k A g ∈
      FieldFourCover.unipOne k := by
  obtain ⟨a, c, rfl⟩ := hg
  have hMM' : (A : Matrix (Fin 3) (Fin 3) k) * ((A⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨(A : Matrix (Fin 3) (Fin 3) k) 0 0 * a *
      ((A⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 1 1,
    ((A : Matrix (Fin 3) (Fin 3) k) * (FieldFourCover.unipU k a 0 c : Matrix (Fin 3) (Fin 3) k) *
      ((A⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 0 2, ?_⟩
  apply Subtype.ext
  rw [coe_slConjugation]
  exact (conj_unipOne_matrix hMM' hA (isUpperTriangular_inv hA) a c).symm

theorem conj_unipTwo_matrix {M M' : Matrix (Fin 3) (Fin 3) k} (hMM' : M * M' = 1)
    (hM : M.IsUpperTriangular) (hM' : M'.IsUpperTriangular) (b c : k) :
    M * (FieldFourCover.unipU k 0 b c : Matrix (Fin 3) (Fin 3) k) * M' =
      (FieldFourCover.unipU k 0 (M 1 1 * b * M' 2 2)
        ((M * (FieldFourCover.unipU k 0 b c : Matrix (Fin 3) (Fin 3) k) * M') 0 2) :
        Matrix (Fin 3) (Fin 3) k) := by
  have r : ∀ i j, (M * M') i j = (1 : Matrix (Fin 3) (Fin 3) k) i j := fun i j => by rw [hMM']
  have z10 : M 1 0 = 0 := hM (by decide)
  have z20 : M 2 0 = 0 := hM (by decide)
  have z21 : M 2 1 = 0 := hM (by decide)
  have z10' : M' 1 0 = 0 := hM' (by decide)
  have z20' : M' 2 0 = 0 := hM' (by decide)
  have z21' : M' 2 1 = 0 := hM' (by decide)
  have e00 : M 0 0 * M' 0 0 = 1 := by
    have h := r 0 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three, z10', z20'] using h
  have e11 : M 1 1 * M' 1 1 = 1 := by
    have h := r 1 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, z10, z21'] using h
  have e22 : M 2 2 * M' 2 2 = 1 := by
    have h := r 2 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three, z20, z21] using h
  have e01 : M 0 0 * M' 0 1 + M 0 1 * M' 1 1 = 0 := by
    have h := r 0 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, z21'] using h
  have e12 : M 1 1 * M' 1 2 + M 1 2 * M' 2 2 = 0 := by
    have h := r 1 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three, z10] using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, FieldFourCover.coe_unipU, z10, z20, z21, z10', z20',
      z21']
  all_goals first | exact e00 | exact e11 | exact e22 | exact e01 | linear_combination e12

theorem slConj_mem_unipTwo {A : GL (Fin 3) k}
    (hA : (A : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular) {g : SpecialLinearGroup (Fin 3) k}
    (hg : g ∈ FieldFourCover.unipTwo k) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k A g ∈
      FieldFourCover.unipTwo k := by
  obtain ⟨b, c, rfl⟩ := hg
  have hMM' : (A : Matrix (Fin 3) (Fin 3) k) * ((A⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨(A : Matrix (Fin 3) (Fin 3) k) 1 1 * b *
      ((A⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 2 2,
    ((A : Matrix (Fin 3) (Fin 3) k) * (FieldFourCover.unipU k 0 b c : Matrix (Fin 3) (Fin 3) k) *
      ((A⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 0 2, ?_⟩
  apply Subtype.ext
  rw [coe_slConjugation]
  exact (conj_unipTwo_matrix hMM' hA (isUpperTriangular_inv hA) b c).symm

theorem map_unipU (ρ : k ≃+* k) (a b c : k) :
    Matrix.SpecialLinearGroup.map ρ.toRingHom (FieldFourCover.unipU k a b c) =
      FieldFourCover.unipU k (ρ a) (ρ b) (ρ c) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [FieldFourCover.coe_unipU]

theorem map_projRad_conjAut [Finite k] {A : GL (Fin 3) k}
    (hA : (A : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular) (i : Fin 2) :
    (FieldFourCover.projRad k i).map (LinearFlag.conjAut 3 k A).toMonoidHom =
      FieldFourCover.projRad k i := by
  refine Subgroup.eq_of_le_of_card_ge ?_ (Subgroup.card_map_of_injective (MulEquiv.injective _)).ge
  rintro _ ⟨y, hy, rfl⟩
  fin_cases i
  · obtain ⟨a, c, rfl⟩ := FieldFourCover.mem_projRad_zero.mp hy
    obtain ⟨a', c', he⟩ := slConj_mem_unipOne hA ⟨a, c, rfl⟩
    refine FieldFourCover.mem_projRad_zero.mpr ⟨a', c', ?_⟩
    show _ = LinearFlag.conjAut 3 k A _
    rw [conjAut_proj, he]
  · obtain ⟨b, c, rfl⟩ := FieldFourCover.mem_projRad_one.mp hy
    obtain ⟨b', c', he⟩ := slConj_mem_unipTwo hA ⟨b, c, rfl⟩
    refine FieldFourCover.mem_projRad_one.mpr ⟨b', c', ?_⟩
    show _ = LinearFlag.conjAut 3 k A _
    rw [conjAut_proj, he]

theorem map_projRad_fieldAut [Finite k] (ρ : k ≃+* k) (i : Fin 2) :
    (FieldFourCover.projRad k i).map (LinearFlag.fieldAut 3 k ρ).toMonoidHom =
      FieldFourCover.projRad k i := by
  refine Subgroup.eq_of_le_of_card_ge ?_ (Subgroup.card_map_of_injective (MulEquiv.injective _)).ge
  rintro _ ⟨y, hy, rfl⟩
  fin_cases i
  · obtain ⟨a, c, rfl⟩ := FieldFourCover.mem_projRad_zero.mp hy
    refine FieldFourCover.mem_projRad_zero.mpr ⟨ρ a, ρ c, ?_⟩
    show _ = LinearFlag.fieldAut 3 k ρ _
    rw [fieldAut_proj, map_unipU, map_zero]
  · obtain ⟨b, c, rfl⟩ := FieldFourCover.mem_projRad_one.mp hy
    refine FieldFourCover.mem_projRad_one.mpr ⟨ρ b, ρ c, ?_⟩
    show _ = LinearFlag.fieldAut 3 k ρ _
    rw [fieldAut_proj, map_unipU, map_zero]

theorem map_mul_aut {X : Type} [Group X] (a b : MulAut X) (R : Subgroup X) :
    R.map (a * b).toMonoidHom = (R.map b.toMonoidHom).map a.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem isUpperTriangular_of_map_nf_one (hk : Nat.card k = 4) {σ : k ≃+* k}
    (hσ : ∀ a, σ a = a ^ 2) {A : GL (Fin 3) k} {a : ZMod 2}
    (hA : (projUnitriangular 3 k).map (nf σ A a 1).toMonoidHom = projUnitriangular 3 k) :
    ((A * KGL34P.w0GL : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have hff := fieldAut_sigma_mul_self hσ hk
  have e : nf σ A a 1 * nf σ KGL34P.w0GL a 1 = LinearFlag.conjAut 3 k (A * KGL34P.w0GL) := by
    rw [nf_mul σ hff, twist_w0GL, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, nf_zero_zero]
  refine isUpperTriangular_of_map_conjAut hk ?_
  rw [← e, map_mul_aut, map_nf_w0, hA]

theorem map_projRad_nf_zero [Finite k] (σ : k ≃+* k) {A : GL (Fin 3) k}
    (hA : (A : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular) (a : ZMod 2) (i : Fin 2) :
    (FieldFourCover.projRad k i).map (nf σ A a 0).toMonoidHom = FieldFourCover.projRad k i := by
  have e : nf σ A a 0 = LinearFlag.conjAut 3 k A * LinearFlag.fieldAut 3 k (σ ^ a.val) := by
    simp [nf, map_pow]
  rw [e, map_mul_aut, map_projRad_fieldAut, map_projRad_conjAut hA]

theorem map_projRad_of_nf (hk : Nat.card k = 4) {σ : k ≃+* k}
    {A : GL (Fin 3) k} {a : ZMod 2}
    (hA : (projUnitriangular 3 k).map (nf σ A a 0).toMonoidHom = projUnitriangular 3 k)
    (i : Fin 2) :
    (FieldFourCover.projRad k i).map (nf σ A a 0).toMonoidHom = FieldFourCover.projRad k i := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have e : nf σ A a 0 = LinearFlag.conjAut 3 k A * LinearFlag.fieldAut 3 k (σ ^ a.val) := by
    simp [nf, map_pow]
  have hU : (projUnitriangular 3 k).map (LinearFlag.conjAut 3 k A).toMonoidHom =
      projUnitriangular 3 k := by
    have h1 : (projUnitriangular 3 k).map (LinearFlag.fieldAut 3 k (σ ^ a.val)).toMonoidHom =
        projUnitriangular 3 k := by
      refine KGL34P.map_projUnitriangular_eq fun x hx => ?_
      obtain ⟨u, hu, rfl⟩ := hx
      rw [fieldAut_proj]
      exact ⟨_, ⟨fun i j hij => by simp [hu.1 i j hij], fun i => by simp [hu.2 i]⟩, rfl⟩
    rw [e, map_mul_aut, h1] at hA
    exact hA
  exact map_projRad_nf_zero σ (isUpperTriangular_of_map_conjAut hk hU) a i

theorem exists_conjAut_of_pow (hk : Nat.card k = 4) {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)
    {e : MulAut (projectiveSL 3 k)} {n : ℕ} (hn : Odd n) (he : e ^ n = 1) :
    ∃ D : GL (Fin 3) k, e = LinearFlag.conjAut 3 k D := by
  obtain ⟨Ψ, hΨ⟩ := exists_outerHom hσ hk
  obtain ⟨⟨D, a, b⟩, rfl⟩ := exists_nf hσ hk e
  have h1 := congrArg (SemidirectProduct.rightHom.comp Ψ) he
  rw [map_pow, map_one, MonoidHom.comp_apply, hΨ, SemidirectProduct.rightHom_eq_right] at h1
  have h2 : ∀ x : ZMod 2, (Multiplicative.ofAdd x) ^ n = 1 → x = 0 := by
    intro x hx
    rw [← ofAdd_nsmul, ofAdd_eq_one] at hx
    rcases zmod_two_cases x with rfl | rfl
    · rfl
    · exfalso
      rw [nsmul_eq_mul, mul_one, ZMod.natCast_eq_zero_iff_even] at hx
      exact (Nat.not_even_iff_odd.mpr hn) hx
  have ha : a = 0 := h2 a (congrArg Prod.fst h1)
  have hb : b = 0 := h2 b (congrArg Prod.snd h1)
  subst ha hb
  exact ⟨D, nf_zero_zero σ D⟩

theorem exists_pow_conjAut_eq_one [Finite k] [CharP k 2] {D : GL (Fin 3) k}
    (hD : (D : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular)
    (h0 : (D : Matrix (Fin 3) (Fin 3) k) 0 0 = (D : Matrix (Fin 3) (Fin 3) k) 2 2)
    (h1 : (D : Matrix (Fin 3) (Fin 3) k) 1 1 = (D : Matrix (Fin 3) (Fin 3) k) 2 2) :
    ∃ m : ℕ, LinearFlag.conjAut 3 k D ^ 2 ^ m = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c := (D : Matrix (Fin 3) (Fin 3) k) 2 2 with hcdef
  have hdet : Matrix.det (D : Matrix (Fin 3) (Fin 3) k) = c ^ 3 := by
    rw [Matrix.det_of_isUpperTriangular hD, Fin.prod_univ_three, h0, h1]
    ring
  have hc : c ≠ 0 := by
    intro h
    have hu := (GeneralLinearGroup.det D).ne_zero
    rw [GeneralLinearGroup.val_det_apply, hdet, h] at hu
    simp at hu
  let s : Matrix.SpecialLinearGroup (Fin 3) k :=
    ⟨c⁻¹ • (D : Matrix (Fin 3) (Fin 3) k), by
      rw [Matrix.det_smul, hdet, Fintype.card_fin]
      field_simp⟩
  have hs : s ∈ unitriangular 3 k := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · show (c⁻¹ • (D : Matrix (Fin 3) (Fin 3) k)) i j = 0
      rw [Matrix.smul_apply, hD hij, smul_zero]
    · show (c⁻¹ • (D : Matrix (Fin 3) (Fin 3) k)) i i = 1
      rw [Matrix.smul_apply, smul_eq_mul]
      fin_cases i
      · show c⁻¹ * (D : Matrix (Fin 3) (Fin 3) k) 0 0 = 1
        rw [h0, inv_mul_cancel₀ hc]
      · show c⁻¹ * (D : Matrix (Fin 3) (Fin 3) k) 1 1 = 1
        rw [h1, inv_mul_cancel₀ hc]
      · exact inv_mul_cancel₀ hc
  have hDs : D = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc) *
      Matrix.SpecialLinearGroup.toGL s := by
    refine Units.ext ?_
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar]
    show (D : Matrix (Fin 3) (Fin 3) k) =
      Matrix.scalar (Fin 3) c * (c⁻¹ • (D : Matrix (Fin 3) (Fin 3) k))
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := k) 2 (n := 3) (by norm_num)
  have hmem : proj 3 k s ∈ (P : Subgroup (projectiveSL 3 k)) := by
    rw [hP]
    exact ⟨s, hs, rfl⟩
  obtain ⟨m, hm⟩ := P.isPGroup' ⟨_, hmem⟩
  refine ⟨m, ?_⟩
  rw [hDs, map_mul, conjAut_scalar, one_mul, conjAut_toGL, ← map_pow]
  have hm' : proj 3 k s ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  rw [hm', map_one]

theorem conj_nf_one (hk : Nat.card k = 4) {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)
    (A D : GL (Fin 3) k) (a : ZMod 2) :
    nf σ A a 1 * LinearFlag.conjAut 3 k D * (nf σ A a 1)⁻¹ =
      LinearFlag.conjAut 3 k (A * twistF σ a (twistD 1 D) * A⁻¹) := by
  have hff := fieldAut_sigma_mul_self hσ hk
  rw [mul_inv_eq_iff_eq_mul, ← nf_zero_zero σ D, ← nf_zero_zero σ (A * _ * A⁻¹), nf_mul σ hff,
    nf_mul σ hff]
  simp [twistF, twistD]

theorem w0_twist_apply (σ : k ≃+* k) (a : ZMod 2) (D : GL (Fin 3) k) (i j : Fin 3) :
    ((KGL34P.w0GL * twistF σ a (twistD 1 D) * KGL34P.w0GL : GL (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k) i j =
      (σ ^ a.val) (((D⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) (Fin.rev j) (Fin.rev i)) := by
  rw [Units.val_mul, Units.val_mul]
  show ((KGL34P.w0M : Matrix (Fin 3) (Fin 3) k) *
    ((twistF σ a (twistD 1 D) : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
      (KGL34P.w0M : Matrix (Fin 3) (Fin 3) k)) i j = _
  rw [KGL34P.w0M_conj_apply]
  rcases zmod_two_cases a with rfl | rfl
  · simp [twistF, twistD, GeneralLinearGroup.coe_inverseTranspose]
  · simp only [twistF, twistD, one_ne_zero, ite_false, val_one_two, pow_one]
    show ((σ : k →+* k).mapMatrix ((GeneralLinearGroup.inverseTranspose D : GL (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k)) (Fin.rev i) (Fin.rev j) = σ _
    rw [GeneralLinearGroup.coe_inverseTranspose]
    rfl

theorem inv_apply_self_of_upper {D : GL (Fin 3) k}
    (hD : (D : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular) (i : Fin 3) :
    ((D⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i i =
      ((D : Matrix (Fin 3) (Fin 3) k) i i)⁻¹ := by
  have h := mul_apply_self_of_isUpperTriangular hD (isUpperTriangular_inv hD) i
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem conj_twist_diag (σ : k ≃+* k) (a : ZMod 2) {A D : GL (Fin 3) k}
    (hA : ((A * KGL34P.w0GL : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular)
    (hD : (D : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular) :
    ((A * twistF σ a (twistD 1 D) * A⁻¹ : GL (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k).IsUpperTriangular ∧
      ∀ i, ((A * twistF σ a (twistD 1 D) * A⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i i =
        (σ ^ a.val) (((D : Matrix (Fin 3) (Fin 3) k) (Fin.rev i) (Fin.rev i))⁻¹) := by
  set B : GL (Fin 3) k := A * KGL34P.w0GL with hB
  have hw : (KGL34P.w0GL : GL (Fin 3) k) * KGL34P.w0GL = 1 :=
    Units.ext KGL34P.w0M_mul_self
  have hAB : A * twistF σ a (twistD 1 D) * A⁻¹ =
      B * (KGL34P.w0GL * twistF σ a (twistD 1 D) * KGL34P.w0GL) * B⁻¹ := by
    have hw' : (KGL34P.w0GL : GL (Fin 3) k)⁻¹ = KGL34P.w0GL := inv_eq_of_mul_eq_one_right hw
    rw [hB, _root_.mul_inv_rev, hw']
    calc A * twistF σ a (twistD 1 D) * A⁻¹ =
        A * (KGL34P.w0GL * KGL34P.w0GL) * twistF σ a (twistD 1 D) *
          (KGL34P.w0GL * KGL34P.w0GL) * A⁻¹ := by rw [hw]; group
      _ = _ := by group
  have hY : ((KGL34P.w0GL * twistF σ a (twistD 1 D) * KGL34P.w0GL : GL (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k).IsUpperTriangular := by
    intro i j hij
    have h0 : ((D⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) (Fin.rev j) (Fin.rev i) = 0 :=
      isUpperTriangular_inv hD (Fin.rev_lt_rev.mpr hij)
    rw [w0_twist_apply, h0, map_zero]
  have hBi := isUpperTriangular_inv hA
  rw [hAB, Units.val_mul, Units.val_mul]
  refine ⟨(hA.mul hY).mul hBi, fun i => ?_⟩
  rw [mul_apply_self_of_isUpperTriangular (hA.mul hY) hBi,
    mul_apply_self_of_isUpperTriangular hA hY,
    w0_twist_apply, inv_apply_self_of_upper hD]
  have h1 := mul_apply_self_of_isUpperTriangular hA hBi i
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq] at h1
  calc (B : Matrix (Fin 3) (Fin 3) k) i i * (σ ^ a.val) (((D : Matrix (Fin 3) (Fin 3) k) (Fin.rev i)
        (Fin.rev i))⁻¹) * ((B⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i i =
      ((B : Matrix (Fin 3) (Fin 3) k) i i * ((B⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i i) *
        (σ ^ a.val) (((D : Matrix (Fin 3) (Fin 3) k) (Fin.rev i) (Fin.rev i))⁻¹) := by ring
    _ = _ := by rw [← h1, one_mul]



theorem conj_rows_eq {M M' H : Matrix (Fin 3) (Fin 3) k} (hMM' : M * M' = 1)
    (hM : M.IsUpperTriangular) (hM' : M'.IsUpperTriangular) (h12 : M 1 2 = 0)
    (h11 : M 1 1 = M 2 2) (hH10 : H 1 0 = 0) (hH20 : H 2 0 = 0) :
    ∀ j, (M * H * M') 1 j = H 1 j ∧ (M * H * M') 2 j = H 2 j ∧ (M * H * M') 0 0 = H 0 0 := by
  have r : ∀ i j, (M * M') i j = (1 : Matrix (Fin 3) (Fin 3) k) i j := fun i j => by rw [hMM']
  have z10 : M 1 0 = 0 := hM (by decide)
  have z20 : M 2 0 = 0 := hM (by decide)
  have z21 : M 2 1 = 0 := hM (by decide)
  have z10' : M' 1 0 = 0 := hM' (by decide)
  have z20' : M' 2 0 = 0 := hM' (by decide)
  have z21' : M' 2 1 = 0 := hM' (by decide)
  have e00 : M 0 0 * M' 0 0 = 1 := by
    have h := r 0 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three, z10', z20'] using h
  have e11 : M 1 1 * M' 1 1 = 1 := by
    have h := r 1 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, z10, z21'] using h
  have e22 : M 2 2 * M' 2 2 = 1 := by
    have h := r 2 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three, z20, z21] using h
  have e12 : M 1 1 * M' 1 2 + M 1 2 * M' 2 2 = 0 := by
    have h := r 1 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three, z10] using h
  have z12' : M' 1 2 = 0 := by
    rw [h12, zero_mul, add_zero] at e12
    rcases mul_eq_zero.mp e12 with h | h
    · rw [h, zero_mul] at e11
      exact absurd e11 zero_ne_one
    · exact h
  intro j
  refine ⟨?_, ?_, ?_⟩ <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, z10, z20, z21, z10', z20', z21', z12', h12, hH10,
      hH20]
  all_goals first
    | linear_combination (H 1 1) * e11
    | linear_combination (H 1 2 * M' 2 2) * h11 + (H 1 2) * e22
    | linear_combination -(H 2 1 * M' 1 1) * h11 + (H 2 1) * e11
    | linear_combination (H 2 2) * e22
    | linear_combination (H 0 0) * e00


theorem conj_mul_inv_matrix_zero {M M' H H' : Matrix (Fin 3) (Fin 3) k} (hMM' : M * M' = 1)
    (hM : M.IsUpperTriangular) (hM' : M'.IsUpperTriangular) (h12 : M 1 2 = 0)
    (h11 : M 1 1 = M 2 2) (hHH' : H * H' = 1) (hH'H : H' * H = 1) (hH10 : H 1 0 = 0)
    (hH20 : H 2 0 = 0) :
    M * H * M' * H' =
      !![1, (M * H * M' * H') 0 1, (M * H * M' * H') 0 2; 0, 1, 0; 0, 0, 1] := by
  have hrows := conj_rows_eq hMM' hM hM' h12 h11 hH10 hH20
  have r : ∀ i j, (H * H') i j = (1 : Matrix (Fin 3) (Fin 3) k) i j := fun i j => by rw [hHH']
  have r' : ∀ i j, (H' * H) i j = (1 : Matrix (Fin 3) (Fin 3) k) i j := fun i j => by rw [hH'H]
  have q00 : H' 0 0 * H 0 0 = 1 := by
    have h := r' 0 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three, hH10, hH20] using h
  have hH00 : H 0 0 ≠ 0 := fun h0 => by rw [h0, mul_zero] at q00; exact zero_ne_one q00
  have w10 : H' 1 0 = 0 := by
    have h := r' 1 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, hH10, hH20] at h
    exact h.resolve_right hH00
  have w20 : H' 2 0 = 0 := by
    have h := r' 2 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, hH10, hH20] at h
    exact h.resolve_right hH00
  set P := M * H * M' with hP
  have row1 : ∀ j, (P * H') 1 j = (H * H') 1 j := by
    intro j
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    rw [(hrows 0).1, (hrows 1).1, (hrows 2).1]
  have row2 : ∀ j, (P * H') 2 j = (H * H') 2 j := by
    intro j
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    rw [(hrows 0).2.1, (hrows 1).2.1, (hrows 2).2.1]
  ext i j
  fin_cases i <;> fin_cases j
  · show (P * H') 0 0 = 1
    simp only [Matrix.mul_apply, Fin.sum_univ_three, w10, w20, mul_zero, add_zero, (hrows 0).2.2]
    have h := r 0 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three, w10, w20] using h
  · rfl
  · rfl
  · show (P * H') 1 0 = 0
    rw [row1, r]
    rfl
  · show (P * H') 1 1 = 1
    rw [row1, r]
    rfl
  · show (P * H') 1 2 = 0
    rw [row1, r]
    rfl
  · show (P * H') 2 0 = 0
    rw [row2, r]
    rfl
  · show (P * H') 2 1 = 0
    rw [row2, r]
    rfl
  · show (P * H') 2 2 = 1
    rw [row2, r]
    rfl

theorem conj_cols_eq {M M' H : Matrix (Fin 3) (Fin 3) k} (hMM' : M * M' = 1)
    (hM : M.IsUpperTriangular) (hM' : M'.IsUpperTriangular) (h01 : M 0 1 = 0)
    (h00 : M 0 0 = M 1 1) (hH20 : H 2 0 = 0) (hH21 : H 2 1 = 0) :
    ∀ i, (M * H * M') i 0 = H i 0 ∧ (M * H * M') i 1 = H i 1 ∧ (M * H * M') 2 2 = H 2 2 := by
  have r : ∀ i j, (M * M') i j = (1 : Matrix (Fin 3) (Fin 3) k) i j := fun i j => by rw [hMM']
  have z10 : M 1 0 = 0 := hM (by decide)
  have z20 : M 2 0 = 0 := hM (by decide)
  have z21 : M 2 1 = 0 := hM (by decide)
  have z10' : M' 1 0 = 0 := hM' (by decide)
  have z20' : M' 2 0 = 0 := hM' (by decide)
  have z21' : M' 2 1 = 0 := hM' (by decide)
  have e00 : M 0 0 * M' 0 0 = 1 := by
    have h := r 0 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three, z10', z20'] using h
  have e11 : M 1 1 * M' 1 1 = 1 := by
    have h := r 1 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, z10, z21'] using h
  have e22 : M 2 2 * M' 2 2 = 1 := by
    have h := r 2 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three, z20, z21] using h
  have e01 : M 0 0 * M' 0 1 + M 0 1 * M' 1 1 = 0 := by
    have h := r 0 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, z21'] using h
  have z01' : M' 0 1 = 0 := by
    rw [h01, zero_mul, add_zero] at e01
    rcases mul_eq_zero.mp e01 with h | h
    · rw [h, zero_mul] at e00
      exact absurd e00 zero_ne_one
    · exact h
  intro i
  refine ⟨?_, ?_, ?_⟩ <;> fin_cases i <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, z10, z20, z21, z10', z20', z21', z01', h01, hH20,
      hH21]
  all_goals first
    | linear_combination (H 0 0) * e00
    | linear_combination (H 1 0 * M' 0 0) * (-h00) + (H 1 0) * e00
    | linear_combination (H 0 1 * M' 1 1) * h00 + (H 0 1) * e11
    | linear_combination (H 1 1) * e11
    | linear_combination (H 2 2) * e22

theorem inv_mul_conj_matrix_one {M M' H H' : Matrix (Fin 3) (Fin 3) k} (hMM' : M * M' = 1)
    (hM : M.IsUpperTriangular) (hM' : M'.IsUpperTriangular) (h01 : M 0 1 = 0)
    (h00 : M 0 0 = M 1 1) (hHH' : H * H' = 1) (hH'H : H' * H = 1) (hH20 : H 2 0 = 0)
    (hH21 : H 2 1 = 0) :
    H' * (M * H * M') =
      !![1, 0, (H' * (M * H * M')) 0 2; 0, 1, (H' * (M * H * M')) 1 2; 0, 0, 1] := by
  have hcols := conj_cols_eq hMM' hM hM' h01 h00 hH20 hH21
  have r : ∀ i j, (H * H') i j = (1 : Matrix (Fin 3) (Fin 3) k) i j := fun i j => by rw [hHH']
  have r' : ∀ i j, (H' * H) i j = (1 : Matrix (Fin 3) (Fin 3) k) i j := fun i j => by rw [hH'H]
  have q22 : H 2 2 * H' 2 2 = 1 := by
    have h := r 2 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three, hH20, hH21] using h
  have hH22 : H 2 2 ≠ 0 := fun h0 => by rw [h0, zero_mul] at q22; exact zero_ne_one q22
  have w20 : H' 2 0 = 0 := by
    have h := r 2 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, hH20, hH21] at h
    exact h.resolve_left hH22
  have w21 : H' 2 1 = 0 := by
    have h := r 2 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, hH20, hH21] at h
    exact h.resolve_left hH22
  set P := M * H * M' with hP
  have col0 : ∀ i, (H' * P) i 0 = (H' * H) i 0 := by
    intro i
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    rw [(hcols 0).1, (hcols 1).1, (hcols 2).1]
  have col1 : ∀ i, (H' * P) i 1 = (H' * H) i 1 := by
    intro i
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    rw [(hcols 0).2.1, (hcols 1).2.1, (hcols 2).2.1]
  ext i j
  fin_cases i <;> fin_cases j
  · show (H' * P) 0 0 = 1
    rw [col0, r']
    rfl
  · show (H' * P) 0 1 = 0
    rw [col1, r']
    rfl
  · rfl
  · show (H' * P) 1 0 = 0
    rw [col0, r']
    rfl
  · show (H' * P) 1 1 = 1
    rw [col1, r']
    rfl
  · rfl
  · show (H' * P) 2 0 = 0
    rw [col0, r']
    rfl
  · show (H' * P) 2 1 = 0
    rw [col1, r']
    rfl
  · show (H' * P) 2 2 = 1
    simp only [Matrix.mul_apply, Fin.sum_univ_three, w20, w21, zero_mul, zero_add, (hcols 0).2.2]
    have h := r' 2 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three, w20, w21] using h

theorem conjAut_mul_inv_mem_projRad_zero (hk : Nat.card k = 4) {D : GL (Fin 3) k}
    (hD : (D : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular)
    (h11 : (D : Matrix (Fin 3) (Fin 3) k) 1 1 = (D : Matrix (Fin 3) (Fin 3) k) 2 2)
    (h12 : (D : Matrix (Fin 3) (Fin 3) k) 1 2 = 0) {y : projectiveSL 3 k}
    (hy : y ∈ Subgroup.normalizer (FieldFourCover.projRad k 0 : Set (projectiveSL 3 k))) :
    LinearFlag.conjAut 3 k D y * y⁻¹ ∈ FieldFourCover.projRad k 0 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  obtain ⟨h, rfl⟩ := proj_surjective 3 k y
  obtain ⟨hH10, hH20⟩ :=
    FieldFourCover.col_zero_of_mem_normalizer (FieldFourCover.three_ne_zero_of_card hk) hy
  have hMM' : (D : Matrix (Fin 3) (Fin 3) k) * ((D⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hHH' : (h : Matrix (Fin 3) (Fin 3) k) * ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hH'H : ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
      (h : Matrix (Fin 3) (Fin 3) k) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have key := conj_mul_inv_matrix_zero hMM' hD (L34T.isUpperTriangular_inv hD) h12 h11 hHH' hH'H
    hH10 hH20
  rw [conjAut_proj, ← map_inv, ← map_mul]
  refine FieldFourCover.mem_projRad_zero.mpr ⟨((D : Matrix (Fin 3) (Fin 3) k) *
    (h : Matrix (Fin 3) (Fin 3) k) * ((D⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
      ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 0 1,
    ((D : Matrix (Fin 3) (Fin 3) k) * (h : Matrix (Fin 3) (Fin 3) k) *
      ((D⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
      ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 0 2, ?_⟩
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_slConjugation, FieldFourCover.coe_unipU]
  exact key.symm

theorem conjAut_mul_inv_mem_projRad_one (hk : Nat.card k = 4) {D : GL (Fin 3) k}
    (hD : (D : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular)
    (h00 : (D : Matrix (Fin 3) (Fin 3) k) 0 0 = (D : Matrix (Fin 3) (Fin 3) k) 1 1)
    (h01 : (D : Matrix (Fin 3) (Fin 3) k) 0 1 = 0) {y : projectiveSL 3 k}
    (hy : y ∈ Subgroup.normalizer (FieldFourCover.projRad k 1 : Set (projectiveSL 3 k))) :
    LinearFlag.conjAut 3 k D y * y⁻¹ ∈ FieldFourCover.projRad k 1 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have hy' := hy
  obtain ⟨h, rfl⟩ := proj_surjective 3 k y
  obtain ⟨hH20, hH21⟩ :=
    FieldFourCover.row_two_of_mem_normalizer (FieldFourCover.three_ne_zero_of_card hk) hy
  have hMM' : (D : Matrix (Fin 3) (Fin 3) k) * ((D⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hHH' : (h : Matrix (Fin 3) (Fin 3) k) * ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hH'H : ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
      (h : Matrix (Fin 3) (Fin 3) k) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have key := inv_mul_conj_matrix_one hMM' hD (L34T.isUpperTriangular_inv hD) h01 h00 hHH' hH'H
    hH20 hH21
  have hmem : (proj 3 k h)⁻¹ * LinearFlag.conjAut 3 k D (proj 3 k h) ∈
      FieldFourCover.projRad k 1 := by
    rw [conjAut_proj, ← map_inv, ← map_mul]
    refine FieldFourCover.mem_projRad_one.mpr ⟨(((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) * ((D : Matrix (Fin 3) (Fin 3) k) * (h : Matrix (Fin 3) (Fin 3) k) *
        ((D⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k))) 1 2,
      (((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
        ((D : Matrix (Fin 3) (Fin 3) k) * (h : Matrix (Fin 3) (Fin 3) k) *
          ((D⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k))) 0 2, ?_⟩
    congr 1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_slConjugation, FieldFourCover.coe_unipU]
    exact key.symm
  have e : LinearFlag.conjAut 3 k D (proj 3 k h) * (proj 3 k h)⁻¹ =
      proj 3 k h * ((proj 3 k h)⁻¹ * LinearFlag.conjAut 3 k D (proj 3 k h)) * (proj 3 k h)⁻¹ := by
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp hy' _).mp hmem

theorem cube_apply_one_two {D : Matrix (Fin 3) (Fin 3) k} (hD : D.IsUpperTriangular) :
    (D ^ 3) 1 2 = D 1 2 * (D 1 1 ^ 2 + D 1 1 * D 2 2 + D 2 2 ^ 2) := by
  have z10 : D 1 0 = 0 := hD (by decide)
  have z20 : D 2 0 = 0 := hD (by decide)
  have z21 : D 2 1 = 0 := hD (by decide)
  rw [pow_succ, pow_two]
  simp [Matrix.mul_apply, Fin.sum_univ_three, z10, z20, z21]
  ring

theorem cube_apply_zero_one {D : Matrix (Fin 3) (Fin 3) k} (hD : D.IsUpperTriangular) :
    (D ^ 3) 0 1 = D 0 1 * (D 0 0 ^ 2 + D 0 0 * D 1 1 + D 1 1 ^ 2) := by
  have z10 : D 1 0 = 0 := hD (by decide)
  have z20 : D 2 0 = 0 := hD (by decide)
  have z21 : D 2 1 = 0 := hD (by decide)
  rw [pow_succ, pow_two]
  simp [Matrix.mul_apply, Fin.sum_univ_three, z10, z20, z21]
  ring

theorem scalar_of_conjAut_pow_eq_one [Finite k] {D : GL (Fin 3) k}
    (h : LinearFlag.conjAut 3 k D ^ 3 = 1) :
    ∃ c : kˣ, GeneralLinearGroup.scalar (Fin 3) c = D ^ 3 := by
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (K := k) (n := 3) le_rfl (D ^ 3) 1
    (by rw [map_one, mul_one, map_pow, h])
  exact ⟨c, hc⟩

theorem apply_one_two_eq_zero [Finite k] [CharP k 2] {D : GL (Fin 3) k}
    (hD : (D : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular)
    (h11 : (D : Matrix (Fin 3) (Fin 3) k) 1 1 = (D : Matrix (Fin 3) (Fin 3) k) 2 2)
    (h3 : LinearFlag.conjAut 3 k D ^ 3 = 1) : (D : Matrix (Fin 3) (Fin 3) k) 1 2 = 0 := by
  obtain ⟨c, hc⟩ := scalar_of_conjAut_pow_eq_one h3
  have h1 := congrArg (fun X : GL (Fin 3) k => (X : Matrix (Fin 3) (Fin 3) k) 1 2) hc
  simp only [GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val] at h1
  rw [cube_apply_one_two hD, h11] at h1
  have hy : (D : Matrix (Fin 3) (Fin 3) k) 2 2 ≠ 0 := by
    intro h0
    have hdet := (GeneralLinearGroup.det D).ne_zero
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular hD, Fin.prod_univ_three,
      h0, mul_zero] at hdet
    exact hdet rfl
  have h2 : (D : Matrix (Fin 3) (Fin 3) k) 2 2 ^ 2 + (D : Matrix (Fin 3) (Fin 3) k) 2 2 *
      (D : Matrix (Fin 3) (Fin 3) k) 2 2 + (D : Matrix (Fin 3) (Fin 3) k) 2 2 ^ 2 =
      (D : Matrix (Fin 3) (Fin 3) k) 2 2 ^ 2 := by
    have h22 : (2 : k) = 0 := CharTwo.two_eq_zero
    linear_combination ((D : Matrix (Fin 3) (Fin 3) k) 2 2 ^ 2) * h22
  rw [h2, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide)] at h1
  exact (mul_eq_zero.mp h1.symm).resolve_right (pow_ne_zero 2 hy)

theorem apply_zero_one_eq_zero [Finite k] [CharP k 2] {D : GL (Fin 3) k}
    (hD : (D : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular)
    (h00 : (D : Matrix (Fin 3) (Fin 3) k) 0 0 = (D : Matrix (Fin 3) (Fin 3) k) 1 1)
    (h3 : LinearFlag.conjAut 3 k D ^ 3 = 1) : (D : Matrix (Fin 3) (Fin 3) k) 0 1 = 0 := by
  obtain ⟨c, hc⟩ := scalar_of_conjAut_pow_eq_one h3
  have h1 := congrArg (fun X : GL (Fin 3) k => (X : Matrix (Fin 3) (Fin 3) k) 0 1) hc
  simp only [GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val] at h1
  rw [cube_apply_zero_one hD, h00] at h1
  have hy : (D : Matrix (Fin 3) (Fin 3) k) 1 1 ≠ 0 := by
    intro h0
    have hdet := (GeneralLinearGroup.det D).ne_zero
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular hD, Fin.prod_univ_three,
      h0, mul_zero, zero_mul] at hdet
    exact hdet rfl
  have h2 : (D : Matrix (Fin 3) (Fin 3) k) 1 1 ^ 2 + (D : Matrix (Fin 3) (Fin 3) k) 1 1 *
      (D : Matrix (Fin 3) (Fin 3) k) 1 1 + (D : Matrix (Fin 3) (Fin 3) k) 1 1 ^ 2 =
      (D : Matrix (Fin 3) (Fin 3) k) 1 1 ^ 2 := by
    have h22 : (2 : k) = 0 := CharTwo.two_eq_zero
    linear_combination ((D : Matrix (Fin 3) (Fin 3) k) 1 1 ^ 2) * h22
  rw [h2, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide)] at h1
  exact (mul_eq_zero.mp h1.symm).resolve_right (pow_ne_zero 2 hy)

end CFSG.Quasithin.H13.Ch9.L34T
