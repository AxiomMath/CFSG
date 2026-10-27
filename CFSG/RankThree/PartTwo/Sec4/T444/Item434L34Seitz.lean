module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434L34
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434L34Words
import CFSG.RankThree.PartTwo.Sec4.Item413AutL3
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import all CFSG.Fischer.F4
import CFSG.RankThree.PartTwo.Sec4.Item413Cases
import CFSG.RankThree.PartTwo.Sec4.Census.CoverSLThree46
import CFSG.RankThree.PartTwo.KFacts.KS12SLCenter

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434L34Seitz

open Matrix CFSG.ComponentClassification.CatalogueBHigherLinearAction

variable {K : Type} [Field K]

@[expose] def fixClosure {X : Type*} [Group X] (E : Subgroup (MulAut X)) : Subgroup X :=
  Subgroup.closure {x | ∃ φ ∈ E, φ ≠ 1 ∧ φ x = x}

theorem mem_fixClosure {X : Type*} [Group X] {E : Subgroup (MulAut X)} {φ : MulAut X} (hφ : φ ∈ E)
    (hφ1 : φ ≠ 1) {x : X} (hx : φ x = x) : x ∈ fixClosure E :=
  Subgroup.subset_closure ⟨φ, hφ, hφ1, hx⟩

theorem slConjugation_diagUnits_transvection {a b c : Kˣ} {i j : Fin 3} (hij : i ≠ j) (t : K)
    (hd : ![(a : K), b, c] i = ![(a : K), b, c] j) :
    slConjugation 3 K (diagUnits a b c) (Matrix.SpecialLinearGroup.transvection hij t) =
      Matrix.SpecialLinearGroup.transvection hij t := by
  apply Subtype.ext
  rw [slConjugation_matrix, Matrix.SpecialLinearGroup.transvection_coe]
  have hcomm : (diagUnits a b c : GL (Fin 3) K).val * (1 + single i j t) =
      (1 + single i j t) * (diagUnits a b c : GL (Fin 3) K).val := by
    rw [Sec4.coe_diagUnits]
    ext k l
    fin_cases i <;> fin_cases j <;> simp at hij hd <;> fin_cases k <;> fin_cases l <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, hd, mul_comm]
  rw [hcomm, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem slConjugation_apply_eq_iff (A : GL (Fin 3) K) (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    slConjugation 3 K A g = g ↔
      A.val * (g : Matrix (Fin 3) (Fin 3) K) = (g : Matrix (Fin 3) (Fin 3) K) * A.val := by
  constructor
  · intro h
    have h' := congrArg
      (fun x : Matrix.SpecialLinearGroup (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) h
    simp only [slConjugation_matrix] at h'
    calc A.val * (g : Matrix (Fin 3) (Fin 3) K) =
          A.val * (g : Matrix (Fin 3) (Fin 3) K) * (A⁻¹).val * A.val := by
            rw [Matrix.mul_assoc _ (A⁻¹).val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
              Matrix.mul_one]
      _ = (g : Matrix (Fin 3) (Fin 3) K) * A.val := by rw [h']
  · intro h
    apply Subtype.ext
    rw [slConjugation_matrix, h, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one]

theorem slConjugation_diagUnits_of_diagonal (a b c : Kˣ) {M : Matrix.SpecialLinearGroup (Fin 3) K}
    (hM : ∀ i j, i ≠ j → (M : Matrix (Fin 3) (Fin 3) K) i j = 0) :
    slConjugation 3 K (diagUnits a b c) M = M := by
  rw [slConjugation_apply_eq_iff, Sec4.coe_diagUnits]
  have h01 := hM 0 1 (by decide)
  have h02 := hM 0 2 (by decide)
  have h10 := hM 1 0 (by decide)
  have h12 := hM 1 2 (by decide)
  have h20 := hM 2 0 (by decide)
  have h21 := hM 2 1 (by decide)
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h01, h02, h10, h12, h20, h21, mul_comm]

theorem slConjugation_diagUnits_ne_one {a b c : Kˣ} {i j : Fin 3} (hij : i ≠ j)
    (hd : ![(a : K), b, c] i ≠ ![(a : K), b, c] j) :
    slConjugation 3 K (diagUnits a b c) ≠ 1 := by
  intro h1
  have h := congrArg (fun φ : MulAut (Matrix.SpecialLinearGroup (Fin 3) K) =>
    φ (Matrix.SpecialLinearGroup.transvection hij 1)) h1
  simp only [MulAut.one_apply] at h
  rw [slConjugation_apply_eq_iff, Sec4.coe_diagUnits,
    Matrix.SpecialLinearGroup.transvection_coe] at h
  have hij' := congrFun (congrFun h i) j
  apply hd
  fin_cases i <;> fin_cases j <;> simp at hij <;>
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply] using hij'

theorem fixClosure_eq_top_of_toral {E : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) K))}
    {a₁ b₁ a₂ b₂ a₃ b₃ : Kˣ} (hab₁ : a₁ ≠ b₁) (hab₂ : a₂ ≠ b₂) (hab₃ : a₃ ≠ b₃)
    (h₁ : slConjugation 3 K (diagUnits a₁ b₁ b₁) ∈ E)
    (h₂ : slConjugation 3 K (diagUnits a₂ b₂ a₂) ∈ E)
    (h₃ : slConjugation 3 K (diagUnits a₃ a₃ b₃) ∈ E) : fixClosure E = ⊤ := by
  have hab₁' : (a₁ : K) ≠ b₁ := fun h => hab₁ (Units.ext h)
  have hab₂' : (a₂ : K) ≠ b₂ := fun h => hab₂ (Units.ext h)
  have hab₃' : (a₃ : K) ≠ b₃ := fun h => hab₃ (Units.ext h)
  have hn₁ : slConjugation 3 K (diagUnits a₁ b₁ b₁) ≠ 1 :=
    slConjugation_diagUnits_ne_one (i := 0) (j := 1) (by decide) (by simpa using hab₁')
  have hn₂ : slConjugation 3 K (diagUnits a₂ b₂ a₂) ≠ 1 :=
    slConjugation_diagUnits_ne_one (i := 0) (j := 1) (by decide) (by simpa using hab₂')
  have hn₃ : slConjugation 3 K (diagUnits a₃ a₃ b₃) ≠ 1 :=
    slConjugation_diagUnits_ne_one (i := 0) (j := 2) (by decide) (by simpa using hab₃')
  apply eq_top_of_diagonal_transvection'
  · intro M hM
    exact mem_fixClosure h₁ hn₁ (slConjugation_diagUnits_of_diagonal _ _ _ hM)
  · intro i j hij t
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact mem_fixClosure h₁ hn₁ (slConjugation_diagUnits_transvection _ t rfl)
      | exact mem_fixClosure h₂ hn₂ (slConjugation_diagUnits_transvection _ t rfl)
      | exact mem_fixClosure h₃ hn₃ (slConjugation_diagUnits_transvection _ t rfl)

section Linear

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_scalar_of_slConjugation_eq_one [Finite K] {A : GL (Fin 3) K}
    (h : slConjugation 3 K A = 1) : ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin 3) c = A := by
  have h' : conjAut 3 K A = 1 := by
    change descendAut 3 K (slConjugation 3 K A) = 1
    rw [h, map_one]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl A 1
    (by rw [map_one, mul_one, h'])
  exact ⟨c, hc⟩

theorem slConjugation_scalar (c : Kˣ) :
    slConjugation 3 K (GeneralLinearGroup.scalar (Fin 3) c) = 1 := by
  refine MulEquiv.ext fun g => ?_
  rw [MulAut.one_apply, slConjugation_apply_eq_iff, GeneralLinearGroup.coe_scalar]
  exact (Matrix.scalar_commute (c : K) (fun r => Commute.all _ r) _).eq

theorem exists_eq_slConjugation (hK : Nat.card K = 4)
    {φ : MulAut (Matrix.SpecialLinearGroup (Fin 3) K)} (hφ : φ ^ 3 = 1) :
    ∃ A : GL (Fin 3) K, φ = slConjugation 3 K A := by
  have := LinearFieldFour.finite_of_card_eq_four hK
  have := LinearFieldFour.charP_two_of_card_eq_four hK
  have hσ : ∀ a, frobeniusEquiv K 2 a = a ^ 2 := fun a => frobeniusEquiv_apply K 2 a
  obtain ⟨Ψ, hΨ⟩ := LinearThreeFourOuter.exists_outerHom hσ hK
  obtain ⟨⟨A, a, b⟩, hnf⟩ := LinearThreeFourOuter.exists_nf hσ hK (descendAut 3 K φ)
  have h3 : Ψ (descendAut 3 K φ) ^ 3 = 1 := by rw [← map_pow, ← map_pow, hφ, map_one, map_one]
  rw [hnf, hΨ] at h3
  have hr := congrArg SemidirectProduct.rightHom h3
  rw [map_pow, map_one, SemidirectProduct.rightHom_eq_right] at hr
  change ((Multiplicative.ofAdd a, Multiplicative.ofAdd b) :
    Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ^ 3 = 1 at hr
  have hab : ∀ a b : ZMod 2, ((Multiplicative.ofAdd a, Multiplicative.ofAdd b) :
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ^ 3 = 1 → a = 0 ∧ b = 0 := by
    decide
  obtain ⟨rfl, rfl⟩ := hab a b hr
  refine ⟨A, Sec4.descendAut_three_injective ?_⟩
  rw [hnf, LinearThreeFourOuter.nf_zero_zero]
  rfl

theorem slConjugation_mem_range_conj_iff (hK : Nat.card K = 4) (A : GL (Fin 3) K) :
    slConjugation 3 K A ∈ (MulAut.conj : SpecialLinearGroup (Fin 3) K →*
        MulAut (Matrix.SpecialLinearGroup (Fin 3) K)).range ↔
      GeneralLinearGroup.det A = 1 := by
  constructor
  · rintro ⟨g, hg⟩
    rw [← LinearThreeFourOuter.conjAut_mem_range_conj_iff hK A]
    refine ⟨proj 3 K g, ?_⟩
    rw [← CFSG.RankThree.PartTwo.KFacts.descendAut_conj, hg]
    rfl
  · intro h
    let g : Matrix.SpecialLinearGroup (Fin 3) K :=
      ⟨(A : Matrix (Fin 3) (Fin 3) K), by rw [← GeneralLinearGroup.val_det_apply, h, Units.val_one]⟩
    have hg : Matrix.SpecialLinearGroup.toGL g = A := Units.ext rfl
    refine ⟨g, MulEquiv.ext fun m => Matrix.SpecialLinearGroup.toGL_injective ?_⟩
    rw [toGL_slConjugation, MulAut.conj_apply, map_mul, map_mul, map_inv, hg]

end Linear

section Heis

theorem coe_slCongr {S S' : Type} [Field S] [Field S'] (φ : S ≃+* S')
    (g : Matrix.SpecialLinearGroup (Fin 3) S) :
    ((Item434L34.slCongr φ g : Matrix.SpecialLinearGroup (Fin 3) S') : Matrix (Fin 3) (Fin 3) S') =
      (g : Matrix (Fin 3) (Fin 3) S).map φ :=
  rfl

theorem map_Ymat {S S' : Type} [Field S] [Field S'] (φ : S ≃+* S') (ν : S) :
    (Ymat ν).map φ = Ymat (φ ν) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ymat]

theorem map_Xmat {S S' : Type} [Field S] [Field S'] (φ : S ≃+* S') (s : S) :
    (Xmat s).map φ = Xmat (φ s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xmat]

theorem map_mul_comm_iff {S S' : Type} [Field S] [Field S'] (φ : S ≃+* S')
    (A B : Matrix (Fin 3) (Fin 3) S) : A.map φ * B.map φ = B.map φ * A.map φ ↔ A * B = B * A := by
  rw [← Matrix.map_mul, ← Matrix.map_mul]
  exact (Matrix.map_injective φ.injective).eq_iff

theorem mem_genSet_iff_slCongr {S S' : Type} [Field S] [Field S'] (φ : S ≃+* S') (ν s : S)
    (g : Matrix.SpecialLinearGroup (Fin 3) S) :
    Item434L34.slCongr φ g ∈ genSet (Ymat (φ ν)) (Xmat (φ s)) ↔ g ∈ genSet (Ymat ν) (Xmat s) := by
  simp only [genSet, Set.mem_ofPred_eq, coe_slCongr, ← map_Ymat φ, ← map_Xmat φ,
    ← Matrix.map_mul, (Matrix.map_injective φ.injective).eq_iff]

theorem closure_genSet_eq_top (hK : Nat.card K = 4) {ν s : K} (hν : ν * ν + ν + 1 = 0)
    (hs : s * s + s + 1 = 0) : Subgroup.closure (genSet (Ymat ν) (Xmat s)) = ⊤ := by
  have := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hK
  have := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card CFSG.Fischer.F4 := by
    rw [← Nat.card_eq_fintype_card, hK, CFSG.Fischer.F4.card]
  set φ : K ≃+* CFSG.Fischer.F4 := FiniteField.ringEquivOfCardEq hc
  have hroot : ∀ x : CFSG.Fischer.F4, x * x + x + 1 = 0 → x = fc 2 ∨ x = fc 3 := by decide
  have hν' := hroot (φ ν) (by rw [← map_mul, ← map_add, ← map_one φ, ← map_add, hν, map_zero])
  have hs' := hroot (φ s) (by rw [← map_mul, ← map_add, ← map_one φ, ← map_add, hs, map_zero])
  have htop := closure_genSet_eq_top_F4 hν' hs'
  set ψ := Item434L34.slCongr φ
  have hmap : (Subgroup.closure (genSet (Ymat ν) (Xmat s))).map ψ.toMonoidHom =
      Subgroup.closure (genSet (Ymat (φ ν)) (Xmat (φ s))) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext h
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (mem_genSet_iff_slCongr φ ν s g).mpr hg
    · intro hh
      refine ⟨ψ.symm h, (mem_genSet_iff_slCongr φ ν s _).mp ?_, ψ.apply_symm_apply h⟩
      rwa [show ψ (ψ.symm h) = h from ψ.apply_symm_apply h]
  rw [eq_top_iff]
  intro g _
  have hg : ψ g ∈ (Subgroup.closure (genSet (Ymat ν) (Xmat s))).map ψ.toMonoidHom := by
    rw [hmap, htop]
    exact Subgroup.mem_top _
  obtain ⟨g', hg', hgg'⟩ := hg
  rwa [ψ.injective hgg'] at hg'

noncomputable abbrev YGL (ν : Kˣ) : GL (Fin 3) K := diagUnits 1 ν (ν * ν)

@[expose] noncomputable def XGL (s : Kˣ) : GL (Fin 3) K :=
  ⟨Xmat (s : K), !![0, 1, 0; 0, 0, 1; (s⁻¹ : Kˣ), 0, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Xmat, Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Xmat, Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem coe_YGL (ν : Kˣ) : ((YGL ν : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Ymat (ν : K) := by
  rw [Sec4.coe_diagUnits]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ymat]

theorem coe_XGL (s : Kˣ) : ((XGL s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Xmat (s : K) :=
  rfl

theorem slConjugation_ne_one_of_zero [Finite K] {A : GL (Fin 3) K}
    (hA : (A : Matrix (Fin 3) (Fin 3) K) 0 0 = 0) : slConjugation 3 K A ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ := exists_scalar_of_slConjugation_eq_one h
  rw [← hc, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at hA
  exact c.ne_zero hA

theorem fixClosure_eq_top_of_heis (hK : Nat.card K = 4)
    {E : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) K))} {ν s : Kˣ}
    (hν : (ν : K) * ν + ν + 1 = 0) (hs : (s : K) * s + s + 1 = 0)
    (hY : slConjugation 3 K (YGL ν) ∈ E) (hX : slConjugation 3 K (XGL s) ∈ E) :
    fixClosure E = ⊤ := by
  have := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hK
  have := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.charP_two_of_card_eq_four hK
  have hν1 : (ν : K) ≠ 1 := by
    intro h
    rw [h] at hν
    have h3 : (1 : K) + 1 + 1 = 1 := by rw [CharTwo.add_self_eq_zero, zero_add]
    rw [mul_one, h3] at hν
    exact one_ne_zero hν
  have hXY : slConjugation 3 K (XGL s * YGL ν) ∈ E := by rw [map_mul]; exact mul_mem hX hY
  have hXYY : slConjugation 3 K (XGL s * YGL ν * YGL ν) ∈ E := by
    rw [map_mul]; exact mul_mem hXY hY
  have hnY : slConjugation 3 K (YGL ν) ≠ 1 :=
    slConjugation_diagUnits_ne_one (i := 0) (j := 1) (by decide) (by simpa using hν1.symm)
  have hnX : slConjugation 3 K (XGL s) ≠ 1 :=
    slConjugation_ne_one_of_zero (by rw [coe_XGL]; simp [Xmat])
  have hnXY : slConjugation 3 K (XGL s * YGL ν) ≠ 1 :=
    slConjugation_ne_one_of_zero (by
      rw [Units.val_mul, coe_XGL, coe_YGL]; simp [Xmat, Ymat, Matrix.mul_apply, Fin.sum_univ_three])
  have hnXYY : slConjugation 3 K (XGL s * YGL ν * YGL ν) ≠ 1 :=
    slConjugation_ne_one_of_zero (by
      rw [Units.val_mul, Units.val_mul, coe_XGL, coe_YGL]
      simp [Xmat, Ymat, Matrix.mul_apply, Fin.sum_univ_three])
  rw [eq_top_iff, ← closure_genSet_eq_top hK hν hs, Subgroup.closure_le]
  rintro g (hg | hg | hg | hg)
  · exact mem_fixClosure hY hnY ((slConjugation_apply_eq_iff _ g).mpr (by rw [coe_YGL]; exact hg))
  · exact mem_fixClosure hX hnX ((slConjugation_apply_eq_iff _ g).mpr (by rw [coe_XGL]; exact hg))
  · exact mem_fixClosure hXY hnXY ((slConjugation_apply_eq_iff _ g).mpr
      (by rw [Units.val_mul, coe_XGL, coe_YGL]; exact hg))
  · exact mem_fixClosure hXYY hnXYY ((slConjugation_apply_eq_iff _ g).mpr
      (by rw [Units.val_mul, Units.val_mul, coe_XGL, coe_YGL]; exact hg))

end Heis

section Conj

variable {X : Type*} [Group X]

theorem fixClosure_map_conj (E : Subgroup (MulAut X)) (ψ : MulAut X) :
    fixClosure (E.map (MulAut.conj ψ).toMonoidHom) = (fixClosure E).map ψ.toMonoidHom := by
  rw [fixClosure, fixClosure, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨φ, hφ, rfl⟩, h1, hx⟩
    have hx' : ψ (φ (ψ⁻¹ x)) = x := hx
    have hy : φ (ψ⁻¹ x) = ψ⁻¹ x := by
      have h2 : (ψ⁻¹ * ψ) (φ (ψ⁻¹ x)) = ψ⁻¹ x := by rw [MulAut.mul_apply, hx']
      rwa [inv_mul_cancel, MulAut.one_apply] at h2
    refine ⟨ψ⁻¹ x, ⟨φ, hφ, fun h => h1 ?_, hy⟩, ?_⟩
    · simp [h]
    · change ψ (ψ⁻¹ x) = x
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  · rintro ⟨y, ⟨φ, hφ, h1, hy⟩, rfl⟩
    refine ⟨ψ * φ * ψ⁻¹, ⟨φ, hφ, rfl⟩, fun h => h1 ?_, ?_⟩
    · have h' : ψ⁻¹ * (ψ * φ * ψ⁻¹) * ψ = φ := by group
      rw [h, mul_one, inv_mul_cancel] at h'
      exact h'.symm
    · change ψ (φ (ψ⁻¹ (ψ y))) = ψ y
      have h3 : ψ⁻¹ (ψ y) = y := by
        rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
      rw [h3, hy]

theorem fixClosure_eq_top_of_map_conj {E : Subgroup (MulAut X)} (ψ : MulAut X)
    (h : fixClosure (E.map (MulAut.conj ψ).toMonoidHom) = ⊤) : fixClosure E = ⊤ := by
  rw [fixClosure_map_conj] at h
  rw [eq_top_iff]
  intro x _
  have hx : ψ x ∈ (fixClosure E).map ψ.toMonoidHom := by rw [h]; exact Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [ψ.injective hyx] at hy

end Conj

section Pair

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem conj_slConjugation (g A : GL (Fin 3) K) :
    MulAut.conj (slConjugation 3 K g) (slConjugation 3 K A) = slConjugation 3 K (g * A * g⁻¹) := by
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem det_pow (A : GL (Fin 3) K) (n : ℕ) :
    GeneralLinearGroup.det (A ^ n) = GeneralLinearGroup.det A ^ n :=
  map_pow _ _ _

theorem exists_outer_inner (hK : Nat.card K = 4)
    {E : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) K))}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hout : ¬ E ≤ (MulAut.conj : Matrix.SpecialLinearGroup (Fin 3) K →*
      MulAut (Matrix.SpecialLinearGroup (Fin 3) K)).range) :
    ∃ A₀ B₀ : GL (Fin 3) K, slConjugation 3 K A₀ ∈ E ∧ GeneralLinearGroup.det A₀ ≠ 1 ∧
      slConjugation 3 K B₀ ∈ E ∧ GeneralLinearGroup.det B₀ = 1 ∧ slConjugation 3 K B₀ ≠ 1 := by
  have := LinearFieldFour.finite_of_card_eq_four hK
  obtain ⟨φ₀, hφ₀E, hφ₀⟩ := Set.not_subset.mp hout
  obtain ⟨A₀, rfl⟩ := exists_eq_slConjugation hK (hEe.2 _ hφ₀E)
  have hdA : GeneralLinearGroup.det A₀ ≠ 1 := fun h =>
    hφ₀ ((slConjugation_mem_range_conj_iff hK A₀).mpr h)
  have hzle : Subgroup.zpowers (slConjugation 3 K A₀) ≤ E := Subgroup.zpowers_le.mpr hφ₀E
  have hzcard : Nat.card (Subgroup.zpowers (slConjugation 3 K A₀)) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hEe.2 _ hφ₀E))
  obtain ⟨ψ, hψE, hψz⟩ : ∃ ψ ∈ E, ψ ∉ Subgroup.zpowers (slConjugation 3 K A₀) := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (fun x hx => hall x hx : E ≤ _)
    omega
  obtain ⟨B, rfl⟩ := exists_eq_slConjugation hK (hEe.2 _ hψE)
  set d := GeneralLinearGroup.det A₀ with hd
  obtain ⟨k, hk, hdet⟩ : ∃ k : ℕ, k < 3 ∧ GeneralLinearGroup.det B = d ^ k := by
    rcases CFSG.RankThree.PartTwo.KFacts.L34.units_eq hK hdA (GeneralLinearGroup.det B) with
      h | h | h
    · exact ⟨0, by norm_num, by rw [h, pow_zero]⟩
    · exact ⟨1, by norm_num, by rw [h, pow_one]⟩
    · exact ⟨2, by norm_num, by rw [h, sq]⟩
  refine ⟨A₀, B * (A₀ ^ k)⁻¹, hφ₀E, hdA, ?_, ?_, ?_⟩
  · rw [map_mul, map_inv, map_pow]
    exact mul_mem hψE (inv_mem (pow_mem hφ₀E k))
  · rw [map_mul, map_inv, det_pow, hdet, mul_inv_cancel]
  · intro h1
    apply hψz
    rw [map_mul, map_inv, map_pow, mul_inv_eq_one] at h1
    rw [h1]
    exact Subgroup.npow_mem_zpowers _ _

theorem exists_conj_diagTau (hK : Nat.card K = 4) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {B₀ : GL (Fin 3) K} (hdet : GeneralLinearGroup.det B₀ = 1)
    (hne : slConjugation 3 K B₀ ≠ 1) (h3 : slConjugation 3 K B₀ ^ 3 = 1) :
    ∃ g : GL (Fin 3) K, slConjugation 3 K (g⁻¹ * B₀ * g) = slConjugation 3 K (diagTau hτ) := by
  have := LinearFieldFour.finite_of_card_eq_four hK
  have hKpi : PiField true 2 2 K := ⟨Nat.prime_two, by norm_num, by
    change Nat.card K = 2 ^ 2
    rw [hK]
    norm_num⟩
  have hq : ModThree true (2 ^ 2) := by
    change (2 ^ 2) % 3 = 1
    norm_num
  have hxH : B₀ ∈ glPi true 3 (2 ^ 2) K := by
    change B₀ ∈ (⊤ : Subgroup (GL (Fin 3) K))
    exact Subgroup.mem_top _
  have hxZ : B₀ ∉ zPi true 3 (2 ^ 2) K := by
    intro h
    obtain ⟨ξ, -, hξ⟩ := exists_scalar_of_mem_zPi hKpi hq hτ hτ1 h
    apply hne
    rw [← hξ, slConjugation_scalar]
  have hx3 : B₀ ^ 3 ∈ zPi true 3 (2 ^ 2) K := by
    obtain ⟨c, hc⟩ := exists_scalar_of_slConjugation_eq_one (A := B₀ ^ 3) (by rw [map_pow, h3])
    rw [← hc]
    refine scalar_mem_zPi hKpi hq hτ hτ1 ?_
    rw [mem_rootsOfUnity]
    exact LinearThreeFourOuter.units_pow_three hK c
  have hinner : ∃ l ∈ slPi true 3 (2 ^ 2) K, ∀ m ∈ slPi true 3 (2 ^ 2) K,
      B₀ * m * B₀⁻¹ = l * m * l⁻¹ := by
    refine ⟨B₀, Subgroup.subset_closure ?_, fun m _ => rfl⟩
    change (B₀ : Matrix (Fin 3) (Fin 3) K).det = 1
    rw [← GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
  rcases (rank3II_4_10_two hKpi hq hτ hτ1 hxH hxZ hx3).mp hinner with
    ⟨y, ⟨z, hz, rfl⟩, g, -, hg⟩ | ⟨-, hmod⟩
  · obtain ⟨ξ, -, rfl⟩ := exists_scalar_of_mem_zPi hKpi hq hτ hτ1 hz
    refine ⟨g, ?_⟩
    rw [← hg]
    simp only [map_mul, slConjugation_scalar, mul_one]
  · change (2 ^ 2) % 9 = 1 at hmod
    norm_num at hmod

end Pair

section Outer

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_scalar_of_commute [Finite K] {A B : GL (Fin 3) K}
    (h : slConjugation 3 K A * slConjugation 3 K B = slConjugation 3 K B * slConjugation 3 K A) :
    ∃ c : Kˣ, A * B * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * B := by
  have h1 : slConjugation 3 K (A * B * A⁻¹ * B⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  obtain ⟨c, hc⟩ := exists_scalar_of_slConjugation_eq_one h1
  exact ⟨c, by rw [hc, inv_mul_cancel_right]⟩

theorem tau_facts {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    τ ≠ 0 ∧ τ ^ 2 ≠ 1 ∧ τ ^ 2 ≠ τ ∧ τ * τ + τ + 1 = 0 := by
  have h0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  refine ⟨h0, fun h => hτ1 ?_, fun h => hτ1 ?_, ?_⟩
  · calc τ = τ ^ 3 * (τ ^ 2)⁻¹ := by field_simp
      _ = 1 := by rw [hτ, h, inv_one, one_mul]
  · calc τ = τ ^ 2 * τ⁻¹ := by field_simp
      _ = 1 := by rw [h, mul_inv_cancel₀ h0]
  · have h' : (τ - 1) * (τ * τ + τ + 1) = 0 := by linear_combination hτ
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hτ1)

theorem entry_eq_zero_of_mul_diagonal {A : Matrix (Fin 3) (Fin 3) K} {d : Fin 3 → K} {c : K}
    (h : A * diagonal d = c • (diagonal d * A)) {i j : Fin 3} (hij : d j ≠ c * d i) :
    A i j = 0 := by
  have h1 := congrFun (congrFun h i) j
  rw [mul_diagonal, Matrix.smul_apply, diagonal_mul, smul_eq_mul] at h1
  have h2 : A i j * (d j - c * d i) = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hij)

theorem mul_eq_smul_of_conj {A D : GL (Fin 3) K} {c : Kˣ}
    (h : A * D * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * D) :
    (A : Matrix (Fin 3) (Fin 3) K) * D = (c : K) • ((D : Matrix (Fin 3) (Fin 3) K) * A) := by
  have h1 : A * D = GeneralLinearGroup.scalar (Fin 3) c * D * A := by
    rw [← h, inv_mul_cancel_right]
  have h2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h1
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h2
  rw [h2, Matrix.mul_assoc, scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mul,
    Matrix.one_mul]

theorem eq_diagUnits_of_commute_diagTau {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {A : GL (Fin 3) K}
    (h : (A : Matrix (Fin 3) (Fin 3) K) * (diagTau hτ : Matrix (Fin 3) (Fin 3) K) =
      (1 : K) • ((diagTau hτ : Matrix (Fin 3) (Fin 3) K) * A)) :
    ∃ a b c : Kˣ, A = diagUnits a b c := by
  obtain ⟨h0, h2, h21, -⟩ := tau_facts hτ hτ1
  rw [coe_diagTau_eq_diagonal] at h
  have hz : ∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    intro i j hij
    refine entry_eq_zero_of_mul_diagonal h ?_
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · show τ ^ 2 ≠ 1 * τ; rw [one_mul]; exact h21
    · show (1 : K) ≠ 1 * τ; rw [one_mul]; exact hτ1.symm
    · show τ ≠ 1 * τ ^ 2; rw [one_mul]; exact h21.symm
    · exact absurd rfl hij
    · show (1 : K) ≠ 1 * τ ^ 2; rw [one_mul]; exact h2.symm
    · show τ ≠ 1 * 1; rw [one_mul]; exact hτ1
    · show τ ^ 2 ≠ 1 * 1; rw [one_mul]; exact h2
    · exact absurd rfl hij
  have hdet : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    (A.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero
  have hdiag : (A : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(A : Matrix (Fin 3) (Fin 3) K) 0 0, (A : Matrix (Fin 3) (Fin 3) K) 1 1,
        (A : Matrix (Fin 3) (Fin 3) K) 2 2] := by
    ext i j
    by_cases hij : i = j
    · subst hij
      fin_cases i <;> simp
    · rw [hz i j hij, diagonal_apply_ne _ hij]
  have hprod : (A : Matrix (Fin 3) (Fin 3) K) 0 0 * (A : Matrix (Fin 3) (Fin 3) K) 1 1 *
      (A : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
    rw [hdiag, det_diagonal, Fin.prod_univ_three] at hdet
    simpa using hdet
  have ha : (A : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro h'; apply hprod; rw [h']; ring
  have hb : (A : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ 0 := by
    intro h'; apply hprod; rw [h']; ring
  have hc : (A : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
    intro h'; apply hprod; rw [h']; ring
  refine ⟨Units.mk0 _ ha, Units.mk0 _ hb, Units.mk0 _ hc, Units.ext ?_⟩
  rw [Sec4.coe_diagUnits]
  ext i j
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp
  · rw [hz i j hij, diagonal_apply_ne _ hij]

theorem entries_of_mul_diagTau {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {A : GL (Fin 3) K}
    (h : (A : Matrix (Fin 3) (Fin 3) K) * (diagTau hτ : Matrix (Fin 3) (Fin 3) K) =
      τ ^ 2 • ((diagTau hτ : Matrix (Fin 3) (Fin 3) K) * A)) :
    ∀ i j, ¬ ((i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 1)) →
      (A : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  obtain ⟨h0, h2, h21, -⟩ := tau_facts hτ hτ1
  have h3 : τ ^ 2 * τ = 1 := by rw [← pow_succ]; exact hτ
  have h4 : τ ^ 2 * τ ^ 2 = τ := by
    rw [← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ, hτ, one_mul]
  rw [coe_diagTau_eq_diagonal] at h
  intro i j hij
  refine entry_eq_zero_of_mul_diagonal h ?_
  fin_cases i <;> fin_cases j
  · show τ ≠ τ ^ 2 * τ; rw [h3]; exact hτ1
  · show τ ^ 2 ≠ τ ^ 2 * τ; rw [h3]; exact h2
  · exact absurd (Or.inl ⟨rfl, rfl⟩) hij
  · exact absurd (Or.inr (Or.inl ⟨rfl, rfl⟩)) hij
  · show τ ^ 2 ≠ τ ^ 2 * τ ^ 2; rw [h4]; exact h21
  · show (1 : K) ≠ τ ^ 2 * τ ^ 2; rw [h4]; exact hτ1.symm
  · show τ ≠ τ ^ 2 * 1; rw [mul_one]; exact h21.symm
  · exact absurd (Or.inr (Or.inr ⟨rfl, rfl⟩)) hij
  · show (1 : K) ≠ τ ^ 2 * 1; rw [mul_one]; exact h2.symm

end Outer

section Configurations

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] noncomputable def diagAut (K : Type) [Field K] :
    Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) K)) :=
  ((slConjugation 3 K).comp (Sec4.diagHom (K := K))).range

theorem diagUnits_self (c : Kˣ) : diagUnits c c c = GeneralLinearGroup.scalar (Fin 3) c := by
  apply Units.ext
  rw [Sec4.coe_diagUnits, GeneralLinearGroup.coe_scalar, scalar_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem card_diagAut_le (hK : Nat.card K = 4) : Nat.card (diagAut K) ≤ 9 := by
  have := LinearFieldFour.finite_of_card_eq_four hK
  set f := (slConjugation 3 K).comp (Sec4.diagHom (K := K)) with hf
  have h := Item434L34.card_ker_mul_card_range f
  have hunits : Nat.card Kˣ = 3 := LinearThreeFourOuter.card_units_eq_three hK
  rw [Nat.card_prod, Nat.card_prod, hunits] at h
  set ι : Kˣ →* Kˣ × Kˣ × Kˣ := (MonoidHom.id _).prod ((MonoidHom.id _).prod (MonoidHom.id _))
  have hι : Function.Injective ι := fun x y hxy => congrArg Prod.fst hxy
  have hle : ι.range ≤ f.ker := by
    rintro _ ⟨c, rfl⟩
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply]
    change slConjugation 3 K (diagUnits c c c) = 1
    rw [diagUnits_self, slConjugation_scalar]
  have hker : 3 ≤ Nat.card f.ker := by
    calc 3 = Nat.card ι.range := by
          rw [← hunits]; exact Nat.card_congr (MonoidHom.ofInjective hι).toEquiv
      _ ≤ Nat.card f.ker := Subgroup.card_le_of_le hle
  change Nat.card f.range ≤ 9
  by_contra hlt
  push Not at hlt
  have : 3 * 10 ≤ Nat.card f.ker * Nat.card f.range := Nat.mul_le_mul hker hlt
  omega

theorem fixClosure_eq_top_of_diagonal (hK : Nat.card K = 4)
    {E : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) K))} (hE9 : Nat.card E = 9)
    {D A : GL (Fin 3) K} (hDE : slConjugation 3 K D ∈ E) (hAE : slConjugation 3 K A ∈ E)
    (hDd : D ∈ (Sec4.diagHom (K := K)).range) (hAd : A ∈ (Sec4.diagHom (K := K)).range)
    (hDdet : GeneralLinearGroup.det D = 1) (hD1 : slConjugation 3 K D ≠ 1)
    (hD3 : slConjugation 3 K D ^ 3 = 1) (hAdet : GeneralLinearGroup.det A ≠ 1) :
    fixClosure E = ⊤ := by
  have := LinearFieldFour.finite_of_card_eq_four hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := E ⊓ diagAut K with hH
  have hDH : slConjugation 3 K D ∈ H := by
    obtain ⟨abc, rfl⟩ := hDd
    exact ⟨hDE, abc, rfl⟩
  have hAH : slConjugation 3 K A ∈ H := by
    obtain ⟨abc, rfl⟩ := hAd
    exact ⟨hAE, abc, rfl⟩
  have hzlt : Subgroup.zpowers (slConjugation 3 K D) < H := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr hDH) fun heq => ?_
    rw [← heq] at hAH
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hAH
    apply hAdet
    rw [← slConjugation_mem_range_conj_iff hK, ← hk]
    exact zpow_mem ((slConjugation_mem_range_conj_iff hK D).mpr hDdet) k
  have hzcard : Nat.card (Subgroup.zpowers (slConjugation 3 K D)) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hD3 hD1
  have hH3 : 3 < Nat.card H := lt_of_eq_of_lt hzcard.symm (Subgroup.card_lt_of_lt hzlt)
  have hH9 : Nat.card H = 9 := by
    have hdvd : Nat.card H ∣ 9 := hE9 ▸ Subgroup.card_dvd_of_le inf_le_left
    have : Nat.card H ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card H <;> simp_all
  have hHeq : H = diagAut K :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hH9]; exact card_diagAut_le hK)
  have hdiagE : diagAut K ≤ E := hHeq ▸ inf_le_left
  obtain ⟨u, hu⟩ := CFSG.RankThree.PartTwo.KFacts.L34.exists_units_ne_one hK
  exact fixClosure_eq_top_of_toral hu hu (Ne.symm hu)
    (hdiagE (MonoidHom.mem_range.mpr ⟨(u, 1, 1), rfl⟩))
    (hdiagE (MonoidHom.mem_range.mpr ⟨(u, 1, u), rfl⟩))
    (hdiagE (MonoidHom.mem_range.mpr ⟨(1, 1, u), rfl⟩))

theorem det_of_shape {A : Matrix (Fin 3) (Fin 3) K}
    (h : ∀ i j, ¬ ((i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 1)) → A i j = 0) :
    A.det = A 0 2 * A 1 0 * A 2 1 := by
  rw [Matrix.det_fin_three, h 0 0 (by decide), h 0 1 (by decide), h 1 1 (by decide),
    h 1 2 (by decide), h 2 0 (by decide), h 2 2 (by decide)]
  ring

theorem fixClosure_eq_top_of_shape (hK : Nat.card K = 4) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {E : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) K))}
    {A : GL (Fin 3) K} (hDE : slConjugation 3 K (diagTau hτ) ∈ E)
    (hAE : slConjugation 3 K A ∈ E) (hAdet : GeneralLinearGroup.det A ≠ 1)
    (hshape : ∀ i j, ¬ ((i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 1)) →
      (A : Matrix (Fin 3) (Fin 3) K) i j = 0) :
    fixClosure E = ⊤ := by
  have := LinearFieldFour.finite_of_card_eq_four hK
  obtain ⟨h0, -, -, hτsq⟩ := tau_facts hτ hτ1
  have hdetA : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    (A.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero
  have hdet3 := det_of_shape hshape
  rw [hdet3] at hdetA
  have hq : (A : Matrix (Fin 3) (Fin 3) K) 1 0 ≠ 0 := by
    intro h'; apply hdetA; rw [h']; ring
  have hr : (A : Matrix (Fin 3) (Fin 3) K) 2 1 ≠ 0 := by
    intro h'; apply hdetA; rw [h']; ring
  set q := Units.mk0 _ hq
  set r := Units.mk0 _ hr
  set u : GL (Fin 3) K := diagUnits 1 q (q * r) with hu
  set s : Kˣ := GeneralLinearGroup.det A with hs
  have hAu : A * u = u * XGL s := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hu, Sec4.coe_diagUnits, coe_XGL, hs,
      GeneralLinearGroup.val_det_apply, hdet3]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Xmat, q, r,
        hshape 0 0 (by decide), hshape 0 1 (by decide), hshape 1 1 (by decide),
        hshape 1 2 (by decide), hshape 2 0 (by decide), hshape 2 2 (by decide)] <;> ring
  have hconjA : u⁻¹ * A * u = XGL s := by rw [mul_assoc, hAu, inv_mul_cancel_left]
  have hconjD : u⁻¹ * diagTau hτ * u = diagTau hτ := by
    have hcomm : diagTau hτ * u = u * diagTau hτ := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hu, Sec4.coe_diagUnits, coe_diagTau_eq_diagonal,
        diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      fin_cases i <;> simp [mul_comm]
    rw [mul_assoc, hcomm, inv_mul_cancel_left]
  set τu := Units.mk0 τ h0
  have hDY : slConjugation 3 K (diagTau hτ) = slConjugation 3 K (YGL τu) := by
    have : diagTau hτ = GeneralLinearGroup.scalar (Fin 3) τu * YGL τu := by
      apply Units.ext
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, coe_diagTau_eq_diagonal,
        Sec4.coe_diagUnits, diagonal_mul_diagonal]
      congr 1
      funext i
      fin_cases i <;> simp [τu, pow_two]
      linear_combination (-1 : K) * hτ
    rw [this, map_mul, slConjugation_scalar, one_mul]
  set E' := E.map (MulAut.conj (slConjugation 3 K u⁻¹)).toMonoidHom with hE'
  have hYE' : slConjugation 3 K (YGL τu) ∈ E' := by
    refine ⟨slConjugation 3 K (diagTau hτ), hDE, ?_⟩
    change MulAut.conj (slConjugation 3 K u⁻¹) (slConjugation 3 K (diagTau hτ)) = _
    rw [conj_slConjugation, inv_inv, hconjD, hDY]
  have hXE' : slConjugation 3 K (XGL s) ∈ E' := by
    refine ⟨slConjugation 3 K A, hAE, ?_⟩
    change MulAut.conj (slConjugation 3 K u⁻¹) (slConjugation 3 K A) = _
    rw [conj_slConjugation, inv_inv, hconjA]
  have hs1 : s ≠ 1 := hAdet
  refine fixClosure_eq_top_of_map_conj (slConjugation 3 K u⁻¹)
    (fixClosure_eq_top_of_heis hK hτsq ?_ hYE' hXE')
  exact CFSG.RankThree.PartTwo.KFacts.L34.val_mul_self_add hK hs1

end Configurations

section Main

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem scalar_mul_comm (c : Kˣ) (B : GL (Fin 3) K) :
    GeneralLinearGroup.scalar (Fin 3) c * B = B * GeneralLinearGroup.scalar (Fin 3) c := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
  exact (Matrix.scalar_commute (c : K) (fun r => Commute.all _ r) _).eq

theorem inv_conj_eq_of_conj {A D : GL (Fin 3) K} {c : Kˣ}
    (h : A * D * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * D) :
    A⁻¹ * D * A⁻¹⁻¹ = GeneralLinearGroup.scalar (Fin 3) c⁻¹ * D := by
  have h1 : GeneralLinearGroup.scalar (Fin 3) c * (A⁻¹ * D * A) = D := by
    calc GeneralLinearGroup.scalar (Fin 3) c * (A⁻¹ * D * A)
        = GeneralLinearGroup.scalar (Fin 3) c * A⁻¹ * D * A := by simp only [mul_assoc]
      _ = A⁻¹ * (GeneralLinearGroup.scalar (Fin 3) c * D) * A := by
          rw [scalar_mul_comm]; simp only [mul_assoc]
      _ = A⁻¹ * (A * D * A⁻¹) * A := by rw [h]
      _ = D := by group
  rw [inv_inv]
  conv_rhs => rw [← h1]
  rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem det_diagTau_eq_one {τ : K} (hτ : τ ^ 3 = 1) : GeneralLinearGroup.det (diagTau hτ) = 1 := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, coe_diagTau_eq_diagonal, det_diagonal, Fin.prod_univ_three,
    Units.val_one]
  show τ * τ ^ 2 * 1 = 1
  rw [mul_one, ← pow_succ']
  exact hτ

theorem fixClosure_eq_top_sl (hK : Nat.card K = 4)
    {E : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) K))}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hout : ¬ E ≤ (MulAut.conj : Matrix.SpecialLinearGroup (Fin 3) K →*
      MulAut (Matrix.SpecialLinearGroup (Fin 3) K)).range) :
    fixClosure E = ⊤ := by
  have := LinearFieldFour.finite_of_card_eq_four hK
  obtain ⟨A₀, B₀, hA₀E, hdA, hB₀E, hdB, hB₀1⟩ := exists_outer_inner hK hEe hE9 hout
  obtain ⟨u, hu⟩ := CFSG.RankThree.PartTwo.KFacts.L34.exists_units_ne_one hK
  have hu3 : u ^ 3 = 1 := LinearThreeFourOuter.units_pow_three hK u
  have hτ : (u : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hu3, Units.val_one]
  have hτ1 : (u : K) ≠ 1 := fun h => hu (Units.ext h)
  obtain ⟨g, hg⟩ := exists_conj_diagTau hK hτ hτ1 hdB hB₀1 (hEe.2 _ hB₀E)
  set ψ := slConjugation 3 K g⁻¹ with hψ
  set E' := E.map (MulAut.conj ψ).toMonoidHom with hE'
  refine fixClosure_eq_top_of_map_conj ψ ?_
  have hmem : ∀ B : GL (Fin 3) K, slConjugation 3 K B ∈ E →
      slConjugation 3 K (g⁻¹ * B * g) ∈ E' := by
    intro B hB
    refine ⟨slConjugation 3 K B, hB, ?_⟩
    change MulAut.conj ψ (slConjugation 3 K B) = _
    rw [hψ, conj_slConjugation, inv_inv]
  have hE'9 : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective (f := (MulAut.conj ψ).toMonoidHom)
      (MulAut.conj ψ).injective, hE9]
  have hE'e : CFSG.Assembly.IsElemAbelian 3 E' := Sec4.isElemAbelian_map _ hEe
  set D := diagTau hτ with hD
  have hDE' : slConjugation 3 K D ∈ E' := by rw [← hg]; exact hmem B₀ hB₀E
  set A₁ := g⁻¹ * A₀ * g with hA₁
  have hA₁E' : slConjugation 3 K A₁ ∈ E' := hmem A₀ hA₀E
  have hdA₁ : GeneralLinearGroup.det A₁ ≠ 1 := by
    rw [hA₁, map_mul, map_mul, map_inv, mul_comm _ (GeneralLinearGroup.det A₀), mul_assoc,
      inv_mul_cancel, mul_one]
    exact hdA
  have hcomm : slConjugation 3 K A₁ * slConjugation 3 K D =
      slConjugation 3 K D * slConjugation 3 K A₁ :=
    congrArg Subtype.val (hE'e.1.1.comm ⟨_, hA₁E'⟩ ⟨_, hDE'⟩)
  obtain ⟨c, hc⟩ := exists_scalar_of_commute hcomm
  have hD1 : slConjugation 3 K D ≠ 1 := by
    intro h1
    apply hB₀1
    have h2 : slConjugation 3 K (g * (g⁻¹ * B₀ * g) * g⁻¹) = 1 := by
      rw [map_mul, map_mul, hg, h1, mul_one, ← map_mul, mul_inv_cancel, map_one]
    rwa [show g * (g⁻¹ * B₀ * g) * g⁻¹ = B₀ by group] at h2
  rcases CFSG.RankThree.PartTwo.KFacts.L34.units_eq hK hu c with h | h | h <;> rw [h] at hc
  ·
    have hm := mul_eq_smul_of_conj hc
    rw [Units.val_one] at hm
    obtain ⟨a, b, c', hA⟩ := eq_diagUnits_of_commute_diagTau hτ hτ1 hm
    refine fixClosure_eq_top_of_diagonal hK hE'9 hDE' hA₁E'
      (MonoidHom.mem_range.mpr ⟨(u, u ^ 2, 1), ?_⟩) (MonoidHom.mem_range.mpr ⟨(a, b, c'), hA.symm⟩)
      (det_diagTau_eq_one hτ) hD1 (hE'e.2 _ hDE') hdA₁
    apply Units.ext
    rw [Sec4.coe_diagHom, hD, coe_diagTau_eq_diagonal]
    congr 1
  ·
    have hc' := inv_conj_eq_of_conj hc
    have hu' : u⁻¹ = u * u := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hu3)
    rw [hu'] at hc'
    have hm := mul_eq_smul_of_conj hc'
    rw [Units.val_mul, ← sq] at hm
    refine fixClosure_eq_top_of_shape hK hτ hτ1 hDE' (by rw [map_inv]; exact inv_mem hA₁E') ?_
      (entries_of_mul_diagTau hτ hτ1 hm)
    rw [map_inv]
    exact inv_ne_one.mpr hdA₁
  ·
    have hm := mul_eq_smul_of_conj hc
    rw [Units.val_mul, ← sq] at hm
    exact fixClosure_eq_top_of_shape hK hτ hτ1 hDE' hA₁E' hdA₁ (entries_of_mul_diagTau hτ hτ1 hm)

theorem exists_eq_conjAut (hK : Nat.card K = 4) {φ : MulAut (projectiveSL 3 K)}
    (hφ : φ ^ 3 = 1) : ∃ A : GL (Fin 3) K, φ = conjAut 3 K A := by
  have := LinearFieldFour.finite_of_card_eq_four hK
  have := LinearFieldFour.charP_two_of_card_eq_four hK
  have hσ : ∀ a, frobeniusEquiv K 2 a = a ^ 2 := fun a => frobeniusEquiv_apply K 2 a
  obtain ⟨Ψ, hΨ⟩ := LinearThreeFourOuter.exists_outerHom hσ hK
  obtain ⟨⟨A, a, b⟩, hnf⟩ := LinearThreeFourOuter.exists_nf hσ hK φ
  have h3 : Ψ φ ^ 3 = 1 := by rw [← map_pow, hφ, map_one]
  rw [hnf, hΨ] at h3
  have hr := congrArg SemidirectProduct.rightHom h3
  rw [map_pow, map_one, SemidirectProduct.rightHom_eq_right] at hr
  change ((Multiplicative.ofAdd a, Multiplicative.ofAdd b) :
    Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ^ 3 = 1 at hr
  have hab : ∀ a b : ZMod 2, ((Multiplicative.ofAdd a, Multiplicative.ofAdd b) :
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ^ 3 = 1 → a = 0 ∧ b = 0 := by
    decide
  obtain ⟨rfl, rfl⟩ := hab a b hr
  exact ⟨A, by rw [hnf, LinearThreeFourOuter.nf_zero_zero]⟩

theorem fixClosure_eq_top_of_surjective {X Y : Type*} [Group X] [Group Y]
    {E : Subgroup (MulAut X)} {E' : Subgroup (MulAut Y)} (f : X →* Y)
    (hf : Function.Surjective f) (hE : fixClosure E = ⊤)
    (h : ∀ φ ∈ E, φ ≠ 1 → ∃ ψ ∈ E', ψ ≠ 1 ∧ ∀ x, f (φ x) = ψ (f x)) :
    fixClosure E' = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  have hx : x ∈ fixClosure E := by rw [hE]; exact Subgroup.mem_top x
  have hle : (fixClosure E).map f ≤ fixClosure E' := by
    rw [fixClosure, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨z, ⟨φ, hφ, hφ1, hz⟩, rfl⟩
    obtain ⟨ψ, hψ, hψ1, hfψ⟩ := h φ hφ hφ1
    exact mem_fixClosure hψ hψ1 (by rw [← hfψ, hz])
  exact hle ⟨x, hx, rfl⟩

theorem fixClosure_eq_top_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (ψ : X ≃* Y)
    {E : Subgroup (MulAut X)} (h : fixClosure (E.map (MulAut.congr ψ).toMonoidHom) = ⊤) :
    fixClosure E = ⊤ := by
  refine fixClosure_eq_top_of_surjective ψ.symm.toMonoidHom ψ.symm.surjective h ?_
  rintro _ ⟨φ, hφ, rfl⟩ h1
  refine ⟨φ, hφ, fun h' => h1 ?_, fun y => ?_⟩
  · rw [h', map_one]
  · change ψ.symm (ψ (φ (ψ.symm y))) = φ (ψ.symm y)
    exact ψ.symm_apply_apply _

theorem not_le_range_conj_map {X Y : Type*} [Group X] [Group Y] (ψ : X ≃* Y)
    {E : Subgroup (MulAut X)} (hout : ¬ E ≤ (MulAut.conj : X →* MulAut X).range) :
    ¬ E.map (MulAut.congr ψ).toMonoidHom ≤ (MulAut.conj : Y →* MulAut Y).range := by
  intro hle
  apply hout
  intro φ hφ
  obtain ⟨y, hy⟩ := hle ⟨φ, hφ, rfl⟩
  refine ⟨ψ.symm y, MulEquiv.ext fun x => ?_⟩
  have h := congrArg (fun χ : MulAut Y => χ (ψ x)) hy
  simp only [MulAut.conj_apply] at h
  change ψ.symm y * x * (ψ.symm y)⁻¹ = φ x
  apply ψ.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h]
  change ψ (φ (ψ.symm (ψ x))) = ψ (φ x)
  rw [MulEquiv.symm_apply_apply]

theorem fixClosure_eq_top_psl (hK : Nat.card K = 4) {E : Subgroup (MulAut (projectiveSL 3 K))}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hout : ¬ E ≤ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) :
    fixClosure E = ⊤ := by
  have := LinearFieldFour.finite_of_card_eq_four hK
  have hinj : Function.Injective (descendAut 3 K) := Sec4.descendAut_three_injective
  set Et := E.comap (descendAut 3 K) with hEt
  have hmap : Et.map (descendAut 3 K) = E := by
    refine le_antisymm (Subgroup.map_comap_le _ _) fun φ hφ => ?_
    obtain ⟨A, rfl⟩ := exists_eq_conjAut hK (hEe.2 φ hφ)
    exact ⟨slConjugation 3 K A, hφ, rfl⟩
  have hcard : Nat.card Et = 9 := by rw [← hE9, ← hmap, Subgroup.card_map_of_injective hinj]
  have hEte : CFSG.Assembly.IsElemAbelian 3 Et := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · change descendAut 3 K (x * y) = descendAut 3 K (y * x)
      rw [map_mul, map_mul]
      exact congrArg Subtype.val
        (hEe.1.1.comm ⟨descendAut 3 K x, x.2⟩ ⟨descendAut 3 K y, y.2⟩)
    · rw [map_pow, map_one]
      exact hEe.2 _ hx
  have hEtout : ¬ Et ≤ (MulAut.conj : Matrix.SpecialLinearGroup (Fin 3) K →*
      MulAut (Matrix.SpecialLinearGroup (Fin 3) K)).range := by
    intro hle
    apply hout
    intro φ hφ
    rw [← hmap] at hφ
    obtain ⟨φ', hφ', rfl⟩ := hφ
    obtain ⟨g, hg⟩ := hle hφ'
    exact ⟨proj 3 K g, by rw [← hg, CFSG.RankThree.PartTwo.KFacts.descendAut_conj]⟩
  refine fixClosure_eq_top_of_surjective (proj 3 K) (proj_surjective 3 K)
    (fixClosure_eq_top_sl hK hEte hcard hEtout) fun φ hφ h1 => ⟨descendAut 3 K φ, hφ, ?_, ?_⟩
  · intro h
    apply h1
    apply hinj
    rw [h, map_one]
  · intro x
    exact (descendAut_proj 3 K φ x).symm

theorem fixClosure_le_seitzHyperGamma {X : Type*} [Group X] {E : Subgroup (MulAut X)}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    fixClosure E ≤ CFSG.LieType.Seitz.seitzHyperGamma 3 E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [fixClosure, Subgroup.closure_le]
  rintro x ⟨φ, hφE, hφ1, hx⟩
  have hF : Subgroup.zpowers φ ≤ E := Subgroup.zpowers_le.mpr hφE
  have hcard : Nat.card (Subgroup.zpowers φ) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hEe.2 φ hφE) hφ1
  have hrel : (Subgroup.zpowers φ).relIndex E = 3 := by
    have h1 := Subgroup.card_mul_index ((Subgroup.zpowers φ).subgroupOf E)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF).toEquiv, hcard, hE9] at h1
    change ((Subgroup.zpowers φ).subgroupOf E).index = 3
    omega
  have hxF : x ∈ CFSG.LieType.Seitz.fixedPoints (Subgroup.zpowers φ) := by
    refine CFSG.LieType.Seitz.mem_fixedPoints.mpr fun ψ hψ => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hψ
    have hs : φ ∈ MulAction.stabilizer (MulAut X) x := hx
    exact MulAction.mem_stabilizer_iff.mp (zpow_mem hs k)
  exact le_iSup₂ (f := fun (F : Subgroup (MulAut X)) (_ : F ≤ E ∧ F.relIndex E = 3) =>
    CFSG.LieType.Seitz.fixedPoints F) (Subgroup.zpowers φ) ⟨hF, hrel⟩ hxF

end Main

end CFSG.RankThree.PartTwo.Sec4.Item434L34Seitz

namespace CFSG.RankThree.PartTwo.Sec4

open Item434L34Seitz

section Final


theorem seitzL34Outer : SeitzL34Outer := by
  intro X _ _ hX hZ3 hL E hEe hE9 hout
  suffices h : fixClosure E = ⊤ by
    rw [eq_top_iff, ← h]
    exact fixClosure_le_seitzHyperGamma hEe hE9
  obtain ⟨e⟩ := hL
  by_cases hZ : Subgroup.center X = ⊥
  · set ψ : X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 2) :=
      (quotientCenterEquivOfBot hZ).symm.trans (e.trans (KFacts.L34.projSLEquivProjectiveSL 3 _))
      with hψ
    refine fixClosure_eq_top_of_mulEquiv ψ (fixClosure_eq_top_psl
      KFacts.L34.card_galoisField_two_two (isElemAbelian_map _ hEe) ?_
      (not_le_range_conj_map ψ hout))
    rw [Subgroup.card_map_of_injective (f := (MulAut.congr ψ).toMonoidHom)
      (MulAut.congr ψ).injective, hE9]
  · obtain ⟨K, _, _, ⟨hK, ⟨ψ₀⟩⟩ | ⟨hK, ⟨ψ₀⟩⟩⟩ := Census.coverSLThree46 X hX hZ3 hZ 2 2
      (by norm_num) (Or.inl rfl) (Or.inl ⟨by norm_num, ⟨e⟩⟩)
    swap
    · exact absurd (KFacts.center_eq_bot_of_mulEquiv ψ₀
        (KFacts.center_statedSU_three_eq_bot (p := 2) (f := 2) (by norm_num) hK (by norm_num))) hZ
    have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
    set ψ : X ≃* Matrix.SpecialLinearGroup (Fin 3) K := ψ₀.trans (statedSLEquiv 3 K) with hψ
    refine fixClosure_eq_top_of_mulEquiv ψ (fixClosure_eq_top_sl hK4 (isElemAbelian_map _ hEe) ?_
      (not_le_range_conj_map ψ hout))
    rw [Subgroup.card_map_of_injective (f := (MulAut.congr ψ).toMonoidHom)
      (MulAut.congr ψ).injective, hE9]

end Final

section Families


theorem item434SecFor_isL34' : Item434SecFor IsL34 :=
  item434SecFor_isL34 seitzL34Outer

end Families

end CFSG.RankThree.PartTwo.Sec4
