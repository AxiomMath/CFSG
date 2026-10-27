module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MatrixFieldTransport
public import CFSG.Quasithin.Background.A318PL3Iso
public import CFSG.Quasithin.EmptyFaithful.R3c6Pa
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A318PL3Unit
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure318Defs
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.J4SNoCompCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.R3c6

open CFSG.ShultStronglyClosedTI CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts Matrix
open CFSG.Assembly.LowTwoRank

section Model

variable (n : ℕ) (K : Type) [Field K] [CharP K 2]

@[expose] noncomputable def guA : Subgroup (GL (Fin 3) K) :=
  (StatedGU 3 (2 ^ n) K).map unitaryGramConj.toMonoidHom

variable {n K}

theorem mem_guA (h : UnitaryFieldData 2 n K) {M : GL (Fin 3) K} :
    M ∈ guA n K ↔ ((M : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * unitaryAntidiagonal *
      (M : Matrix (Fin 3) (Fin 3) K) = unitaryAntidiagonal := by
  rw [guA, Subgroup.mem_map_equiv, A318P.statedGU_eq_unitaryIsom3 h, mem_unitaryIsom3]
  have := unitaryGramConj_condition_iff (K := K) n (unitaryGramConj.symm M)
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

omit [CharP K 2] in
theorem gram_apply (σ : K →+* K) (M : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    ((M.map σ)ᵀ * (unitaryAntidiagonal : Matrix (Fin 3) (Fin 3) K) * M) i j =
      σ (M 0 i) * M 2 j + σ (M 1 i) * M 1 j + σ (M 2 i) * M 0 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_three, unitaryAntidiagonal]
  ring

theorem guA_entry (h : UnitaryFieldData 2 n K) {M : GL (Fin 3) K} (hM : M ∈ guA n K) (i j : Fin 3) :
    h.bar (M.1 0 i) * M.1 2 j + h.bar (M.1 1 i) * M.1 1 j + h.bar (M.1 2 i) * M.1 0 j =
      (unitaryAntidiagonal : Matrix (Fin 3) (Fin 3) K) i j := by
  have h1 := congrFun (congrFun ((mem_guA h).1 hM) i) j
  rw [gram_apply] at h1
  exact h1

variable (n K) in
@[expose] noncomputable def rtA : Subgroup (GL (Fin 3) K) where
  carrier := {M | M ∈ guA n K ∧ M.1 0 0 = 1 ∧ M.1 1 1 = 1 ∧ M.1 2 2 = 1 ∧ M.1 1 0 = 0 ∧
    M.1 2 0 = 0 ∧ M.1 2 1 = 0}
  mul_mem' := by
    rintro M N ⟨hM, hM00, hM11, hM22, hM10, hM20, hM21⟩ ⟨hN, hN00, hN11, hN22, hN10, hN20, hN21⟩
    refine ⟨mul_mem hM hN, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, hM00, hM11, hM22, hM10, hM20, hM21,
      hN00, hN11, hN22, hN10, hN20, hN21]
  one_mem' := by
    refine ⟨one_mem _, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  inv_mem' := by
    rintro M ⟨hM, hM00, hM11, hM22, hM10, hM20, hM21⟩
    have hMN : M.1 * (M⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e : ∀ i j, M.1 i 0 * (M⁻¹).1 0 j + M.1 i 1 * (M⁻¹).1 1 j + M.1 i 2 * (M⁻¹).1 2 j =
        (1 : Matrix (Fin 3) (Fin 3) K) i j := by
      intro i j
      have := congrFun (congrFun hMN i) j
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
    have e20 := e 2 0
    have e21 := e 2 1
    have e22 := e 2 2
    have e10 := e 1 0
    have e11 := e 1 1
    have e00 := e 0 0
    simp only [hM00, hM11, hM22, hM10, hM20, hM21, one_mul, zero_mul, zero_add, add_zero,
      Matrix.one_apply_ne, Matrix.one_apply_eq, ne_eq, Fin.reduceEq, not_false_eq_true] at e20 e21 e22 e10 e11 e00
    have n10 : (M⁻¹).1 1 0 = 0 := by
      rw [e20] at e10
      simpa using e10
    have n11 : (M⁻¹).1 1 1 = 1 := by
      rw [e21] at e11
      simpa using e11
    have n00 : (M⁻¹).1 0 0 = 1 := by
      rw [n10, e20] at e00
      simpa using e00
    exact ⟨inv_mem hM, n00, n11, e22, n10, e20, e21⟩

section Uni

variable (h : UnitaryFieldData 2 n K)

omit h in
theorem two_eq_zero_K : (2 : K) = 0 := CharTwo.two_eq_zero

@[expose] noncomputable def uniGL (x y : K) (hxy : y + h.bar y = x * h.bar x) : GL (Fin 3) K where
  val := !![1, x, y; 0, 1, h.bar x; 0, 0, 1]
  inv := !![1, x, h.bar y; 0, 1, h.bar x; 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    all_goals first
      | exact CharTwo.add_self_eq_zero _
      | linear_combination hxy + (x * h.bar x) * (two_eq_zero_K (K := K))
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    all_goals first
      | exact CharTwo.add_self_eq_zero _
      | linear_combination hxy + (x * h.bar x) * (two_eq_zero_K (K := K))

theorem uniGL_val (x y : K) (hxy : y + h.bar y = x * h.bar x) :
    ((uniGL h x y hxy : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, x, y; 0, 1, h.bar x; 0, 0, 1] := rfl

theorem uniGL_mem (x y : K) (hxy : y + h.bar y = x * h.bar x) : uniGL h x y hxy ∈ rtA n K := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_guA h]
    ext i j
    rw [gram_apply, uniGL_val]
    fin_cases i <;> fin_cases j <;> simp [unitaryAntidiagonal, UnitaryFieldData.bar_bar]
    all_goals first
      | exact CharTwo.add_self_eq_zero _
      | linear_combination hxy + (x * h.bar x) * (two_eq_zero_K (K := K))
  all_goals simp [uniGL_val]

theorem exists_trace_one : ∃ t : K, t + h.bar t = 1 := by
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have hτ : c + h.bar c ≠ 0 := by
    intro h0
    apply hc
    have h1 : h.bar c = -c := by linear_combination h0
    rw [h1, CharTwo.neg_eq]
  have hτσ : h.bar (c + h.bar c) = c + h.bar c := by
    rw [map_add, h.bar_bar, add_comm]
  refine ⟨c / (c + h.bar c), ?_⟩
  rw [map_div₀, hτσ, ← add_div]
  exact div_self hτ

theorem one_add_one_bar : (1 : K) + h.bar 1 = 0 * h.bar 0 := by
  rw [map_one, map_zero, zero_mul]
  exact CharTwo.add_self_eq_zero _

omit [CharP K 2] in
theorem trace_one_rel {t : K} (ht : t + h.bar t = 1) : t + h.bar t = 1 * h.bar 1 := by
  rw [map_one, one_mul]
  exact ht

theorem uniGL_zero_one_mem : uniGL h 0 1 (one_add_one_bar h) ∈ rtA n K := uniGL_mem h _ _ _

theorem uniGL_one_t_mem {t : K} (ht : t + h.bar t = 1) :
    uniGL h 1 t (trace_one_rel h ht) ∈ rtA n K := uniGL_mem h _ _ _

include h in
theorem flag_of_conj {M : GL (Fin 3) K} (h1 : ∀ u ∈ rtA n K, M⁻¹ * u * M ∈ rtA n K) :
    M.1 1 0 = 0 ∧ M.1 2 0 = 0 := by
  have key : ∀ (w : GL (Fin 3) K), w ∈ rtA n K →
      ∀ i : Fin 3, M.1 i 0 = w.1 i 0 * M.1 0 0 + w.1 i 1 * M.1 1 0 + w.1 i 2 * M.1 2 0 := by
    intro w hw i
    obtain ⟨-, h00, -, -, h10, h20, -⟩ := h1 w hw
    have hrel : M * (M⁻¹ * w * M) = w * M := by group
    have := congrArg (fun A : GL (Fin 3) K => A.1 i 0) hrel
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three] at this
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three] at h00 h10 h20
    rw [h00, h10, h20] at this
    simp only [mul_one, mul_zero, add_zero] at this
    exact this
  have e1 := key _ (uniGL_zero_one_mem h) 0
  have hM20 : M.1 2 0 = 0 := by
    rw [uniGL_val] at e1
    simp at e1
    exact e1
  obtain ⟨t, ht⟩ := exists_trace_one h
  have e2 := key _ (uniGL_one_t_mem h ht) 0
  rw [uniGL_val] at e2
  simp [hM20] at e2
  exact ⟨e2, hM20⟩

omit [CharP K 2] in
theorem scalar_entry (c : Kˣ) (i k : Fin 3) :
    ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i k =
      if i = k then (c : K) else 0 := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]

omit [CharP K 2] in
theorem det_ne_zero_of_col {M : GL (Fin 3) K} (hM : M.1 0 0 = 0 ∧ M.1 1 0 = 0 ∧ M.1 2 0 = 0) : False := by
  have hdet : M.1.det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det (M : Matrix (Fin 3) (Fin 3) K)).1 M.isUnit
    exact this.ne_zero
  apply hdet
  refine Matrix.det_eq_zero_of_column_eq_zero 0 fun i => ?_
  fin_cases i
  · exact hM.1
  · exact hM.2.1
  · exact hM.2.2

theorem scalar_eq_one_of_conj {M u u' : GL (Fin 3) K} {c : Kˣ} (hu : u ∈ rtA n K)
    (hu' : u' ∈ rtA n K) (hrel : u' * GeneralLinearGroup.scalar (Fin 3) c = M * u * M⁻¹) : c = 1 := by
  obtain ⟨-, hu00, -, -, hu10, hu20, -⟩ := hu
  obtain ⟨-, hu'00, hu'11, hu'22, hu'10, hu'20, hu'21⟩ := hu'
  have hrel' : u' * GeneralLinearGroup.scalar (Fin 3) c * M = M * u := by
    calc u' * GeneralLinearGroup.scalar (Fin 3) c * M = M * u * M⁻¹ * M := by rw [hrel]
      _ = M * u := by group
  have e : ∀ i : Fin 3, (c : K) * (u'.1 i 0 * M.1 0 0 + u'.1 i 1 * M.1 1 0 + u'.1 i 2 * M.1 2 0) =
      M.1 i 0 := by
    intro i
    have := congrArg (fun A : GL (Fin 3) K => A.1 i 0) hrel'
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, scalar_entry] at this
    rw [hu00, hu10, hu20] at this
    simp at this
    linear_combination this
  by_contra hc1
  have hc1' : (c : K) - 1 ≠ 0 := by
    intro h0
    exact hc1 (Units.ext (by rw [Units.val_one]; linear_combination h0))
  have e2 := e 2
  have e1 := e 1
  have e0 := e 0
  simp only [hu'20, hu'21, hu'22, hu'10, hu'11, hu'00, zero_mul, one_mul, zero_add] at e2 e1 e0
  have v2 : M.1 2 0 = 0 := by
    have : ((c : K) - 1) * M.1 2 0 = 0 := by linear_combination e2
    exact (mul_eq_zero.1 this).resolve_left hc1'
  have v1 : M.1 1 0 = 0 := by
    have : ((c : K) - 1) * M.1 1 0 = 0 := by rw [v2] at e1; linear_combination e1
    exact (mul_eq_zero.1 this).resolve_left hc1'
  have v0 : M.1 0 0 = 0 := by
    have : ((c : K) - 1) * M.1 0 0 = 0 := by rw [v2, v1] at e0; linear_combination e0
    exact (mul_eq_zero.1 this).resolve_left hc1'
  exact det_ne_zero_of_col ⟨v0, v1, v2⟩

end Uni

section Lift

variable (h : UnitaryFieldData 2 n K)

local notation "PGL3" => ProjGenLinGroup (Fin 3) K

include h in
theorem normalizer_flag {M : GL (Fin 3) K}
    (hg : ProjGenLinGroup.mk M ∈ Subgroup.normalizer
      (((rtA n K).map ProjGenLinGroup.mk : Subgroup PGL3) : Set PGL3)) :
    M.1 1 0 = 0 ∧ M.1 2 0 = 0 := by
  have key : ∀ M : GL (Fin 3) K, ProjGenLinGroup.mk M ∈ Subgroup.normalizer
      (((rtA n K).map ProjGenLinGroup.mk : Subgroup PGL3) : Set PGL3) →
      ∀ u ∈ rtA n K, M * u * M⁻¹ ∈ rtA n K := by
    intro M hM u hu
    have hmem : ProjGenLinGroup.mk u ∈ (rtA n K).map ProjGenLinGroup.mk := ⟨u, hu, rfl⟩
    have h2 := (Subgroup.mem_normalizer_iff.1 hM (ProjGenLinGroup.mk u)).1 hmem
    obtain ⟨u', hu', hu'eq⟩ := h2
    have h3 : ProjGenLinGroup.mk u' = ProjGenLinGroup.mk (M * u * M⁻¹) := by
      rw [hu'eq]
      simp [map_mul, map_inv]
    obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.1 h3
    have hc1 := scalar_eq_one_of_conj hu hu' hc
    rw [hc1, map_one, mul_one] at hc
    rw [← hc]
    exact hu'
  have hM' := key M hg
  have hMinv : ProjGenLinGroup.mk M⁻¹ ∈ Subgroup.normalizer
      (((rtA n K).map ProjGenLinGroup.mk : Subgroup PGL3) : Set PGL3) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hg
  have hM'' := key M⁻¹ hMinv
  exact flag_of_conj h (fun u hu => by simpa using hM'' u hu)

include h in
theorem ut_of_flag {M : GL (Fin 3) K} (hM : M ∈ guA n K) (h10 : M.1 1 0 = 0) (h20 : M.1 2 0 = 0) :
    M.1 2 1 = 0 ∧ M.1 0 0 ≠ 0 ∧ M.1 1 1 ≠ 0 ∧ h.bar (M.1 1 1) * M.1 1 1 = 1 ∧
      h.bar (M.1 0 0) * M.1 2 2 = 1 := by
  have e02 : h.bar (M.1 0 0) * M.1 2 2 = 1 := by
    simpa [unitaryAntidiagonal, h10, h20] using guA_entry h hM 0 2
  have e01 : h.bar (M.1 0 0) * M.1 2 1 = 0 := by
    simpa [unitaryAntidiagonal, h10, h20] using guA_entry h hM 0 1
  have hσ0 : h.bar (M.1 0 0) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at e02
    exact zero_ne_one e02
  have h21 : M.1 2 1 = 0 := (mul_eq_zero.1 e01).resolve_left hσ0
  have e11 : h.bar (M.1 1 1) * M.1 1 1 = 1 := by
    have := guA_entry h hM 1 1
    simpa [unitaryAntidiagonal, h10, h20, h21] using this
  have hM11 : M.1 1 1 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e11
    exact zero_ne_one e11
  refine ⟨h21, ?_, hM11, e11, e02⟩
  intro h0
  apply hσ0
  rw [h0, map_zero]

end Lift

section Chi

variable (h : UnitaryFieldData 2 n K)

local notation "PGL3" => ProjGenLinGroup (Fin 3) K

include h in
theorem scalar_mem_guA {c : Kˣ} (hc : h.bar (c : K) * c = 1) :
    GeneralLinearGroup.scalar (Fin 3) c ∈ guA n K := by
  rw [mem_guA h]
  ext i j
  rw [gram_apply]
  fin_cases i <;> fin_cases j <;> simp [scalar_entry, unitaryAntidiagonal, hc]

variable (n K) in
@[expose] def IsLift (g : PGL3) (M : GL (Fin 3) K) : Prop :=
  M ∈ guA n K ∧ ProjGenLinGroup.mk M = g ∧ M.1 1 0 = 0 ∧ M.1 2 0 = 0

@[expose] def chiHat (M : GL (Fin 3) K) : K := M.1 0 0 * (M.1 1 1)⁻¹

omit [CharP K 2] in
theorem chiHat_mul_scalar (M : GL (Fin 3) K) (c : Kˣ) :
    chiHat (M * GeneralLinearGroup.scalar (Fin 3) c) = chiHat M := by
  unfold chiHat
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, scalar_entry]
  simp only [Fin.isValue, ite_true, mul_zero, add_zero, Fin.reduceEq, ite_false, zero_add]
  rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ c.ne_zero, mul_one]

omit [CharP K 2] in
theorem chiHat_mul {M N : GL (Fin 3) K} (hM : M.1 1 0 = 0 ∧ M.1 2 0 = 0 ∧ M.1 2 1 = 0)
    (hN : N.1 1 0 = 0 ∧ N.1 2 0 = 0 ∧ N.1 2 1 = 0) :
    chiHat (M * N) = chiHat M * chiHat N := by
  unfold chiHat
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, hM.1, hN.1,
    hN.2.1, hN.2.2, mul_zero, zero_mul, add_zero, zero_add]
  rw [mul_inv]
  ring

theorem chiHat_eq_of_isLift {g : PGL3} {M M' : GL (Fin 3) K} (hM : M ∈ guA n K ∧ ProjGenLinGroup.mk M = g)
    (hM' : ProjGenLinGroup.mk M' = g) : chiHat M = chiHat M' := by
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.1 (hM.2.trans hM'.symm)
  rw [← hc, chiHat_mul_scalar]

open Classical in
noncomputable def chi (g : PGL3) : K :=
  if hg : ∃ M, IsLift n K g M then chiHat (Classical.choose hg) else 1

theorem chi_eq {g : PGL3} {M : GL (Fin 3) K} (hM : IsLift n K g M) : chi (n := n) g = chiHat M := by
  have hex : ∃ M, IsLift n K g M := ⟨M, hM⟩
  rw [chi]
  split
  · next hg =>
    exact chiHat_eq_of_isLift ⟨(Classical.choose_spec hg).1, (Classical.choose_spec hg).2.1⟩ hM.2.1
  · next hg => exact absurd hex hg

theorem isLift_one : IsLift n K 1 1 := by
  refine ⟨one_mem _, rfl, ?_, ?_⟩ <;> simp

theorem isLift_mul {g g' : PGL3} {M M' : GL (Fin 3) K} (hM : IsLift n K g M)
    (hM' : IsLift n K g' M') : IsLift n K (g * g') (M * M') := by
  obtain ⟨hMg, hMk, h10, h20⟩ := hM
  obtain ⟨hMg', hMk', h10', h20'⟩ := hM'
  refine ⟨mul_mem hMg hMg', by rw [map_mul, hMk, hMk'], ?_, ?_⟩
  · simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, h10, h10', h20']
  · simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, h20, h10', h20']

include h in
theorem chi_mul {g g' : PGL3} {M M' : GL (Fin 3) K} (hM : IsLift n K g M)
    (hM' : IsLift n K g' M') : chi (n := n) (g * g') = chi (n := n) g * chi (n := n) g' := by
  rw [chi_eq (isLift_mul hM hM'), chi_eq hM, chi_eq hM']
  exact chiHat_mul ⟨hM.2.2.1, hM.2.2.2, (ut_of_flag h hM.1 hM.2.2.1 hM.2.2.2).1⟩
    ⟨hM'.2.2.1, hM'.2.2.2, (ut_of_flag h hM'.1 hM'.2.2.1 hM'.2.2.2).1⟩

theorem chi_one : chi (n := n) (1 : PGL3) = 1 := by
  rw [chi_eq (isLift_one (n := n) (K := K)), chiHat]
  simp

include h in
theorem mem_map_rtA_of_chi {g : PGL3} {M : GL (Fin 3) K} (hM : IsLift n K g M)
    (hχ : chi (n := n) g = 1) : g ∈ (rtA n K).map ProjGenLinGroup.mk := by
  rw [chi_eq hM] at hχ
  obtain ⟨hMg, hMk, h10, h20⟩ := hM
  obtain ⟨h21, h00ne, h11ne, hN11, hN00⟩ := ut_of_flag h hMg h10 h20
  have h00 : M.1 0 0 = M.1 1 1 := by
    have : M.1 0 0 * (M.1 1 1)⁻¹ = 1 := hχ
    exact (mul_inv_eq_one₀ h11ne).1 this
  have hσb : h.bar (M.1 1 1) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hN11
    exact zero_ne_one hN11
  have h22 : M.1 2 2 = M.1 1 1 := by
    rw [h00] at hN00
    exact mul_left_cancel₀ hσb (hN00.trans hN11.symm)
  set b : K := M.1 1 1 with hb
  have h11 : M.1 1 1 ≠ 0 := h11ne
  let c : Kˣ := Units.mk0 b⁻¹ (inv_ne_zero h11ne)
  have hc : h.bar (c : K) * c = 1 := by
    show h.bar b⁻¹ * b⁻¹ = 1
    rw [map_inv₀, ← mul_inv, hN11, inv_one]
  have hscal := scalar_mem_guA h hc
  refine ⟨M * GeneralLinearGroup.scalar (Fin 3) c, ⟨mul_mem hMg hscal, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, scalar_entry]
    simp [h00, hb, c, h11]
  · simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, scalar_entry]
    simp [hb, c, h11]
  · simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, scalar_entry]
    simp [h22, hb, c, h11]
  · simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, scalar_entry]
    simp [h10]
  · simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, scalar_entry]
    simp [h20]
  · simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, scalar_entry]
    simp [h21]
  · rw [map_mul, ProjGenLinGroup.mk_scalar, mul_one]
    exact hMk

end Chi

section Syl

variable (h : UnitaryFieldData 2 n K)

local notation "PGL3" => ProjGenLinGroup (Fin 3) K

variable (n K) in
@[expose] noncomputable def pguA : Subgroup (ProjGenLinGroup (Fin 3) K) :=
  (guA n K).map ProjGenLinGroup.mk

variable (n K) in
@[expose] noncomputable def q0A : Subgroup (ProjGenLinGroup (Fin 3) K) :=
  (rtA n K).map ProjGenLinGroup.mk

theorem rtA_le_guA : rtA n K ≤ guA n K := fun _ hM => hM.1

theorem q0A_le_pguA : q0A n K ≤ pguA n K := Subgroup.map_mono rtA_le_guA

theorem rtA_pow_four {M : GL (Fin 3) K} (hM : M ∈ rtA n K) : M ^ 4 = 1 := by
  obtain ⟨-, h00, h11, h22, h10, h20, h21⟩ := hM
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  set N : Matrix (Fin 3) (Fin 3) K := M.1 - 1 with hN
  have hMN : M.1 = 1 + N := by rw [hN]; abel
  have hN3 : N ^ 3 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, hN, Matrix.sub_apply, Matrix.one_apply,
        h00, h11, h22, h10, h20, h21]
  have hN4 : N ^ 4 = 0 := by rw [pow_succ, hN3, zero_mul]
  have hc : Commute (1 : Matrix (Fin 3) (Fin 3) K) N := Commute.one_left N
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := add_pow_char_pow_of_commute (R := Matrix (Fin 3) (Fin 3) K) 2 2 hc
  rw [hMN]
  simpa [hN4] using h2

theorem isPGroup_two_q0A : IsPGroup 2 ↥((q0A n K).subgroupOf (pguA n K)) := by
  rintro ⟨⟨y, hy⟩, hyQ⟩
  obtain ⟨u, hu, hmk⟩ := hyQ
  refine ⟨2, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  show y ^ 2 ^ 2 = 1
  have hmk' : ProjGenLinGroup.mk u = y := hmk
  rw [← hmk', ← map_pow, show (2 : ℕ) ^ 2 = 4 by norm_num, rtA_pow_four hu, map_one]

omit [CharP K 2] in
theorem eq_one_of_pow_two_pow [Finite K] (h : UnitaryFieldData 2 n K) (t : K) (k : ℕ)
    (ht : t ^ 2 ^ k = 1) : t = 1 := by
  have hne : t ≠ 0 := by
    rintro rfl
    simp at ht
  have : Fintype K := Fintype.ofFinite K
  have h1 : t ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one t hne
  rw [← Nat.card_eq_fintype_card, h.card] at h1
  have hodd : Odd (2 ^ (2 * n) - 1) := by
    have hpos : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
    have hn := h.one_le
    have heven : Even (2 ^ (2 * n)) := Nat.even_pow.2 ⟨even_two, by omega⟩
    exact Nat.Even.sub_odd hpos heven odd_one
  have hcop : Nat.Coprime (2 ^ k) (2 ^ (2 * n) - 1) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
      (fun hd => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd)))
  have h3 : t ^ Nat.gcd (2 ^ k) (2 ^ (2 * n) - 1) = 1 := pow_gcd_eq_one.2 ⟨ht, h1⟩
  rwa [hcop.gcd_eq_one, pow_one] at h3

include h in
theorem model_sylow_cyclic [Finite K] :
    ∃ S : Sylow 2 ↥(pguA n K), (S : Subgroup ↥(pguA n K)) = (q0A n K).subgroupOf (pguA n K) ∧
      ∀ R : Subgroup ↥(pguA n K),
        R ≤ Subgroup.normalizer
          (((q0A n K).subgroupOf (pguA n K) : Subgroup ↥(pguA n K)) : Set ↥(pguA n K)) →
        IsPGroup 3 ↥R → IsCyclic ↥R := by
  have : Finite PGL3 := Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  set P := pguA n K with hP
  set Q0 : Subgroup ↥P := (q0A n K).subgroupOf P with hQ0
  have hQmap : Q0.map P.subtype = q0A n K := Subgroup.map_subgroupOf_eq_of_le q0A_le_pguA
  have hlift : ∀ g : ↥(Subgroup.normalizer (Q0 : Set ↥P)),
      ∃ M, IsLift n K ((g : ↥P) : PGL3) M := by
    intro g
    have hgn : ((g : ↥P) : PGL3) ∈ Subgroup.normalizer ((q0A n K : Subgroup PGL3) : Set PGL3) := by
      rw [← hQmap]
      exact mem_normalizer_map_subtype.2 g.2
    obtain ⟨M, hM, hmk⟩ := (g : ↥P).2
    have hmk' : ProjGenLinGroup.mk M = ((g : ↥P) : PGL3) := hmk
    refine ⟨M, hM, hmk', ?_⟩
    exact normalizer_flag h (n := n) (M := M) (by rw [hmk']; exact hgn)
  let φ : ↥(Subgroup.normalizer (Q0 : Set ↥P)) →* K :=
    { toFun := fun g => chi (n := n) ((g : ↥P) : PGL3)
      map_one' := chi_one
      map_mul' := fun g g' => by
        obtain ⟨M, hM⟩ := hlift g
        obtain ⟨M', hM'⟩ := hlift g'
        exact chi_mul h hM hM' }
  have hφ : ∀ x : ↥(Subgroup.normalizer (Q0 : Set ↥P)), φ x = 1 → (x : ↥P) ∈ Q0 := by
    intro x hx
    obtain ⟨M, hM⟩ := hlift x
    exact mem_map_rtA_of_chi h hM hx
  obtain ⟨⟨S, hS⟩, hcyc⟩ := sylow_and_cyclic_of_hom isPGroup_two_q0A (F := K)
    (fun t k ht => eq_one_of_pow_two_pow h t k ht) φ hφ
  exact ⟨S, hS, hcyc⟩

end Syl

end Model

end CFSG.Quasithin.R3c6
