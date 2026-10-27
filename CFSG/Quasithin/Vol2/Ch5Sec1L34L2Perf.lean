module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs
public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
  (even_SL2_full_automorphism_semilinear_model)
open scoped MatrixGroups

section Matrices

variable (F : Type*) [Field F] [CharP F 2]

@[expose] def slOrderThree : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 1], by
    rw [Matrix.det_fin_two_of]
    simp [CharTwo.neg_eq]⟩

theorem slOrderThree_pow_three : slOrderThree F ^ 3 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  fin_cases i <;> fin_cases j <;>
    simp [slOrderThree, pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination h2

theorem slOrderThree_ne_scalar (r : F) :
    Matrix.scalar (Fin 2) r ≠ ((slOrderThree F : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [slOrderThree] at this

theorem three_dvd_card_psl_two [Finite F] :
    3 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F := QuotientGroup.mk (slOrderThree F)
    with hx
  have h3 : x ^ 3 = 1 := by
    rw [hx, ← QuotientGroup.mk_pow, slOrderThree_pow_three, QuotientGroup.mk_one]
  have h1 : x ≠ 1 := by
    rw [hx, Ne, QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff]
    rintro ⟨r, -, hr⟩
    exact slOrderThree_ne_scalar F r hr
  rw [← orderOf_eq_prime h3 h1]
  exact orderOf_dvd_natCard x

theorem three_dvd_card_pgl_two [Finite F] :
    3 ∣ Nat.card (Matrix.ProjGenLinGroup (Fin 2) F) :=
  (three_dvd_card_psl_two F).trans (Subgroup.card_dvd_of_injective _
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective)

end Matrices

section Dickson

theorem isSolvable_of_isCyclic' {H : Type*} [Group H] (h : IsCyclic H) : Group.IsSolvable H := by
  let _ : CommGroup H := IsCyclic.commGroup
  exact Group.isSolvable_of_comm fun a b => mul_comm a b

theorem isSolvable_or_three_dvd_card {K : Type*} [Field K]
    [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) :
    Group.IsSolvable ↥H ∨ 3 ∣ Nat.card ↥H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.Glauberman.Dickson.dickson_psl2_subgroup_list hK H with
    ⟨m, -, -, hel⟩ | ⟨z, -, -, hcyc⟩ | ⟨z, hz2, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, -, -, -, -, E, C, hEn, hEel, -, hCcyc, -, -, hsup, -, -⟩ | ⟨m, -, ⟨e⟩⟩ | ⟨m, -, ⟨e⟩⟩
  ·
    left
    exact Group.isSolvable_of_comm fun a b => hel.toIsMulCommutative.is_comm.comm a b
  ·
    exact Or.inl (isSolvable_of_isCyclic' hcyc)
  ·
    left
    have : NeZero z := ⟨by omega⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup z
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  ·
    right
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  ·
    right
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  ·
    right
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  ·
    left
    have hEsolv : Group.IsSolvable ↥E :=
      Group.isSolvable_of_comm fun a b => hEel.toIsMulCommutative.is_comm.comm a b
    have hCcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
      intro a ha b hb
      let _ : CommGroup ↥C := IsCyclic.commGroup
      exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥C) ⟨b, hb⟩)
    have hmem : ∀ h : ↥H, ∃ c ∈ C, (QuotientGroup.mk h : ↥H ⧸ E) = QuotientGroup.mk c := by
      intro h
      have hh : h ∈ ((E ⊔ C : Subgroup ↥H) : Set ↥H) := by rw [hsup]; trivial
      rw [Subgroup.normal_mul] at hh
      obtain ⟨a, ha, c, hc, rfl⟩ := hh
      refine ⟨c, hc, ?_⟩
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff a).mpr ha, one_mul]
    have hQsolv : Group.IsSolvable (↥H ⧸ E) := by
      refine Group.isSolvable_of_comm fun a b => ?_
      induction a using QuotientGroup.induction_on with
      | H a =>
        induction b using QuotientGroup.induction_on with
        | H b =>
          obtain ⟨c, hc, hac⟩ := hmem a
          obtain ⟨d, hd, hbd⟩ := hmem b
          rw [hac, hbd, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hCcomm c hc d hd]
    exact Group.isSolvable_of_ker_le_range E.subtype (QuotientGroup.mk' E)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  ·
    right
    rw [Nat.card_congr e.toEquiv]
    exact three_dvd_card_psl_two (GaloisField 2 m)
  ·
    right
    rw [Nat.card_congr e.toEquiv]
    exact three_dvd_card_pgl_two (GaloisField 2 m)

end Dickson

theorem l2PerfectThreePrimeFact : L2PerfectThreePrimeFact := by
  intro X _ n hX Y _ _ φ hY h3
  classical
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  have : CharP K 2 := CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card hK
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hK
      have := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K)
      omega
    · exact h0
  let e' : X ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    e.trans (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL K)
  let φ' : Y →* MulAut (Matrix.SpecialLinearGroup (Fin 2) K) :=
    (MulAut.congr e').toMonoidHom.comp φ
  suffices h : φ' = 1 by
    refine MonoidHom.ext fun y => (MulAut.congr e').injective ?_
    have := DFunLike.congr_fun h y
    rw [MonoidHom.one_apply, map_one]
    exact this
  obtain ⟨-, -, hcyc, -, -⟩ := even_SL2_full_automorphism_semilinear_model hn hK
  have hinn : ∀ y, φ' y ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (Matrix.SpecialLinearGroup (Fin 2) K) := by
    let π : MulAut (Matrix.SpecialLinearGroup (Fin 2) K) →*
        Outer (Matrix.SpecialLinearGroup (Fin 2) K) := QuotientGroup.mk' _
    let _ : CommGroup (Outer (Matrix.SpecialLinearGroup (Fin 2) K)) := IsCyclic.commGroup
    have hker : commutator Y ≤ (π.comp φ').ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    intro y
    have hy : y ∈ (π.comp φ').ker := hker (hY ▸ Subgroup.mem_top y)
    rw [MonoidHom.mem_ker] at hy
    exact (QuotientGroup.eq_one_iff _).mp hy
  have hcen : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center,
      CFSG.LocalAnalysis.ComponentInitial.LinearCover.scalars_two_eq_bot]
  have hinj : Function.Injective
      (MulAut.conj : Matrix.SpecialLinearGroup (Fin 2) K →*
        MulAut (Matrix.SpecialLinearGroup (Fin 2) K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hcen]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun f : MulAut (Matrix.SpecialLinearGroup (Fin 2) K) => f g) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * x = x * g * x⁻¹ * x := by rw [this]
      _ = x * g := by group
  let ψ : Y →* Matrix.SpecialLinearGroup (Fin 2) K :=
    (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (φ'.codRestrict _ hinn)
  have hψ : ∀ y, MulAut.conj (ψ y) = φ' y := fun y => by
    have := MonoidHom.apply_ofInjective_symm hinj (φ'.codRestrict _ hinn y)
    exact this
  let ι : Matrix.SpecialLinearGroup (Fin 2) K →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    QuotientGroup.mk' _
  have hι : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hcen
  let ψ' := ι.comp ψ
  have hperf : commutator ↥ψ'.range = ⊤ := by
    have h1 := map_commutator_eq Y ψ'.rangeRestrict
    rw [hY, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr ψ'.rangeRestrict_surjective]
      at h1
    rw [commutator_def, ← h1]
  have hrange : ψ'.range = ⊥ := by
    by_contra hne
    have : Nontrivial ↥ψ'.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    rcases isSolvable_or_three_dvd_card hK ψ'.range with hs | h3'
    · have hP : Group.IsPerfect ↥ψ'.range := ⟨hperf⟩
      exact Group.IsPerfect.not_isSolvable ↥ψ'.range hs
    · exact h3 (h3'.trans (Subgroup.card_range_dvd ψ'))
  have hψ1 : ψ = 1 := MonoidHom.ext fun y => hι (by
    have : ψ' y ∈ ψ'.range := ⟨y, rfl⟩
    rw [hrange, Subgroup.mem_bot] at this
    rw [MonoidHom.one_apply, map_one]
    exact this)
  refine MonoidHom.ext fun y => ?_
  rw [← hψ y, hψ1, MonoidHom.one_apply, map_one, MonoidHom.one_apply]

end CFSG.Quasithin.H13
