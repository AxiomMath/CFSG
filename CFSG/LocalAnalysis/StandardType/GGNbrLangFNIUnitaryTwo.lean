module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA
public import CFSG.Models.PGLSimple
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
public import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryComponent
public import CFSG.Timmesfeld.RankOne.SL2
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOne

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial Matrix
open scoped Matrix

theorem unitaryTwo_trace_surjective {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) (z : h.fixedField) :
    ∃ g : LargeEvenSUGroup (Fin 2) K (2 ^ f),
      Matrix.trace (g.val : Matrix (Fin 2) (Fin 2) K) = (z : K) := by
  classical
  obtain ⟨a, ha⟩ := h.traceLin_surjective z
  have htrace : a + h.bar a = (z : K) := by
    simpa [UnitaryFieldData.trace] using congrArg Subtype.val ha
  have hfix : h.bar (1 + a * h.bar a) = 1 + a * h.bar a := by
    rw [map_add, map_one, map_mul, h.bar_bar]
    ring
  obtain ⟨b, hb⟩ := h.normHom_surjective ⟨1 + a * h.bar a, hfix⟩
  have hb' : b * h.bar b = 1 + a * h.bar a := by
    simpa [UnitaryFieldData.norm] using congrArg Subtype.val hb
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  let A : Matrix (Fin 2) (Fin 2) K := !![a, b; h.bar b, h.bar a]
  have hdet : A.det = 1 := by
    simp only [A, Matrix.det_fin_two]
    change a * h.bar a - b * h.bar b = 1
    linear_combination -hb' - h2
  let g : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [hdet]; exact one_ne_zero)
  have hunit : (A.map (· ^ (2 ^ f)))ᵀ * A = 1 := by
    have hmap : A.map (· ^ (2 ^ f)) = A.map h.bar := by
      ext i j
      exact (h.bar_apply (A i j)).symm
    rw [hmap]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.mul_apply, Fin.sum_univ_two, h.bar_bar]
    · linear_combination hb' + h2 * (a * h.bar a)
    · linear_combination h2 * (b * h.bar a)
    · linear_combination h2 * (a * h.bar b)
    · linear_combination hb' + h2 * (a * h.bar a)
  have hmem : g ∈ LargeEvenSUGroup (Fin 2) K (2 ^ f) := by
    exact Subgroup.subset_closure ⟨hdet, hunit⟩
  refine ⟨⟨g, hmem⟩, ?_⟩
  simpa [g, A, Matrix.trace, Fin.sum_univ_two] using htrace


theorem unitaryTwo_trace_map_ringEquiv {K : Type} [Field K] (τ : K ≃+* K)
    (M : Matrix (Fin 2) (Fin 2) K) :
    Matrix.trace (M.map τ) = τ (Matrix.trace M) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, map_sum]

theorem unitaryTwo_trace_gl_conj {K : Type} [Field K] (D : GL (Fin 2) K)
    (M : Matrix (Fin 2) (Fin 2) K) :
    Matrix.trace ((D : Matrix (Fin 2) (Fin 2) K) * M *
      (((D⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) =
      Matrix.trace M :=
  Matrix.trace_units_conj D M

theorem unitaryTwo_fieldAction_not_inner {f : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (h : UnitaryFieldData 2 f K)
    (f' : MulAut ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f)))
    {B : GL (Fin 2) K} (hB : B ∈ LargeEvenGUSet (Fin 2) K (2 ^ f))
    {τ : K ≃+* K}
    (hpoint : ∀ c : ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f)),
      (f' c : GL (Fin 2) K) =
        B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut τ
          (c : GL (Fin 2) K) * B⁻¹)
    (z : h.fixedField) (hz : τ (z : K) ≠ (z : K)) :
    ¬ ∃ C : ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f)),
      f' = MulAut.conj C := by
  classical
  rintro ⟨C, hC⟩
  obtain ⟨g, hgtr⟩ := unitaryTwo_trace_surjective h z
  have haction : Matrix.trace (((f' g : ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f))) :
      GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = τ (z : K) := by
    rw [hpoint g]
    rw [show ((B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut τ
        (g : GL (Fin 2) K) * B⁻¹ : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) =
      (B : Matrix (Fin 2) (Fin 2) K) *
        (((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut τ
          (g : GL (Fin 2) K) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
        (((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) from rfl]
    rw [unitaryTwo_trace_gl_conj]
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut]
    rw [unitaryTwo_trace_map_ringEquiv, hgtr]
  have hinner : Matrix.trace (((f' g : ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f))) :
      GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = (z : K) := by
    have hcongr : f' g = MulAut.conj C g := by
      rw [hC]
    rw [hcongr, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_inv]
    rw [unitaryTwo_trace_gl_conj, hgtr]
  exact hz (haction.symm.trans hinner)


theorem unitaryTwo_odd_card_units {F : Type} [Field F] [Finite F] [CharP F 2] :
    Odd (Nat.card Fˣ) := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨k, -, hk⟩ := FiniteField.card F 2
  rw [Nat.card_units, Nat.card_eq_fintype_card, hk]
  obtain ⟨j, hj⟩ : ∃ j, (k : ℕ) = j + 1 := ⟨(k : ℕ) - 1, by have := k.pos; omega⟩
  rw [hj, pow_succ]
  have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  exact ⟨2 ^ j - 1, by omega⟩

theorem unitaryTwo_largeEvenSL_two_perfect {F : Type} [Field F] [Finite F]
    (h4card : 4 ≤ Nat.card F) :
    Group.IsPerfect ↥(LargeEvenSLGroup (Fin 2) F) := by
  letI : Fintype F := Fintype.ofFinite F
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have hle : 4 ≤ (Finset.univ : Finset F).card := by
      simpa [Finset.card_univ, Nat.card_eq_fintype_card] using h4card
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := Finset.univ) (n := 4) hle
    exact ⟨s, hs⟩
  have hperfSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.LinearGroups.special_linear_isPerfect (n := 2) (K := F) (by norm_num) (Or.inr h4)
  let eSL : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(LargeEvenSLGroup (Fin 2) F) :=
    InnerDiagA.slEquiv 1 F
  exact Group.IsPerfect.ofSurjective (f := eSL.toMonoidHom) eSL.surjective

theorem unitaryTwo_largeEvenProj_two_simple {F : Type} [Field F] [Finite F]
    (hcard4 : 4 ≤ Nat.card F) :
    IsSimpleGroup (LargeEvenProj (LargeEvenSLGroup (Fin 2) F)) := by
  rw [CFSG.Assembly.largeEvenSLGroup_eq_statedSL 2]
  change IsSimpleGroup (CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F))
  exact CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL F (by norm_num)
    (by omega) (by omega)

theorem unitaryTwo_largeEvenProj_two_noncomm {F : Type} [Field F] [Finite F]
    (hcard4 : 4 ≤ Nat.card F) :
    ∃ a b : LargeEvenProj (LargeEvenSLGroup (Fin 2) F), a * b ≠ b * a := by
  have hperf := unitaryTwo_largeEvenSL_two_perfect hcard4
  have hperfR : Group.IsPerfect (LargeEvenProj (LargeEvenSLGroup (Fin 2) F)) :=
    Group.IsPerfect.ofSurjective (f := LargeEvenProjMk (LargeEvenSLGroup (Fin 2) F))
      (QuotientGroup.mk'_surjective _)
  have hsimple := unitaryTwo_largeEvenProj_two_simple hcard4
  haveI : Nontrivial (LargeEvenProj (LargeEvenSLGroup (Fin 2) F)) := hsimple.toNontrivial
  have hnc : ¬ IsMulCommutative (LargeEvenProj (LargeEvenSLGroup (Fin 2) F)) :=
    Group.IsPerfect.not_isMulCommutative _
  by_contra h
  exact hnc ⟨⟨fun a b => by
    by_contra hab
    exact h ⟨a, b, hab⟩⟩⟩

theorem unitaryTwo_matConjImage_subset_inn {F : Type} [Field F] [Finite F] [CharP F 2] :
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) F)) Set.univ ⊆
      LargeEvenInnSet (LargeEvenProj (LargeEvenSLGroup (Fin 2) F)) :=
  CFSG.StandardType.matConjImage_gl_subset_inn (K := F) (d := 2)
    (unitaryTwo_odd_card_units (F := F)).coprime_two_right

theorem unitaryTwo_largeEvenMarking_PSL2_not_inner {F : Type} [Field F] [Finite F]
    [CharP F 2] {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f)
    (g : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) F)))
    (hg : ¬ ∃ C : LargeEvenProj (LargeEvenSLGroup (Fin 2) F), g = MulAut.conj C) :
    LargeEvenMarking (LargeEvenProj (LargeEvenSLGroup (Fin 2) F))
      (fun _ _ _ I _ θ => ¬ ∃ φ ∈ Subgroup.closure I,
        LargeEvenInduces θ (fun j k => k = g j) φ) := by
  classical
  let L := LargeEvenSLGroup (Fin 2) F
  have hcard4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hperfL : Group.IsPerfect ↥L := by
    rw [show L = LargeEvenSLGroup (Fin 2) F from rfl]
    exact unitaryTwo_largeEvenSL_two_perfect (F := F) hcard4
  have hperfR : commutator (LargeEvenProj L) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := LargeEvenProjMk L)
      (QuotientGroup.mk'_surjective _)).commutator_eq_top
  have hsimpleR : IsSimpleGroup (LargeEvenProj L) := by
    change IsSimpleGroup (LargeEvenProj (LargeEvenSLGroup (Fin 2) F))
    exact unitaryTwo_largeEvenProj_two_simple (F := F) hcard4
  have hnonabR : ∃ a b : LargeEvenProj L, a * b ≠ b * a := by
    change ∃ a b : LargeEvenProj (LargeEvenSLGroup (Fin 2) F), a * b ≠ b * a
    exact unitaryTwo_largeEvenProj_two_noncomm (F := F) hcard4
  have hcenterR : Subgroup.center (LargeEvenProj L) = ⊥ := by
    haveI : Group.IsPerfect (LargeEvenProj L) := ⟨hperfR⟩
    rcases (inferInstance : (Subgroup.center (LargeEvenProj L)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hcomm : IsMulCommutative (LargeEvenProj L) :=
        ⟨⟨fun a b => Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a⟩⟩
      exact (Group.IsPerfect.not_isMulCommutative (LargeEvenProj L)) hcomm
  let θ : LargeEvenProj L ⧸ Subgroup.center (LargeEvenProj L) ≃* LargeEvenProj L :=
    (QuotientGroup.quotientMulEquivOfEq hcenterR).trans (QuotientGroup.quotientBot)
  have hIinn : LargeEvenMatConjImage (LargeEvenProjMk L) Set.univ ⊆
      LargeEvenInnSet (LargeEvenProj L) := by
    change LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) F)) Set.univ ⊆
      LargeEvenInnSet (LargeEvenProj (LargeEvenSLGroup (Fin 2) F))
    exact unitaryTwo_matConjImage_subset_inn (F := F)
  have hneg : ¬ ∃ φ ∈ Subgroup.closure (LargeEvenMatConjImage (LargeEvenProjMk L) Set.univ),
      LargeEvenInduces θ (fun j k : LargeEvenProj L => k = g j) φ := by
    rintro ⟨φ, hφmem, hφind⟩
    have hφinn : φ ∈ LargeEvenInnSet (LargeEvenProj L) := by
      have hclosure : Subgroup.closure (LargeEvenMatConjImage (LargeEvenProjMk L) Set.univ) ≤
          (MulAut.conj : LargeEvenProj L →* MulAut (LargeEvenProj L)).range :=
        (Subgroup.closure_le _).mpr (fun ψ hψ => hIinn hψ)
      exact hclosure hφmem
    obtain ⟨r, rfl⟩ := hφinn
    refine hg ⟨r, ?_⟩
    apply MulEquiv.ext
    intro x
    have hx := hφind x (g x) rfl
    have hq : (QuotientGroup.quotientBot (G := LargeEvenProj L))
        (QuotientGroup.mk x) = x := by
      change (QuotientGroup.kerLift (MonoidHom.id (LargeEvenProj L)))
        (QuotientGroup.mk x) = x
      rw [QuotientGroup.kerLift_mk]
      rfl
    have hθ (y : LargeEvenProj L) : θ (QuotientGroup.mk y) = y := by
      change (QuotientGroup.quotientBot (G := LargeEvenProj L))
        ((QuotientGroup.quotientMulEquivOfEq hcenterR) (QuotientGroup.mk y)) = y
      rw [QuotientGroup.quotientMulEquivOfEq_mk]
      change (QuotientGroup.kerLift (MonoidHom.id (LargeEvenProj L)))
        (QuotientGroup.mk y) = y
      rw [QuotientGroup.kerLift_mk]
      rfl
    change g x = r * x * r⁻¹
    simpa [MulAut.conj_apply, hθ] using hx.symm
  refine ⟨hperfR, ⟨⟨.A, 1, f⟩, ?_, ?_⟩⟩
  · simp only [LargeEvenInLambda2]
    exact ⟨by omega, ⟨le_rfl, by omega⟩⟩
  · simp only [LargeEvenRawDatum]
    refine ⟨F, inferInstance, inferInstance, hF, ?_⟩
    exact ⟨hsimpleR, hnonabR, θ, hneg⟩


theorem unitaryTwo_fieldAction_oneMarking {f : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (f' : MulAut ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f)))
    {B : GL (Fin 2) K} (hB : B ∈ LargeEvenGUSet (Fin 2) K (2 ^ f))
    {τ : K ≃+* K}
    (hpoint : ∀ c : ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f)),
      (f' c : GL (Fin 2) K) =
        B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut τ
          (c : GL (Fin 2) K) * B⁻¹)
    (z : h.fixedField) (hz : τ (z : K) ≠ (z : K)) :
    LargeEvenMarking ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f))
      (fun _ _ _ I _ θ => ¬ ∃ φ ∈ Subgroup.closure I,
        LargeEvenInduces θ
          (fun j k : ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f)) => k = f' j) φ) := by
  classical
  have hf'not := unitaryTwo_fieldAction_not_inner h f' hB hpoint z hz
  obtain ⟨F, hFfield, hFfin, hFcard, ⟨eSL⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.nonempty_sl2_mulEquiv_unitarySU_two
      (p := 2) (f := f) h
  letI : Field F := hFfield
  letI : Finite F := hFfin
  letI : Fintype F := Fintype.ofFinite F
  have hFcard' : Fintype.card F = 2 ^ f := by
    simpa [Nat.card_eq_fintype_card] using hFcard
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hFcard'
  let SU := LargeEvenSUGroup (Fin 2) K (2 ^ f)
  let eSU0 : ↥SU ≃* Matrix.SpecialLinearGroup (Fin 2) F := eSL.symm
  let L := LargeEvenSLGroup (Fin 2) F
  let eL : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥L := InnerDiagA.slEquiv 1 F
  have hcenterSL : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ :=
    CFSG.Timmesfeld.RankOne.center_SL2_eq_bot F
  have hcenterL : Subgroup.center ↥L = ⊥ := by
    rw [← Subgroup.map_center_eq eL, hcenterSL, Subgroup.map_bot]
  let Z0 := (LargeEvenScalars (Fin 2) F).subgroupOf L
  have hZ0le : Z0 ≤ Subgroup.center ↥L := by
    intro A hA
    rw [Subgroup.mem_center_iff]
    intro B
    apply Subtype.ext
    have hA' : (A : GL (Fin 2) F) ∈ LargeEvenScalars (Fin 2) F :=
      Subgroup.mem_subgroupOf.mp hA
    have hA'' : (A : GL (Fin 2) F) ∈ (Matrix.GeneralLinearGroup.scalar (Fin 2)).range := by
      simpa [largeEvenScalars_def] using hA'
    have hcenter : (A : GL (Fin 2) F) ∈ Subgroup.center (GL (Fin 2) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hA''
    exact Subgroup.mem_center_iff.mp hcenter (B : GL (Fin 2) F)
  have hZ0 : Z0 = ⊥ := le_antisymm (by simpa [hcenterL] using hZ0le) bot_le
  let q : ↥L →* LargeEvenProj L := LargeEvenProjMk L
  have hqker : q.ker = Z0 := QuotientGroup.ker_mk' Z0
  have hqinj : Function.Injective q := by
    rw [← MonoidHom.ker_eq_bot_iff, hqker, hZ0]
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective Z0
  let eLR : ↥L ≃* LargeEvenProj L := MulEquiv.ofBijective q ⟨hqinj, hqsurj⟩
  let e : ↥SU ≃* LargeEvenProj L := eSU0.trans (eL.trans eLR)
  let g : MulAut (LargeEvenProj L) := MulAut.congr e f'
  have hg : ¬ ∃ C : LargeEvenProj L, g = MulAut.conj C := by
    rintro ⟨C, hC⟩
    apply hf'not
    refine ⟨e.symm C, ?_⟩
    apply MulEquiv.ext
    intro x
    apply e.injective
    have hcongr : e (f' x) = g (e x) := by simp [g, MulAut.congr_apply]
    rw [hcongr, hC, MulAut.conj_apply]
    simp
  have hmarkR := unitaryTwo_largeEvenMarking_PSL2_not_inner
    (F := F) hFcard hf g hg
  refine largeEvenMarking_congr e ?_ hmarkR
  intro lab R' _ I F' θ hθ
  rintro ⟨φ, hφ, hindSU⟩
  have hrel : ∀ j k : ↥SU, (k = f' j) ↔
      (e k = g (e j)) := by
    intro j k
    have hcongr : g (e j) = e (f' j) := by simp [g, MulAut.congr_apply]
    rw [hcongr]
    exact e.injective.eq_iff.symm
  exact hθ ⟨φ, hφ, (largeEvenInduces_congr_equiv e θ
    (fun j k : ↥SU => k = f' j)
    (fun y y' : LargeEvenProj L => y' = g y) hrel φ).1 hindSU⟩


theorem unitaryTwo_two_le_f_of_fixedField {f : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (h : UnitaryFieldData 2 f K) (z : h.fixedField) {τ : K ≃+* K}
    (hz : τ (z : K) ≠ (z : K)) : 2 ≤ f := by
  by_contra hfnot
  have hf1 : 1 ≤ f := by
    have hpow := h.one_lt_pow
    by_contra hf0
    have hfzero : f = 0 := by omega
    rw [hfzero, pow_zero] at hpow
    omega
  have hf_eq : f = 1 := by omega
  letI : Fintype h.fixedField := Fintype.ofFinite h.fixedField
  have hcard2 : Nat.card h.fixedField = 2 := by
    rw [h.card_fixedField, hf_eq, pow_one]
  have hcard2' : Fintype.card h.fixedField = 2 := by
    simpa [Nat.card_eq_fintype_card] using hcard2
  have hz2 : z ^ 2 = z := by
    have hpow := FiniteField.pow_card (K := h.fixedField) z
    simpa [hcard2'] using hpow
  have hzprod : z * (z - 1) = 0 := by
    calc z * (z - 1) = z ^ 2 - z := by ring
      _ = 0 := by rw [hz2, sub_self]
  have hz01 : z = 0 ∨ z = 1 := by
    rcases mul_eq_zero.mp hzprod with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  rcases hz01 with rfl | rfl
  · exact hz (by simp)
  · exact hz (by simp)

theorem unitaryTwo_fieldAction_oneMarking_no_hf {f : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)
    (f' : MulAut ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f)))
    {B : GL (Fin 2) K} (hB : B ∈ LargeEvenGUSet (Fin 2) K (2 ^ f))
    {τ : K ≃+* K}
    (hpoint : ∀ c : ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f)),
      (f' c : GL (Fin 2) K) =
        B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut τ
          (c : GL (Fin 2) K) * B⁻¹)
    (z : h.fixedField) (hz : τ (z : K) ≠ (z : K)) :
    LargeEvenMarking ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f))
      (fun _ _ _ I _ θ => ¬ ∃ φ ∈ Subgroup.closure I,
        LargeEvenInduces θ
          (fun j k : ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f)) => k = f' j) φ) :=
  unitaryTwo_fieldAction_oneMarking h
    (unitaryTwo_two_le_f_of_fixedField h z hz) f' hB hpoint z hz



theorem unitaryTwo_fieldAction_allMarkings {f : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (h : UnitaryFieldData 2 f K)
    (f' : MulAut ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f)))
    {B : GL (Fin 2) K} (hB : B ∈ LargeEvenGUSet (Fin 2) K (2 ^ f))
    {τ : K ≃+* K}
    (hpoint : ∀ c : ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f)),
      (f' c : GL (Fin 2) K) =
        B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut τ
          (c : GL (Fin 2) K) * B⁻¹)
    (z : h.fixedField) (hz : τ (z : K) ≠ (z : K)) :
    GGMarkingAll (K := ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f)))
      fun _ _ _ I _ θ => kgInducedAut θ f' ∉ I :=
  kgFieldRestriction_of_oneMarking f'
    (unitaryTwo_fieldAction_oneMarking_no_hf h f' hB hpoint z hz)

theorem unitaryTwo_fieldAction_allMarkings_congr {f : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)
    {X : Type} [Group X] (e : X ≃* ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f)))
    (fX : MulAut X) (f' : MulAut ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f)))
    (he : ∀ x : X, e (fX x) = f' (e x))
    {B : GL (Fin 2) K} (hB : B ∈ LargeEvenGUSet (Fin 2) K (2 ^ f))
    {τ : K ≃+* K}
    (hpoint : ∀ c : ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f)),
      (f' c : GL (Fin 2) K) =
        B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut τ
          (c : GL (Fin 2) K) * B⁻¹)
    (z : h.fixedField) (hz : τ (z : K) ≠ (z : K)) :
    GGMarkingAll (K := X) fun _ _ _ I _ θ => kgInducedAut θ fX ∉ I :=
  kgFieldRestriction_of_oneMarking_congr e fX f' he
    (unitaryTwo_fieldAction_oneMarking_no_hf h f' hB hpoint z hz)

end CFSG.StandardType

end
