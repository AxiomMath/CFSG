module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines
import CFSG.GroupTheory.PGroup.RankTwoCommute
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesU4Lo
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open Matrix CFSG.Open Subgroup
open scoped commutatorElement
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.Universal.Unitary (SU mem_SU traceZero rootHom coe_rootHom longRootHom
  coe_longRootHom rootMatrix longRootMatrix rootGroup mem_traceZero signedPerm_mul_rootMatrix
  signedPerm_mul_longRootMatrix)
open CFSG.LieType.Universal.SpecialLinear (signedPerm signedPerm_apply)
open CFSG.LieType.Universal.Unitary.SUExtras (mat mat_apply mat_injective)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive unitaryInvolution_apply)
open CFSG.RankThree.PartOne.KFU (D8Mod diagU diagUHom diagU_val det_diagU diagU_pow diagU_one
  diagU_gram permGL coe_permGL coe_permGL_inv permGL_mem_SU)
open CFSG.RankThree.PartTwo.Sec21.U4Lines (torusD torusD_apply coe_torusD longSL shortSL iotaL
  iotaS coe_iotaL coe_iotaS blkL blkS iotaL_injective iotaS_injective longSL_le_SU
  shortSL_le_SU perfectResidual_short perfectResidual_conj weyl₂ conj_weyl₂
  nonempty_shortSL_mulEquiv_galois mem_shortSL_of)
open CFSG.LieType.Steinberg (rankOne_two_eq_top rootGroup_two_eq_range rootGroup_two_neg_eq_range)
open CFSG.RankThree.PartTwo.Sec21.U4Lines (entry_zero_zero_of_mem_longSL)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes (diag_commute_longSL
  dvd_card_longSL diagU_four_mem_SU orderOf_diagU_four not_mem_longSL_diagU_four
  not_mem_zpowers_of_not_mem_longSL)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b : ℕ}

omit [Finite F] in
private theorem kOf_three_eq_shortSL {σ : F ≃+* F} (hσσ : ∀ c, σ (σ c) = c)
    {ω : rootsOfUnity 3 F} (hω : ω ≠ 1)
    (hperf : ⁅shortSL σ, shortSL σ⁆ = shortSL σ) :
    F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω) : D8Mod 3 F))) = shortSL σ := by
  set a : F := ((ω : Fˣ) : F) with ha
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp ω.2, Units.val_one]
  have ha1 : a ≠ 1 := fun h => hω (Subtype.ext (Units.ext h))
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha3; norm_num at ha3
  have hainv : a ≠ a⁻¹ := by
    intro h
    apply ha1
    have h2 : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ ha0
    calc a = a ^ 3 * a⁻¹ * a⁻¹ := by field_simp
      _ = 1 := by rw [ha3, one_mul, ← h, h2]
  have ht : ((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      diagonal ![a, a, a⁻¹, a⁻¹] := by
    rw [coe_torusD]
    simp [ha]
  change inSubgroup perfectResidual
      (SU σ 4 ⊓ centralizer (zpowers (torusD ((ω, ω) : D8Mod 3 F)) :
        Set (GL (Fin 4) F))) = shortSL σ
  exact perfectResidual_short σ hσσ ht hainv hperf

private theorem kOf_four_eq_map {σ : F ≃+* F} {ω : rootsOfUnity 3 F}
    (hK₃ : F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω) : D8Mod 3 F))) = shortSL σ) :
    F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) =
      (shortSL σ).map (MulAut.conj (weyl₂ : GL (Fin 4) F)).toMonoidHom := by
  have hw : (weyl₂ : GL (Fin 4) F) ∈ SU σ 4 := permGL_mem_SU σ (Equiv.swap 1 2) (by decide)
  have hmap : (zpowers (torusD ((ω, ω) : D8Mod 3 F))).map
      (MulAut.conj (weyl₂ : GL (Fin 4) F)).toMonoidHom =
        zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) := by
    rw [MonoidHom.map_zpowers]
    congr 1
    simpa [MulAut.conj_apply] using (conj_weyl₂ ((ω, ω) : D8Mod 3 F))
  change inSubgroup perfectResidual
      (SU σ 4 ⊓ centralizer (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) :
        Set (GL (Fin 4) F))) = (shortSL σ).map (MulAut.conj (weyl₂ : GL (Fin 4) F)).toMonoidHom
  rw [← hmap]
  rw [perfectResidual_conj (Y := SU σ 4) hw (zpowers (torusD ((ω, ω) : D8Mod 3 F)))]
  change (F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω) : D8Mod 3 F)))).map
    (MulAut.conj (weyl₂ : GL (Fin 4) F)).toMonoidHom = _
  rw [hK₃]

private theorem isPerfect_shortSL_unitary (hb : 0 < b) (hF : Nat.card F = (2 ^ b) ^ 2) :
    ⁅shortSL (unitaryInvolution F 2 b), shortSL (unitaryInvolution F 2 b)⁆ =
      shortSL (unitaryInvolution F 2 b) := by
  obtain ⟨eS⟩ := nonempty_shortSL_mulEquiv_galois (unitaryInvolution F 2 b) hb hF
  exact Subgroup.isPerfect_iff.mp
    (CFSG.RankThree.PartTwo.Sec21.isPerfect_of_mulEquiv_projSL (by omega) eS)

omit [Finite F] in
private theorem rootHom_one_zero_eq_iotaS {σ : F ≃+* F} (hσσ : ∀ c, σ (σ c) = c) (t : F) :
    (rootHom σ hσσ (i := (1 : Fin 4)) (j := (0 : Fin 4)) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd t) : GL (Fin 4) F) =
      iotaS σ (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := (0 : Fin 2))
        (by decide) t) := by
  apply Units.ext
  rw [coe_rootHom, coe_iotaS, Matrix.SpecialLinearGroup.transvection_coe, toAdd_ofAdd]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, blkS, Matrix.single, CharTwo.sub_eq_add, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem rootHom_zero_one_eq_iotaS {σ : F ≃+* F} (hσσ : ∀ c, σ (σ c) = c) (t : F) :
    (rootHom σ hσσ (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd t) : GL (Fin 4) F) =
      iotaS σ (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := (1 : Fin 2))
        (by decide) t) := by
  apply Units.ext
  rw [coe_rootHom, coe_iotaS, Matrix.SpecialLinearGroup.transvection_coe, toAdd_ofAdd]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, blkS, Matrix.single, CharTwo.sub_eq_add, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem rootHom_one_zero_mem_shortSL {σ : F ≃+* F} (hσσ : ∀ c, σ (σ c) = c) (t : F) :
    (rootHom σ hσσ (i := (1 : Fin 4)) (j := (0 : Fin 4)) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd t) : GL (Fin 4) F) ∈ shortSL σ := by
  rw [rootHom_one_zero_eq_iotaS (σ := σ) hσσ t]
  exact ⟨_, rfl⟩

omit [Finite F] in
private theorem rootHom_zero_one_mem_shortSL {σ : F ≃+* F} (hσσ : ∀ c, σ (σ c) = c) (t : F) :
    (rootHom σ hσσ (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd t) : GL (Fin 4) F) ∈ shortSL σ := by
  rw [rootHom_zero_one_eq_iotaS (σ := σ) hσσ t]
  exact ⟨_, rfl⟩

omit [Finite F] [CharP F 2] in
private theorem weyl₂_mul_self : (weyl₂ : GL (Fin 4) F) * weyl₂ = 1 := by
  rw [weyl₂, ← map_mul, Equiv.swap_mul_self, map_one]

omit [Finite F] [CharP F 2] in
private theorem weyl₂_mul_rootMatrix {σ : F ≃+* F} (i j : Fin 4) (c : F) :
    ((weyl₂ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * rootMatrix σ i j c *
        ((weyl₂ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      rootMatrix σ (Equiv.swap 1 2 i) (Equiv.swap 1 2 j) c := by
  have hP : ((weyl₂ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      signedPerm (Equiv.swap 1 2) (fun _ => (1 : F)) := by
    rw [weyl₂, coe_permGL]
    symm
    ext r s
    simp only [signedPerm_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Equiv.Perm.inv_def]
    by_cases h : r = (Equiv.swap 1 2) s
    · have h' : (Equiv.swap 1 2) r = s := by
        rwa [Equiv.swap_apply_eq_iff]
      simp [h]
    · have h' : ¬ (Equiv.swap 1 2) r = s := by
        intro h'
        exact h ((Equiv.swap_apply_eq_iff).mp h')
      simp [h, h']
  have h := signedPerm_mul_rootMatrix (σ := σ) (π := Equiv.swap 1 2)
    (d := fun _ => (1 : F)) (by decide) (by intro s; simp) i j c
  rw [hP]
  rw [h, Matrix.mul_assoc, ← hP, ← Units.val_mul, weyl₂_mul_self, Units.val_one,
    Matrix.mul_one]
  simp only [one_mul, inv_one, mul_one]

omit [Finite F] [CharP F 2] in
private theorem conj_weyl₂_rootHom_zero_one {σ : F ≃+* F} (hσσ : ∀ c, σ (σ c) = c) (t : F) :
    (weyl₂ : GL (Fin 4) F) *
        (rootHom σ hσσ (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide) (by decide) (by decide)
          (Multiplicative.ofAdd t) : GL (Fin 4) F) * (weyl₂ : GL (Fin 4) F)⁻¹ =
      (rootHom σ hσσ (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd t) : GL (Fin 4) F) := by
  have hwinv : (weyl₂ : GL (Fin 4) F)⁻¹ = weyl₂ := inv_eq_of_mul_eq_one_right weyl₂_mul_self
  rw [hwinv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_rootHom, coe_rootHom, weyl₂_mul_rootMatrix]
  simp only [toAdd_ofAdd]
  change rootMatrix σ 0 2 t = rootMatrix σ 0 2 t
  rfl

omit [Finite F] [CharP F 2] in
private theorem conj_weyl₂_rootHom_one_zero {σ : F ≃+* F} (hσσ : ∀ c, σ (σ c) = c) (t : F) :
    (weyl₂ : GL (Fin 4) F) *
        (rootHom σ hσσ (i := (1 : Fin 4)) (j := (0 : Fin 4)) (by decide) (by decide) (by decide)
          (Multiplicative.ofAdd t) : GL (Fin 4) F) * (weyl₂ : GL (Fin 4) F)⁻¹ =
      (rootHom σ hσσ (i := (2 : Fin 4)) (j := (0 : Fin 4)) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd t) : GL (Fin 4) F) := by
  have hwinv : (weyl₂ : GL (Fin 4) F)⁻¹ = weyl₂ := inv_eq_of_mul_eq_one_right weyl₂_mul_self
  rw [hwinv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_rootHom, coe_rootHom, weyl₂_mul_rootMatrix]
  simp only [toAdd_ofAdd]
  change rootMatrix σ 2 0 t = rootMatrix σ 2 0 t
  rfl


omit [Finite F] in
private theorem add_self_mem_traceZero {σ : F ≃+* F} (hσσ : ∀ c, σ (σ c) = c) (t : F) :
    t + σ t ∈ traceZero σ := by
  rw [mem_traceZero, map_add, hσσ]
  have h : t + σ t + (σ t + t) = (t + σ t) + (t + σ t) := by abel
  rw [h, CharTwo.add_self_eq_zero]

omit [Finite F] [CharP F 2] in
private theorem coe_iotaL_longRootHom_zero {σ : F ≃+* F}
    (c : Multiplicative (traceZero σ)) :
    ((iotaL σ (longRootHom σ (i := (0 : Fin 2)) (by decide) c) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = 1 + Matrix.single 1 2 (c.toAdd : F) := by
  rw [coe_iotaL, coe_longRootHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [longRootMatrix, blkL, Matrix.single]

omit [Finite F] [CharP F 2] in
private theorem coe_iotaL_longRootHom_one {σ : F ≃+* F}
    (c : Multiplicative (traceZero σ)) :
    ((iotaL σ (longRootHom σ (i := (1 : Fin 2)) (by decide) c) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = 1 + Matrix.single 2 1 (c.toAdd : F) := by
  rw [coe_iotaL, coe_longRootHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [longRootMatrix, blkL, Matrix.single]

omit [Finite F] in
private theorem commutator_one_zero_two {σ : F ≃+* F} (hσσ : ∀ c, σ (σ c) = c) (t : F) :
    (((⁅rootHom σ hσσ (i := (1 : Fin 4)) (j := (0 : Fin 4)) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd t),
      rootHom σ hσσ (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd (1 : F))⁆ : SU σ 4) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = 1 + Matrix.single 1 2 (t + σ t) := by
  let x := rootHom σ hσσ (i := (1 : Fin 4)) (j := (0 : Fin 4)) (by decide) (by decide) (by decide)
    (Multiplicative.ofAdd t)
  let y := rootHom σ hσσ (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide) (by decide) (by decide)
    (Multiplicative.ofAdd (1 : F))
  let c : traceZero σ := ⟨t + σ t, add_self_mem_traceZero hσσ t⟩
  let z : SU σ 4 := longRootHom σ (i := (1 : Fin 4)) (by decide) (Multiplicative.ofAdd c)
  have hcomm : ⁅x, y⁆ = z := by
    rw [commutatorElement_def, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
    apply mat_injective
    simp only [map_mul, mat_apply]
    change rootMatrix σ 1 0 t * rootMatrix σ 0 2 1 =
      longRootMatrix 1 (t + σ t) * rootMatrix σ 0 2 1 * rootMatrix σ 1 0 t
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rootMatrix, longRootMatrix, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single,
        CharTwo.sub_eq_add, CharTwo.add_self_eq_zero]
    all_goals rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hcomm]
  rw [coe_longRootHom]
  simp [c, longRootMatrix, Matrix.single]

omit [Finite F] in
private theorem commutator_two_zero_zero_one {σ : F ≃+* F} (hσσ : ∀ c, σ (σ c) = c) (t : F) :
    (((⁅rootHom σ hσσ (i := (2 : Fin 4)) (j := (0 : Fin 4)) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd (1 : F)),
      rootHom σ hσσ (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd t)⁆ : SU σ 4) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = 1 + Matrix.single 2 1 (t + σ t) := by
  let x := rootHom σ hσσ (i := (2 : Fin 4)) (j := (0 : Fin 4)) (by decide) (by decide) (by decide)
    (Multiplicative.ofAdd (1 : F))
  let y := rootHom σ hσσ (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide) (by decide) (by decide)
    (Multiplicative.ofAdd t)
  let c : traceZero σ := ⟨t + σ t, add_self_mem_traceZero hσσ t⟩
  let z : SU σ 4 := longRootHom σ (i := (2 : Fin 4)) (by decide) (Multiplicative.ofAdd c)
  have hcomm : ⁅x, y⁆ = z := by
    rw [commutatorElement_def, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
    apply mat_injective
    simp only [map_mul, mat_apply]
    change rootMatrix σ 2 0 1 * rootMatrix σ 0 1 t =
      longRootMatrix 2 (t + σ t) * rootMatrix σ 0 1 t * rootMatrix σ 2 0 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rootMatrix, longRootMatrix, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single,
        CharTwo.sub_eq_add, CharTwo.add_self_eq_zero]
    all_goals rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hcomm]
  rw [coe_longRootHom]
  simp [c, longRootMatrix, Matrix.single]


omit [Finite F] in
private theorem iotaL_longRootHom_zero_mem_sup {σ : F ≃+* F} (hσσ : ∀ c, σ (σ c) = c)
    (hsurj : ∀ a, σ a = a → ∃ t, t + σ t = a) {ω : rootsOfUnity 3 F}
    (hK₃ : F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω) : D8Mod 3 F))) = shortSL σ)
    (hK₄ : F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) =
      (shortSL σ).map (MulAut.conj (weyl₂ : GL (Fin 4) F)).toMonoidHom)
    (c : Multiplicative (traceZero σ)) :
    (iotaL σ (longRootHom σ (i := (0 : Fin 2)) (by decide) c) : GL (Fin 4) F) ∈
      F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω) : D8Mod 3 F))) ⊔
        F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) := by
  have hc : σ (c.toAdd : F) = c.toAdd := by
    have h := (c.toAdd).2
    rw [mem_traceZero] at h
    exact (CharTwo.add_eq_zero.mp h).symm
  obtain ⟨t, ht⟩ := hsurj (c.toAdd : F) hc
  have hx : (rootHom σ hσσ (i := (1 : Fin 4)) (j := (0 : Fin 4)) (by decide) (by decide)
      (by decide) (Multiplicative.ofAdd t) : GL (Fin 4) F) ∈
      F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω) : D8Mod 3 F))) := by
    rw [hK₃]
    exact rootHom_one_zero_mem_shortSL hσσ t
  have hy0 : (rootHom σ hσσ (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide) (by decide)
      (by decide) (Multiplicative.ofAdd (1 : F)) : GL (Fin 4) F) ∈ shortSL σ :=
    rootHom_zero_one_mem_shortSL hσσ 1
  have hy : (rootHom σ hσσ (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide) (by decide)
      (by decide) (Multiplicative.ofAdd (1 : F)) : GL (Fin 4) F) ∈
      F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) := by
    rw [hK₄, ← conj_weyl₂_rootHom_zero_one (σ := σ) hσσ (1 : F)]
    exact Subgroup.mem_map_of_mem _ hy0
  have hcomm : ((⁅rootHom σ hσσ (i := (1 : Fin 4)) (j := (0 : Fin 4)) (by decide) (by decide)
      (by decide) (Multiplicative.ofAdd t),
      rootHom σ hσσ (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd (1 : F))⁆ : SU σ 4) : GL (Fin 4) F) ∈
      F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω) : D8Mod 3 F))) ⊔
        F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) := by
    change ⁅(rootHom σ hσσ (i := (1 : Fin 4)) (j := (0 : Fin 4)) (by decide) (by decide)
      (by decide) (Multiplicative.ofAdd t) : GL (Fin 4) F),
      (rootHom σ hσσ (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd (1 : F)) : GL (Fin 4) F)⁆ ∈ _
    exact mul_mem (mul_mem (mul_mem (mem_sup_left hx) (mem_sup_right hy))
      (inv_mem (mem_sup_left hx))) (inv_mem (mem_sup_right hy))
  have hcomm_eq : ((⁅rootHom σ hσσ (i := (1 : Fin 4)) (j := (0 : Fin 4)) (by decide) (by decide)
      (by decide) (Multiplicative.ofAdd t),
      rootHom σ hσσ (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd (1 : F))⁆ : SU σ 4) : GL (Fin 4) F) =
      (iotaL σ (longRootHom σ (i := (0 : Fin 2)) (by decide) c) : GL (Fin 4) F) := by
    apply Units.ext
    rw [commutator_one_zero_two (σ := σ) hσσ t, coe_iotaL_longRootHom_zero c, ht]
  rw [← hcomm_eq]
  exact hcomm

omit [Finite F] in
private theorem iotaL_longRootHom_one_mem_sup {σ : F ≃+* F} (hσσ : ∀ c, σ (σ c) = c)
    (hsurj : ∀ a, σ a = a → ∃ t, t + σ t = a) {ω : rootsOfUnity 3 F}
    (hK₃ : F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω) : D8Mod 3 F))) = shortSL σ)
    (hK₄ : F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) =
      (shortSL σ).map (MulAut.conj (weyl₂ : GL (Fin 4) F)).toMonoidHom)
    (c : Multiplicative (traceZero σ)) :
    (iotaL σ (longRootHom σ (i := (1 : Fin 2)) (by decide) c) : GL (Fin 4) F) ∈
      F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω) : D8Mod 3 F))) ⊔
        F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) := by
  have hc : σ (c.toAdd : F) = c.toAdd := by
    have h := (c.toAdd).2
    rw [mem_traceZero] at h
    exact (CharTwo.add_eq_zero.mp h).symm
  obtain ⟨t, ht⟩ := hsurj (c.toAdd : F) hc
  have hx0 : (rootHom σ hσσ (i := (1 : Fin 4)) (j := (0 : Fin 4)) (by decide) (by decide)
      (by decide) (Multiplicative.ofAdd (1 : F)) : GL (Fin 4) F) ∈ shortSL σ :=
    rootHom_one_zero_mem_shortSL hσσ 1
  have hx : (rootHom σ hσσ (i := (2 : Fin 4)) (j := (0 : Fin 4)) (by decide) (by decide)
      (by decide) (Multiplicative.ofAdd (1 : F)) : GL (Fin 4) F) ∈
      F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) := by
    rw [hK₄, ← conj_weyl₂_rootHom_one_zero (σ := σ) hσσ (1 : F)]
    exact Subgroup.mem_map_of_mem _ hx0
  have hy : (rootHom σ hσσ (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide) (by decide)
      (by decide) (Multiplicative.ofAdd t) : GL (Fin 4) F) ∈
      F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω) : D8Mod 3 F))) := by
    rw [hK₃]
    exact rootHom_zero_one_mem_shortSL hσσ t
  have hcomm : ((⁅rootHom σ hσσ (i := (2 : Fin 4)) (j := (0 : Fin 4)) (by decide) (by decide)
      (by decide) (Multiplicative.ofAdd (1 : F)),
      rootHom σ hσσ (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd t)⁆ : SU σ 4) : GL (Fin 4) F) ∈
      F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω) : D8Mod 3 F))) ⊔
        F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) := by
    change ⁅(rootHom σ hσσ (i := (2 : Fin 4)) (j := (0 : Fin 4)) (by decide) (by decide)
      (by decide) (Multiplicative.ofAdd (1 : F)) : GL (Fin 4) F),
      (rootHom σ hσσ (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd t) : GL (Fin 4) F)⁆ ∈ _
    exact mul_mem (mul_mem (mul_mem (mem_sup_right hx) (mem_sup_left hy))
      (inv_mem (mem_sup_right hx))) (inv_mem (mem_sup_left hy))
  have hcomm_eq : ((⁅rootHom σ hσσ (i := (2 : Fin 4)) (j := (0 : Fin 4)) (by decide) (by decide)
      (by decide) (Multiplicative.ofAdd (1 : F)),
      rootHom σ hσσ (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd t)⁆ : SU σ 4) : GL (Fin 4) F) =
      (iotaL σ (longRootHom σ (i := (1 : Fin 2)) (by decide) c) : GL (Fin 4) F) := by
    apply Units.ext
    rw [commutator_two_zero_zero_one (σ := σ) hσσ t, coe_iotaL_longRootHom_one c, ht]
  rw [← hcomm_eq]
  exact hcomm

omit [Finite F] in
private theorem longSL_le_sup {σ : F ≃+* F} (hσσ : ∀ c, σ (σ c) = c)
    (hsurj : ∀ a, σ a = a → ∃ t, t + σ t = a) {ω : rootsOfUnity 3 F}
    (hK₃ : F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω) : D8Mod 3 F))) = shortSL σ)
    (hK₄ : F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) =
      (shortSL σ).map (MulAut.conj (weyl₂ : GL (Fin 4) F)).toMonoidHom)
    (hgen : (⊤ : Subgroup (SU σ 2)) =
      rootGroup σ hσσ 2 (Pi.single 0 1) ⊔ rootGroup σ hσσ 2 (-Pi.single 0 1)) :
    longSL σ ≤ F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω) : D8Mod 3 F))) ⊔
      F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) := by
  rw [longSL, MonoidHom.range_eq_map, hgen, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    rw [rootGroup_two_eq_range (σ := σ) hσσ] at hy
    rcases hy with ⟨c, rfl⟩
    exact iotaL_longRootHom_zero_mem_sup hσσ hsurj hK₃ hK₄ c
  · rintro _ ⟨y, hy, rfl⟩
    rw [rootGroup_two_neg_eq_range (σ := σ) hσσ] at hy
    rcases hy with ⟨c, rfl⟩
    exact iotaL_longRootHom_one_mem_sup hσσ hsurj hK₃ hK₄ c

private theorem two_le_pRank_of_le {p : ℕ} (hb : 0 < b)
    (hF : Nat.card F = (2 ^ b) ^ 2) (hp : p.Prime) (hpq : p ∣ 2 ^ b + 1)
    {H : Subgroup (GL (Fin 4) F)}
    (hLH : longSL (unitaryInvolution F 2 b) ≤ H)
    (hSH : shortSL (unitaryInvolution F 2 b) ≤ H) :
    2 ≤ Open.pRank p H := by
  have hdvd : p ∣ (2 ^ b) ^ 2 - 1 := by
    have hsq : (2 ^ b) ^ 2 - 1 = ((2 ^ b) - 1) * (2 ^ b + 1) := by
      have h1 : (1 : ℕ) = 1 ^ 2 := by norm_num
      rw [h1, Nat.sq_sub_sq, mul_comm]
      norm_num
    rw [hsq]
    exact Dvd.dvd.mul_left hpq _
  have hpF : p ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    exact hdvd
  obtain ⟨ν, hν⟩ := @exists_prime_orderOf_dvd_card' (Fˣ) _ _ p ⟨hp⟩ hpF
  have hνpow : ν ^ (2 ^ b + 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (by rw [hν]; exact hpq)
  have hν1 : ν ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hν
    exact hp.one_lt.ne' hν.symm
  have hσν : unitaryInvolution F 2 b ((ν : Fˣ) : F) * ((ν : Fˣ) : F) = 1 := by
    rw [unitaryInvolution_apply, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_succ]
    exact congrArg (fun u : Fˣ => (u : F)) hνpow
  have hνp : ν ^ p = 1 := by
    rw [← hν]
    exact pow_orderOf_eq_one ν
  have hνinvp : (ν⁻¹ : Fˣ) ^ p = 1 := by
    rw [inv_pow, hνp, inv_one]
  let d : GL (Fin 4) F := diagU ![ν, ν⁻¹, ν⁻¹, ν]
  have hd_SU : d ∈ SU (unitaryInvolution F 2 b) 4 := by
    change (diagU ![ν, ν⁻¹, ν⁻¹, ν] : GL (Fin 4) F) ∈ SU (unitaryInvolution F 2 b) 4
    exact diagU_four_mem_SU hσν
  have hdord : orderOf d = p := by
    change orderOf (diagU ![ν, ν⁻¹, ν⁻¹, ν] : GL (Fin 4) F) = p
    exact orderOf_diagU_four hp hνp hνinvp hν1
  have hd_not_longSL : d ∉ longSL (unitaryInvolution F 2 b) := by
    change (diagU ![ν, ν⁻¹, ν⁻¹, ν] : GL (Fin 4) F) ∉ longSL (unitaryInvolution F 2 b)
    exact not_mem_longSL_diagU_four hν1
  have hp_longSL : p ∣ Nat.card (longSL (unitaryInvolution F 2 b)) :=
    dvd_card_longSL hb hF hpq
  obtain ⟨s, hsord'⟩ := @exists_prime_orderOf_dvd_card'
    (longSL (unitaryInvolution F 2 b)) _ _ p ⟨hp⟩ hp_longSL
  have hs_longSL : (s : GL (Fin 4) F) ∈ longSL (unitaryInvolution F 2 b) := s.2
  have hsord : orderOf (s : GL (Fin 4) F) = p := (Subgroup.orderOf_coe s).trans hsord'
  have hd_shortSL : d ∈ shortSL (unitaryInvolution F 2 b) := by
    change (diagU ![ν, ν⁻¹, ν⁻¹, ν] : GL (Fin 4) F) ∈ shortSL (unitaryInvolution F 2 b)
    refine mem_shortSL_of (unitaryInvolution F 2 b) hd_SU ?_ ?_
    · simp [diagU_val]
    · simp [diagU_val]
  have hdH : d ∈ H := hSH hd_shortSL
  have hsH : (s : GL (Fin 4) F) ∈ H := hLH hs_longSL
  have hds : Commute d (s : GL (Fin 4) F) := diag_commute_longSL ν hs_longSL
  have hs_not : (s : GL (Fin 4) F) ∉ Subgroup.zpowers d :=
    not_mem_zpowers_of_not_mem_longSL hdord hsord hs_longSL hd_not_longSL
  exact @CFSG.GroupTheory.two_le_pRank_of_commute (GL (Fin 4) F) _ _ p ⟨hp⟩
    H d (s : GL (Fin 4) F) hdH hsH hdord hsord hds hs_not

theorem u4_two_le_pRank (hb : 0 < b) (hF : Nat.card F = (2 ^ b) ^ 2)
    {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ b + 1) :
    2 ≤ Open.pRank p
      (F08.KOf8103 (SU (unitaryInvolution F 2 b) 4) (zpowers (torusD ((ω, ω) : D8Mod 3 F))) ⊔
        F08.KOf8103 (SU (unitaryInvolution F 2 b) 4)
          (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)))) := by
  have hσσ : ∀ c, unitaryInvolution F 2 b (unitaryInvolution F 2 b c) = c :=
    unitaryInvolution_involutive hF
  have hsurj : ∀ a, unitaryInvolution F 2 b a = a →
      ∃ t, t + unitaryInvolution F 2 b t = a :=
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution
      (p := 2) (f := b) hF).trace_surj
  have hperf : ⁅shortSL (unitaryInvolution F 2 b), shortSL (unitaryInvolution F 2 b)⁆ =
      shortSL (unitaryInvolution F 2 b) := isPerfect_shortSL_unitary hb hF
  have hK₃ : F08.KOf8103 (SU (unitaryInvolution F 2 b) 4)
      (zpowers (torusD ((ω, ω) : D8Mod 3 F))) = shortSL (unitaryInvolution F 2 b) :=
    kOf_three_eq_shortSL (σ := unitaryInvolution F 2 b) hσσ hω hperf
  have hK₄ : F08.KOf8103 (SU (unitaryInvolution F 2 b) 4)
      (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) =
      (shortSL (unitaryInvolution F 2 b)).map
        (MulAut.conj (weyl₂ : GL (Fin 4) F)).toMonoidHom :=
    kOf_four_eq_map (σ := unitaryInvolution F 2 b) hK₃
  have hgen : (⊤ : Subgroup (SU (unitaryInvolution F 2 b) 2)) =
      rootGroup (unitaryInvolution F 2 b) hσσ 2 (Pi.single 0 1) ⊔
        rootGroup (unitaryInvolution F 2 b) hσσ 2 (-Pi.single 0 1) := by
    simpa only [CFSG.LieType.CurtisTits.rankOne] using
      (rankOne_two_eq_top (F := F) (p := 2) (f := b) hF).symm
  have hlong : longSL (unitaryInvolution F 2 b) ≤
      F08.KOf8103 (SU (unitaryInvolution F 2 b) 4) (zpowers (torusD ((ω, ω) : D8Mod 3 F))) ⊔
        F08.KOf8103 (SU (unitaryInvolution F 2 b) 4)
          (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) :=
    longSL_le_sup (σ := unitaryInvolution F 2 b) hσσ hsurj hK₃ hK₄ hgen
  refine two_le_pRank_of_le (H := F08.KOf8103 (SU (unitaryInvolution F 2 b) 4)
      (zpowers (torusD ((ω, ω) : D8Mod 3 F))) ⊔
        F08.KOf8103 (SU (unitaryInvolution F 2 b) 4)
          (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)))) hb hF hp hpq hlong ?_
  rw [← hK₃]
  exact le_sup_left

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
