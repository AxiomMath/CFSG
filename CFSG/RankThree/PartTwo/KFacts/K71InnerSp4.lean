module

public import CFSG.RankThree.PartTwo.KFacts.K71Residual
public import CFSG.RankThree.PartTwo.KFacts.K71Sp4
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.GH74.GLS.IVK (fixedField)
open Matrix
open scoped MatrixGroups

section Plane

variable {F : Type} [Field F]

@[expose] def planeBlock (i : Fin 2) (B : Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  CFSG.LieType.SteinbergBR.EvenSp.planeMat fun j => if j = i then B else 1

@[expose] noncomputable def planeSp (i : Fin 2) : SL(2, F) →* StatedSp 2 F :=
  ((CFSG.LieType.SteinbergBR.EvenSp.planeHom.comp
      (MonoidHom.mulSingle (fun _ : Fin 2 => GL (Fin 2) F) i)).comp
      SpecialLinearGroup.toGL).codRestrict (StatedSp 2 F) fun B =>
    CFSG.LieType.SteinbergBR.EvenSp.planeHom_mem_statedSp _ fun j => by
      rw [MonoidHom.mulSingle_apply, Pi.mulSingle_apply]
      split_ifs
      · rw [SpecialLinearGroup.coe_GL_coe_matrix]
        exact B.2
      · simp

theorem coe_planeSp (i : Fin 2) (B : SL(2, F)) :
    (((planeSp i B : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = planeBlock i (B : Matrix (Fin 2) (Fin 2) F) := by
  change ((CFSG.LieType.SteinbergBR.EvenSp.planeHom
    (Pi.mulSingle i (SpecialLinearGroup.toGL B)) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = _
  rw [CFSG.LieType.SteinbergBR.EvenSp.planeHom_val, planeBlock]
  congr 1
  funext j
  rw [Pi.mulSingle_apply]
  split_ifs <;> simp

theorem planeSp_injective (i : Fin 2) : Function.Injective (planeSp (F := F) i) := by
  intro B B' h
  have h1 := congrArg (fun g : StatedSp 2 F => (g : GL (Fin 2 ⊕ Fin 2) F)) h
  change CFSG.LieType.SteinbergBR.EvenSp.planeHom (Pi.mulSingle i (SpecialLinearGroup.toGL B)) =
    CFSG.LieType.SteinbergBR.EvenSp.planeHom (Pi.mulSingle i (SpecialLinearGroup.toGL B')) at h1
  exact SpecialLinearGroup.toGL_injective
    (Pi.mulSingle_injective i (CFSG.LieType.SteinbergBR.EvenSp.planeHom_injective h1))

theorem planeSp_commute (B B' : SL(2, F)) :
    planeSp 0 B * planeSp 1 B' = planeSp 1 B' * planeSp 0 B := by
  apply Subtype.ext
  change CFSG.LieType.SteinbergBR.EvenSp.planeHom (Pi.mulSingle 0 (SpecialLinearGroup.toGL B)) *
      CFSG.LieType.SteinbergBR.EvenSp.planeHom (Pi.mulSingle 1 (SpecialLinearGroup.toGL B')) =
    CFSG.LieType.SteinbergBR.EvenSp.planeHom (Pi.mulSingle 1 (SpecialLinearGroup.toGL B')) *
      CFSG.LieType.SteinbergBR.EvenSp.planeHom (Pi.mulSingle 0 (SpecialLinearGroup.toGL B))
  rw [← map_mul, ← map_mul, (Pi.mulSingle_commute (by decide : (0 : Fin 2) ≠ 1) _ _).eq]

end Plane

section OrdThree

variable (F : Type) [Field F]

@[expose] def ordThreeMat : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, -1]

theorem det_ordThreeMat : (ordThreeMat F).det = 1 := by
  simp [ordThreeMat, Matrix.det_fin_two]

@[expose] def ordThreeSL : SL(2, F) := ⟨ordThreeMat F, det_ordThreeMat F⟩

theorem coe_ordThreeSL : (ordThreeSL F : Matrix (Fin 2) (Fin 2) F) = ordThreeMat F :=
  rfl

theorem ordThreeSL_pow_three : ordThreeSL F ^ 3 = 1 := by
  have h : ordThreeMat F ^ 3 = 1 := by
    rw [pow_three']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ordThreeMat, Matrix.mul_apply, Fin.sum_univ_two]
  exact Subtype.ext h

@[expose] noncomputable def sp4T : StatedSp 2 F := planeSp 0 (ordThreeSL F)

@[expose] noncomputable def sp4T' : StatedSp 2 F := planeSp 1 (ordThreeSL F)

theorem coe_sp4T :
    (((sp4T F : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = planeBlock 0 (ordThreeMat F) :=
  coe_planeSp 0 _

theorem sp4T_pow_three : sp4T F ^ 3 = 1 := by
  rw [sp4T, ← map_pow, ordThreeSL_pow_three, map_one]

theorem sp4T'_pow_three : sp4T' F ^ 3 = 1 := by
  rw [sp4T', ← map_pow, ordThreeSL_pow_three, map_one]

theorem sp4T_commute : sp4T F * sp4T' F = sp4T' F * sp4T F :=
  planeSp_commute _ _

theorem ordThreeSL_ne_one : ordThreeSL F ≠ 1 := by
  intro h
  have := congrArg (fun B : SL(2, F) => (B : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [ordThreeSL, ordThreeMat] at this

theorem sp4T_ne_one : sp4T F ≠ 1 := by
  rw [sp4T, Ne, ← map_one (planeSp 0), (planeSp_injective 0).eq_iff]
  exact ordThreeSL_ne_one F

theorem sp4T'_not_mem_zpowers : sp4T' F ∉ Subgroup.zpowers (sp4T F) := by
  rintro ⟨k, hk⟩
  have hk' : planeSp 0 (ordThreeSL F ^ k) = planeSp 1 (ordThreeSL F) := by
    rw [map_zpow]
    exact hk
  have h := congrArg (fun g : StatedSp 2 F =>
    ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (.inl 1) (.inl 1)) hk'
  simp only [coe_planeSp] at h
  simp [planeBlock, CFSG.LieType.SteinbergBR.EvenSp.planeMat, ordThreeSL, ordThreeMat] at h

variable {F}

theorem spIncl_planeSp_ordThreeSL (σ : F ≃+* F) (i : Fin 2) :
    spIncl σ (planeSp i (ordThreeSL (fixedField σ))) = planeSp i (ordThreeSL F) := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro x y
  rw [coe_spIncl_apply]
  change ((((planeSp i (ordThreeSL (fixedField σ)) : StatedSp 2 (fixedField σ)) :
      GL (Fin 2 ⊕ Fin 2) (fixedField σ)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (fixedField σ))
        x y : F) = (((planeSp i (ordThreeSL F) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) x y
  rw [coe_planeSp, coe_planeSp, coe_ordThreeSL, coe_ordThreeSL]
  rcases x with a | a <;> rcases y with b | b <;> fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [planeBlock, CFSG.LieType.SteinbergBR.EvenSp.planeMat, ordThreeMat]

end OrdThree

section Centralizer

variable {F : Type} [Field F]

theorem commute_of_commute_ordThreeMat {B B' : Matrix (Fin 2) (Fin 2) F}
    (hB : B * ordThreeMat F = ordThreeMat F * B) (hB' : B' * ordThreeMat F = ordThreeMat F * B') :
    B * B' = B' * B := by
  have key : ∀ {C : Matrix (Fin 2) (Fin 2) F}, C * ordThreeMat F = ordThreeMat F * C →
      C 1 0 = -C 0 1 ∧ C 1 1 = C 0 0 - C 0 1 := by
    intro C hC
    have e00 := congrFun (congrFun hC 0) 0
    have e01 := congrFun (congrFun hC 0) 1
    simp [ordThreeMat, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
    constructor
    · first | linear_combination e00 | linear_combination -e00
    · first | linear_combination e01 | linear_combination -e01
  obtain ⟨hc, he⟩ := key hB
  obtain ⟨hc', he'⟩ := key hB'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc, he, hc', he'] <;>
    ring

theorem planeEntries_eq_zero (h3 : (3 : F) ≠ 0) {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hX : X * planeBlock 0 (ordThreeMat F) = planeBlock 0 (ordThreeMat F) * X) :
    (X (.inl 1) (.inl 0) = 0 ∧ X (.inl 1) (.inr 0) = 0 ∧ X (.inr 1) (.inl 0) = 0 ∧
      X (.inr 1) (.inr 0) = 0) ∧
    (X (.inl 0) (.inl 1) = 0 ∧ X (.inl 0) (.inr 1) = 0 ∧ X (.inr 0) (.inl 1) = 0 ∧
      X (.inr 0) (.inr 1) = 0) := by
  have e : ∀ x y, (X * planeBlock 0 (ordThreeMat F)) x y = (planeBlock 0 (ordThreeMat F) * X) x y :=
    fun x y => by rw [hX]
  have e1 := e (.inl 1) (.inl 0)
  have e2 := e (.inl 1) (.inr 0)
  have e3 := e (.inr 1) (.inl 0)
  have e4 := e (.inr 1) (.inr 0)
  have e5 := e (.inl 0) (.inl 1)
  have e6 := e (.inr 0) (.inl 1)
  have e7 := e (.inl 0) (.inr 1)
  have e8 := e (.inr 0) (.inr 1)
  simp [planeBlock, CFSG.LieType.SteinbergBR.EvenSp.planeMat, ordThreeMat, Matrix.mul_apply,
    Fintype.sum_sum_type, Fin.sum_univ_two] at e1 e2 e3 e4 e5 e6 e7 e8
  have z : ∀ {u : F}, 3 * u = 0 → u = 0 := fun hu => (mul_eq_zero.mp hu).resolve_left h3
  have k2 : X (.inl 1) (.inr 0) = 0 := z (by linear_combination -e1 - e2)
  have k4 : X (.inr 1) (.inr 0) = 0 := z (by linear_combination -e3 - e4)
  have k6 : X (.inr 0) (.inl 1) = 0 := z (by linear_combination e6 - e5)
  have k8 : X (.inr 0) (.inr 1) = 0 := z (by linear_combination e8 - e7)
  exact ⟨⟨by linear_combination -e1 - k2, k2, by linear_combination -e3 - k4, k4⟩,
    ⟨by linear_combination e5 + k6, by linear_combination e7 + k8, k6, k8⟩⟩

@[expose] def block0 (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  !![X (.inl 0) (.inl 0), X (.inl 0) (.inr 0); X (.inr 0) (.inl 0), X (.inr 0) (.inr 0)]

theorem block0_one : block0 (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [block0, one_apply]

theorem block0_mul {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hX : X (.inl 0) (.inl 1) = 0 ∧ X (.inl 0) (.inr 1) = 0 ∧ X (.inr 0) (.inl 1) = 0 ∧
      X (.inr 0) (.inr 1) = 0) (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    block0 (X * Y) = block0 X * block0 Y := by
  obtain ⟨h1, h2, h3, h4⟩ := hX
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block0, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h1, h2, h3, h4]

theorem mul_planeBlock_eq_of_mem_centralizer {x : StatedSp 2 F}
    (hx : x ∈ Subgroup.centralizer {sp4T F}) :
    ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        planeBlock 0 (ordThreeMat F) =
      planeBlock 0 (ordThreeMat F) *
        ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  have h := congrArg (fun y : StatedSp 2 F =>
    ((y : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F))
    (Subgroup.mem_centralizer_singleton_iff.mp hx)
  simpa only [Subgroup.coe_mul, Units.val_mul, coe_sp4T] using h

variable (F) in
@[expose] noncomputable def block0Hom (h3 : (3 : F) ≠ 0) :
    Subgroup.centralizer {sp4T F} →* Matrix (Fin 2) (Fin 2) F where
  toFun x := block0 (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
  map_one' := by
    simp only [OneMemClass.coe_one, Units.val_one]
    exact block0_one
  map_mul' x y := by
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact block0_mul (planeEntries_eq_zero h3 (mul_planeBlock_eq_of_mem_centralizer x.2)).2 _

theorem block0Hom_apply (h3 : (3 : F) ≠ 0) (x : Subgroup.centralizer {sp4T F}) :
    block0Hom F h3 x = block0 (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :=
  rfl

theorem block0_mul_ordThreeMat (h3 : (3 : F) ≠ 0) {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hX : X * planeBlock 0 (ordThreeMat F) = planeBlock 0 (ordThreeMat F) * X) :
    block0 X * ordThreeMat F = ordThreeMat F * block0 X := by
  obtain ⟨-, z1, z2, z3, z4⟩ := planeEntries_eq_zero h3 hX
  have e : ∀ x y, (X * planeBlock 0 (ordThreeMat F)) x y = (planeBlock 0 (ordThreeMat F) * X) x y :=
    fun x y => by rw [hX]
  have e00 := e (.inl 0) (.inl 0)
  have e01 := e (.inl 0) (.inr 0)
  have e10 := e (.inr 0) (.inl 0)
  have e11 := e (.inr 0) (.inr 0)
  simp [planeBlock, CFSG.LieType.SteinbergBR.EvenSp.planeMat, ordThreeMat, Matrix.mul_apply,
    Fintype.sum_sum_type, Fin.sum_univ_two, z1, z2, z3, z4] at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [block0, ordThreeMat, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination e00
  · linear_combination e01
  · linear_combination e10
  · linear_combination e11

theorem mem_range_planeSp_one (h3 : (3 : F) ≠ 0) {x : StatedSp 2 F}
    (hx : x ∈ Subgroup.centralizer {sp4T F})
    (h1 : block0 (((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) = 1) :
    x ∈ (planeSp (F := F) 1).range := by
  obtain ⟨⟨y1, y2, y3, y4⟩, ⟨z1, z2, z3, z4⟩⟩ :=
    planeEntries_eq_zero h3 (mul_planeBlock_eq_of_mem_centralizer hx)
  have hsp := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mp x.2
  have hd := congrFun (congrFun hsp (.inl 1)) (.inr 1)
  generalize hX : ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
    X at y1 y2 y3 y4 z1 z2 z3 z4 hd h1
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, z1, z2, z3, z4] at hd
  have b00 := congrFun (congrFun h1 0) 0
  have b01 := congrFun (congrFun h1 0) 1
  have b10 := congrFun (congrFun h1 1) 0
  have b11 := congrFun (congrFun h1 1) 1
  simp [block0] at b00 b01 b10 b11
  set B₁ : Matrix (Fin 2) (Fin 2) F :=
    !![X (.inl 1) (.inl 1), X (.inl 1) (.inr 1); X (.inr 1) (.inl 1), X (.inr 1) (.inr 1)] with hB₁
  have hdet : B₁.det = 1 := by
    rw [hB₁, Matrix.det_fin_two_of]
    linear_combination hd
  refine ⟨⟨B₁, hdet⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  refine (coe_planeSp 1 _).trans ?_
  rw [hX]
  change planeBlock 1 B₁ = X
  ext u v
  rcases u with a | a <;> rcases v with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [planeBlock, CFSG.LieType.SteinbergBR.EvenSp.planeMat, hB₁, y1, y2, y3, y4, z1, z2, z3,
      z4, b00, b01, b10, b11]

theorem inSubgroup_perfectResidual_centralizer_sp4T_eq [Finite F] (h3 : (3 : F) ≠ 0)
    (hF : 4 ≤ Nat.card F) :
    inSubgroup perfectResidual (Subgroup.centralizer {sp4T F}) = (planeSp (F := F) 1).range := by
  apply le_antisymm
  · refine inSubgroup_perfectResidual_le (block0Hom F h3).toHomUnits (fun x y => ?_) fun x hx => ?_
    · apply Units.ext
      simp only [Units.val_mul, MonoidHom.coe_toHomUnits, block0Hom_apply]
      exact commute_of_commute_ordThreeMat
        (block0_mul_ordThreeMat h3 (mul_planeBlock_eq_of_mem_centralizer x.2))
        (block0_mul_ordThreeMat h3 (mul_planeBlock_eq_of_mem_centralizer y.2))
    · have h1 := congrArg Units.val hx
      rw [MonoidHom.coe_toHomUnits, block0Hom_apply, Units.val_one] at h1
      exact mem_range_planeSp_one h3 x.2 h1
  · refine le_inSubgroup_perfectResidual ?_ ?_
    · have : Group.IsPerfect SL(2, F) := by
        classical
        apply CFSG.LinearGroups.special_linear_dimension_two_perfect
        have : Fintype F := Fintype.ofFinite F
        obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
          (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF)
        exact ⟨s, hs⟩
      exact Group.IsPerfect.ofSurjective (f := (planeSp (F := F) 1).rangeRestrict)
        (planeSp (F := F) 1).rangeRestrict_surjective
    · rintro _ ⟨B, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (planeSp_commute _ _).symm

theorem nonempty_perfectResidual_centralizer_mulEquiv_sl2 [Finite F] (h3 : (3 : F) ≠ 0)
    (hF : 4 ≤ Nat.card F) {M : Type*} [Group M] (φ : StatedSp 2 F ≃* M) :
    Nonempty (inSubgroup perfectResidual (Subgroup.centralizer {φ (sp4T F)}) ≃* SL(2, F)) := by
  have hc : Subgroup.centralizer {φ (sp4T F)} =
      (Subgroup.centralizer {sp4T F}).map φ.toMonoidHom := by
    ext z
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      apply φ.injective
      rw [map_mul, map_mul, φ.apply_symm_apply]
      exact h
    · intro h
      have := congrArg φ h
      rwa [map_mul, map_mul, φ.apply_symm_apply] at this
  rw [hc, ← map_inSubgroup_perfectResidual, inSubgroup_perfectResidual_centralizer_sp4T_eq h3 hF]
  exact ⟨(φ.subgroupMap _).symm.trans (MonoidHom.ofInjective (planeSp_injective 1)).symm⟩

end Centralizer

section Bar

open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem imageModTheta_mulEquiv_projSL_of_sp4 {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) {M : Type*} [Group M]
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* M) (φ : StatedSp 2 F ≃* M) {d : G}
    (hd : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : ∃ j : ℕ, d ^ 3 ^ j = 1)
    (hdt : inducedAutHom L e ⟨d, hd⟩ = MulAut.conj (φ (sp4T F))) :
    Nonempty (Sec8.imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ≃*
      projSL 2 (GaloisField 2 f)) ∧
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) ≠ ⊥ := by
  have h3 : (3 : F) ≠ 0 := by
    have h31 : (3 : F) = 1 := by
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination h2
    rw [h31]
    exact one_ne_zero
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    exact (Nat.pow_le_pow_right (by norm_num) hf : 2 ^ 2 ≤ 2 ^ f)
  obtain ⟨ι⟩ := nonempty_imageModTheta_perfectResidual_mulEquiv hd hd3 e
    (Subgroup.centralizer {φ (sp4T F)}) fun z => by
      rw [hdt, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul,
        eq_comm]
  obtain ⟨κ⟩ := nonempty_perfectResidual_centralizer_mulEquiv_sl2 h3 hF4 φ
  obtain ⟨μ⟩ := nonempty_sl2_mulEquiv_projSL hF
  have := nontrivial_sl2 F
  exact ⟨⟨(ι.trans κ).trans μ⟩, ne_bot_of_imageModTheta_mulEquiv (ι.trans κ)⟩

theorem inducesKindPSp4Even_inner_of_conj {F : Type} [Field F] [Finite F] [CharP F 2]
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* StatedProj (StatedSp 2 F)) {d : G}
    (hd : d ∈ Subgroup.normalizer (L : Set G)) (y : StatedProj (StatedSp 2 F))
    (hdt : inducedAutHom L e ⟨d, hd⟩ = MulAut.conj y) :
    InducesKindPSp4Even F L d .inner :=
  ⟨e, hd, y, hdt.symm⟩

end Bar

end CFSG.RankThree.PartTwo.KFacts
