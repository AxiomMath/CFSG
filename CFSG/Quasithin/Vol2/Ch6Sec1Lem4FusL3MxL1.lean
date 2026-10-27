module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3MxDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3 CFSG.RankThree.SubgroupLists

private def unipUpL3mx1 (F : Type) [Field F] : GL (Fin 2) F :=
  ⟨!![1, 1; 0, 1], !![1, -1; 0, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private def unipLowL3mx1 (F : Type) [Field F] : GL (Fin 2) F :=
  ⟨!![1, 0; 1, 1], !![1, 0; -1, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private theorem det_unipUpL3mx1 (F : Type) [Field F] :
    (unipUpL3mx1 F : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  show Matrix.det !![(1 : F), 1; 0, 1] = 1
  rw [Matrix.det_fin_two_of]
  ring

private theorem det_unipLowL3mx1 (F : Type) [Field F] :
    (unipLowL3mx1 F : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  show Matrix.det !![(1 : F), 0; 1, 1] = 1
  rw [Matrix.det_fin_two_of]
  ring

private theorem sl2Of_top_eq_L3mx1 (F : Type) [Field F] :
    sl2Of (⊤ : Subgroup (GL (Fin 2) F)) = StatedSL 2 F := by
  rw [sl2Of, top_inf_eq, CFSG.Open.StatedAPI.statedSL_eq_ker_det]

private theorem mem_sl2Of_top_L3mx1 (F : Type) [Field F] (A : GL (Fin 2) F) :
    A ∈ sl2Of (⊤ : Subgroup (GL (Fin 2) F)) ↔ (A : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [sl2Of_top_eq_L3mx1 F]
  exact CFSG.GH74.GLS.IVK.Proofs2.linConj_mem_statedSL A

private theorem det_scalar2_L3mx1 (F : Type) [Field F] (c : Fˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      (c : F) ^ 2 := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  simp [Matrix.det_diagonal, sq]

private theorem blk_scalar_neg_L3mx1 (F : Type) [Field F] :
    blk (Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : Fˣ) : GL (Fin 2) F) = negDiag3 F := by
  have hd : ((Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : Fˣ) : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [det_scalar2_L3mx1]
    simp
  apply Units.ext
  rw [coe_blk, hd, inv_one, coe_negDiag3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkMat, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]

private def diagUnit3L3mx1 (F : Type) [Field F] (d : F) (hd : d ≠ 0) : GL (Fin 3) F :=
  ⟨Matrix.diagonal ![1, 1, d⁻¹], Matrix.diagonal ![1, 1, d], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hd],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hd]⟩

private theorem coe_diagUnit3L3mx1 (F : Type) [Field F] (d : F) (hd : d ≠ 0) :
    ((diagUnit3L3mx1 F d hd : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![1, 1, d⁻¹] :=
  rfl

private theorem conj_L3mx1 (F : Type) [Field F] (h2 : (2 : F) ≠ 0) (s : GL (Fin 3) F)
    (hs : s ∈ StatedSL 3 F) (hss : s * s = 1) (hs1 : s ≠ 1) :
    ∃ g ∈ StatedSL 3 F, g⁻¹ * s * g = negDiag3 F := by
  have hdet : (s : Matrix (Fin 3) (Fin 3) F).det = 1 :=
    (CFSG.GH74.GLS.IVK.Proofs2.linConj_mem_statedSL s).mp hs
  obtain ⟨P, hP⟩ := exists_conj_negDiag3 h2 hss hs1 hdet
  have hd0 : (P : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero P
  obtain ⟨c, hc⟩ : ∃ c : GL (Fin 3) F, c = diagUnit3L3mx1 F _ hd0 := ⟨_, rfl⟩
  have hcdet : (c : Matrix (Fin 3) (Fin 3) F).det = ((P : Matrix (Fin 3) (Fin 3) F).det)⁻¹ := by
    rw [hc, coe_diagUnit3L3mx1, Matrix.det_diagonal, Fin.prod_univ_three]
    simp
  have hcomm : negDiag3 F * c = c * negDiag3 F := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_negDiag3, hc, coe_diagUnit3L3mx1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]
  refine ⟨P * c, ?_, ?_⟩
  · refine (CFSG.GH74.GLS.IVK.Proofs2.linConj_mem_statedSL _).mpr ?_
    rw [Units.val_mul, Matrix.det_mul, hcdet, mul_inv_cancel₀ hd0]
  · calc (P * c)⁻¹ * s * (P * c) = c⁻¹ * (P⁻¹ * s * P) * c := by group
      _ = c⁻¹ * negDiag3 F * c := by rw [hP]
      _ = negDiag3 F := by rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem cent_L3mx1 (F : Type) [Field F] (h2 : (2 : F) ≠ 0) (A : GL (Fin 3) F)
    (hA : A ∈ StatedSL 3 F) :
    A * negDiag3 F = negDiag3 F * A ↔ ∃ B ∈ (⊤ : Subgroup (GL (Fin 2) F)), blk B = A := by
  constructor
  · intro hc
    obtain ⟨B, hB⟩ :=
      exists_blk_of_commute h2 hc ((CFSG.GH74.GLS.IVK.Proofs2.linConj_mem_statedSL A).mp hA)
    exact ⟨B, Subgroup.mem_top B, hB⟩
  · rintro ⟨B, -, rfl⟩
    exact blk_commute_negDiag3 B

private theorem scalar_of_comm_unipL3mx1 (F : Type) [Field F] (B : GL (Fin 2) F)
    (h1 : B * unipUpL3mx1 F = unipUpL3mx1 F * B)
    (h2 : B * unipLowL3mx1 F = unipLowL3mx1 F * B) :
    ∃ c : Fˣ, B = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  have e1 : (B : Matrix (Fin 2) (Fin 2) F) * (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) =
      (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) :=
    congrArg Units.val h1
  have e2 : (B : Matrix (Fin 2) (Fin 2) F) * (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) =
      (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) :=
    congrArg Units.val h2
  have hM10 : (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have := congrFun (congrFun e1 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hM01 : (B : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have := congrFun (congrFun e2 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hab : (B : Matrix (Fin 2) (Fin 2) F) 0 0 = (B : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    have := congrFun (congrFun e1 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    first
      | linear_combination this
      | linear_combination -this
  have hdet := Matrix.GeneralLinearGroup.det_ne_zero B
  have hne : (B : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h0
    apply hdet
    simp [Matrix.det_fin_two, h0, hM01, hM10]
  refine ⟨Units.mk0 ((B : Matrix (Fin 2) (Fin 2) F) 0 0) hne, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_apply, hM01, hM10, hab.symm]

private theorem scalar_of_commute_L3mx1 (F : Type) [Field F] (B : GL (Fin 2) F)
    (hB : ∀ B' ∈ sl2Of (⊤ : Subgroup (GL (Fin 2) F)), B * B' = B' * B) :
    ∃ c : Fˣ, B = Matrix.GeneralLinearGroup.scalar (Fin 2) c :=
  scalar_of_comm_unipL3mx1 F B
    (hB _ ((mem_sl2Of_top_L3mx1 F _).mpr (det_unipUpL3mx1 F)))
    (hB _ ((mem_sl2Of_top_L3mx1 F _).mpr (det_unipLowL3mx1 F)))

private theorem derived_L3mx1 (F : Type) [Field F]
    [Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F)] :
    ⁅(⊤ : Subgroup (GL (Fin 2) F)), ⊤⁆ = sl2Of (⊤ : Subgroup (GL (Fin 2) F)) := by
  apply le_antisymm
  · show ⁅(⊤ : Subgroup (GL (Fin 2) F)), ⊤⁆ ≤
      (⊤ : Subgroup (GL (Fin 2) F)) ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker
    refine le_inf le_top (Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_)
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  · rw [sl2Of_top_eq_L3mx1 F, CFSG.Open.StatedAPI.statedSL_eq_range_toGL,
      MonoidHom.range_eq_map]
    have hgeq : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)), ⊤⁆ = ⊤ :=
      Subgroup.commutator_eq_self
    calc Subgroup.map Matrix.SpecialLinearGroup.toGL
          (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
        = Subgroup.map Matrix.SpecialLinearGroup.toGL
            ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)), ⊤⁆ := by
          rw [hgeq]
      _ = ⁅Subgroup.map Matrix.SpecialLinearGroup.toGL
            (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
          Subgroup.map Matrix.SpecialLinearGroup.toGL
            (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))⁆ := by
          rw [Subgroup.map_commutator]
      _ ≤ ⁅(⊤ : Subgroup (GL (Fin 2) F)), ⊤⁆ := Subgroup.commutator_mono le_top le_top

private noncomputable def sl2TopEquivL3mx1 (F : Type) [Field F] :
    ↥(sl2Of (⊤ : Subgroup (GL (Fin 2) F))) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
  (MulEquiv.subgroupCongr (sl2Of_top_eq_L3mx1 F)).trans
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm

private theorem sl2_perfect_L3mx1 (F : Type) [Field F]
    [Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F)] :
    Group.IsPerfect ↥(sl2Of (⊤ : Subgroup (GL (Fin 2) F))) :=
  Group.IsPerfect.ofSurjective (f := (sl2TopEquivL3mx1 F).symm.toMonoidHom)
    (sl2TopEquivL3mx1 F).symm.surjective

private theorem sl2_psl_L3mx1 (F : Type) [Field F] :
    Nonempty (↥(sl2Of (⊤ : Subgroup (GL (Fin 2) F))) ⧸
      Subgroup.center ↥(sl2Of (⊤ : Subgroup (GL (Fin 2) F))) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
  ⟨QuotientGroup.congr _ _ (sl2TopEquivL3mx1 F) (Subgroup.map_center_eq (sl2TopEquivL3mx1 F))⟩

private theorem sl2_center_L3mx1 (F : Type) [Field F]
    (B : ↥(sl2Of (⊤ : Subgroup (GL (Fin 2) F)))) :
    B ∈ Subgroup.center ↥(sl2Of (⊤ : Subgroup (GL (Fin 2) F))) ↔
      (blk (B : GL (Fin 2) F) = 1 ∨ blk (B : GL (Fin 2) F) = negDiag3 F) := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro hc
    have hT1 : unipUpL3mx1 F ∈ sl2Of (⊤ : Subgroup (GL (Fin 2) F)) :=
      (mem_sl2Of_top_L3mx1 F _).mpr (det_unipUpL3mx1 F)
    have hT2 : unipLowL3mx1 F ∈ sl2Of (⊤ : Subgroup (GL (Fin 2) F)) :=
      (mem_sl2Of_top_L3mx1 F _).mpr (det_unipLowL3mx1 F)
    have c1 : unipUpL3mx1 F * (B : GL (Fin 2) F) = (B : GL (Fin 2) F) * unipUpL3mx1 F :=
      congrArg Subtype.val (hc ⟨_, hT1⟩)
    have c2 : unipLowL3mx1 F * (B : GL (Fin 2) F) = (B : GL (Fin 2) F) * unipLowL3mx1 F :=
      congrArg Subtype.val (hc ⟨_, hT2⟩)
    obtain ⟨c, hBc⟩ := scalar_of_comm_unipL3mx1 F (B : GL (Fin 2) F) c1.symm c2.symm
    have hdet : ((B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 :=
      (mem_sl2Of_top_L3mx1 F _).mp B.2
    rw [hBc, det_scalar2_L3mx1] at hdet
    have hc2 : (c : F) * (c : F) = 1 := by
      rw [← sq]
      exact hdet
    rcases mul_self_eq_one_iff.mp hc2 with h1 | h1
    · left
      have hc1 : c = 1 := Units.ext h1
      rw [hBc, hc1]
      simp
    · right
      have hc1 : c = -1 := Units.ext (by rw [h1, Units.val_neg, Units.val_one])
      rw [hBc, hc1, blk_scalar_neg_L3mx1]
  · rintro (h | h)
    · have hB1 : (B : GL (Fin 2) F) = 1 := blk_injective (h.trans (map_one blk).symm)
      intro g
      apply Subtype.ext
      show (g : GL (Fin 2) F) * (B : GL (Fin 2) F) = (B : GL (Fin 2) F) * g
      rw [hB1, mul_one, one_mul]
    · have hB1 : (B : GL (Fin 2) F) = Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : Fˣ) :=
        blk_injective (h.trans (blk_scalar_neg_L3mx1 F).symm)
      intro g
      apply Subtype.ext
      show (g : GL (Fin 2) F) * (B : GL (Fin 2) F) = (B : GL (Fin 2) F) * g
      rw [hB1]
      exact (Matrix.GeneralLinearGroup.scalar_commute (-1 : Fˣ) (g : GL (Fin 2) F)).symm

theorem l3ShapeBase_statedSL {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hF : Nat.card F = p) : L3ShapeBase F (StatedSL 3 F) ⊤ p := by
  have hfact : Fact p.Prime := ⟨hp⟩
  letI : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = p ^ 1 := by rw [pow_one, ← Nat.card_eq_fintype_card, hF]
  have hchar : CharP F p := charP_of_card_eq_prime_pow hFc
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F p] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    omega
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F hF4
  exact
    { charP := hchar
      det_one := fun A hA => (CFSG.GH74.GLS.IVK.Proofs2.linConj_mem_statedSL A).mp hA
      neg_mem := (CFSG.GH74.GLS.IVK.Proofs2.linConj_mem_statedSL _).mpr (by
        simp [coe_negDiag3, Matrix.det_diagonal, Fin.prod_univ_three])
      conj := fun s hs hss hs1 => conj_L3mx1 F h2 s hs hss hs1
      cent := fun A hA => cent_L3mx1 F h2 A hA
      blk_mem := fun B _ => (CFSG.GH74.GLS.IVK.Proofs2.linConj_mem_statedSL _).mpr (det_blk B)
      derived_eq := derived_L3mx1 F
      sl2_perfect := sl2_perfect_L3mx1 F
      sl2_center := fun B => sl2_center_L3mx1 F B
      sl2_psl := ⟨F, inferInstance, inferInstance, hF, sl2_psl_L3mx1 F⟩
      scalar_of_commute := fun B _ hB => scalar_of_commute_L3mx1 F B hB }

end CFSG.Quasithin.H13
