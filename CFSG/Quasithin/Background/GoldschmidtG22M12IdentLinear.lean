module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3AutClass
public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.F6

namespace G22M12Ident

open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBGraphForm Matrix

theorem exists_cube_of_sq_eq {G : Type*} [CommGroup G] (Z : Subgroup G) {d c : G} (hd : d ∈ Z)
    (hc : c ∈ Z) (h : d ^ 2 = c ^ 3) : ∃ m ∈ Z, m ^ 3 = d := by
  refine ⟨d * c⁻¹, mul_mem hd (inv_mem hc), ?_⟩
  calc (d * c⁻¹) ^ 3 = d ^ 3 * (c ^ 3)⁻¹ := by rw [mul_pow, inv_pow]
    _ = d ^ 3 * (d ^ 2)⁻¹ := by rw [h]
    _ = d := by group

section Diag

variable {F : Type} [Field F]

@[expose] def diagOne (δ : Fˣ) : GL (Fin 3) F where
  val := Matrix.diagonal ![(δ : F), 1, 1]
  inv := Matrix.diagonal ![((δ⁻¹ : Fˣ) : F), 1, 1]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp

theorem coe_diagOne (δ : Fˣ) :
    ((diagOne δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![(δ : F), 1, 1] :=
  rfl

theorem transpose_diagOne (δ : Fˣ) :
    ((diagOne δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).transpose =
      ((diagOne δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  rw [coe_diagOne, Matrix.diagonal_transpose]

theorem det_diagOne (δ : Fˣ) : GeneralLinearGroup.det (diagOne δ : GL (Fin 3) F) = δ := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, coe_diagOne, Matrix.det_diagonal, Fin.prod_univ_three]
  simp

theorem inverseTranspose_inv_diagOne (δ : Fˣ) :
    GeneralLinearGroup.inverseTranspose ((diagOne δ : GL (Fin 3) F)⁻¹) = diagOne δ := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_inverseTranspose, inv_inv]
  exact transpose_diagOne δ

end Diag

section Det

variable {F : Type} [Field F]

theorem det_toGL (s : SpecialLinearGroup (Fin 3) F) :
    GeneralLinearGroup.det (SpecialLinearGroup.toGL s) = 1 := by
  apply Units.ext
  simp

theorem det_scalar_three (c : Fˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) F) = c ^ 3 := by
  apply Units.ext
  simp

theorem exists_toGL_eq_of_det_eq_one {B : GL (Fin 3) F} (h : GeneralLinearGroup.det B = 1) :
    ∃ A : SpecialLinearGroup (Fin 3) F, SpecialLinearGroup.toGL A = B := by
  have h' : (B : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, h]
    rfl
  exact ⟨⟨B, h'⟩, Units.ext rfl⟩

theorem det_scalar_inv_mul_diagOne_mul (B : GL (Fin 3) F) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det B)⁻¹ *
      (diagOne (GeneralLinearGroup.det B) * B * diagOne (GeneralLinearGroup.det B))) = 1 := by
  simp only [map_mul, det_scalar_three, det_diagOne]
  group

end Det

section Psl

variable {F : Type} [Field F]

theorem conjAut_mul_dualAut_conj {x : GL (Fin 3) F}
    (hx : GeneralLinearGroup.inverseTranspose (x⁻¹) = x) (B : GL (Fin 3) F) :
    LinearFlag.conjAut 3 F x * (LinearFlag.conjAut 3 F B * LinearFlag.dualAut 3 F) *
        (LinearFlag.conjAut 3 F x)⁻¹ = LinearFlag.conjAut 3 F (x * B * x) *
          LinearFlag.dualAut 3 F := by
  have htrans := standard_automorphism_transport (K := F) (n := 3)
  have hdd : LinearFlag.dualAut 3 F * LinearFlag.dualAut 3 F = 1 := htrans.2.2.2.1
  have h3 := htrans.2.2.2.2.1 x⁻¹
  rw [hx] at h3
  have hconj : LinearFlag.conjAut 3 F x⁻¹ =
      LinearFlag.dualAut 3 F * LinearFlag.conjAut 3 F x * LinearFlag.dualAut 3 F := by
    calc LinearFlag.conjAut 3 F x⁻¹
        = (LinearFlag.dualAut 3 F * LinearFlag.dualAut 3 F) * LinearFlag.conjAut 3 F x⁻¹ *
          (LinearFlag.dualAut 3 F * LinearFlag.dualAut 3 F) := by rw [hdd, one_mul, mul_one]
      _ = LinearFlag.dualAut 3 F * (LinearFlag.dualAut 3 F * LinearFlag.conjAut 3 F x⁻¹ *
          LinearFlag.dualAut 3 F) * LinearFlag.dualAut 3 F := by group
      _ = _ := by rw [h3]
  rw [← map_inv, hconj]
  calc LinearFlag.conjAut 3 F x * (LinearFlag.conjAut 3 F B * LinearFlag.dualAut 3 F) *
        (LinearFlag.dualAut 3 F * LinearFlag.conjAut 3 F x * LinearFlag.dualAut 3 F)
      = LinearFlag.conjAut 3 F x * LinearFlag.conjAut 3 F B *
        (LinearFlag.dualAut 3 F * LinearFlag.dualAut 3 F) * LinearFlag.conjAut 3 F x *
          LinearFlag.dualAut 3 F := by group
    _ = LinearFlag.conjAut 3 F (x * B * x) * LinearFlag.dualAut 3 F := by
        rw [hdd, mul_one, htrans.1, htrans.1]

variable {p : ℕ} [Fact p.Prime]

theorem linear_classify_psl [Finite F] (hF : Nat.card F = p) (θ : MulAut (projectiveSL 3 F))
    (h1 : ¬ IsInnerAut θ) (h2 : IsInnerAut (θ * θ)) :
    ∃ (x : GL (Fin 3) F) (A : SpecialLinearGroup (Fin 3) F),
      LinearFlag.conjAut 3 F x * θ * (LinearFlag.conjAut 3 F x)⁻¹ =
        LinearFlag.conjAut 3 F (SpecialLinearGroup.toGL A) * LinearFlag.dualAut 3 F := by
  have hsub : Subsingleton (F ≃+* F) :=
    CFSG.QuasithinUnique.Ch1.subsingleton_ringEquiv_of_card_prime hF
  obtain ⟨B, σ, ε, hε, hθ⟩ := (automorphism_generation (n := 3) (K := F) le_rfl).2 θ
  have hσ : σ = 1 := Subsingleton.elim _ _
  subst hσ
  rw [map_one, mul_one] at hθ
  have htrans := standard_automorphism_transport (K := F) (n := 3)
  interval_cases ε
  ·
    exfalso
    rw [pow_zero, mul_one] at hθ
    obtain ⟨y, hy⟩ := h2
    obtain ⟨s, rfl⟩ := proj_surjective 3 F y
    have hcs : LinearFlag.conjAut 3 F (B * B * (SpecialLinearGroup.toGL s)⁻¹) *
        LinearFlag.fieldAut 3 F (1 : F ≃+* F) = 1 := by
      rw [map_one, mul_one, map_mul, map_inv, ← htrans.1, conjAut_toGL, hy, hθ]
      exact mul_inv_cancel _
    obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (K := F) (n := 3) le_rfl _ 1 hcs
    have hBB : B * B = GeneralLinearGroup.scalar (Fin 3) c * SpecialLinearGroup.toGL s := by
      rw [hc]
      group
    have hdet : GeneralLinearGroup.det B ^ 2 = c ^ 3 := by
      have := congrArg GeneralLinearGroup.det hBB
      rwa [map_mul, map_mul, det_scalar_three, det_toGL, mul_one, ← pow_two] at this
    obtain ⟨m, -, hm⟩ := exists_cube_of_sq_eq (⊤ : Subgroup Fˣ) (Subgroup.mem_top _)
      (Subgroup.mem_top _) hdet
    have hdetB' : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) m⁻¹ * B) = 1 := by
      rw [map_mul, det_scalar_three, inv_pow, hm]
      group
    obtain ⟨A', hA'⟩ := exists_toGL_eq_of_det_eq_one hdetB'
    have hconjB : LinearFlag.conjAut 3 F B =
        LinearFlag.conjAut 3 F (SpecialLinearGroup.toGL A') := by
      rw [hA', map_mul, conjAut_scalar, one_mul]
    apply h1
    refine ⟨proj 3 F A', ?_⟩
    rw [← conjAut_toGL, ← hconjB, hθ]
  ·
    rw [pow_one] at hθ
    obtain ⟨A, hA⟩ := exists_toGL_eq_of_det_eq_one (det_scalar_inv_mul_diagOne_mul B)
    refine ⟨diagOne (GeneralLinearGroup.det B), A, ?_⟩
    rw [hA, map_mul, conjAut_scalar, one_mul, hθ, conjAut_mul_dualAut_conj
      (inverseTranspose_inv_diagOne _)]

end Psl

section Sl

variable {F : Type} [Field F]

theorem descendAut_injective_three : Function.Injective (descendAut 3 F) := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin 3) F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  rw [injective_iff_map_eq_one]
  intro τ hτ
  refine eq_one_of_forall_mul_inv_mem_center fun s => ?_
  have h := congrArg (fun φ : MulAut (projectiveSL 3 F) => φ (proj 3 F s)) hτ
  simp only [descendAut_proj, MulAut.one_apply] at h
  rw [eq_comm, proj_eq_proj_iff] at h
  exact scalars_le_center 3 F h

theorem linear_classify_sl [Finite F] {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p)
    (φ : MulAut (SpecialLinearGroup (Fin 3) F)) (h1 : ¬ IsInnerAut φ) (h2 : IsInnerAut (φ * φ)) :
    ∃ (x : GL (Fin 3) F) (A : SpecialLinearGroup (Fin 3) F),
      slConjugation 3 F x * φ * (slConjugation 3 F x)⁻¹ =
        slConjugation 3 F (SpecialLinearGroup.toGL A) * slGraphAut 3 F := by
  have hθ1 : ¬ IsInnerAut (descendAut 3 F φ) := fun h =>
    h1 ((isInnerAut_descendAut_iff (by norm_num)).mp h)
  have hθ2 : IsInnerAut (descendAut 3 F φ * descendAut 3 F φ) := by
    rw [← map_mul]
    exact isInnerAut_descendAut h2
  obtain ⟨x, A, hxA⟩ := linear_classify_psl hF _ hθ1 hθ2
  refine ⟨x, A, descendAut_injective_three ?_⟩
  simp only [map_mul, map_inv]
  exact hxA

end Sl

section Stated

variable {F : Type} [Field F]

theorem coe_inv_special (s : SpecialLinearGroup (Fin 3) F) :
    ((s⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (s : Matrix (Fin 3) (Fin 3) F)⁻¹ := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.inv_def, s.det_coe]
  simp

theorem coe_symm_stated (s : ↥(StatedSL 3 F)) :
    (((specialLinearGroupEquivStatedSL 3 F).symm s : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  have h := specialLinearGroupEquivStatedSL_coe 3 F ((specialLinearGroupEquivStatedSL 3 F).symm s)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem coe_congr_graph_apply (A : SpecialLinearGroup (Fin 3) F) (s : ↥(StatedSL 3 F)) :
    ((((MulAut.congr (specialLinearGroupEquivStatedSL 3 F)
        (slConjugation 3 F (SpecialLinearGroup.toGL A) * slGraphAut 3 F)) s : ↥(StatedSL 3 F)) :
          GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((specialLinearGroupEquivStatedSL 3 F A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)⁻¹)ᵀ *
          (((specialLinearGroupEquivStatedSL 3 F A : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F) := by
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulAut.mul_apply]
  change ((slConjugation 3 F (SpecialLinearGroup.toGL A)
    (slGraphAut 3 F ((specialLinearGroupEquivStatedSL 3 F).symm s)) :
      SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = _
  rw [slConjugation_matrix, slGraphAut_matrix, coe_inv_special, coe_symm_stated]
  rfl

@[expose] noncomputable def projEquivStated :
    projectiveSL 3 F ≃* StatedProj (StatedSL 3 F) :=
  (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 F)).trans
    (projectiveSpecialLinearGroupEquivStatedProj 3 F)

theorem projEquivStated_proj (s : SpecialLinearGroup (Fin 3) F) :
    projEquivStated (proj 3 F s) =
      (QuotientGroup.mk (specialLinearGroupEquivStatedSL 3 F s) : StatedProj (StatedSL 3 F)) :=
  rfl

variable [Finite F] {p : ℕ} [Fact p.Prime]

theorem classify_linear_stated_sl (hF : Nat.card F = p) (φ : MulAut ↥(StatedSL 3 F))
    (h1 : ¬ IsInnerAut φ) (h2 : IsInnerAut (φ * φ)) :
    ∃ (ε : MulAut ↥(StatedSL 3 F)) (g : ↥(StatedSL 3 F)), ∀ s : ↥(StatedSL 3 F),
      ((((ε * φ * ε⁻¹) s : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)⁻¹)ᵀ *
            (((g : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  set e := specialLinearGroupEquivStatedSL 3 F with he
  set φ' : MulAut (SpecialLinearGroup (Fin 3) F) := MulAut.congr e.symm φ with hφ'
  have h1' : ¬ IsInnerAut φ' := fun h => h1 ((isInnerAut_congr e.symm φ).mp h)
  have h2' : IsInnerAut (φ' * φ') := by
    rw [hφ', ← map_mul]
    exact (isInnerAut_congr e.symm (φ * φ)).mpr h2
  obtain ⟨x, A, hxA⟩ := linear_classify_sl hF φ' h1' h2'
  have hφ : MulAut.congr e φ' = φ := by
    ext s
    simp [hφ', MulAut.congr_apply]
  refine ⟨MulAut.congr e (slConjugation 3 F x), e A, fun s => ?_⟩
  have h3 : MulAut.congr e (slConjugation 3 F x) * φ * (MulAut.congr e (slConjugation 3 F x))⁻¹ =
      MulAut.congr e (slConjugation 3 F (SpecialLinearGroup.toGL A) * slGraphAut 3 F) := by
    rw [← hxA, map_mul, map_mul, map_inv, hφ]
  rw [h3]
  exact coe_congr_graph_apply A s

theorem classify_linear_stated_psl (hF : Nat.card F = p)
    (θ : MulAut (StatedProj (StatedSL 3 F))) (h1 : ¬ IsInnerAut θ) (h2 : IsInnerAut (θ * θ)) :
    ∃ (ε : MulAut (StatedProj (StatedSL 3 F))) (Θ : MulAut ↥(StatedSL 3 F))
      (g : ↥(StatedSL 3 F)), (∀ s : ↥(StatedSL 3 F),
        ((((Θ s : ↥(StatedSL 3 F)) : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) =
          ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
            (((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)⁻¹)ᵀ *
              (((g : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ∧
        ∀ s : ↥(StatedSL 3 F), (ε * θ * ε⁻¹) (QuotientGroup.mk s) = QuotientGroup.mk (Θ s) := by
  set eP : projectiveSL 3 F ≃* StatedProj (StatedSL 3 F) := projEquivStated with heP
  set e := specialLinearGroupEquivStatedSL 3 F with he
  set θ' : MulAut (projectiveSL 3 F) := MulAut.congr eP.symm θ with hθ'
  have h1' : ¬ IsInnerAut θ' := fun h => h1 ((isInnerAut_congr eP.symm θ).mp h)
  have h2' : IsInnerAut (θ' * θ') := by
    rw [hθ', ← map_mul]
    exact (isInnerAut_congr eP.symm (θ * θ)).mpr h2
  obtain ⟨x, A, hxA⟩ := linear_classify_psl hF θ' h1' h2'
  have hθ : MulAut.congr eP θ' = θ := by
    ext y
    simp [hθ', MulAut.congr_apply]
  refine ⟨MulAut.congr eP (LinearFlag.conjAut 3 F x),
    MulAut.congr e (slConjugation 3 F (SpecialLinearGroup.toGL A) * slGraphAut 3 F), e A,
    fun s => coe_congr_graph_apply A s, fun s => ?_⟩
  have h3 : MulAut.congr eP (LinearFlag.conjAut 3 F x) * θ *
      (MulAut.congr eP (LinearFlag.conjAut 3 F x))⁻¹ =
        MulAut.congr eP (LinearFlag.conjAut 3 F (SpecialLinearGroup.toGL A) *
          LinearFlag.dualAut 3 F) := by
    rw [← hxA, map_mul, map_mul, map_inv, hθ]
  rw [h3]
  obtain ⟨s', rfl⟩ := e.surjective s
  have h4 : (QuotientGroup.mk (e s') : StatedProj (StatedSL 3 F)) = eP (proj 3 F s') := rfl
  rw [h4]
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.mul_apply]
  rw [dualAut_proj, conjAut_proj]
  rfl

end Stated

end G22M12Ident

end CFSG.Quasithin.F6
