module

public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNode
import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.StandardType

open Matrix CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section LowerAut

variable {n : ℕ} {F : Type} [Field F]

theorem slLowerBlockMat_transpose (A : Matrix (Fin n) (Fin n) F) :
    (slLowerBlockMat n F A).transpose = slLowerBlockMat n F A.transpose := by
  ext a b
  obtain ⟨p, rfl⟩ := (slLowerBlockEquiv n).surjective a
  obtain ⟨q, rfl⟩ := (slLowerBlockEquiv n).surjective b
  rw [Matrix.transpose_apply, slLowerBlockMat_apply, slLowerBlockMat_apply]
  rcases p with p | p <;> rcases q with q | q <;> simp [Matrix.one_apply, eq_comm]

theorem slLowerBlockMat_map {f : F → F} (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (A : Matrix (Fin n) (Fin n) F) :
    (slLowerBlockMat n F A).map f = slLowerBlockMat n F (A.map f) := by
  ext a b
  obtain ⟨p, rfl⟩ := (slLowerBlockEquiv n).surjective a
  obtain ⟨q, rfl⟩ := (slLowerBlockEquiv n).surjective b
  rw [Matrix.map_apply, slLowerBlockMat_apply, slLowerBlockMat_apply]
  rcases p with p | p <;> rcases q with q | q <;> simp [Matrix.one_apply, apply_ite f, hf0, hf1]

theorem slFieldAut_slLowerBlockHom (σ : F ≃+* F) (g : Matrix.SpecialLinearGroup (Fin n) F) :
    CatalogueBHigherLinearField.slFieldAut (Fin (n + 1)) F σ (slLowerBlockHom n F g) =
      slLowerBlockHom n F (CatalogueBHigherLinearField.slFieldAut (Fin n) F σ g) := by
  apply Subtype.ext
  change (slLowerBlockMat n F (g : Matrix (Fin n) (Fin n) F)).map σ =
    slLowerBlockMat n F ((g : Matrix (Fin n) (Fin n) F).map σ)
  exact slLowerBlockMat_map (map_zero σ) (map_one σ) _

theorem slGraphAut_slLowerBlockHom (g : Matrix.SpecialLinearGroup (Fin n) F) :
    CatalogueBGraphForm.slGraphAut (n + 1) F (slLowerBlockHom n F g) =
      slLowerBlockHom n F (CatalogueBGraphForm.slGraphAut n F g) := by
  apply Subtype.ext
  rw [CatalogueBGraphForm.slGraphAut_matrix, ← map_inv, coe_slLowerBlockHom,
    slLowerBlockMat_transpose, coe_slLowerBlockHom, CatalogueBGraphForm.slGraphAut_matrix]

theorem diagonal_mul_slLowerBlockMat {v : Fin (n + 1) → F} (hv : ∀ i, i ≠ 0 → v i = 1)
    (A : Matrix (Fin n) (Fin n) F) :
    Matrix.diagonal v * slLowerBlockMat n F A = slLowerBlockMat n F A * Matrix.diagonal v := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  obtain ⟨p, rfl⟩ := (slLowerBlockEquiv n).surjective a
  obtain ⟨q, rfl⟩ := (slLowerBlockEquiv n).surjective b
  rw [slLowerBlockMat_apply]
  rcases p with p | p <;> rcases q with q | q
  · obtain rfl : p = 0 := Subsingleton.elim _ _
    obtain rfl : q = 0 := Subsingleton.elim _ _
    simp [mul_comm]
  · simp [slLowerBlockEquiv_inr, hv _ (Fin.succ_ne_zero _)]
  · simp [slLowerBlockEquiv_inr, hv _ (Fin.succ_ne_zero _)]
  · simp [slLowerBlockEquiv_inr, hv _ (Fin.succ_ne_zero _)]

theorem exists_sl_slConjugation_slLowerBlockHom (A : GL (Fin (n + 1)) F) :
    ∃ s : Matrix.SpecialLinearGroup (Fin (n + 1)) F, ∀ g : Matrix.SpecialLinearGroup (Fin n) F,
      CatalogueBHigherLinearAction.slConjugation (n + 1) F A (slLowerBlockHom n F g) =
        s * slLowerBlockHom n F g * s⁻¹ := by
  have hδ0 : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero
  set v : Fin (n + 1) → F :=
    fun i => if i = 0 then ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) F).det)⁻¹ else 1 with hvdef
  have hv1 : ∀ i, i ≠ 0 → v i = 1 := fun i hi => by simp [hvdef, hi]
  have hv : (Matrix.diagonal v).det = ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) F).det)⁻¹ := by
    rw [Matrix.det_diagonal, Fin.prod_univ_succ, Finset.prod_eq_one
      (fun i _ => hv1 _ (Fin.succ_ne_zero i)), mul_one]
    simp [hvdef]
  let s : Matrix.SpecialLinearGroup (Fin (n + 1)) F :=
    ⟨(A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) * Matrix.diagonal v,
      by rw [Matrix.det_mul, hv, mul_inv_cancel₀ hδ0]⟩
  refine ⟨s, fun g => ?_⟩
  rw [eq_comm, mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    CatalogueBHigherLinearAction.slConjugation_matrix, coe_slLowerBlockHom]
  change (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) * Matrix.diagonal v *
      slLowerBlockMat n F (g : Matrix (Fin n) (Fin n) F) =
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *
        slLowerBlockMat n F (g : Matrix (Fin n) (Fin n) F) *
      ((A⁻¹ : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *
        ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) * Matrix.diagonal v)
  rw [Matrix.mul_assoc (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Matrix.diagonal v),
    diagonal_mul_slLowerBlockMat hv1, Matrix.mul_assoc _ (((A⁻¹ : GL (Fin (n + 1)) F) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F)), ← Matrix.mul_assoc (((A⁻¹ : GL (Fin (n + 1)) F) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F)), Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc]

theorem exists_conj_of_mulAut_slLowerBlockHom [Finite F] (hn : 2 ≤ n)
    (α : MulAut (Matrix.SpecialLinearGroup (Fin (n + 1)) F)) :
    ∃ s : Matrix.SpecialLinearGroup (Fin (n + 1)) F,
      (slLowerBlockHom n F).range.map α.toMonoidHom =
        (slLowerBlockHom n F).range.map (MulAut.conj s).toMonoidHom := by
  obtain ⟨A, σ, ε, hε, rfl⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl (by omega : 3 ≤ n + 1) α
  obtain ⟨s, hs⟩ := exists_sl_slConjugation_slLowerBlockHom A
  refine ⟨s, ?_⟩
  set β : MulAut (Matrix.SpecialLinearGroup (Fin n) F) :=
    CatalogueBHigherLinearField.slFieldAut (Fin n) F σ * CatalogueBGraphForm.slGraphAut n F ^ ε
    with hβ
  have hγ : ∀ g, (CatalogueBGraphForm.slGraphAut (n + 1) F ^ ε) (slLowerBlockHom n F g) =
      slLowerBlockHom n F ((CatalogueBGraphForm.slGraphAut n F ^ ε) g) := by
    intro g
    interval_cases ε
    · rfl
    · simp only [pow_one]
      exact slGraphAut_slLowerBlockHom g
  have hα : ∀ g, (CatalogueBHigherLinearAction.slConjugation (n + 1) F A *
      CatalogueBHigherLinearField.slFieldAut (Fin (n + 1)) F σ *
        CatalogueBGraphForm.slGraphAut (n + 1) F ^ ε) (slLowerBlockHom n F g) =
      s * slLowerBlockHom n F (β g) * s⁻¹ := by
    intro g
    simp only [MulAut.mul_apply, hβ]
    rw [hγ, slFieldAut_slLowerBlockHom, hs]
  ext z
  simp only [Subgroup.mem_map, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨_, ⟨β g, rfl⟩, (hα g).symm⟩
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    refine ⟨_, ⟨β⁻¹ g, rfl⟩, ?_⟩
    rw [hα, show β (β⁻¹ g) = g from MulEquiv.apply_symm_apply β g]

end LowerAut

section Unique

variable {m : ℕ} {F : Type} [Field F] {X : Type*} [Group X]

theorem eq_one_of_isPerfect_of_commute {S Y : Type*} [Group S] [Group Y] [Group.IsPerfect S]
    (z : S →* Y) (hz : ∀ a b, z a * z b = z b * z a) : z = 1 := by
  have hle : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ ≤ z.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hz a b
  have htop : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
  rw [htop] at hle
  ext s
  exact hle (Subgroup.mem_top s)

theorem mem_center_of_forall_commute_slLift (hm : 3 ≤ m)
    {φ : Matrix.SpecialLinearGroup (Fin m) F →* X}
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) F))
    {g : Matrix.SpecialLinearGroup (Fin m) F} (hg : ∀ h, φ g * φ h = φ h * φ g) :
    g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) F) := by
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin m) F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hm
  have hc : ∀ s, ⁅g, s⁆ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) F) := fun s =>
    hker (by rw [MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]; exact hg s)
  let c : Matrix.SpecialLinearGroup (Fin m) F →* Matrix.SpecialLinearGroup (Fin m) F :=
    { toFun := fun s => ⁅g, s⁆
      map_one' := by simp
      map_mul' := fun s t => by
        have ht := Subgroup.mem_center_iff.mp (hc t) s
        simp only [commutatorElement_def] at ht ⊢
        calc g * (s * t) * g⁻¹ * (s * t)⁻¹ = g * s * g⁻¹ * s⁻¹ * (s * (g * t * g⁻¹ * t⁻¹)) *
              s⁻¹ := by group
          _ = g * s * g⁻¹ * s⁻¹ * ((g * t * g⁻¹ * t⁻¹) * s) * s⁻¹ := by rw [ht]
          _ = g * s * g⁻¹ * s⁻¹ * (g * t * g⁻¹ * t⁻¹) := by group }
  have hc1 : c = 1 := eq_one_of_isPerfect_of_commute c fun a b =>
    (Subgroup.mem_center_iff.mp (hc a) (c b)).symm
  rw [Subgroup.mem_center_iff]
  intro s
  have h1 : ⁅g, s⁆ = 1 := DFunLike.congr_fun hc1 s
  exact ((commutatorElement_eq_one_iff_mul_comm).mp h1).symm

theorem exists_mulAut_of_slLift [Finite F] (hm : 3 ≤ m)
    {φ ψ : Matrix.SpecialLinearGroup (Fin m) F →* X} (hrange : φ.range = ψ.range)
    (hφ : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) F))
    (hψ : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) F)) :
    ∃ α : MulAut (Matrix.SpecialLinearGroup (Fin m) F), ψ = φ.comp α.toMonoidHom := by
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin m) F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hm
  set H := φ.range with hH
  let φH : Matrix.SpecialLinearGroup (Fin m) F →* H := φ.rangeRestrict
  let ψH : Matrix.SpecialLinearGroup (Fin m) F →* H :=
    (MulEquiv.subgroupCongr hrange.symm).toMonoidHom.comp ψ.rangeRestrict
  have hφH : ∀ g, (φH g : X) = φ g := fun g => rfl
  have hψH : ∀ g, (ψH g : X) = ψ g := fun g => rfl
  have sφ : Function.Surjective φH := φ.rangeRestrict_surjective
  have sψ : Function.Surjective ψH := by
    intro h
    obtain ⟨g, hg⟩ : (h : X) ∈ ψ.range := hrange ▸ h.2
    exact ⟨g, Subtype.ext (by rw [hψH]; exact hg)⟩
  have hφHker : φH.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) F) := fun g hg =>
    hφ (by rw [MonoidHom.mem_ker, ← hφH, MonoidHom.mem_ker.mp hg]; rfl)
  have hψHker : ψH.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) F) := fun g hg =>
    hψ (by rw [MonoidHom.mem_ker, ← hψH, MonoidHom.mem_ker.mp hg]; rfl)
  let q := QuotientGroup.mk' (Subgroup.center H)
  have hkerq : ∀ θ : Matrix.SpecialLinearGroup (Fin m) F →* H, Function.Surjective θ →
      θ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) F) →
      (q.comp θ).ker = LinearFlag.scalars m F := by
    intro θ hθ hθker
    rw [LinearFlag.scalars_eq_center]
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hg
      exact mem_center_of_forall_commute_slLift hm hθker
        (fun h => (Subgroup.mem_center_iff.mp hg (θ h)).symm)
    · intro hg
      rw [Subgroup.mem_center_iff]
      intro h
      obtain ⟨s, rfl⟩ := hθ h
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hg s]
  let eφ : LinearFlag.projectiveSL m F ≃* H ⧸ Subgroup.center H :=
    (QuotientGroup.quotientMulEquivOfEq (hkerq φH sφ hφHker).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp sφ))
  let eψ : LinearFlag.projectiveSL m F ≃* H ⧸ Subgroup.center H :=
    (QuotientGroup.quotientMulEquivOfEq (hkerq ψH sψ hψHker).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp sψ))
  have heφ : ∀ g, eφ (LinearFlag.proj m F g) = q (φH g) := fun g => rfl
  have heψ : ∀ g, eψ (LinearFlag.proj m F g) = q (ψH g) := fun g => rfl
  obtain ⟨A, σ, ε, -, hβ⟩ := (LinearFlag.automorphism_generation hm).2 (eψ.trans eφ.symm)
  set α : MulAut (Matrix.SpecialLinearGroup (Fin m) F) :=
    CatalogueBHigherLinearAction.slConjugation m F A *
      CatalogueBHigherLinearField.slFieldAut (Fin m) F σ * CatalogueBGraphForm.slGraphAut m F ^ ε
    with hαdef
  have hdesc : LinearFlag.descendAut m F α = eψ.trans eφ.symm := by
    rw [hβ, hαdef]
    simp only [LinearFlag.conjAut, LinearFlag.fieldAut, LinearFlag.dualAut, map_mul, map_pow,
      MonoidHom.comp_apply]
  have hmod : ∀ g, (φH (α g))⁻¹ * ψH g ∈ Subgroup.center H := by
    intro g
    have h1 : eφ (LinearFlag.descendAut m F α (LinearFlag.proj m F g)) =
        eψ (LinearFlag.proj m F g) := by
      rw [hdesc]
      exact eφ.apply_symm_apply (eψ (LinearFlag.proj m F g))
    rw [LinearFlag.descendAut_proj, heφ, heψ] at h1
    exact QuotientGroup.eq.mp h1
  let z : Matrix.SpecialLinearGroup (Fin m) F →* H :=
    { toFun := fun g => (φH (α g))⁻¹ * ψH g
      map_one' := by simp
      map_mul' := fun a b => by
        have hc := Subgroup.mem_center_iff.mp (hmod a) (φH (α b))⁻¹
        simp only [map_mul, _root_.mul_inv_rev]
        calc (φH (α b))⁻¹ * (φH (α a))⁻¹ * (ψH a * ψH b)
            = ((φH (α b))⁻¹ * ((φH (α a))⁻¹ * ψH a)) * ψH b := by group
          _ = (((φH (α a))⁻¹ * ψH a) * (φH (α b))⁻¹) * ψH b := by rw [hc]
          _ = (φH (α a))⁻¹ * ψH a * ((φH (α b))⁻¹ * ψH b) := by group }
  have hz : z = 1 := eq_one_of_isPerfect_of_commute z fun a b =>
    (Subgroup.mem_center_iff.mp (hmod a) (z b)).symm
  refine ⟨α, ?_⟩
  ext g
  have h1 : (φH (α g))⁻¹ * ψH g = 1 := DFunLike.congr_fun hz g
  have h3 := congrArg Subtype.val (inv_mul_eq_one.mp h1).symm
  rw [hψH, hφH] at h3
  exact h3

end Unique

@[expose] def GGTypeAEndBlockLExInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeASplitNbr p B Bs x L D J n f y K →
    ∃ φ : Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ.range = L ∧
      φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      (φ.comp (slLowerBlockHom n (GaloisField 2 f))).range = J

theorem ggTypeAEndBlockLInput_of_ex (h : GGTypeAEndBlockLExInput) : GGTypeAEndBlockLInput := by
  intro G _ _ p B Bs x L D J n f y K hN φ₁ hφL hker
  obtain ⟨-, -, -, -, -, -, hn, -⟩ := id hN
  obtain ⟨φ, hφL', hφker, hJ⟩ := h G p B Bs x L D J n f y K hN
  obtain ⟨α, hα⟩ := exists_mulAut_of_slLift (by omega : 3 ≤ n + 1) (hφL'.trans hφL.symm) hφker hker
  obtain ⟨s, hs⟩ := exists_conj_of_mulAut_slLowerBlockHom (by omega : 2 ≤ n) α⁻¹
  have hsL : φ₁ s ∈ L := by
    rw [← hφL]
    exact ⟨s, rfl⟩
  refine ⟨φ₁ s, hsL, ?_⟩
  have e1 : (MulAut.conj (φ₁ s)).toMonoidHom.comp φ₁ = φ₁.comp (MulAut.conj s).toMonoidHom := by
    ext g
    simp [MulAut.conj_apply]
  have e2 : φ = φ₁.comp (α⁻¹).toMonoidHom := by
    rw [hα]
    ext g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact congrArg φ (MulEquiv.apply_symm_apply α g).symm
  rw [← hJ, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.map_map, e1,
    ← Subgroup.map_map, ← hs, Subgroup.map_map, ← e2]

theorem ggTypeAEndNodeInput_of_inputs' (hA : GGTypeAEndBlockLExInput)
    (hB : GGTypeAEndBlockKInput) (hC : GGTypeAFarCommuteInput) (hD : GGTypeAJoinInput) :
    GGTypeAEndNodeInput :=
  ggTypeAEndNodeInput_of_inputs (ggTypeAEndBlockLInput_of_ex hA) hB hC hD

section Assembly

open CFSG.Assembly CFSG.Blueprint CFSG.RankThree.PartTwo.Sec21

theorem lc_gl_std_of_typeAEndNode (hHolt : HoltUniqueFixedPointSimple) (ha : GGBstarInput)
    (ha₀ : GGLNoncyclicInput) (hb : GGStdSubPreInput) (hc₀ : GGFieldNbrCanonicalInput)
    (hc₁ : GGProp41Input) (hc₂ : GGCor42Input) (hc₃ : GGNoTransvectionInput)
    (hd : GGCoxeterLabelInput) (heL : GGTypeAEndBlockLExInput) (heK : GGTypeAEndBlockKInput)
    (heC : GGTypeAFarCommuteInput) (heD : GGTypeAJoinInput) (heR : GGSecFiveDataInputRest)
    (hf : GGHypSixV2Input) (hg₁ : GGCorFiveTwentyInput) (hg₂ : GGOmegaOneInput)
    (hR1 : GGLieModelMarkingInput) (hR : GGInnerDiagBridgeInput) (h1 : GGSixStepOneV2Input)
    (h2 : GGSixStepTwoV2Input) (h3a : GGSixStepThreeAInput) (h3b : GGSixStepThreeBInput)
    (h3c : GGSixStepThreeCInput) (h3d : GGSixStepThreeDInput)
    (hKG : GGRootInvolutionCentralInput)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he4 : 4 ≤ evenRank G) (p : ℕ) (hp : p ∈ LargeEvenBeta 4 G) (B : Subgroup G) (x : G)
    (L : Subgroup G) (hS : LargeEvenSStar p B x L) (hst : LargeEvenStandardType p B x L) :
    InCatalog G :=
  lc_gl_std_of_typeA hHolt ha ha₀ hb hc₀ hc₁ hc₂ hc₃ hd
    (ggTypeAEndNodeInput_of_inputs' heL heK heC heD) heR hf hg₁ hg₂ hR1 hR h1 h2 h3a h3b h3c h3d
    hKG G hnonab hK hchar he4 p hp B x L hS hst

end Assembly

end CFSG.StandardType
