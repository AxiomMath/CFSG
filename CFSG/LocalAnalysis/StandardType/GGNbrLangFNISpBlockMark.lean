module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOne
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagSp
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagLinear
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOrthogonalBlocks
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSymplectic
public import CFSG.RankThree.PartTwo.KFacts.AutPSpFaithful
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatReindex

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedSp StatedProj StatedSL)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  (gsp conjAut fieldAut conjAut_proj fieldAut_proj coe_conjSp coe_fieldSp statedSp_le_gsp)
open CFSG.StandardType.ClassicalBlocks
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm

theorem kgfniSpMark_map_reindexGL {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {K : Type} [Field K] (e : ι ≃ ι')
    (φ : K →+* K) (A : GL ι K) :
    Matrix.GeneralLinearGroup.map φ (CFSG.RankThree.GF2n.Stroth80.reindexGL e A) =
      CFSG.RankThree.GF2n.Stroth80.reindexGL e
        (Matrix.GeneralLinearGroup.map φ A) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp [CFSG.RankThree.GF2n.Stroth80.coe_reindexGL, Matrix.reindex_apply,
    Matrix.GeneralLinearGroup.map_apply]


theorem kgfniSpMark_spBlock_of_semilinear {H : Type} [Group H]
    {F : Subgroup H} {n₁ : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : ↥F ≃* ↥(StatedSp n₁ K)) {C0 : Subgroup H} (hC0 : IsComponentOf C0 F)
    (hn₁ : 2 ≤ n₁)
    (f' : MulAut ↥C0) (B : GL (Fin n₁ ⊕ Fin n₁) K) (hB : B ∈ StatedSp n₁ K)
    (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hsq : ∀ c : ↥C0,
      ((e ⟨f' c, hC0.1 (f' c).2⟩ : StatedSp n₁ K) : GL (Fin n₁ ⊕ Fin n₁) K) =
        B * Matrix.GeneralLinearGroup.map (σ : K →+* K)
          ((e ⟨c, hC0.1 c.2⟩ : StatedSp n₁ K) : GL (Fin n₁ ⊕ Fin n₁) K) * B⁻¹) :
    LargeEvenMarking ↥C0 (fun _ _ _ I _ θ =>
      ¬ ∃ φ ∈ Subgroup.closure I,
        LargeEvenInduces θ (fun c c' : ↥C0 => f' c = c') φ) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hfcard⟩ := FiniteField.card K 2
  let fe : ℕ := (f : ℕ)
  have hfcard' : Fintype.card K = 2 ^ fe := by
    dsimp only [fe]
    exact hfcard
  have hcard : Nat.card K = 2 ^ fe := by
    rw [Nat.card_eq_fintype_card, hfcard']
  have hfpos : 0 < fe := f.pos
  have hf2 : 2 ≤ fe := by
    rcases Nat.lt_or_ge fe 2 with hlt | hge
    · interval_cases fe
      have hK2 : Nat.card K = 2 := by rw [hcard]; norm_num
      exact absurd (RingEquiv.ext (fun x => ringEquiv_apply_eq_of_card_two hK2 σ x)) hσ
    · exact hge
  have h4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ fe := Nat.pow_le_pow_right (by norm_num) hf2
  haveI : NeZero n₁ := ⟨by omega⟩
  have hqSp : CFSG.Assembly.IsQuasisimple ↥(StatedSp n₁ K) :=
    Sp.isQuasisimple_statedSp_of_not_small
      (m := n₁) (by omega) (by omega) (by omega)
  have hqF : CFSG.Assembly.IsQuasisimple ↥F :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv e hqSp
  have hC0_eq : C0 = F := GGHalf.eq_of_isComponentOf_isQuasisimple hqF hC0
  have hlab : LargeEvenInLambda2 (⟨.C, n₁, fe⟩ : LargeEvenLabel) :=
    ⟨Nat.succ_le_of_lt hfpos, hn₁, fun _ => hf2⟩
  let eC0 : ↥C0 ≃* ↥(StatedSp n₁ K) :=
    (MulEquiv.subgroupCongr hC0_eq).trans e
  have heC0_coe : ∀ c : ↥C0,
      (((eC0 c : ↥(StatedSp n₁ K)) : GL (Fin n₁ ⊕ Fin n₁) K) :
        Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁ ⊕ Fin n₁) K) =
      (((e ⟨c, hC0.1 c.2⟩ : ↥(StatedSp n₁ K)) : GL (Fin n₁ ⊕ Fin n₁) K) :
        Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁ ⊕ Fin n₁) K) := by
    intro c
    rfl
  have hscal : (LargeEvenScalars (Fin n₁ ⊕ Fin n₁) K).subgroupOf (StatedSp n₁ K) = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := n₁) (K := K)
  have hcenter : Subgroup.center (StatedSp n₁ K) =
      (LargeEvenScalars (Fin n₁ ⊕ Fin n₁) K).subgroupOf (StatedSp n₁ K) := by
    rw [Sp.center_statedSp_eq_bot,
      hscal]
  have hmap : (Subgroup.center ↥C0).map eC0.toMonoidHom =
      (LargeEvenScalars (Fin n₁ ⊕ Fin n₁) K).subgroupOf (StatedSp n₁ K) := by
    change (Subgroup.center ↥C0).map (eC0 : ↥C0 →* ↥(StatedSp n₁ K)) = _
    rw [Subgroup.map_center_eq eC0, hcenter]
  let θ : ↥C0 ⧸ Subgroup.center ↥C0 ≃* LargeEvenProj (LargeEvenSpGroup K n₁) :=
    QuotientGroup.congr (Subgroup.center ↥C0)
      ((LargeEvenScalars (Fin n₁ ⊕ Fin n₁) K).subgroupOf (StatedSp n₁ K)) eC0 hmap
  have hθmk : ∀ c : ↥C0,
      θ (QuotientGroup.mk c) =
        LargeEvenProjMk (LargeEvenSpGroup K n₁) (eC0 c) := by
    intro c
    exact QuotientGroup.congr_mk _ _ _ _ c
  have hsimple : IsSimpleGroup (LargeEvenProj (LargeEvenSpGroup K n₁)) := by
    change IsSimpleGroup (StatedProj (StatedSp n₁ K))
    exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K n₁ (by omega)
      (Or.inl (Or.inr h4))
  have hnaSp : ∃ a b : ↥(StatedSp n₁ K), a * b ≠ b * a := by
    have hnab := exists_mul_ne_mul_centerQuot_of_perfect hqSp.1 hqSp.2.toNontrivial
    have hcen : Subgroup.center ↥(StatedSp n₁ K) = ⊥ :=
      Sp.center_statedSp_eq_bot
        (m := n₁)
    let eb : (↥(StatedSp n₁ K) ⧸ Subgroup.center ↥(StatedSp n₁ K)) ≃* ↥(StatedSp n₁ K) :=
      (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
    exact nonabelian_of_mulEquiv eb hnab
  have hna : ∃ a b : LargeEvenProj (LargeEvenSpGroup K n₁), a * b ≠ b * a :=
    nonabelian_of_mulEquiv (TableBSymp.spProjEquivSp (K := K) (m := n₁)).symm hnaSp
  refine ⟨hC0.2.2.1, ⟨⟨.C, n₁, fe⟩, hlab, ?_⟩⟩
  change LargeEvenRecipeSymplectic n₁ (2 ^ fe) false
    (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : ↥C0 ⧸ Subgroup.center ↥C0 ≃* R,
        ¬ ∃ φ ∈ Subgroup.closure I,
          LargeEvenInduces θ (fun c c' : ↥C0 => f' c = c') φ)
  refine ⟨K, inferInstance, inferInstance, hcard, hsimple, hna, θ, ?_⟩
  rintro ⟨φ, hφcl, hind⟩
  have hIrange : (LargeEvenMatConjImage (LargeEvenProjMk
      (if false = true then ⁅LargeEvenSpGroup K n₁, LargeEvenSpGroup K n₁⁆
        else LargeEvenSpGroup K n₁)) (LargeEvenGSpSet K n₁) : Set _) =
      ((conjAut n₁ K).range : Set (MulAut (LargeEvenProj (LargeEvenSpGroup K n₁)))) := by
    ext ψ
    constructor
    · intro hψ
      obtain ⟨A, rfl⟩ := RecipeFieldSp.exists_conjAut_of_mem hψ
      exact ⟨A, rfl⟩
    · rintro ⟨A, rfl⟩
      exact NbrGraphSymplectic.conjAut_mem A
  rw [hIrange, Subgroup.closure_eq] at hφcl
  obtain ⟨A, rfl⟩ := hφcl
  let B' : gsp n₁ K := ⟨B, statedSp_le_gsp hB⟩
  have hpoint : ∀ c : ↥C0,
      conjAut n₁ K A (θ (QuotientGroup.mk c)) =
        conjAut n₁ K B' (fieldAut n₁ K σ (θ (QuotientGroup.mk c))) := by
    intro c
    have h1 := hind c (f' c) rfl
    rw [hθmk c, hθmk (f' c)] at h1
    rw [hθmk c, h1]
    change proj n₁ K (eC0 (f' c)) =
      conjAut n₁ K B' (fieldAut n₁ K σ (proj n₁ K (eC0 c)))
    rw [fieldAut_proj, conjAut_proj]
    apply congrArg (proj n₁ K)
    apply Subtype.ext
    rw [coe_conjSp]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_fieldSp]
    rw [heC0_coe (f' c), heC0_coe c]
    simpa [Matrix.GeneralLinearGroup.map_apply] using
      congrArg (fun x : GL (Fin n₁ ⊕ Fin n₁) K =>
        (x : Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁ ⊕ Fin n₁) K)) (hsq c)
  have hsurj : Function.Surjective
      (fun c : ↥C0 => θ (QuotientGroup.mk c)) :=
    θ.surjective.comp (QuotientGroup.mk_surjective (s := Subgroup.center ↥C0))
  have hforall : ∀ y : LargeEvenProj (LargeEvenSpGroup K n₁),
      conjAut n₁ K A y =
        conjAut n₁ K B' (fieldAut n₁ K σ y) := by
    intro y
    obtain ⟨c, rfl⟩ := hsurj y
    exact hpoint c
  have hcomp : conjAut n₁ K A = conjAut n₁ K B' * fieldAut n₁ K σ := by
    ext y
    simpa using hforall y
  have hfield : fieldAut n₁ K σ ∈ (conjAut n₁ K).range := by
    refine ⟨B'⁻¹ * A, ?_⟩
    rw [map_mul, map_inv, hcomp]
    group
  exact hσ ((CFSG.RankThree.PartTwo.KFacts.fieldAut_mem_range_conjAut_iff
    (r := n₁) (K := K) (by omega)).mp hfield)

theorem kgfniSp_spBlock_negMarking_congr {X H : Type} [Group X] [Group H] {F C : Subgroup H}
    {n₁ : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : ↥F ≃* ↥(StatedSp n₁ K)) (hC : IsComponentOf C F)
    (θ : X ≃* ↥C) (fX : MulAut X) (fC : MulAut ↥C) (hθ : ∀ x : X, θ (fX x) = fC (θ x))
    (B : GL (Fin n₁ ⊕ Fin n₁) K) (hB : B ∈ StatedSp n₁ K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hsq : ∀ c : ↥C,
      ((e ⟨fC c, hC.1 (fC c).2⟩ : StatedSp n₁ K) : GL (Fin n₁ ⊕ Fin n₁) K) =
        B * Matrix.GeneralLinearGroup.map (σ : K →+* K)
          ((e ⟨c, hC.1 c.2⟩ : StatedSp n₁ K) : GL (Fin n₁ ⊕ Fin n₁) K) * B⁻¹) :
    GGMarkingAll (K := X) fun _ _ _ I _ θ' => kgInducedAut θ' fX ∉ I := by
  rcases Nat.eq_zero_or_pos n₁ with h0 | hpos
  · subst n₁
    exfalso
    have hCsub : IsComponentOf (C.subgroupOf F) ⊤ :=
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
        (f := F.subtype) F.subtype_injective).1 (by
          simpa only [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hC.1,
            Subgroup.map_top, Subgroup.range_subtype] using hC)
    have hC' : IsComponentOf ((C.subgroupOf F).map e.toMonoidHom)
        (⊤ : Subgroup ↥(StatedSp 0 K)) := by
      have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective
        hCsub e.toMonoidHom e.injective
      rwa [Subgroup.map_top_of_surjective _ e.surjective] at h
    have htop : (⊤ : Subgroup ↥(StatedSp 0 K)).map (StatedSp 0 K).subtype =
        StatedSp 0 K := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
    have hGL : IsComponentOf (((C.subgroupOf F).map e.toMonoidHom).map
        (StatedSp 0 K).subtype) (StatedSp 0 K) := by
      have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
        (f := (StatedSp 0 K).subtype) (StatedSp 0 K).subtype_injective).2 hC'
      rwa [htop] at h
    exact not_isComponentOf_statedSp_of_small (Or.inl rfl) _ hGL
  · rcases Nat.lt_or_ge 1 n₁ with hlt | hge
    · have hn2 : 2 ≤ n₁ := by omega
      apply kgFieldRestriction_of_oneMarking_congr θ fX fC hθ
      refine largeEvenMarking_mono ?_
        (kgfniSpMark_spBlock_of_semilinear e hC hn2 fC B hB σ hσ hsq)
      intro lab R _ I F' θ' hneg
      rintro ⟨φ, hφ, hind⟩
      exact hneg ⟨φ, hφ, fun c c' hcc' => hind c c' hcc'.symm⟩
    · have hn1 : n₁ = 1 := by omega
      subst hn1
      have hK2 : Nat.card K ≠ 2 := by
        intro h
        exact hσ (RingEquiv.ext (fun x => ringEquiv_apply_eq_of_card_two h σ x))
      have hqSp : CFSG.Assembly.IsQuasisimple ↥(StatedSp 1 K) :=
        Sp.isQuasisimple_statedSp_of_not_small
          (m := 1) (by omega) (fun h => hK2 h.2) (by omega)
      have hCF : C = F := GGHalf.eq_of_isComponentOf_isQuasisimple
        (CFSG.Assembly.IsQuasisimple.of_mulEquiv e hqSp) hC
      let eC : ↥C ≃* ↥(StatedSp 1 K) := (MulEquiv.subgroupCongr hCF).trans e
      let eSL : ↥(StatedSp 1 K) ≃* ↥(StatedSL 2 K) :=
        (Subgroup.equivMapOfInjective (StatedSp 1 K)
          (CFSG.RankThree.GF2n.Stroth80.reindexGL
            CFSG.RankThree.GF2n.Stroth80.sumFinTwo).toMonoidHom
          (CFSG.RankThree.GF2n.Stroth80.reindexGL
            CFSG.RankThree.GF2n.Stroth80.sumFinTwo).injective).trans
          (MulEquiv.subgroupCongr
            CFSG.RankThree.GF2n.Stroth80.map_reindexGL_statedSp_one)
      let φ : ↥C ≃* ↥(StatedSL 2 K) := eC.trans eSL
      let θst : X ≃* ↥(StatedSL 2 K) := θ.trans φ
      let fSt : MulAut ↥(StatedSL 2 K) := φ.symm.trans (fC.trans φ)
      have hθst : ∀ x : X, θst (fX x) = fSt (θst x) := by
        intro x
        dsimp only [θst, fSt, φ]
        simp only [MulEquiv.trans_apply]
        rw [hθ x]
        have hcancel : (eC.trans eSL).symm (eSL (eC (θ x))) = θ x := by
          show (eC.trans eSL).symm ((eC.trans eSL) (θ x)) = θ x
          rw [MulEquiv.symm_apply_apply]
        rw [hcancel]
      have hSLnormal : (StatedSL 2 K).Normal := by
        rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det]
        infer_instance
      have hqSL : CFSG.Assembly.IsQuasisimple ↥(StatedSL 2 K) :=
        CFSG.Assembly.IsQuasisimple.of_mulEquiv eSL.symm hqSp
      have hSLcomp : IsComponentOf (StatedSL 2 K) ⊤ :=
        ⟨le_top, CFSG.Assembly.IsSubnormal.step le_top (hSLnormal.subgroupOf ⊤)
          (CFSG.Assembly.IsSubnormal.refl ⊤), hqSL⟩
      let Bst : GL (Fin 2) K :=
        CFSG.RankThree.GF2n.Stroth80.reindexGL
          CFSG.RankThree.GF2n.Stroth80.sumFinTwo B
      have heC_coe : ∀ c : ↥C,
          ((eC c : ↥(StatedSp 1 K)) : GL (Fin 1 ⊕ Fin 1) K) =
            ((e ⟨c, hC.1 c.2⟩ : ↥(StatedSp 1 K)) : GL (Fin 1 ⊕ Fin 1) K) := by
        intro c
        rfl
      have heSL_coe : ∀ g : ↥(StatedSp 1 K),
          ((eSL g : ↥(StatedSL 2 K)) : GL (Fin 2) K) =
            CFSG.RankThree.GF2n.Stroth80.reindexGL
              CFSG.RankThree.GF2n.Stroth80.sumFinTwo g := by
        intro g
        rfl
      have hsqSt : ∀ c : ↥(StatedSL 2 K),
          ((fSt c : ↥(StatedSL 2 K)) : GL (Fin 2) K) =
            Bst * Matrix.GeneralLinearGroup.map (σ : K →+* K)
              ((c : ↥(StatedSL 2 K)) : GL (Fin 2) K) * Bst⁻¹ := by
        intro c
        obtain ⟨c', rfl⟩ := φ.surjective c
        have h := congrArg (fun x : GL (Fin 1 ⊕ Fin 1) K =>
          CFSG.RankThree.GF2n.Stroth80.reindexGL
            CFSG.RankThree.GF2n.Stroth80.sumFinTwo x) (hsq c')
        rw [map_mul, map_mul, map_inv, ← kgfniSpMark_map_reindexGL] at h
        have hfst : fSt (φ c') = φ (fC c') := by
          simp only [fSt, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
        have hL : ((fSt (φ c') : ↥(StatedSL 2 K)) : GL (Fin 2) K) =
            CFSG.RankThree.GF2n.Stroth80.reindexGL
              CFSG.RankThree.GF2n.Stroth80.sumFinTwo
              (e ⟨fC c', hC.1 (fC c').2⟩) := by
          rw [hfst]
          change ((eSL (eC (fC c')) : ↥(StatedSL 2 K)) : GL (Fin 2) K) = _
          rw [heSL_coe]
          congr 1
        have hR : ((φ c' : ↥(StatedSL 2 K)) : GL (Fin 2) K) =
            CFSG.RankThree.GF2n.Stroth80.reindexGL
              CFSG.RankThree.GF2n.Stroth80.sumFinTwo
              (e ⟨c', hC.1 c'.2⟩) := by
          change ((eSL (eC c') : ↥(StatedSL 2 K)) : GL (Fin 2) K) = _
          rw [heSL_coe]
          congr 1
        rw [hL, hR]
        simpa [Bst] using h
      exact ClassicalBlocks.kgFieldRestriction_linearBlock_of_semilinear_congr
        (F := ⊤) (C := StatedSL 2 K) (m := 2) (E := K)
        (e := Subgroup.topEquiv) (hC := hSLcomp) (θ := θst) (fX := fX)
        (fC := fSt) (hθ := hθst) (B := Bst) (τ := σ) (hτ := hσ) (hsq := hsqSt)

end CFSG.StandardType
