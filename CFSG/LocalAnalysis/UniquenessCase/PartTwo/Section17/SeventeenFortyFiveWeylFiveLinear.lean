module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveWeylFiveProj
import CFSG.LieType.ChevTwo.OppCl.SLAut
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open CFSG.Open
open Matrix

private theorem semilinConjGL_apply_coe {n : ℕ} {K : Type} [Field K] (A : GL (Fin n) K)
    (σ : K ≃+* K) (x : GL (Fin n) K) :
    ((semilinConjGL A σ x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K).map σ *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  unfold semilinConjGL
  change (((MulAut.conj A) ((GeneralLinearGroup.map σ.toRingHom) x) : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K) = _
  rw [MulAut.conj_apply]
  rfl

private theorem semilinConjGL_mem_statedSL {n : ℕ} {K : Type} [Field K] (A : GL (Fin n) K)
    (σ : K ≃+* K) {x : GL (Fin n) K} (hx : x ∈ StatedSL n K) :
    semilinConjGL A σ x ∈ StatedSL n K := by
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff] at hx ⊢
  have hdet : GeneralLinearGroup.det (semilinConjGL A σ x) = 1 := by
    unfold semilinConjGL
    change GeneralLinearGroup.det
      ((MulAut.conj A) ((GeneralLinearGroup.map σ.toRingHom) x)) = 1
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, GeneralLinearGroup.map_det]
    have hx' : GeneralLinearGroup.det x = 1 := by
      ext
      simpa using hx
    rw [hx']
    simp
  have := congrArg (fun u : Kˣ => (u : K)) hdet
  simpa using this

private noncomputable def semilinConjStatedSL {n : ℕ} {K : Type} [Field K] (A : GL (Fin n) K)
    (σ : K ≃+* K) : StatedSL n K →* StatedSL n K where
  toFun x := ⟨semilinConjGL A σ x, semilinConjGL_mem_statedSL A σ x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul (semilinConjGL A σ) (x : GL (Fin n) K) (y : GL (Fin n) K))

@[simp] private theorem semilinConjStatedSL_coe {n : ℕ} {K : Type} [Field K] (A : GL (Fin n) K)
    (σ : K ≃+* K) (x : StatedSL n K) :
    ((semilinConjStatedSL A σ x : StatedSL n K) : GL (Fin n) K) =
      semilinConjGL A σ (x : GL (Fin n) K) :=
  rfl

private theorem statedProj_symm_mk {n : ℕ} {K : Type} [Field K] (x : StatedSL n K) :
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm
        (QuotientGroup.mk (s := (StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) x :
          StatedProj (StatedSL n K)) =
      QuotientGroup.mk (s := Subgroup.center (SpecialLinearGroup (Fin n) K))
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K).symm x) := by
  unfold CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
  rw [QuotientGroup.congr_symm]
  rfl

private theorem statedProj_apply_mk {n : ℕ} {K : Type} [Field K]
    (y : SpecialLinearGroup (Fin n) K) :
    CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K
        (QuotientGroup.mk (s := Subgroup.center (SpecialLinearGroup (Fin n) K)) y :
          ProjectiveSpecialLinearGroup (Fin n) K) =
      QuotientGroup.mk (s := (StatedScalars (Fin n) K).subgroupOf (StatedSL n K))
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K y) := by
  unfold CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
  rfl

private theorem exists_semilinear_conj_statedProj {n : ℕ} {K : Type} [Field K] [Finite K]
    (hn : 3 ≤ n) (α : MulAut (StatedProj (StatedSL n K))) (hα : α ^ 5 = 1) :
    ∃ (A : GL (Fin n) K) (σ : K ≃+* K), ∀ x : StatedSL n K,
      α (QuotientGroup.mk x) = QuotientGroup.mk (semilinConjStatedSL A σ x) := by
  obtain ⟨A, σ, hAσ⟩ :=
    CFSG.LieType.ChevTwo.OppCl.exists_conj_of_odd_pow (F := K) (n := n) hn
      (m := 5) (show Odd 5 from ⟨2, rfl⟩) α hα
  refine ⟨A, σ, fun x => ?_⟩
  obtain ⟨x', hx'mat, hx'α⟩ := hAσ x
  have hx'eq : x' = semilinConjStatedSL A σ x := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    rw [semilinConjStatedSL_coe, semilinConjGL_apply_coe]
    exact congrFun (congrFun hx'mat i) j
  rw [hx'eq] at hx'α
  exact hx'α

private theorem exists_semilinear_conj_statedProj_two {K : Type} [Field K] [Finite K]
    (α : MulAut (StatedProj (StatedSL 2 K))) :
    ∃ (A : GL (Fin 2) K) (σ : K ≃+* K), ∀ x : StatedSL 2 K,
      α (QuotientGroup.mk x) =
        QuotientGroup.mk (s := (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K))
          (semilinConjStatedSL A σ x) := by
  classical
  let e₂ : StatedProj (StatedSL 2 K) ≃* ProjectiveSpecialLinearGroup (Fin 2) K :=
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  let eS : SpecialLinearGroup (Fin 2) K ≃* StatedSL 2 K :=
    CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K
  let β : ProjectiveSpecialLinearGroup (Fin 2) K ≃*
      ProjectiveSpecialLinearGroup (Fin 2) K := e₂.symm.trans (α.trans e₂)
  obtain ⟨γ, hγ⟩ :=
    (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearEquivAut K).surjective β
  let σ : K ≃+* K := γ.right
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective γ.left
  have hpgl : CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction K
        (Matrix.ProjGenLinGroup.mk A) =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.innerDiagonalAction 2 K A := by
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.innerDiagonalAction_eq_pglAction]
    ext x
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    rw [CFSG.ComponentClassification.CatalogueSchreierLinearTwo.toPGL_pglAction,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.toPGL_pglAction]
  have hdecomp : γ = SemidirectProduct.inl γ.left * SemidirectProduct.inr γ.right :=
    (SemidirectProduct.inl_left_mul_inr_right γ).symm
  have hβ : β =
      CFSG.ComponentClassification.CatalogueBLinearSemilinear.semilinearAction 2 K A σ := by
    have hγ' : β = CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction K γ :=
      hγ.symm
    rw [hγ', hdecomp, map_mul,
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_inl,
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_inr,
      ← hA, hpgl]
    change CFSG.ComponentClassification.CatalogueBHigherLinearAction.innerDiagonalAction 2 K A *
        CFSG.GorensteinWalter.psl2FieldAut K σ =
      CFSG.ComponentClassification.CatalogueBLinearSemilinear.semilinearAction 2 K A σ
    rw [show CFSG.ComponentClassification.CatalogueBLinearSemilinear.semilinearAction 2 K A σ =
        CFSG.ComponentClassification.CatalogueBHigherLinearAction.innerDiagonalAction 2 K A *
          CFSG.ComponentClassification.CatalogueBHigherLinearField.pslFieldAut (Fin 2) K σ from
      rfl]
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearField.pslFieldAut_two]
  have hβapply : ∀ y, β y = e₂ (α (e₂.symm y)) := by
    intro y
    simp [β, MulEquiv.trans_apply]
  have hαe₂ : ∀ y, α (e₂.symm y) = e₂.symm (β y) := by
    intro y
    rw [hβapply y, MulEquiv.symm_apply_apply]
  refine ⟨A, σ, fun x => ?_⟩
  have hxy : ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (((eS.symm x : SpecialLinearGroup (Fin 2) K) : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) := by
    have h := congrArg (fun z : StatedSL 2 K =>
      ((z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
      (MulEquiv.apply_symm_apply eS x)
    rw [CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 2 K (eS.symm x)] at h
    exact h.symm
  have hcoe : (((eS (CFSG.ComponentClassification.CatalogueBLinearSemilinear.slSemilinearAction
        2 K A σ (eS.symm x)) : StatedSL 2 K) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (((semilinConjStatedSL A σ x : StatedSL 2 K) : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) := by
    rw [CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe,
      CFSG.ComponentClassification.CatalogueBLinearSemilinear.slSemilinearAction_matrix,
      semilinConjStatedSL_coe, semilinConjGL_apply_coe, hxy]
    rfl
  calc α (QuotientGroup.mk x)
      = α (e₂.symm (e₂ (QuotientGroup.mk x))) := by rw [MulEquiv.symm_apply_apply]
    _ = e₂.symm (β (e₂ (QuotientGroup.mk x))) := hαe₂ _
    _ = e₂.symm (β (QuotientGroup.mk (eS.symm x))) := by rw [statedProj_symm_mk]
    _ = e₂.symm (CFSG.ComponentClassification.CatalogueBLinearSemilinear.semilinearAction 2 K A σ
          (QuotientGroup.mk (eS.symm x))) := by rw [hβ]
    _ = e₂.symm (QuotientGroup.mk
          (CFSG.ComponentClassification.CatalogueBLinearSemilinear.slSemilinearAction 2 K A σ
            (eS.symm x))) := by
          simpa only [QuotientGroup.mk'_apply] using
            congrArg e₂.symm
              (CFSG.ComponentClassification.CatalogueBLinearSemilinear.semilinearAction_mk
                2 K A σ (eS.symm x))
    _ = QuotientGroup.mk (eS
          (CFSG.ComponentClassification.CatalogueBLinearSemilinear.slSemilinearAction 2 K A σ
            (eS.symm x))) := statedProj_apply_mk _
    _ = QuotientGroup.mk (semilinConjStatedSL A σ x) := by
          congr 1
          apply Subtype.ext
          apply Units.ext
          ext i j
          exact congrFun (congrFun hcoe i) j

private theorem weylFivePower_of_model_PSL_aux {K : Type} [Field K] [Finite K] {X : Type}
    [Group X] {n p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hKcard : Nat.card K = p ^ f)
    (hn2 : 2 ≤ n) (hn : n ≤ 4) (hp31 : p ≠ 31) (e : X ≃* StatedProj (StatedSL n K)) :
    WeylFivePower X := by
  have hcharP : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hKcard
  have hring : ringChar K = p := (CharP.eq K hcharP (ringChar.charP K)).symm
  have hK31 : ringChar K ≠ 31 := by
    rw [hring]
    exact hp31
  have hZ : ∀ c : Kˣ, GeneralLinearGroup.scalar (Fin n) c ∈ StatedSL n K → c ^ 31 = 1 → c = 1 := by
    intro c hc hc31
    have hmatrix : ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K).det = 1 :=
      CFSG.Open.StatedAPI.mem_statedSL_iff.mp hc
    have hdet : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) c) = 1 := by
      ext
      simpa using hmatrix
    rw [GeneralLinearGroup.det_scalar] at hdet
    simp only [Fintype.card_fin] at hdet
    have hndvd : ¬ 31 ∣ n := by
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
    have hcop : Nat.Coprime n 31 :=
      Nat.coprime_comm.mp ((by norm_num : Nat.Prime 31).coprime_iff_not_dvd.mpr hndvd)
    have hgcd : orderOf c ∣ Nat.gcd n 31 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hdet) (orderOf_dvd_of_pow_eq_one hc31)
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hgcd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
  have hnf : ∀ α : MulAut (StatedProj (StatedSL n K)), α ^ 5 = 1 →
      ∃ (m : ℕ) (A : GL (Fin n) K) (σ : K ≃+* K), ¬ 5 ∣ m ∧
        ∃ θ : StatedSL n K →* StatedSL n K,
          (∀ x : StatedSL n K, (θ x : GL (Fin n) K) = semilinConjGL A σ x) ∧
          ∀ x : StatedSL n K,
            (α ^ m) (QuotientGroup.mk x : StatedProj (StatedSL n K)) =
              QuotientGroup.mk (θ x) := by
    intro α hα
    have hmain : ∃ (A : GL (Fin n) K) (σ : K ≃+* K), ∀ x : StatedSL n K,
        α (QuotientGroup.mk x) = QuotientGroup.mk (semilinConjStatedSL A σ x) := by
      by_cases h2 : n = 2
      · subst h2
        exact exists_semilinear_conj_statedProj_two α
      · exact exists_semilinear_conj_statedProj (by omega) α hα
    obtain ⟨A, σ, hAσ⟩ := hmain
    exact ⟨1, A, σ, by norm_num, semilinConjStatedSL A σ, fun x => rfl,
      fun x => by simpa using hAσ x⟩
  exact WeylFivePower.of_mulEquiv e.symm
    (weylFivePower_statedProj (ι := Fin n) (K := K) hK31 (StatedSL n K) hZ
      (Or.inl (by simpa using hn)) hnf)

theorem weylFivePower_of_model_PSL {X : Type} [Group X] {n p f : ℕ}
    (h : StatedClassicalModel X .PSL n p f) (hn : n ≤ 4) (hp2 : p ≠ 2) (hp31 : p ≠ 31) :
    WeylFivePower X := by
  obtain ⟨⟨hp, hf, hn2, hne2, hne3⟩, K, hfield, hfin, hKcard, ⟨e⟩⟩ := h
  have _hp2 : p ≠ 2 := hp2
  exact @weylFivePower_of_model_PSL_aux K hfield hfin X _ n p f hp hf hKcard hn2 hn hp31 e

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
