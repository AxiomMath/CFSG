module

public import CFSG.LocalAnalysis.StandardType.KGLangTorusMPartDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixLabel
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms
public import CFSG.Assembly.GL83LieDefs
import CFSG.LocalAnalysis.StandardType.KGLangTorusSpan
import CFSG.LocalAnalysis.StandardType.KGLangTorusSpanH90
import CFSG.LocalAnalysis.StandardType.KGLangTorusInnerModel
import CFSG.LocalAnalysis.StandardType.KGLangTorusClassicalInner
import CFSG.LocalAnalysis.StandardType.KGLangTorusDatumOfModels
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinearLang
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearProj
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclicLabels
import CFSG.LocalAnalysis.StandardType.GGTableBTypeALift
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.Quasithin.Vol2.Ch10Reselect.GaloisDescent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType CFSG.RankThree.PerfectCover CFSG.HardMathSupport.C14Exc

private noncomputable def kgLangCLinAux_cHom (d : ℕ) (𝕂 : Type) [Field 𝕂] :
    GL (Fin d) 𝕂 →* MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) 𝕂)) :=
  (MulAut.congr (TypeA.recipeEquiv d 𝕂)).symm.toMonoidHom.comp
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d 𝕂)

private theorem kgLangCLinAux_cHom_apply_mk {d : ℕ} {𝕂 : Type} [Field 𝕂]
    (A : GL (Fin d) 𝕂) (h : LargeEvenSLGroup (Fin d) 𝕂) :
    kgLangCLinAux_cHom d 𝕂 A (LargeEvenProjMk (LargeEvenSLGroup (Fin d) 𝕂) h) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin d) 𝕂)
        ⟨A * (h : GL (Fin d) 𝕂) * A⁻¹, by
          rw [TypeA.mem_largeEvenSLGroup_iff]
          have hd : Matrix.GeneralLinearGroup.det (A * (h : GL (Fin d) 𝕂) * A⁻¹) = 1 := by
            have hh : Matrix.GeneralLinearGroup.det (h : GL (Fin d) 𝕂) = 1 := by
              apply Units.ext
              rw [Matrix.GeneralLinearGroup.val_det_apply,
                TypeA.mem_largeEvenSLGroup_iff.mp h.2, Units.val_one]
            rw [map_mul, map_mul, map_inv, hh, mul_one, mul_inv_cancel]
          rw [← Matrix.GeneralLinearGroup.val_det_apply, hd, Units.val_one]⟩ := by
  have h1 : MulAut.congr (TypeA.recipeEquiv d 𝕂) (kgLangCLinAux_cHom d 𝕂 A) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d 𝕂 A := by
    simp only [kgLangCLinAux_cHom, MonoidHom.comp_apply]
    exact MulEquiv.apply_symm_apply _ _
  have h2 := congrArg (fun φ => φ ((TypeA.recipeEquiv d 𝕂)
    (LargeEvenProjMk (LargeEvenSLGroup (Fin d) 𝕂) h))) h1
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulEquiv.apply_symm_apply] at h2
  apply (TypeA.recipeEquiv d 𝕂).injective
  rw [h2, TypeA.recipeEquiv_mk, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj,
    TypeA.recipeEquiv_mk]
  congr 1
  apply Subtype.ext
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation, TypeA.coe_slKerEquiv,
    TypeA.coe_slKerEquiv]
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv]

private theorem kgLangCLinAux_cHom_mem {d : ℕ} {𝕂 : Type} [Field 𝕂] (A : GL (Fin d) 𝕂) :
    kgLangCLinAux_cHom d 𝕂 A ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) 𝕂)) Set.univ := by
  refine ⟨A, Set.mem_univ _, ?_⟩
  intro h h' hh
  rw [kgLangCLinAux_cHom_apply_mk]
  congr 1
  exact Subtype.ext hh.symm

private theorem kgLangCLinAux_cHom_range {d : ℕ} {𝕂 : Type} [Field 𝕂] :
    (kgLangCLinAux_cHom d 𝕂).range =
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) 𝕂)) Set.univ := by
  ext φ
  constructor
  · rintro ⟨A, rfl⟩
    exact kgLangCLinAux_cHom_mem A
  · intro hφ
    obtain ⟨A, -, hA⟩ := hφ
    refine ⟨A, ?_⟩
    ext x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin d) 𝕂).subgroupOf (LargeEvenSLGroup (Fin d) 𝕂)) x
    rw [kgLangCLinAux_cHom_apply_mk]
    exact (hA h ⟨A * (h : GL (Fin d) 𝕂) * A⁻¹, _⟩ rfl).symm

private theorem kgLangCLinAux_cHom_ker {d : ℕ} {𝕂 : Type} [Field 𝕂] [Finite 𝕂] (hd : 3 ≤ d) :
    (kgLangCLinAux_cHom d 𝕂).ker = LargeEvenScalars (Fin d) 𝕂 := by
  ext A
  rw [MonoidHom.mem_ker]
  constructor
  · intro hA
    have h1 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d 𝕂 A = 1 := by
      have h2 : MulAut.congr (TypeA.recipeEquiv d 𝕂) (kgLangCLinAux_cHom d 𝕂 A) =
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d 𝕂 A := by
        simp only [kgLangCLinAux_cHom, MonoidHom.comp_apply]
        exact MulEquiv.apply_symm_apply _ _
      rw [← h2, hA, map_one]
    obtain ⟨-, c, hc⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one
        (K := 𝕂) (n := d) hd A 1 (by rw [map_one, mul_one, h1])
    exact ⟨c, hc⟩
  · rintro ⟨c, rfl⟩
    rw [kgLangCLinAux_cHom, MonoidHom.comp_apply,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_scalar, map_one]

private theorem kgLangCLinAux_prod_range_cyclic {M : Type*} [Monoid M] {p : ℕ} (hp : 0 < p)
    (S : Monoid.End M) (hS : S ^ p = 1) (f : ℕ → M) (hf : ∀ i, f (i+1) = S (f i))
    (hcomm : ∀ i, f i * f 0 = f 0 * f i) :
    ((List.range p).map (fun i => f (i+1))).prod = ((List.range p).map f).prod := by
  have hfp : f p = f 0 := by
    have h : ∀ i, f i = (S ^ i) (f 0) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [hf, ih, pow_succ']; rfl
    rw [h p, hS]
    rfl
  have hcomm0 : ∀ l : List ℕ, (∀ i ∈ l, f i * f 0 = f 0 * f i) →
      (l.map f).prod * f 0 = f 0 * (l.map f).prod := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
        intro hl
        have hi : f i * f 0 = f 0 * f i := hl i List.mem_cons_self
        have hl' : ∀ j ∈ l, f j * f 0 = f 0 * f j :=
          fun j hj => hl j (List.mem_cons_of_mem i hj)
        simp only [List.map_cons, List.prod_cons]
        calc (f i * (l.map f).prod) * f 0
            = f i * ((l.map f).prod * f 0) := by rw [mul_assoc]
          _ = f i * (f 0 * (l.map f).prod) := by rw [ih hl']
          _ = (f i * f 0) * (l.map f).prod := by rw [mul_assoc]
          _ = (f 0 * f i) * (l.map f).prod := by rw [hi]
          _ = f 0 * (f i * (l.map f).prod) := by rw [mul_assoc]
  have hC : ((List.range (p - 1)).map (fun i => f (i+1))).prod * f 0 =
      f 0 * ((List.range (p - 1)).map (fun i => f (i+1))).prod := by
    have h := hcomm0 ((List.range (p - 1)).map (fun i => i+1)) (fun i _ => hcomm i)
    rwa [List.map_map] at h
  have hp1 : p = (p - 1) + 1 := (Nat.succ_pred_eq_of_pos hp).symm
  have hA : ((List.range p).map (fun i => f (i+1))).prod =
      ((List.range (p - 1)).map (fun i => f (i+1))).prod * f p := by
    conv_lhs => rw [hp1]
    rw [List.prod_range_succ, show p - 1 + 1 = p by omega]
  have hB : ((List.range p).map f).prod =
      f 0 * ((List.range (p - 1)).map (fun i => f (i+1))).prod := by
    conv_lhs => rw [hp1]
    rw [List.prod_range_succ']
  rw [hA, hB, hfp]
  exact hC

private theorem kgLangCLinAux_h90_image {p : ℕ} (hp : p.Prime) {ι 𝕂 R : Type} [Fintype ι]
    [DecidableEq ι] [Field 𝕂] [Finite 𝕂] [CharP 𝕂 2] [Group R] [Nonempty ι]
    {σ : 𝕂 ≃+* 𝕂} (hσ : orderOf σ = p)
    (c : GL ι 𝕂 →* MulAut R) (S : Monoid.End (GL ι 𝕂)) (hSp : S ^ p = 1)
    {f : MulAut R} (hfconj : ∀ A : GL ι 𝕂, f * c A * f⁻¹ = c (S A))
    (hker : ∀ A : GL ι 𝕂, c A = 1 → ∃ lam : 𝕂ˣ, A = Matrix.GeneralLinearGroup.scalar ι lam)
    (hsc_ker : ∀ lam : 𝕂ˣ, c (Matrix.GeneralLinearGroup.scalar ι lam) = 1)
    (P : Subgroup (GL ι 𝕂)) (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hPodd : Odd (Nat.card P))
    (B : Subalgebra 𝕂 (Matrix ι ι 𝕂))
    (hB : B = Algebra.adjoin 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _)))
    (β : Matrix ι ι 𝕂 →+* Matrix ι ι 𝕂)
    (hβP : ∀ g ∈ P, β (g : Matrix ι ι 𝕂) ∈ (fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _))
    (hβsc : ∀ r : 𝕂, β (Matrix.scalar ι r) = Matrix.scalar ι (σ r))
    (hβp : ∀ a ∈ B, (⇑β)^[p] a = a)
    (U : Subgroup (GL ι 𝕂)) (hUB : ∀ u : GL ι 𝕂, u ∈ U ↔ (u : Matrix ι ι 𝕂) ∈ B)
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hβU : ∀ u ∈ U, S u ∈ U)
    (hβSiter : ∀ (i : ℕ) (w : GL ι 𝕂),
      (⇑β)^[i] (w : Matrix ι ι 𝕂) = (((S ^ i) w : GL ι 𝕂) : Matrix ι ι 𝕂)) :
    ∀ x ∈ U.map c, ((List.range p).map fun i => endPow (MulAut.conj f).toMonoidHom i x).prod = 1 →
      ∃ s ∈ U.map c, x = s⁻¹ * (MulAut.conj f).toMonoidHom s := by
  have hβS : ∀ w : GL ι 𝕂, β (w : Matrix ι ι 𝕂) = ((S w : GL ι 𝕂) : Matrix ι ι 𝕂) := by
    intro w
    simpa using hβSiter 1 w
  intro x hx hnorm
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
  let seq : ℕ → GL ι 𝕂 := fun i => (S ^ i) u
  have hseq : ∀ i : ℕ, seq (i+1) = S (seq i) := fun i => by
    simp only [seq, pow_succ']; rfl
  have hiter : ∀ i : ℕ, endPow (MulAut.conj f).toMonoidHom i (c u) = c (seq i) := by
    intro i
    induction i with
    | zero => rw [endPow_apply]; rfl
    | succ i ih =>
        rw [show endPow (MulAut.conj f).toMonoidHom (i+1) (c u) =
            (MulAut.conj f) (endPow (MulAut.conj f).toMonoidHom i (c u)) from by
          rw [endPow_apply, Function.iterate_succ_apply']; rfl, ih]
        change f * c (seq i) * f⁻¹ = c (seq (i+1))
        rw [hfconj (seq i)]
        congr 1
        show S (seq i) = seq (i+1)
        rw [hseq i]
  have hnorm_u : c (((List.range p).map seq).prod) = 1 := by
    rw [map_list_prod, List.map_map, ← hnorm]
    apply congrArg List.prod
    apply List.map_congr_left
    intro i _
    exact (hiter i).symm
  obtain ⟨lam, hlam⟩ : ∃ lam : 𝕂ˣ, ((List.range p).map seq).prod =
      Matrix.GeneralLinearGroup.scalar ι lam := by
    have h : ((List.range p).map seq).prod ∈ c.ker := MonoidHom.mem_ker.mpr hnorm_u
    obtain ⟨lam, hlam⟩ := hker _ h
    exact ⟨lam, hlam⟩
  have hβfix : β (((List.range p).map seq).prod : Matrix ι ι 𝕂) =
      (((List.range p).map seq).prod : Matrix ι ι 𝕂) := by
    let coeU : GL ι 𝕂 →* Matrix ι ι 𝕂 := Units.coeHom _
    let m : List (GL ι 𝕂) := (List.range p).map seq
    have hmS : m.map S = (List.range p).map (fun i => seq (i+1)) := by
      dsimp only [m]
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact (hseq i).symm
    have hcomm : ∀ i, seq i * seq 0 = seq 0 * seq i := fun i => by
      have h1 : seq i ∈ U := by
        simp only [seq]
        induction i with
        | zero => simpa using hu
        | succ i ih => rw [pow_succ']; exact hβU _ ih
      have h2 : seq 0 ∈ U := by simpa [seq] using hu
      exact hUab _ h1 _ h2
    have hmain : β (coeU m.prod) = coeU m.prod := by
      calc β (coeU m.prod)
          = β ((m.map coeU).prod) := by rw [map_list_prod coeU m]
        _ = ((m.map coeU).map β).prod := by rw [map_list_prod β]
        _ = (m.map (β ∘ coeU)).prod := by rw [List.map_map]
        _ = (m.map (coeU ∘ S)).prod :=
              congrArg List.prod (List.map_congr_left (fun w _ => hβS w))
        _ = ((m.map S).map coeU).prod :=
              congrArg List.prod (List.comp_map coeU S m)
        _ = coeU ((m.map S).prod) := by rw [map_list_prod coeU]
        _ = coeU ((List.range p).map (fun i => seq (i+1))).prod := by rw [hmS]
        _ = coeU ((List.range p).map seq).prod := by
              rw [kgLangCLinAux_prod_range_cyclic hp.pos S hSp seq hseq hcomm]
        _ = coeU m.prod := rfl
    exact hmain
  have hσlam : σ lam = lam := by
    have h := hβfix
    rw [hlam] at h
    simp only [Matrix.GeneralLinearGroup.coe_scalar] at h
    rw [hβsc] at h
    exact Matrix.scalar_inj.mp h
  have hσlam' : σ ((↑lam)⁻¹) = (↑lam)⁻¹ := by
    rw [map_inv₀, hσlam]
  obtain ⟨μ, hμ0, hμ⟩ := CFSG.Quasithin.Vol2.Ch10Reselect.gd_norm_surj σ hσ.symm hp.pos
    (↑lam)⁻¹ (inv_ne_zero lam.ne_zero) hσlam'
  let μu : 𝕂ˣ := Units.mk0 μ hμ0
  let u' : GL ι 𝕂 := Matrix.GeneralLinearGroup.scalar ι μu * u
  have hu'_mem : (u' : Matrix ι ι 𝕂) ∈ B := by
    have h1 : (u' : Matrix ι ι 𝕂) = Matrix.scalar ι μ *
        (u : Matrix ι ι 𝕂) := by
      simp only [u', μu, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    rw [h1]
    exact mul_mem (Subalgebra.algebraMap_mem _ μ) ((hUB u).mp hu)
  have hnorm_u' : ((List.range p).map (fun i => (⇑β)^[i] (u' : Matrix ι ι 𝕂))).prod = 1 := by
    have hterm : ∀ i : ℕ, (⇑β)^[i] (u' : Matrix ι ι 𝕂) =
        Matrix.scalar ι ((σ ^ i) μ) * (⇑β)^[i] (u : Matrix ι ι 𝕂) := by
      intro i
      have hval : (u' : Matrix ι ι 𝕂) = Matrix.scalar ι μ *
          (u : Matrix ι ι 𝕂) := by
        simp only [u', μu, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
      rw [hval]
      induction i with
      | zero => simp
      | succ i ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, hβsc]
          congr 1
          rw [pow_succ', RingAut.mul_apply]
    have hsplit : ∀ l : List ℕ,
        (l.map (fun i => Matrix.scalar ι ((σ ^ i) μ) *
          (⇑β)^[i] (u : Matrix ι ι 𝕂))).prod =
        (l.map (fun i => Matrix.scalar ι ((σ ^ i) μ))).prod *
        (l.map (fun i => (⇑β)^[i] (u : Matrix ι ι 𝕂))).prod := by
      intro l
      induction l with
      | nil => simp
      | cons i l ih =>
          simp only [List.map_cons, List.prod_cons, ih]
          have hcomm : Commute ((⇑β)^[i] (u : Matrix ι ι 𝕂))
              ((l.map fun j => Matrix.scalar ι ((σ ^ j) μ)).prod) := by
            apply Commute.list_prod_right
            intro x hx
            obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
            exact (Matrix.scalar_commute ((σ ^ j) μ) (fun r' => mul_comm _ _) _).symm
          exact hcomm.mul_mul_mul_comm _ _
    have hA : (List.map (fun i => (⇑β)^[i] (u : Matrix ι ι 𝕂)) (List.range p)).prod =
        (List.map (fun i => (seq i : Matrix ι ι 𝕂)) (List.range p)).prod := by
      congr 1
      apply List.map_congr_left
      intro i _
      exact hβSiter i u
    have hcoe : (List.map (fun i => (seq i : Matrix ι ι 𝕂)) (List.range p)).prod =
        (Units.coeHom (Matrix ι ι 𝕂)) (((List.range p).map seq).prod) := by
      rw [map_list_prod (Units.coeHom (Matrix ι ι 𝕂)) ((List.range p).map seq), List.map_map]
      rfl
    have hlam_matrix : (List.map (fun i => (seq i : Matrix ι ι 𝕂)) (List.range p)).prod =
        Matrix.scalar ι (↑lam) := by
      rw [hcoe, hlam]
      simp [Matrix.GeneralLinearGroup.coe_scalar]
    have hscalar : (List.map (fun i => Matrix.scalar ι ((σ ^ i) μ)) (List.range p)).prod =
        Matrix.scalar ι ((List.map (fun i => (σ ^ i) μ) (List.range p)).prod) := by
      rw [map_list_prod (Matrix.scalar ι) (List.map (fun i => (σ ^ i) μ) (List.range p)),
        List.map_map]
      rfl
    have hlam_list : (List.map (fun i => (σ ^ i) μ) (List.range p)).prod = (↑lam)⁻¹ := by
      rw [← List.prod_toFinset (f := fun i => (σ ^ i) μ) (l := List.range p) List.nodup_range,
        List.toFinset_range]
      exact hμ
    rw [List.map_congr_left (fun i _ => hterm i), hsplit (List.range p), hscalar, hlam_list,
      hA, hlam_matrix]
    simp
  obtain ⟨s, hsB, hs⟩ := kgLangC_span_h90 hp hσ P hPab hPodd B hB β hβP hβsc hβp u' hu'_mem hnorm_u'
  have hsU : s ∈ U := (hUB s).mpr hsB
  refine ⟨c s, Subgroup.mem_map.mpr ⟨s, hsU, rfl⟩, ?_⟩
  have hsu : c u' = c u := by
    have hc1 : c (Matrix.GeneralLinearGroup.scalar ι μu) = 1 := hsc_ker μu
    rw [show u' = Matrix.GeneralLinearGroup.scalar ι μu * u from rfl, map_mul, hc1, one_mul]
  have hsGL : u' = s⁻¹ * S s := by
    apply Units.ext
    rw [hs, Units.val_mul]
    congr 1
    exact hβS s
  have hcu : c u = (c s)⁻¹ * (f * c s * f⁻¹) := by
    rw [← hsu, hsGL, map_mul, map_inv, hfconj s]
  simpa [MulAut.conj_apply] using hcu


theorem kgLangC_torusInput_linear {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d n : ℕ} (hd : 3 ≤ d)
    (hpd : ¬ p ∣ d) (𝕂 : Type) [Field 𝕂] [Finite 𝕂] (h𝕂 : Nat.card 𝕂 = 2 ^ n)
    (J : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) 𝕂))))
    (hJ : (J : Set (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) 𝕂)))) =
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) 𝕂)) Set.univ)
    {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) 𝕂))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) 𝕂)))
    (hfp : orderOf f = p) :
    KGLangTorusInput p J (MulAut.conj f).toMonoidHom := by
  classical
  haveI : CharP 𝕂 2 := charP_two_of_card h𝕂
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let c := kgLangCLinAux_cHom (d := d) (𝕂 := 𝕂)
  have hc_range : c.range =
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) 𝕂)) Set.univ :=
    kgLangCLinAux_cHom_range
  have hc_ker : c.ker = LargeEvenScalars (Fin d) 𝕂 := kgLangCLinAux_cHom_ker hd
  have hJc : J = c.range := by
    rw [← SetLike.coe_set_eq]
    rw [hJ, hc_range]
  obtain ⟨σ, hσeq⟩ := RecipeFieldLinear.congr_field_eq hf
  have hfieldAut_inj :
      Function.Injective (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut d 𝕂) := by
    intro σ τ h
    have h1 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut d 𝕂 (σ * τ⁻¹) = 1 := by
      rw [map_mul, map_inv, h]
      group
    have h2 : σ * τ⁻¹ = 1 := by
      by_contra hne
      exact hne (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one
        (K := 𝕂) (n := d) hd (1 : GL (Fin d) 𝕂) (σ * τ⁻¹) (by rwa [map_one, one_mul])).1
    exact mul_inv_eq_one.mp h2
  have hσord : orderOf σ = p := by
    have h1 : orderOf (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut d 𝕂 σ) = p := by
      rw [← hσeq]
      exact (orderOf_injective ((MulAut.congr (TypeA.recipeEquiv d 𝕂)).toMonoidHom)
        (MulAut.congr (TypeA.recipeEquiv d 𝕂)).injective f).trans hfp
    rw [← orderOf_injective (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut d 𝕂)
      hfieldAut_inj σ]
    exact h1
  have hconj : ∀ A : GL (Fin d) 𝕂,
      f * c A * f⁻¹ = c (Matrix.GeneralLinearGroup.map (σ : 𝕂 →+* 𝕂) A) := by
    intro A
    have h2 : MulAut.congr (TypeA.recipeEquiv d 𝕂) (c A) =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d 𝕂 A := by
      simp only [c, kgLangCLinAux_cHom, MonoidHom.comp_apply]
      exact MulEquiv.apply_symm_apply _ _
    have h3 : MulAut.congr (TypeA.recipeEquiv d 𝕂)
          (c (Matrix.GeneralLinearGroup.map (σ : 𝕂 →+* 𝕂) A)) =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d 𝕂
          (Matrix.GeneralLinearGroup.map (σ : 𝕂 →+* 𝕂) A) := by
      simp only [c, kgLangCLinAux_cHom, MonoidHom.comp_apply]
      exact MulEquiv.apply_symm_apply _ _
    apply (MulAut.congr (TypeA.recipeEquiv d 𝕂)).injective
    rw [map_mul, map_mul, map_inv, hσeq, h2, h3,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut_mul_conjAut]
    group
  intro E hE hEfix
  let P : Subgroup (GL (Fin d) 𝕂) := E.comap c
  have hPmem : ∀ x, x ∈ P ↔ c x ∈ E := fun x => Iff.rfl
  have hEfix' : ∀ x ∈ E, f * x * f⁻¹ = x := by
    intro x hx
    have h := (hEfix x hx).2
    change MulAut.conj f x = x at h
    rwa [MulAut.conj_apply] at h
  have hEJ : E ≤ J := fun x hx => (hEfix x hx).1
  have hEcr : E ≤ c.range := by rw [← hJc]; exact hEJ
  have hPmap : P.map c = E := by
    show (E.comap c).map c = E
    exact Subgroup.map_comap_eq_self hEcr
  have hc_ker_le_P : c.ker ≤ P := by
    intro x hx
    show c x ∈ E
    rw [MonoidHom.mem_ker.mp hx]
    exact E.one_mem
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    have hcomm : c a * c b = c b * c a := by
      letI : IsMulCommutative E := hE.1
      exact congrArg Subtype.val (mul_comm' (⟨c a, ha⟩ : E) (⟨c b, hb⟩ : E))
    have hker : a * b * (b * a)⁻¹ ∈ c.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hcomm]
      group
    obtain ⟨lam, hlam⟩ : ∃ lam : 𝕂ˣ, Matrix.GeneralLinearGroup.scalar (Fin d) lam =
        a * b * (b * a)⁻¹ := by
      have h := hker
      rw [hc_ker, largeEvenScalars_def] at h
      exact MonoidHom.mem_range.mp h
    have hap : a ^ p ∈ c.ker := by
      rw [MonoidHom.mem_ker, map_pow, hE.2 (c a) ha]
    obtain ⟨μ, hμ⟩ : ∃ μ : 𝕂ˣ, Matrix.GeneralLinearGroup.scalar (Fin d) μ = a ^ p := by
      have h := hap
      rw [hc_ker, largeEvenScalars_def] at h
      exact MonoidHom.mem_range.mp h
    exact kgLangC_pairing hp hpd (by rw [hlam]; group) hμ.symm
  have hEp : IsPGroup p E := by
    apply IsPGroup.of_exponent_dvd_pow (n := 1)
    rw [pow_one]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 x x.2
  have hEodd : Odd (Nat.card E) := by
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  have h2neven : Even (2 ^ n) := by
    have hn1 : 1 ≤ n := by
      by_contra h
      have hn0 : n = 0 := by omega
      rw [hn0, pow_zero] at h𝕂
      have := Finite.one_lt_card (α := 𝕂)
      omega
    refine ⟨2 ^ (n - 1), ?_⟩
    rw [← two_mul, ← pow_succ', Nat.sub_add_cancel hn1]
  have hker_odd : Odd (Nat.card c.ker) := by
    rw [hc_ker, largeEvenScalars_def]
    haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    have hinj : Function.Injective
        (Matrix.GeneralLinearGroup.scalar (Fin d) : 𝕂ˣ →* GL (Fin d) 𝕂) := by
      intro a b hab
      apply Units.ext
      exact Matrix.scalar_inj.mp (congrArg (fun u : GL (Fin d) 𝕂 =>
        (u : Matrix (Fin d) (Fin d) 𝕂)) hab)
    have hcard : Nat.card
        ((Matrix.GeneralLinearGroup.scalar (Fin d) : 𝕂ˣ →* GL (Fin d) 𝕂).range) =
        Nat.card 𝕂ˣ := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top]
    rw [hcard, Nat.card_units, h𝕂]
    have h1ne : ¬ Even 1 := by rw [Nat.even_iff]; norm_num
    exact (Nat.odd_sub (Nat.one_le_two_pow)).mpr
      ⟨fun ho => absurd ho (Nat.not_odd_iff_even.mpr h2neven), fun he => absurd he h1ne⟩
  have hPcard : Nat.card P = Nat.card c.ker * Nat.card E := by
    have h1 : Nat.card (c.comp P.subtype).ker * Nat.card (c.comp P.subtype).range =
        Nat.card P := Subgroup.card_ker_mul_card_range (c.comp P.subtype)
    have h2 : (c.comp P.subtype).range = E := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype,
        hPmap]
    have h3 : Nat.card (c.comp P.subtype).ker = Nat.card c.ker := by
      apply Nat.card_congr
      refine
        { toFun := fun x => ⟨x.1.1, MonoidHom.mem_ker.mpr (by
            simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype] using
              MonoidHom.mem_ker.mp x.2)⟩
          invFun := fun y => ⟨⟨y.1, hc_ker_le_P y.2⟩, MonoidHom.mem_ker.mpr (by
            simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
            exact MonoidHom.mem_ker.mp y.2)⟩
          left_inv := fun x => by ext; rfl
          right_inv := fun y => by ext; rfl }
    rw [h3, h2] at h1
    exact h1.symm
  have hPodd : Odd (Nat.card P) := by
    rw [hPcard]
    exact hker_odd.mul hEodd
  let B : Subalgebra 𝕂 (Matrix (Fin d) (Fin d) 𝕂) :=
    Algebra.adjoin 𝕂 ((fun g : GL (Fin d) 𝕂 => (g : Matrix (Fin d) (Fin d) 𝕂)) '' (P : Set _))
  let β : Matrix (Fin d) (Fin d) 𝕂 →+* Matrix (Fin d) (Fin d) 𝕂 :=
    (σ : 𝕂 →+* 𝕂).mapMatrix
  have hβP : ∀ g ∈ P, β (g : Matrix (Fin d) (Fin d) 𝕂) ∈
      (fun g : GL (Fin d) 𝕂 => (g : Matrix (Fin d) (Fin d) 𝕂)) '' (P : Set _) := by
    intro g hg
    refine ⟨Matrix.GeneralLinearGroup.map (σ : 𝕂 →+* 𝕂) g, ?_, ?_⟩
    · show c (Matrix.GeneralLinearGroup.map (σ : 𝕂 →+* 𝕂) g) ∈ E
      rw [← hconj g, hEfix' (c g) hg]
      exact hg
    · ext i j
      simp only [β, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.GeneralLinearGroup.map_apply]
  have hβsc : ∀ r : 𝕂, β (Matrix.scalar (Fin d) r) = Matrix.scalar (Fin d) (σ r) := by
    intro r
    ext i j
    by_cases h : i = j
    · subst h
      simp [β, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply]
    · simp [β, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply, h]
  have hσp : σ ^ p = 1 := by rw [← hσord]; exact pow_orderOf_eq_one σ
  let S : Monoid.End (GL (Fin d) 𝕂) := Matrix.GeneralLinearGroup.map (σ : 𝕂 →+* 𝕂)
  have hmap_pow : ∀ k : ℕ, S ^ k =
      (Matrix.GeneralLinearGroup.map (((σ ^ k : 𝕂 ≃+* 𝕂)) : 𝕂 →+* 𝕂) : Monoid.End (GL (Fin d) 𝕂)) := by
    intro k
    induction k with
    | zero =>
        rw [pow_zero]
        exact (Matrix.GeneralLinearGroup.map_id (n := Fin d) (R := 𝕂)).symm
    | succ k ih =>
        rw [pow_succ', ih]
        apply MonoidHom.ext
        intro g
        change ((Matrix.GeneralLinearGroup.map (σ : 𝕂 →+* 𝕂)).comp
            (Matrix.GeneralLinearGroup.map (((σ ^ k : 𝕂 ≃+* 𝕂)) : 𝕂 →+* 𝕂))) g =
          (Matrix.GeneralLinearGroup.map (((σ ^ (k+1) : 𝕂 ≃+* 𝕂)) : 𝕂 →+* 𝕂)) g
        rw [← Matrix.GeneralLinearGroup.map_comp,
          show ((σ : 𝕂 →+* 𝕂).comp ((σ ^ k : 𝕂 ≃+* 𝕂) : 𝕂 →+* 𝕂)) =
            (((σ ^ (k+1) : 𝕂 ≃+* 𝕂)) : 𝕂 →+* 𝕂) from by
              ext x
              rw [RingHom.comp_apply, pow_succ']
              rfl]
  have hSp : S ^ p = 1 := by
    rw [hmap_pow p]
    rw [show (((σ ^ p : 𝕂 ≃+* 𝕂)) : 𝕂 →+* 𝕂) = RingHom.id 𝕂 from by
      rw [hσp]; rfl]
    exact Matrix.GeneralLinearGroup.map_id
  have hβpow : β ^ p = 1 := by
    ext M i j
    have hiter : ∀ (k : ℕ) (N : Matrix (Fin d) (Fin d) 𝕂) (a b : Fin d),
        ((β ^ k) N) a b = (σ ^ k) (N a b) := by
      intro k
      induction k with
      | zero => intro N a b; rw [pow_zero, pow_zero]; rfl
      | succ k ih =>
          intro N a b
          rw [pow_succ']
          change β ((β ^ k) N) a b = (σ ^ (k+1)) (N a b)
          have h1 : β ((β ^ k) N) a b = σ (((β ^ k) N) a b) := rfl
          rw [h1, ih N a b, pow_succ']
          simp
    rw [hiter p M i j, hσp]
    rfl
  have hβp : ∀ a ∈ B, (⇑β)^[p] a = a := by
    intro a _
    rw [← RingHom.coe_pow, hβpow]
    rfl
  have hβB : ∀ x ∈ B, β x ∈ B := by
    intro x hx
    refine Algebra.adjoin_induction (p := fun x _ => β x ∈ B) ?_ ?_ ?_ ?_ hx
    · intro y hy
      obtain ⟨g, hg, rfl⟩ := hy
      exact Algebra.subset_adjoin (hβP g hg)
    · intro r
      have hr : algebraMap 𝕂 (Matrix (Fin d) (Fin d) 𝕂) r = Matrix.scalar (Fin d) r := by
        simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
      rw [hr, hβsc]
      have hr2 : Matrix.scalar (Fin d) (σ r) = algebraMap 𝕂 (Matrix (Fin d) (Fin d) 𝕂) (σ r) := by
        simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
      rw [hr2]
      exact Subalgebra.algebraMap_mem _ _
    · intro x y hx hy hx' hy'
      rw [map_add]; exact add_mem hx' hy'
    · intro x y hx hy hx' hy'
      rw [map_mul]; exact mul_mem hx' hy'
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x :=
    (kgLangC_span_comm_reduced P hPab hPodd).1
  letI : CommRing ↥B :=
    { (inferInstance : Ring ↥B) with
      mul_comm := fun a b => Subtype.ext (hBcomm a a.2 b b.2) }
  let U : Subgroup (GL (Fin d) 𝕂) :=
    (⊤ : Subgroup (Units ↥B)).map (Units.map B.val.toMonoidHom)
  have mem_U_iff : ∀ g : GL (Fin d) 𝕂, g ∈ U ↔ (g : Matrix (Fin d) (Fin d) 𝕂) ∈ B := by
    intro g
    constructor
    · intro hg
      rw [show U = (⊤ : Subgroup (Units ↥B)).map (Units.map B.val.toMonoidHom) from rfl] at hg
      obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hg
      exact (u : B).2
    · intro hg
      have hunit : IsUnit (⟨(g : Matrix (Fin d) (Fin d) 𝕂), hg⟩ : B) := by
        rw [isUnit_iff_mem_nonZeroDivisors_of_finite]
        rw [mem_nonZeroDivisors_iff_right]
        intro y hy
        apply Subtype.ext
        have h := congrArg (fun z : B => (z : Matrix (Fin d) (Fin d) 𝕂)) hy
        simp only [Subalgebra.coe_mul, Subalgebra.coe_zero] at h
        have hgunit : IsUnit (g : Matrix (Fin d) (Fin d) 𝕂) := ⟨g, rfl⟩
        have h' : (y : Matrix (Fin d) (Fin d) 𝕂) * (g : Matrix (Fin d) (Fin d) 𝕂) =
            (0 : Matrix (Fin d) (Fin d) 𝕂) * (g : Matrix (Fin d) (Fin d) 𝕂) := by
          rw [h, zero_mul]
        exact hgunit.mul_right_cancel h'
      exact Subgroup.mem_map.mpr ⟨hunit.unit, Subgroup.mem_top _, by
        apply Units.ext
        rw [Units.coe_map, IsUnit.unit_spec]
        rfl⟩
  have hPU : P ≤ U := by
    intro g hg
    rw [mem_U_iff]
    exact Algebra.subset_adjoin ⟨g, hg, rfl⟩
  let N : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) 𝕂))) := U.map c
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact hBcomm (a : Matrix (Fin d) (Fin d) 𝕂) ((mem_U_iff a).mp ha)
      (b : Matrix (Fin d) (Fin d) 𝕂) ((mem_U_iff b).mp hb)
  have hβU : ∀ u ∈ U, Matrix.GeneralLinearGroup.map (σ : 𝕂 →+* 𝕂) u ∈ U := by
    intro u hu
    rw [mem_U_iff] at hu ⊢
    have h : (Matrix.GeneralLinearGroup.map (σ : 𝕂 →+* 𝕂) u : Matrix (Fin d) (Fin d) 𝕂) =
        β (u : Matrix (Fin d) (Fin d) 𝕂) := by
      ext i j
      simp only [β, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.GeneralLinearGroup.map_apply]
    rw [h]
    exact hβB _ hu
  have hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, hUab a' ha' b' hb']
  have hNstab : ∀ x ∈ N, f * x * f⁻¹ ∈ N := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨Matrix.GeneralLinearGroup.map (σ : 𝕂 →+* 𝕂) u, hβU u hu,
      (hconj u).symm⟩
  have hNleJ : N ≤ J := by
    rw [hJc]
    exact Subgroup.map_le_range c U
  have hEN : E ≤ N := by
    rw [← hPmap]
    exact Subgroup.map_mono hPU
  have hN90 : ∀ x ∈ N, ((List.range p).map fun i =>
      endPow (MulAut.conj f).toMonoidHom i x).prod = 1 →
      ∃ s ∈ N, x = s⁻¹ * (MulAut.conj f).toMonoidHom s := by
    have hN90' := kgLangCLinAux_h90_image (p := p) hp hσord c S hSp hconj
      (fun A hA => by
        have hmem : A ∈ c.ker := MonoidHom.mem_ker.mpr hA
        rw [hc_ker, largeEvenScalars_def] at hmem
        obtain ⟨lam, hlam⟩ := MonoidHom.mem_range.mp hmem
        exact ⟨lam, hlam.symm⟩)
      (fun lam => by
        simp only [c, kgLangCLinAux_cHom, MonoidHom.comp_apply,
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_scalar, map_one])
      P hPab hPodd B rfl β hβP hβsc hβp U mem_U_iff hUab hβU
      (fun i w => by
        ext a b
        rw [← RingHom.coe_pow]
        have hβiter : ∀ (k : ℕ) (N : Matrix (Fin d) (Fin d) 𝕂) (a b : Fin d),
            ((β ^ k) N) a b = (σ ^ k) (N a b) := by
          intro k
          induction k with
          | zero => intro N a b; rw [pow_zero, pow_zero]; rfl
          | succ k ih =>
              intro N a b
              rw [pow_succ']
              change β ((β ^ k) N) a b = (σ ^ (k+1)) (N a b)
              have h1 : β ((β ^ k) N) a b = σ (((β ^ k) N) a b) := rfl
              rw [h1, ih N a b, pow_succ']
              simp
        rw [hβiter i (w : Matrix (Fin d) (Fin d) 𝕂) a b, hmap_pow i]
        exact (Matrix.GeneralLinearGroup.map_apply (↑(σ ^ i) : 𝕂 →+* 𝕂) a b w).symm)
    intro x hx hnorm
    exact hN90' x hx hnorm
  exact ⟨N, hNleJ, hNab, hNstab, hN90, hEN⟩

theorem kgLangTorusDatumCont_linear {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d n : ℕ} (hd : 3 ≤ d)
    (hpd : ¬ p ∣ d) (hpn : p ∣ n) (𝕂 : Type) [Field 𝕂] [Finite 𝕂] (h𝕂 : Nat.card 𝕂 = 2 ^ n)
    (hcyc : GGRawFieldCycW p (LargeEvenProj (LargeEvenSLGroup (Fin d) 𝕂))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) 𝕂)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) 𝕂))))
    (hZ : ∀ [Finite (HopfCover (LargeEvenProj (LargeEvenSLGroup (Fin d) 𝕂)))]
      (θ : HopfCover (LargeEvenProj (LargeEvenSLGroup (Fin d) 𝕂)) ⧸
        Subgroup.center (HopfCover (LargeEvenProj (LargeEvenSLGroup (Fin d) 𝕂))) ≃*
          LargeEvenProj (LargeEvenSLGroup (Fin d) 𝕂)),
      commutator (HopfCover (LargeEvenProj (LargeEvenSLGroup (Fin d) 𝕂))) = ⊤ →
      Nat.Coprime (Nat.card (Subgroup.center (HopfCover (LargeEvenProj (LargeEvenSLGroup (Fin d) 𝕂))))) p) :
    KGLangTorusDatumCont p (LargeEvenProj (LargeEvenSLGroup (Fin d) 𝕂))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) 𝕂)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) 𝕂))) := by
  classical
  refine kgLangTorusDatumCont_of_models hp
    (hcyc (LinearFieldFix.isSimpleGroup_proj hd 𝕂)
      (LinearFieldFix.exists_noncomm_proj hd 𝕂)) ?_
  exact kgLangTorusMPart_of_inner hp
    (LinearFieldFix.isSimpleGroup_proj hd 𝕂)
    (LinearFieldFix.exists_noncomm_proj hd 𝕂)
    hcyc
    (RecipeFieldLang.ggRawFieldConj_linear (d := d) (K := 𝕂) (by omega) (Or.inl hd) hp)
    (fun r => by
      rw [← RecipeFieldLinear.coe_recI]
      exact RecipeFieldLinear.conj_mem_recI r)
    (fun u hu hpu => by
      obtain ⟨k, hk⟩ := hpu
      obtain ⟨r, hr⟩ := kgLangC_conjImage_pow_inner_linear (d := d) (by omega) 𝕂 u hu
      have hmem : u ∈ (MulAut.conj : LargeEvenProj (LargeEvenSLGroup (Fin d) 𝕂) →*
          MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) 𝕂))).range :=
        kgLangC_mem_of_pow_mem hp hpd (MulAut.conj : LargeEvenProj (LargeEvenSLGroup (Fin d) 𝕂) →*
          MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) 𝕂))).range ⟨r, hr.symm⟩ hk
      obtain ⟨r', hr'⟩ := hmem
      exact ⟨r', hr'.symm⟩)
    (fun J hJ f hf hfp => kgLangC_torusInput_linear hp hp2 hd hpd 𝕂 h𝕂 J hJ hf hfp)
    hZ

end CFSG.StandardType
