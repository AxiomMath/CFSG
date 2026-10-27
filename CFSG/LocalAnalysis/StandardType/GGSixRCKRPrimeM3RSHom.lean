module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3RSDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSL

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
variable {K : Type} [Field K] [Algebra F K]
variable {k : ℕ} {S : Set (GL ι F)} {e : Matrix ι ι F}
variable [Module K (LinearMap.range (Matrix.mulVecLin e))]
variable [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e))]

private lemma rckM3hm_E_comp_E (hee : e * e = e) :
    (Matrix.mulVecLin e).comp (Matrix.mulVecLin e) = Matrix.mulVecLin e := by
  rw [← Matrix.mulVecLin_mul, hee]

private lemma rckM3hm_E_E_apply (hee : e * e = e) (v : ι → F) :
    Matrix.mulVecLin e (Matrix.mulVecLin e v) = Matrix.mulVecLin e v := by
  simpa only [LinearMap.comp_apply] using
    congrArg (fun f : (ι → F) →ₗ[F] (ι → F) => f v) (rckM3hm_E_comp_E hee)

private lemma rckM3hm_E_apply_w (hee : e * e = e) (w : LinearMap.range (Matrix.mulVecLin e)) :
    Matrix.mulVecLin e (w : ι → F) = (w : ι → F) := by
  obtain ⟨v, hv⟩ := w.2
  rw [← hv, rckM3hm_E_E_apply hee v]

private lemma rckM3hm_rangeRestrict_coe (hee : e * e = e)
    (w : LinearMap.range (Matrix.mulVecLin e)) :
    (Matrix.mulVecLin e).rangeRestrict (w : ι → F) = w := by
  apply Subtype.ext
  simpa using rckM3hm_E_apply_w hee w

private lemma rckM3hm_rangeRestrict_eq_zero {v : ι → F} (h : Matrix.mulVecLin e v = 0) :
    (Matrix.mulVecLin e).rangeRestrict v = 0 := by
  apply Subtype.ext
  simpa using h

private noncomputable def rckM3hm_A
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)))
    (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K) :
    (ι → F) →ₗ[F] (ι → F) :=
  (LinearMap.range (Matrix.mulVecLin e)).subtype ∘ₗ
    ((Matrix.toLin b b x).restrictScalars F) ∘ₗ (Matrix.mulVecLin e).rangeRestrict

private noncomputable def rckM3hm_sub : (ι → F) →ₗ[F] (ι → F) :=
  LinearMap.id - Matrix.mulVecLin e

private noncomputable def rckM3hm_L
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)))
    (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K) :
    (ι → F) →ₗ[F] (ι → F) :=
  rckM3hm_sub (e := e) + rckM3hm_A b x

private lemma rckM3hm_mat_eq
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)))
    (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K) :
    rckBlockRSMat b x = LinearMap.toMatrix' (rckM3hm_L b x) := rfl

private lemma rckM3hm_A_apply
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)))
    (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K) (v : ι → F) :
    rckM3hm_A b x v = (LinearMap.range (Matrix.mulVecLin e)).subtype
      ((Matrix.toLin b b x) ((Matrix.mulVecLin e).rangeRestrict v)) := rfl

private lemma rckM3hm_L_apply
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)))
    (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K) (v : ι → F) :
    rckM3hm_L b x v = (v - Matrix.mulVecLin e v) + rckM3hm_A b x v := rfl

private lemma rckM3hm_A_apply_w (hee : e * e = e)
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)))
    (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K)
    (w : LinearMap.range (Matrix.mulVecLin e)) :
    rckM3hm_A b x (w : ι → F) =
      (LinearMap.range (Matrix.mulVecLin e)).subtype ((Matrix.toLin b b x) w) := by
  rw [rckM3hm_A_apply, rckM3hm_rangeRestrict_coe hee w]

private lemma rckM3hm_L_apply_w (hee : e * e = e)
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)))
    (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K)
    (w : LinearMap.range (Matrix.mulVecLin e)) :
    rckM3hm_L b x (w : ι → F) =
      (LinearMap.range (Matrix.mulVecLin e)).subtype ((Matrix.toLin b b x) w) := by
  rw [rckM3hm_L_apply, rckM3hm_A_apply_w hee b x w, rckM3hm_E_apply_w hee w, sub_self, zero_add]

private lemma rckM3hm_sub_apply_w (hee : e * e = e)
    (w : LinearMap.range (Matrix.mulVecLin e)) :
    rckM3hm_sub (e := e) (w : ι → F) = 0 := by
  rw [rckM3hm_sub, LinearMap.sub_apply, LinearMap.id_apply, rckM3hm_E_apply_w hee w, sub_self]

private lemma rckM3hm_sub_comp_sub (hee : e * e = e) :
    (rckM3hm_sub (e := e)).comp (rckM3hm_sub (e := e)) = rckM3hm_sub (e := e) := by
  apply LinearMap.ext; intro v
  simp only [rckM3hm_sub, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
  have h : Matrix.mulVecLin e (v - Matrix.mulVecLin e v) = 0 := by
    rw [map_sub, rckM3hm_E_E_apply hee v, sub_self]
  rw [h, sub_zero]

private lemma rckM3hm_sub_comp_A (hee : e * e = e)
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)))
    (y : Matrix (Fin (k + 1)) (Fin (k + 1)) K) :
    (rckM3hm_sub (e := e)).comp (rckM3hm_A b y) = 0 := by
  apply LinearMap.ext; intro v
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [rckM3hm_A_apply]
  exact rckM3hm_sub_apply_w hee _

private lemma rckM3hm_A_comp_sub (hee : e * e = e)
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)))
    (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K) :
    (rckM3hm_A b x).comp (rckM3hm_sub (e := e)) = 0 := by
  apply LinearMap.ext; intro v
  simp only [rckM3hm_sub, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.zero_apply]
  rw [rckM3hm_A_apply]
  have h : Matrix.mulVecLin e (v - Matrix.mulVecLin e v) = 0 := by
    rw [map_sub, rckM3hm_E_E_apply hee v, sub_self]
  rw [rckM3hm_rangeRestrict_eq_zero h]
  simp

private lemma rckM3hm_A_comp_A (hee : e * e = e)
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)))
    (x y : Matrix (Fin (k + 1)) (Fin (k + 1)) K) :
    (rckM3hm_A b x).comp (rckM3hm_A b y) = rckM3hm_A b (x * y) := by
  apply LinearMap.ext; intro v
  rw [LinearMap.comp_apply]
  let X : LinearMap.range (Matrix.mulVecLin e) :=
    (Matrix.toLin b b y) ((Matrix.mulVecLin e).rangeRestrict v)
  have hX : (rckM3hm_A b y) v = (X : ι → F) := rckM3hm_A_apply b y v
  rw [hX, rckM3hm_A_apply_w hee b x X, rckM3hm_A_apply]
  rw [← Matrix.toLin_mul_apply]

private lemma rckM3hm_L_comp_L
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)))
    (x y : Matrix (Fin (k + 1)) (Fin (k + 1)) K) :
    rckM3hm_L b (x * y) = (rckM3hm_L b x).comp (rckM3hm_L b y) := by
  have hee : e * e = e := he.2.1.eq
  rw [rckM3hm_L, rckM3hm_L, rckM3hm_L]
  rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
  rw [rckM3hm_sub_comp_sub hee, rckM3hm_sub_comp_A hee b y, rckM3hm_A_comp_sub hee b x,
    rckM3hm_A_comp_A hee b x y]
  abel

private lemma rckM3hm_L_one
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e))) :
    rckM3hm_L b (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) K) = LinearMap.id := by
  have hA1 : rckM3hm_A b (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) K) = Matrix.mulVecLin e := by
    simp only [rckM3hm_A, Matrix.toLin_one, LinearMap.restrictScalars_apply, LinearMap.comp_id,
      LinearMap.id_comp]
    exact LinearMap.subtype_comp_rangeRestrict (Matrix.mulVecLin e)
  rw [rckM3hm_L, rckM3hm_sub, hA1, sub_add_cancel]

private lemma rckM3hm_eq_of_agree (hee : e * e = e)
    {f h : (ι → F) →ₗ[F] (ι → F)}
    (hfW : ∀ v, f (Matrix.mulVecLin e v) = h (Matrix.mulVecLin e v))
    (hfK : ∀ v, Matrix.mulVecLin e v = 0 → f v = h v) :
    f = h := by
  apply LinearMap.ext; intro v
  have hv : v = Matrix.mulVecLin e v + (v - Matrix.mulVecLin e v) := by abel
  conv_lhs => rw [hv]
  conv_rhs => rw [hv]
  rw [map_add, map_add, hfW v]
  exact congrArg (fun z => h (Matrix.mulVecLin e v) + z)
    (hfK (v - Matrix.mulVecLin e v) (by rw [map_sub, rckM3hm_E_E_apply hee v, sub_self]))

private lemma rckM3hm_ext (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    [Finite K]
    (g : LinearMap.range (Matrix.mulVecLin e) →ₗ[K] LinearMap.range (Matrix.mulVecLin e))
    (hg : LinearMap.det g = 1) :
    ∃ u : (ι → F) →ₗ[F] (ι → F),
      (∀ w : LinearMap.range (Matrix.mulVecLin e),
        u (w : ι → F) = (g w : ι → F)) ∧
      (∀ x : ι → F, Matrix.mulVecLin e x = 0 → u x = x) ∧
      LinearMap.det u = 1 := by
  classical
  have hE : IsIdempotentElem (Matrix.mulVecLin e) := by
    change (Matrix.mulVecLin e).comp (Matrix.mulVecLin e) = Matrix.mulVecLin e
    rw [← Matrix.mulVecLin_mul, he.2.1.eq]
  let W : Submodule F (ι → F) := LinearMap.range (Matrix.mulVecLin e)
  let W' : Submodule F (ι → F) := LinearMap.ker (Matrix.mulVecLin e)
  have hcompl : IsCompl W W' := LinearMap.IsIdempotentElem.isCompl hE
  let ψ := Submodule.prodEquivOfIsCompl W W' hcompl
  let fmap : W × W' →ₗ[F] W × W' :=
    (g.restrictScalars F).prodMap (LinearMap.id : W' →ₗ[F] W')
  let u : (ι → F) →ₗ[F] (ι → F) :=
    (ψ : W × W' →ₗ[F] (ι → F)) ∘ₗ fmap ∘ₗ
      (ψ.symm : (ι → F) →ₗ[F] W × W')
  refine ⟨u, ?_, ?_, ?_⟩
  · intro w
    have hφ : (ψ.symm : (ι → F) →ₗ[F] W × W') (w : ι → F) = (w, 0) := by
      simpa [ψ] using Submodule.prodEquivOfIsCompl_symm_apply_left W W' hcompl w
    have hf : fmap (w, 0) = (g w, 0) := by
      simp [fmap, LinearMap.prodMap_apply]
    have hφs : (ψ : W × W' →ₗ[F] (ι → F)) (g w, 0) = (g w : ι → F) := by
      simp [ψ, Submodule.coe_prodEquivOfIsCompl']
    simp only [u, LinearMap.comp_apply, hφ, hf, hφs]
  · intro x hx
    have hφ : (ψ.symm : (ι → F) →ₗ[F] W × W') x = (0, ⟨x, hx⟩) := by
      simpa [ψ] using
        Submodule.prodEquivOfIsCompl_symm_apply_right W W' hcompl (⟨x, hx⟩ : W')
    have hf : fmap (0, ⟨x, hx⟩) = (0, ⟨x, hx⟩) := by
      simp [fmap, LinearMap.prodMap_apply]
    have hφs : (ψ : W × W' →ₗ[F] (ι → F)) (0, ⟨x, hx⟩) = x := by
      simp [ψ, Submodule.coe_prodEquivOfIsCompl']
    simp only [u, LinearMap.comp_apply, hφ, hf, hφs]
  · change LinearMap.det ((ψ : W × W' →ₗ[F] (ι → F)) ∘ₗ fmap ∘ₗ
      (ψ.symm : (ι → F) →ₗ[F] W × W')) = 1
    rw [LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_restrictScalars, hg]
    simp

private lemma rckM3hm_ext_commute
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K)
    (hcomp : ∀ (a : Algebra.adjoin F (Units.val '' S))
      (w : LinearMap.range (Matrix.mulVecLin e)),
      ((π a • w : LinearMap.range (Matrix.mulVecLin e)) : ι → F) =
        (a : Matrix ι ι F).mulVec w)
    (g : LinearMap.range (Matrix.mulVecLin e) →ₗ[K] LinearMap.range (Matrix.mulVecLin e))
    (u : (ι → F) →ₗ[F] (ι → F))
    (huW : ∀ w : LinearMap.range (Matrix.mulVecLin e),
      u (w : ι → F) = (g w : ι → F))
    (huK : ∀ x : ι → F, Matrix.mulVecLin e x = 0 → u x = x) :
    ∀ (a : Algebra.adjoin F (Units.val '' S)) (x : ι → F),
      u (Matrix.mulVec (a : Matrix ι ι F) x) =
        Matrix.mulVec (a : Matrix ι ι F) (u x) := by
  classical
  let A := Algebra.adjoin F (Units.val '' S)
  have hpair : (Units.val '' S : Set (Matrix ι ι F)).Pairwise Commute := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ _
    exact (hS s hs s' hs').map (Units.coeHom (Matrix ι ι F))
  letI : CommRing A := Algebra.adjoinCommRingOfComm F (s := Units.val '' S) hpair
  have hcomm (a : A) : (a : Matrix ι ι F) * e = e * (a : Matrix ι ι F) :=
    congrArg Subtype.val (mul_comm a (⟨e, he.1⟩ : A))
  have hu_form (x : ι → F) :
      u x = (g ⟨Matrix.mulVec e x, ⟨x, rfl⟩⟩ : ι → F) +
        Matrix.mulVec (1 - e) x := by
    have hdecomp : x = Matrix.mulVec e x + Matrix.mulVec (1 - e) x := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    have hker : Matrix.mulVecLin e (Matrix.mulVec (1 - e) x) = 0 := by
      rw [Matrix.mulVecLin_apply]
      rw [Matrix.mulVec_mulVec (x : ι → F) e (1 - e)]
      rw [show e * (1 - e) = 0 by rw [Matrix.mul_sub, Matrix.mul_one, he.2.1.eq, sub_self]]
      exact Matrix.zero_mulVec x
    conv_lhs => rw [hdecomp]
    rw [map_add, huW ⟨Matrix.mulVec e x, ⟨x, rfl⟩⟩, huK _ hker]
  intro a x
  rw [hu_form (Matrix.mulVec (a : Matrix ι ι F) x), hu_form x]
  rw [Matrix.mulVec_add]
  congr 1
  · have hw : (⟨Matrix.mulVec e (Matrix.mulVec (a : Matrix ι ι F) x),
          ⟨_, rfl⟩⟩ : LinearMap.range (Matrix.mulVecLin e)) =
        π a • (⟨Matrix.mulVec e x, ⟨x, rfl⟩⟩ : LinearMap.range (Matrix.mulVecLin e)) := by
      apply Subtype.ext
      simp only [hcomp a (⟨Matrix.mulVec e x, ⟨x, rfl⟩⟩ : LinearMap.range (Matrix.mulVecLin e)),
        Matrix.mulVec_mulVec, hcomm a]
    rw [hw, map_smul]
    exact hcomp a (g ⟨Matrix.mulVec e x, ⟨x, rfl⟩⟩)
  · rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hcomm a]

private lemma rckM3hm_ext_mem (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (g : LinearMap.range (Matrix.mulVecLin e) →ₗ[K] LinearMap.range (Matrix.mulVecLin e))
    (u : (ι → F) →ₗ[F] (ι → F))
    (hcomm : ∀ (a : Algebra.adjoin F (Units.val '' S)) (x : ι → F),
      u (Matrix.mulVec (a : Matrix ι ι F) x) =
        Matrix.mulVec (a : Matrix ι ι F) (u x))
    (hfix : ∀ x : ι → F, Matrix.mulVecLin e x = 0 → u x = x)
    (hdet : LinearMap.det u = 1) :
    ∃ uM : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      ∀ x : ι → F,
        Matrix.mulVec ((uM : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) x = u x := by
  let M : Matrix ι ι F := Matrix.toLinAlgEquiv'.symm u
  have hMmul : Matrix.mulVecLin M = u := by
    change Matrix.toLin' M = u
    rw [show M = Matrix.toLinAlgEquiv'.symm u from rfl]
    exact Matrix.toLinAlgEquiv'.apply_symm_apply u
  have hMdet : M.det = 1 := by
    change Matrix.det (LinearMap.toMatrix' u) = 1
    rw [LinearMap.det_toMatrix']
    exact hdet
  let uSL : Matrix.SpecialLinearGroup ι F := ⟨M, hMdet⟩
  have hker (x : ι → F) : Matrix.mulVecLin e (Matrix.mulVec (1 - e) x) = 0 := by
    rw [Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_mulVec (x : ι → F) e (1 - e)]
    rw [show e * (1 - e) = 0 by rw [Matrix.mul_sub, Matrix.mul_one, he.2.1.eq, sub_self]]
    exact Matrix.zero_mulVec x
  have hMs (s : GL ι F) (hs : s ∈ S) :
      (s : Matrix ι ι F) * M = M * (s : Matrix ι ι F) := by
    have hsA : (s : Matrix ι ι F) ∈ Algebra.adjoin F (Units.val '' S) :=
      Algebra.subset_adjoin ⟨s, hs, rfl⟩
    have hmul : Matrix.mulVecLin ((s : Matrix ι ι F) * M) =
        Matrix.mulVecLin (M * (s : Matrix ι ι F)) := by
      rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, hMmul]
      apply LinearMap.ext
      intro x
      exact (hcomm ⟨(s : Matrix ι ι F), hsA⟩ x).symm
    exact Matrix.toLin'.injective (by simpa only [Matrix.toLin'_apply'] using hmul)
  have hMfix : M * (1 - e) = 1 - e := by
    have hmul : Matrix.mulVecLin (M * (1 - e)) = Matrix.mulVecLin (1 - e) := by
      rw [Matrix.mulVecLin_mul, hMmul]
      apply LinearMap.ext
      intro x
      exact hfix (Matrix.mulVec (1 - e) x) (hker x)
    exact Matrix.toLin'.injective (by simpa only [Matrix.toLin'_apply'] using hmul)
  have hmem : uSL ∈ glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e := by
    rw [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf]
    constructor
    · rw [Subgroup.mem_centralizer_iff]
      intro s hs
      apply Units.ext
      show (s : Matrix ι ι F) * M = M * (s : Matrix ι ι F)
      exact hMs s hs
    · show ((Matrix.SpecialLinearGroup.toGL uSL : GL ι F) : Matrix ι ι F) * (1 - e) = 1 - e
      show M * (1 - e) = 1 - e
      exact hMfix
  refine ⟨⟨uSL, hmem⟩, ?_⟩
  intro x
  show Matrix.mulVec (uSL : Matrix ι ι F) x = u x
  show Matrix.mulVec M x = u x
  rw [← hMmul]
  rfl

private lemma rckM3hm_commutator_det_one
    (actK : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e →*
      Module.End K (LinearMap.range (Matrix.mulVecLin e))) :
    ∀ u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      (u : Matrix.SpecialLinearGroup ι F) ∈
        ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
          glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ →
      LinearMap.det (actK u) = 1 := by
  let H := glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e
  let φ : H →* K :=
    (LinearMap.det : (LinearMap.range (Matrix.mulVecLin e) →ₗ[K]
      LinearMap.range (Matrix.mulVecLin e)) →* K).comp actK
  let ψ : H →* Kˣ := φ.toHomUnits
  have htop : (⊤ : Subgroup H).map H.subtype = H := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, -, hy⟩ := hx
      exact hy ▸ y.2
    · intro hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have hmap : (⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H).map H.subtype = ⁅H, H⁆ := by
    rw [Subgroup.map_commutator, htop]
  have hker : ⁅(⊤ : Subgroup H), ⊤⁆ ≤ (⊥ : Subgroup Kˣ).comap ψ := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_comap, Subgroup.mem_bot, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  intro u hu
  have hu' : H.subtype u ∈ (⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H).map H.subtype := by
    rw [hmap]
    exact hu
  rw [Subgroup.mem_map] at hu'
  obtain ⟨v, hv, hvu⟩ := hu'
  have hvu' : v = u := Subtype.ext hvu
  rw [hvu'] at hv
  have h1 : ψ u = 1 := by
    have := hker hv
    rwa [Subgroup.mem_comap, Subgroup.mem_bot] at this
  have h2 : (ψ u : K) = 1 := by rw [h1]; rfl
  simpa [φ, ψ] using h2

private lemma rckM3hm_commute_adjoin
    (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
    {a : Matrix ι ι F} (ha : a ∈ Algebra.adjoin F (Units.val '' S)) :
    ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) * a =
      a * ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) := by
  let M : Matrix ι ι F := ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F)
  have hT : Matrix.SpecialLinearGroup.toGL (u : Matrix.SpecialLinearGroup ι F) ∈
      Subgroup.centralizer S :=
    (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp u.2)).1
  have hgen : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F ({M} : Set (Matrix ι ι F)) : Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact congrArg (fun g : GL ι F => (g : Matrix ι ι F))
      ((Subgroup.mem_centralizer_iff.mp hT) s hs).symm
  have hA : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F ({M} : Set (Matrix ι ι F)) :=
    Algebra.adjoin_le hgen
  exact (Subalgebra.mem_centralizer_iff F).mp (hA ha) M (Set.mem_singleton M)

private lemma rckM3hm_stable
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :
    ∀ w ∈ LinearMap.range (Matrix.mulVecLin e),
      Matrix.mulVecLin ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) w ∈
        LinearMap.range (Matrix.mulVecLin e) := by
  intro w hw
  obtain ⟨v, hv⟩ := hw
  refine ⟨Matrix.mulVec ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) v, ?_⟩
  rw [← hv]
  calc Matrix.mulVecLin e (Matrix.mulVec ((u : Matrix.SpecialLinearGroup ι F) :
          Matrix ι ι F) v)
      = Matrix.mulVec e (Matrix.mulVec ((u : Matrix.SpecialLinearGroup ι F) :
          Matrix ι ι F) v) := rfl
    _ = Matrix.mulVec (e * ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F)) v :=
        Matrix.mulVec_mulVec v e _
    _ = Matrix.mulVec (((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) * e) v := by
        rw [rckM3hm_commute_adjoin u he.1]
    _ = Matrix.mulVec ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F)
          (Matrix.mulVec e v) := (Matrix.mulVec_mulVec v _ e).symm
    _ = Matrix.mulVecLin ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F)
          (Matrix.mulVecLin e v) := rfl

private lemma rckM3hm_fix_ker (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
    (v : ι → F) (hv : Matrix.mulVecLin e v = 0) :
    Matrix.mulVecLin
      ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) v = v := by
  have hue : ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) * (1 - e) = 1 - e :=
    (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp u.2)).2
  have hve : Matrix.mulVec e v = 0 := by simpa only [Matrix.mulVecLin_apply] using hv
  have hv' : Matrix.mulVec (1 - e) v = v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hve, sub_zero]
  calc Matrix.mulVecLin ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) v
      = Matrix.mulVec ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) v := rfl
    _ = Matrix.mulVec ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F)
          (Matrix.mulVec (1 - e) v) := by rw [hv']
    _ = Matrix.mulVec (((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) * (1 - e)) v :=
        Matrix.mulVec_mulVec v _ _
    _ = Matrix.mulVec (1 - e) v := by rw [hue]
    _ = v := hv'

private lemma rckM3hm_L_eq_extension
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    [Finite K]
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)))
    (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K) (hx : x.det = 1) :
    ∃ u : (ι → F) →ₗ[F] (ι → F),
      rckM3hm_L b x = u ∧
      (∀ w : LinearMap.range (Matrix.mulVecLin e),
        u (w : ι → F) = ((Matrix.toLin b b x) w : ι → F)) ∧
      (∀ v, Matrix.mulVecLin e v = 0 → u v = v) ∧
      LinearMap.det u = 1 := by
  have hee : e * e = e := he.2.1.eq
  have hg : LinearMap.det (Matrix.toLin b b x) = 1 := by
    rw [LinearMap.det_toLin, hx]
  obtain ⟨u, huW, huK, hdetu⟩ := rckM3hm_ext he (Matrix.toLin b b x) hg
  have hLu : rckM3hm_L b x = u := by
    apply rckM3hm_eq_of_agree hee
    · intro v
      change rckM3hm_L b x ((Matrix.mulVecLin e).rangeRestrict v) =
        u ((Matrix.mulVecLin e).rangeRestrict v)
      rw [rckM3hm_L_apply_w hee b x ((Matrix.mulVecLin e).rangeRestrict v)]
      exact (huW ((Matrix.mulVecLin e).rangeRestrict v)).symm
    · intro v hv
      have hLv : rckM3hm_L b x v = v := by
        rw [rckM3hm_L_apply, hv, rckM3hm_A_apply, rckM3hm_rangeRestrict_eq_zero hv]
        simp
      rw [hLv]
      exact (huK v hv).symm
  exact ⟨u, hLu, huW, huK, hdetu⟩

lemma rckBlockRSMat_det
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    [Finite K]
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)))
    (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K) (hx : x.det = 1) :
    (rckBlockRSMat b x).det = 1 := by
  obtain ⟨u, hLu, -, -, hdetu⟩ := rckM3hm_L_eq_extension he b x hx
  rw [rckM3hm_mat_eq, hLu, LinearMap.det_toMatrix', hdetu]

lemma rckBlockRSMat_one
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e))) :
    rckBlockRSMat b (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) K) = 1 := by
  rw [rckM3hm_mat_eq, rckM3hm_L_one he b, LinearMap.toMatrix'_id]

lemma rckBlockRSMat_mul
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)))
    (x y : Matrix (Fin (k + 1)) (Fin (k + 1)) K) :
    rckBlockRSMat b (x * y) = rckBlockRSMat b x * rckBlockRSMat b y := by
  apply Matrix.toLin'.injective
  rw [rckM3hm_mat_eq, rckM3hm_mat_eq, rckM3hm_mat_eq, Matrix.toLin'_mul]
  rw [Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
  exact rckM3hm_L_comp_L he b x y

private lemma rckM3hm_toLin_eq_of_L_eq (hee : e * e = e)
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)))
    {x y : Matrix (Fin (k + 1)) (Fin (k + 1)) K}
    (h : rckM3hm_L b x = rckM3hm_L b y) :
    Matrix.toLin b b x = Matrix.toLin b b y := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  have hw := congrArg (fun f : (ι → F) →ₗ[F] (ι → F) => f (w : ι → F)) h
  rwa [rckM3hm_L_apply_w hee b x w, rckM3hm_L_apply_w hee b y w] at hw

private lemma rckM3hm_L_eq_mulVecLin
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)))
    (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
    (actK : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e →*
      Module.End K (LinearMap.range (Matrix.mulVecLin e)))
    (hact : ∀ (v : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actK v w : ι → F) =
        Matrix.mulVec ((v : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) w) :
    rckM3hm_L b (LinearMap.toMatrix b b (actK u)) =
      Matrix.mulVecLin ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) := by
  have hee : e * e = e := he.2.1.eq
  have hxlin : Matrix.toLin b b (LinearMap.toMatrix b b (actK u)) = actK u :=
    Matrix.toLin_toMatrix b b (actK u)
  apply rckM3hm_eq_of_agree hee
  · intro v
    change rckM3hm_L b (LinearMap.toMatrix b b (actK u))
        ((Matrix.mulVecLin e).rangeRestrict v) =
      Matrix.mulVecLin ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F)
        ((Matrix.mulVecLin e).rangeRestrict v)
    calc rckM3hm_L b (LinearMap.toMatrix b b (actK u))
          ((Matrix.mulVecLin e).rangeRestrict v)
        = (LinearMap.range (Matrix.mulVecLin e)).subtype
            ((Matrix.toLin b b (LinearMap.toMatrix b b (actK u)))
              ((Matrix.mulVecLin e).rangeRestrict v)) := by
          rw [rckM3hm_L_apply_w hee b (LinearMap.toMatrix b b (actK u))
            ((Matrix.mulVecLin e).rangeRestrict v)]
      _ = (LinearMap.range (Matrix.mulVecLin e)).subtype
            ((actK u) ((Matrix.mulVecLin e).rangeRestrict v)) := by rw [hxlin]
      _ = Matrix.mulVec ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F)
            ((Matrix.mulVecLin e).rangeRestrict v) :=
          hact u ((Matrix.mulVecLin e).rangeRestrict v)
      _ = Matrix.mulVecLin ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F)
            ((Matrix.mulVecLin e).rangeRestrict v) := rfl
  · intro v hv
    have hLv : rckM3hm_L b (LinearMap.toMatrix b b (actK u)) v = v := by
      rw [rckM3hm_L_apply, hv, rckM3hm_A_apply, rckM3hm_rangeRestrict_eq_zero hv]
      simp
    rw [hLv, rckM3hm_fix_ker u v hv]

private lemma rckM3hm_exists_uM
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    [Finite K]
    {π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K}
    (hπ : RCKBlockCoord S e K π)
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)))
    (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K) (hx : x.det = 1) :
    ∃ uM : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      rckBlockRSMat b x =
        ((uM : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) := by
  obtain ⟨u, hLu, huW, huK, hdetu⟩ := rckM3hm_L_eq_extension he b x hx
  have hcomm := rckM3hm_ext_commute hS he π hπ.2.1 (Matrix.toLin b b x) u huW huK
  obtain ⟨uM, huM⟩ := rckM3hm_ext_mem he (Matrix.toLin b b x) u hcomm huK hdetu
  refine ⟨uM, ?_⟩
  apply Matrix.toLin'.injective
  rw [rckM3hm_mat_eq, hLu, Matrix.toLin'_toMatrix', Matrix.toLin'_apply']
  exact LinearMap.ext fun v => (huM v).symm

theorem rckBlockRS_hom
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    {K : Type} [Field K] [Finite K] [Algebra F K]
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e))]
    {π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K} (hπ : RCKBlockCoord S e K π)
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e))) :
    ∃ ρ : Matrix.SpecialLinearGroup (Fin (k + 1)) K →* Matrix.SpecialLinearGroup ι F,
      (∀ x, ((ρ x : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) =
        rckBlockRSMat b (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K)) ∧
      Function.Injective ρ ∧ ρ.range ≤ glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e ∧
      ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ ≤ ρ.range := by
  classical
  have hee : e * e = e := he.2.1.eq
  let rhoF (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :
      (LinearMap.range (Matrix.mulVecLin e)) →ₗ[F]
        (LinearMap.range (Matrix.mulVecLin e)) :=
    ((Matrix.mulVecLin ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F)).comp
      (LinearMap.range (Matrix.mulVecLin e)).subtype).codRestrict
        (LinearMap.range (Matrix.mulVecLin e)) (fun v => by
          rw [LinearMap.comp_apply, Submodule.coe_subtype]
          exact rckM3hm_stable he u v v.2)
  have hrhoF_apply (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
      (v : LinearMap.range (Matrix.mulVecLin e)) :
      (rhoF u v : ι → F) =
        Matrix.mulVec ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) v := rfl
  have hrhoF_smul (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) (c : K)
      (v : LinearMap.range (Matrix.mulVecLin e)) : rhoF u (c • v) = c • rhoF u v := by
    obtain ⟨a, ha⟩ := hπ.1 c
    have hv : ((c • v : LinearMap.range (Matrix.mulVecLin e)) : ι → F) =
        Matrix.mulVec (a : Matrix ι ι F) (v : ι → F) := by
      rw [← ha]; exact hπ.2.1 a v
    have hu : ((c • rhoF u v : LinearMap.range (Matrix.mulVecLin e)) : ι → F) =
        Matrix.mulVec (a : Matrix ι ι F) (rhoF u v : ι → F) := by
      rw [← ha]; exact hπ.2.1 a (rhoF u v)
    apply Subtype.ext
    rw [hrhoF_apply, hv, hu, hrhoF_apply]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    exact rckM3hm_commute_adjoin u a.2
  let rhoK (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :
      (LinearMap.range (Matrix.mulVecLin e)) →ₗ[K]
        (LinearMap.range (Matrix.mulVecLin e)) :=
    { toFun := fun v => rhoF u v
      map_add' := fun v v' => (rhoF u).map_add v v'
      map_smul' := fun c v => hrhoF_smul u c v }
  let actK : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e →*
      Module.End K (LinearMap.range (Matrix.mulVecLin e)) :=
    { toFun := rhoK
      map_one' := by
        refine LinearMap.ext fun v => Subtype.ext ?_
        change (rhoF 1 v : ι → F) = (v : ι → F)
        rw [hrhoF_apply]
        change Matrix.mulVec (1 : Matrix ι ι F) v = (v : ι → F)
        rw [Matrix.one_mulVec]
      map_mul' := by
        intro u u'
        refine LinearMap.ext fun v => Subtype.ext ?_
        change (rhoF (u * u') v : ι → F) = (rhoF u (rhoF u' v) : ι → F)
        rw [hrhoF_apply, hrhoF_apply, hrhoF_apply]
        have hcoe : (((u * u' : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :
              Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) =
            ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) *
            ((u' : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) := rfl
        rw [hcoe, Matrix.mulVec_mulVec] }
  have hact (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
      (v : LinearMap.range (Matrix.mulVecLin e)) :
      (actK u v : ι → F) =
        Matrix.mulVec ((u : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) v :=
    hrhoF_apply u v
  let ρ : Matrix.SpecialLinearGroup (Fin (k + 1)) K →*
      Matrix.SpecialLinearGroup ι F :=
    { toFun := fun x => ⟨rckBlockRSMat b (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K),
          rckBlockRSMat_det he b (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K) x.2⟩
      map_one' := Subtype.ext (rckBlockRSMat_one he b)
      map_mul' := fun x y => Subtype.ext (rckBlockRSMat_mul he b
        (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K)
        (y : Matrix (Fin (k + 1)) (Fin (k + 1)) K)) }
  refine ⟨ρ, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x y hxy
    have hmat : rckBlockRSMat b (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K) =
        rckBlockRSMat b (y : Matrix (Fin (k + 1)) (Fin (k + 1)) K) := by
      exact congrArg Subtype.val hxy
    have hL : rckM3hm_L b (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K) =
        rckM3hm_L b (y : Matrix (Fin (k + 1)) (Fin (k + 1)) K) := by
      have := congrArg Matrix.toLin' hmat
      simpa only [rckM3hm_mat_eq, Matrix.toLin'_toMatrix'] using this
    have hx : Matrix.toLin b b (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K) =
        Matrix.toLin b b (y : Matrix (Fin (k + 1)) (Fin (k + 1)) K) :=
      rckM3hm_toLin_eq_of_L_eq hee b hL
    have hmat' : (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K) =
        (y : Matrix (Fin (k + 1)) (Fin (k + 1)) K) := by
      have := congrArg (LinearMap.toMatrix b b) hx
      simpa only [LinearMap.toMatrix_toLin] using this
    exact Subtype.ext hmat'
  · intro y hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨uM, hmat⟩ := rckM3hm_exists_uM hS he hπ b
      (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K) x.2
    have hrho : ρ x = (uM : Matrix.SpecialLinearGroup ι F) := Subtype.ext hmat
    rw [hrho]
    exact uM.2
  · intro u hu
    have huG : u ∈ glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e :=
      Subgroup.commutator_le_self _ hu
    let uG : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e := ⟨u, huG⟩
    have hdetu : LinearMap.det (actK uG) = 1 :=
      rckM3hm_commutator_det_one actK uG (by simpa using hu)
    let x : Matrix (Fin (k + 1)) (Fin (k + 1)) K := LinearMap.toMatrix b b (actK uG)
    have hx : x.det = 1 := by
      dsimp only [x]
      rw [← LinearMap.det_toLin b (LinearMap.toMatrix b b (actK uG)), Matrix.toLin_toMatrix, hdetu]
    have hL : rckM3hm_L b x = Matrix.mulVecLin ((uG : Matrix.SpecialLinearGroup
        ι F) : Matrix ι ι F) :=
      rckM3hm_L_eq_mulVecLin he b uG actK hact
    have hmat : rckBlockRSMat b x = ((uG : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) := by
      rw [rckM3hm_mat_eq, hL]
      exact LinearMap.toMatrix'_toLin' _
    refine MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hmat

end CFSG.StandardType.RCKRP
