module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNISpFixedCoordAux
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNISpPrimary
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNISpVecMap
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.ClassicalGroups.Symplectic.Model

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedSp)
open CFSG.StandardType.ClassicalPosition CFSG.StandardType.ClassicalBlocks
open Matrix
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

variable {K : Type} [Field K]

theorem kgfniSpFix_toLin'_symm_coe {W : Type} [AddCommGroup W] [Module K W]
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K W)
    (g : LinearMap.GeneralLinearGroup K W) :
    (((Matrix.GeneralLinearGroup.toLin' b).symm g : GL ι K) : Matrix ι ι K) =
      LinearMap.toMatrix b b (g : W →ₗ[K] W) := by
  ext i j
  have h := CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply b
    ((Matrix.GeneralLinearGroup.toLin' b).symm g) (b j)
  rw [MulEquiv.apply_symm_apply, Module.Basis.equivFun_apply] at h
  have hsingle : b.equivFun (b j) = Pi.single j 1 := by
    rw [Module.Basis.equivFun_apply, Module.Basis.repr_self, Finsupp.single_eq_pi_single]
  have hi := congrFun h i
  rw [LinearMap.toMatrix_apply, hi, hsingle, Matrix.mulVec_single_one, Matrix.col_apply]

theorem kgfniSpFix_basisMatrixEquiv_eq_toLin'_symm {W : Type} [AddCommGroup W] [Module K W]
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K W)
    (g : W ≃ₗ[K] W) :
    basisMatrixEquiv b g = (Matrix.GeneralLinearGroup.toLin' b).symm
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm g) := by
  apply Units.ext
  rw [basisMatrixEquiv_val, kgfniSpFix_toLin'_symm_coe]
  congr 1

theorem kgfniSp_fixedBlock_coord {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (u : GL (Fin n ⊕ Fin n) K) (hu : u ∈ StatedSp n K) (hodd : Odd (orderOf u))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (Algebra.adjoin K (Units.val '' ({u} : Set (GL (Fin n ⊕ Fin n) K)))) ε)
    (h1 : (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε)
    {σ : K ≃+* K} (hσu : Matrix.GeneralLinearGroup.map (σ : K →+* K) u = u) :
    ∃ (n₁ : ℕ) (eG : ↥(glBlockCentralizer (StatedSp n K).subtype {u} ε) ≃* ↥(StatedSp n₁ K))
      (B : GL (Fin n₁ ⊕ Fin n₁) K), B ∈ StatedSp n₁ K ∧
      ∀ g g' : ↥(glBlockCentralizer (StatedSp n K).subtype {u} ε),
        ((g' : StatedSp n K) : GL (Fin n ⊕ Fin n) K) =
            Matrix.GeneralLinearGroup.map (σ : K →+* K)
              ((g : StatedSp n K) : GL (Fin n ⊕ Fin n) K) →
          ((eG g' : StatedSp n₁ K) : GL (Fin n₁ ⊕ Fin n₁) K) =
            B * Matrix.GeneralLinearGroup.map (σ : K →+* K)
              ((eG g : StatedSp n₁ K) : GL (Fin n₁ ⊕ Fin n₁) K) * B⁻¹ := by
  classical
  let V := Fin n ⊕ Fin n → K
  let G : Subgroup (StatedSp n K) :=
    glBlockCentralizer (StatedSp n K).subtype {u} ε
  let p : Module.End K V := Matrix.toLin' ε
  let W : Submodule K V := p.range
  let Z : Submodule K V := p.ker
  let B₀ : LinearMap.BilinForm K V := ggJS1_B n K
  let BW : LinearMap.BilinForm K W := B₀.restrict W
  have hWker : W = LinearMap.ker (Matrix.toLin' (u : Matrix (Fin n ⊕ Fin n)
      (Fin n ⊕ Fin n) K) - 1) := by
    simpa only [W, p] using kgfniSpFix_range_toLin'_eq_ker u hu hodd hε h1
  have hB₀alt : B₀.IsAlt := ggJS1_B_isAlt n K
  have hB₀nd : B₀.Nondegenerate := ggJS1_B_nondegenerate n K
  have hBWalt : BW.IsAlt := fun x => hB₀alt.self_eq_zero (x : V)
  have hpow : (Matrix.toLin' (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) ^
      orderOf u = 1 := by
    rw [← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one,
      Matrix.toLin'_one]
    rfl
  have hiso : ∀ x y, B₀ (Matrix.toLin' (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) x)
      (Matrix.toLin' (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) y) = B₀ x y := by
    intro x y
    have h := (CFSG.ComponentClassification.CatalogueBSymplecticB.mem_statedSp_iff_isometry u).mp hu
    rw [TauCeti.BilinForm.mem_isometryGroup_iff] at h
    have hcoe : ((ggJS1_matrixLinIso u : V ≃ₗ[K] V) : V →ₗ[K] V) =
        Matrix.toLin' (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
      apply LinearMap.ext
      intro v
      rw [Matrix.toLin'_apply]
      exact CFSG.ComponentClassification.CatalogueBSymplecticB.matrixLinIso_apply u v
    change ggJS1_B n K (Matrix.toLin' (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) x)
      (Matrix.toLin' (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) y) = ggJS1_B n K x y
    rw [show ggJS1_B n K = CFSG.LocalAnalysis.ComponentInitial.pairedSympForm K n from rfl]
    rw [← hcoe]
    exact h x y
  have hBWnd : BW.Nondegenerate := by
    have h := kgfniSpFix_restrict_ker_sub_one_nondegenerate B₀ hB₀nd hodd hpow hiso
    change (B₀.restrict W).Nondegenerate
    rw [hWker]
    exact h
  obtain ⟨m, b, hdim, hbJ⟩ := exists_symplectic_basis BW hBWalt hBWnd
  have hdim' : Module.finrank K W = 2 * m := hdim
  have hmem_G : ∀ g : ↥G, (g : StatedSp n K).val ∈
      Subgroup.centralizer ({u} : Set (GL (Fin n ⊕ Fin n) K)) ∧
      (g : StatedSp n K).val ∈ glFixing (1 - ε) := fun g =>
    Subgroup.mem_inf.mp (Subgroup.mem_comap.mp g.property)
  have hcomm_mat : ∀ g : ↥G, ((g : StatedSp n K).val : Matrix (Fin n ⊕ Fin n)
      (Fin n ⊕ Fin n) K) * ε =
      ε * ((g : StatedSp n K).val : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
    intro g
    have hcent := (hmem_G g).1
    have hb_u : u * (g : StatedSp n K).val = (g : StatedSp n K).val * u :=
      Subgroup.mem_centralizer_iff.mp hcent u (by simp)
    have hbM : (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
        ((g : StatedSp n K).val : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        ((g : StatedSp n K).val : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * u := by
      simpa only [Units.val_mul] using congrArg
        (fun w : GL (Fin n ⊕ Fin n) K => (w : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hb_u
    exact ggJS1_mem_adjoin_comm (S := ({u} : Set (GL (Fin n ⊕ Fin n) K)))
      (g := ((g : StatedSp n K).val : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))
      (fun s hs => by
        rw [Set.mem_singleton_iff] at hs
        subst hs
        exact hbM) hε.1
  have hmap : ∀ g : ↥G, Submodule.map
      (Matrix.toLin' (((g : StatedSp n K).val) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))
      W = W := by
    intro g
    simpa only [W, p] using ggJS1_map_range_eq_toLin' (g : StatedSp n K).val (hcomm_mat g)
  let restrict (g : ↥G) : W ≃ₗ[K] W :=
    (ggJS1_matrixLinIso ((g : StatedSp n K).val)).ofSubmodules W W (hmap g)
  have restrict_apply (g : ↥G) (v : W) :
      ((restrict g) v : V) = ggJS1_matrixLinIso ((g : StatedSp n K).val) v :=
    LinearEquiv.ofSubmodules_apply (ggJS1_matrixLinIso ((g : StatedSp n K).val)) (hmap g) v
  have hiso_mem : ∀ g : ↥G, restrict g ∈ isometryGroup BW := by
    intro g
    have hiso := (CFSG.ComponentClassification.CatalogueBSymplecticB.mem_statedSp_iff_isometry
      ((g : StatedSp n K).val)).mp (g : StatedSp n K).property
    rw [TauCeti.BilinForm.mem_isometryGroup_iff] at hiso
    rw [TauCeti.BilinForm.mem_isometryGroup_iff]
    intro x y
    change B₀ (((restrict g) x : W) : V) (((restrict g) y : W) : V) =
      B₀ (x : V) (y : V)
    rw [restrict_apply g x, restrict_apply g y]
    exact hiso x y
  let toIso : ↥G →* ↥(isometryGroup BW) :=
    { toFun := fun g => ⟨restrict g, hiso_mem g⟩
      map_one' := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        apply Subtype.ext
        rw [restrict_apply]
        simp
      map_mul' := by
        intro g h
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        apply Subtype.ext
        change ggJS1_matrixLinIso ((g : StatedSp n K).val * (h : StatedSp n K).val) (x : V) =
          ggJS1_matrixLinIso ((g : StatedSp n K).val)
            (ggJS1_matrixLinIso ((h : StatedSp n K).val) (x : V))
        rw [map_mul]
        rfl }
  have hcomplWZ : IsCompl W Z := by
    have hp : IsIdempotentElem p := by
      rw [isIdempotentElem_iff]
      rw [show p = Matrix.toLin' ε from rfl, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
        hε.2.1.eq]
    exact LinearMap.IsIdempotentElem.isCompl hp
  have hfixZ : ∀ g : ↥G, ∀ z : Z, ggJS1_matrixLinIso ((g : StatedSp n K).val) (z : V) = z := by
    intro g z
    have hgl : (((g : StatedSp n K).val) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
        (1 - ε) = 1 - ε := (hmem_G g).2
    have hz : (z : V) ∈ (Matrix.toLin' (1 - ε)).range := by
      have hp : IsIdempotentElem p := by
        rw [isIdempotentElem_iff]
        rw [show p = Matrix.toLin' ε from rfl, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
          hε.2.1.eq]
      have hz' : (z : V) ∈ (1 - p).range := by
        rw [← LinearMap.IsIdempotentElem.ker_eq_range_one_sub hp]
        exact z.2
      have hsub : Matrix.toLin' (1 - ε) = 1 - p := by
        apply LinearMap.ext
        intro v
        rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, LinearMap.sub_apply,
          Module.End.one_apply, Matrix.toLin'_apply]
      rwa [hsub]
    obtain ⟨v, hv⟩ := hz
    rw [← hv]
    change Matrix.toLin' (((g : StatedSp n K).val) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Matrix.toLin' (1 - ε) v) =
      Matrix.toLin' (1 - ε) v
    rw [← Matrix.toLin'_mul_apply (((g : StatedSp n K).val) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (1 - ε) v, hgl]
  have hinj : Function.Injective toIso := by
    intro g h hgh
    apply Subtype.ext
    apply Subtype.ext
    apply ggJS1_matrixLinIso.injective
    apply LinearEquiv.ext
    intro x
    have hghW : ∀ w : W, ggJS1_matrixLinIso ((g : StatedSp n K).val) (w : V) =
        ggJS1_matrixLinIso ((h : StatedSp n K).val) (w : V) := by
      intro w
      have hgh' : restrict g = restrict h := by
        have := congrArg (fun e : ↥(isometryGroup BW) => e.val) hgh
        have hco : (toIso g).val = restrict g := rfl
        have hco' : (toIso h).val = restrict h := rfl
        rwa [hco, hco'] at this
      have hw : ((restrict g) w : V) = ((restrict h) w : V) := by rw [hgh']
      rwa [restrict_apply g w, restrict_apply h w] at hw
    have hx : x ∈ W ⊔ Z := by rw [hcomplWZ.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, map_add, hghW ⟨w, hw⟩, hfixZ g ⟨z, hz⟩, hfixZ h ⟨z, hz⟩]
  obtain ⟨m', hm', ⟨eBlock⟩⟩ := blockGroup_iso_Sp_one u hu hodd hε h1
  have hm_eq : m' = m := by
    have h : 2 * m' = 2 * m := by rw [hm', hdim]
    exact Nat.mul_left_cancel (by norm_num) h
  let eBlock' : ↥G ≃* ↥(StatedSp m K) := hm_eq ▸ eBlock
  let eIsoSp : ↥(isometryGroup BW) ≃* ↥(StatedSp m K) :=
    (isometryMatrixEquiv b BW hbJ).trans
      (MulEquiv.subgroupCongr (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic
        (n := m) (K := K)).symm)
  let eGiso : ↥G ≃* ↥(isometryGroup BW) :=
    MulEquiv.ofBijective toIso
      ⟨hinj, hinj.surjective_of_finite (eBlock'.toEquiv.trans eIsoSp.toEquiv.symm)⟩
  let eG : ↥G ≃* ↥(StatedSp m K) := eGiso.trans eIsoSp
  have heG_val : ∀ g : ↥G, ((eG g : StatedSp m K) : GL (Fin m ⊕ Fin m) K) =
      (Matrix.GeneralLinearGroup.toLin' b).symm
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm (restrict g)) := by
    intro g
    change (basisMatrixEquiv b (restrict g)) = _
    exact kgfniSpFix_basisMatrixEquiv_eq_toLin'_symm b (restrict g)
  let S : V ≃+ V := vecMap σ
  have hSU : ∀ v : V, S (Matrix.toLin' (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) v) =
      Matrix.toLin' (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (S v) := by
    intro v
    have hmat : ((u : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map
        (σ : K →+* K) = ((u : GL (Fin n ⊕ Fin n) K) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
      simpa only [Matrix.GeneralLinearGroup.val_map_apply] using
        congrArg (fun w : GL (Fin n ⊕ Fin n) K =>
          (w : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hσu
    exact vecMap_mulVec_of_map_eq σ hmat v
  have hSW : ∀ v : V, v ∈ W → S v ∈ W := by
    intro v hv
    rw [hWker] at hv ⊢
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv ⊢
    rw [← hSU v, hv]
  have hSWinv : ∀ v : V, v ∈ W → S.symm v ∈ W := by
    intro v hv
    rw [hWker] at hv ⊢
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv ⊢
    apply S.injective
    rw [hSU, S.apply_symm_apply, hv]
  let SW : W ≃+ W :=
    { toFun := fun v => ⟨S v.1, hSW v.1 v.2⟩
      invFun := fun v => ⟨S.symm v.1, hSWinv v.1 v.2⟩
      left_inv := fun v => Subtype.ext (S.left_inv v.1)
      right_inv := fun v => Subtype.ext (S.right_inv v.1)
      map_add' := fun v w => Subtype.ext (S.map_add v.1 w.1) }
  have hSWsmul : ∀ (c : K) (v : W), SW (c • v) = σ c • SW v := by
    intro c v
    apply Subtype.ext
    exact vecMap_smul σ c v.1
  let B : GL (Fin m ⊕ Fin m) K := semMatUnit b SW hSWsmul
  have hJfrom : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      - Matrix.J (Fin m) K := CFSG.ClassicalGroups.Symplectic.blueprintGram_eq_neg_J
  have hJfix : ∀ i j, σ (Matrix.J (Fin m) K i j) = Matrix.J (Fin m) K i j := by
    intro i j
    rw [show Matrix.J (Fin m) K = -(Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) by rw [hJfrom, neg_neg]]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
  have hform : ∀ x y : W, BW (SW x) (SW y) = σ (BW x y) := by
    intro x y
    have hSx : S x.1 = σ ∘ x.1 := rfl
    have hSy : S y.1 = σ ∘ y.1 := rfl
    have hJmap : (ggJS1_J n K).map (σ : K →+* K) = ggJS1_J n K := by
      ext (i | i) (j | j) <;>
        simp [ggJS1_J, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
    have hmv : (ggJS1_J n K) *ᵥ (σ ∘ y.1) =
        σ ∘ ((ggJS1_J n K) *ᵥ y.1) := by
      funext i
      have h := RingHom.map_mulVec (σ : K →+* K) (ggJS1_J n K) y.1 i
      rw [hJmap] at h
      exact h.symm
    change B₀ (S x.1) (S y.1) = σ (B₀ x.1 y.1)
    rw [show B₀ = Matrix.toBilin' (ggJS1_J n K) from rfl,
      Matrix.toBilin'_apply', Matrix.toBilin'_apply', hSx, hSy, hmv]
    exact (RingHom.map_dotProduct (σ : K →+* K) x.1
      ((ggJS1_J n K) *ᵥ y.1)).symm
  have hB : B ∈ StatedSp m K := by
    have hgram := kgfniSpFix_semMat_transpose_mul_form b (Matrix.J (Fin m) K) BW hbJ
      SW hSWsmul hform hJfix
    rw [CFSG.Open.StatedAPI.mem_statedSp_iff, hJfrom]
    have h := congrArg Neg.neg hgram
    simpa only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, B, coe_semMatUnit] using h
  let restrictUnit (g : ↥G) : LinearMap.GeneralLinearGroup K W :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm (restrict g)
  have restrictUnit_coe (g : ↥G) :
      ((restrictUnit g : LinearMap.GeneralLinearGroup K W) : W →ₗ[K] W) =
        (restrict g : W →ₗ[K] W) := rfl
  have hcoe : ∀ (x : GL (Fin n ⊕ Fin n) K) (v : V),
      ggJS1_matrixLinIso x v =
        Matrix.toLin' (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) v := by
    intro x v
    rw [Matrix.toLin'_apply]
    exact CFSG.ComponentClassification.CatalogueBSymplecticB.matrixLinIso_apply x v
  refine ⟨m, eG, B, hB, ?_⟩
  intro g g' hgg'
  have hpoint : ∀ v : W, (restrictUnit g' : W →ₗ[K] W) v =
      SW ((restrictUnit g : W →ₗ[K] W) (SW.symm v)) := by
    intro v
    apply Subtype.ext
    change ((restrictUnit g' : W →ₗ[K] W) v : V) =
      S (((restrictUnit g : W →ₗ[K] W) (SW.symm v)) : V)
    have hL : ((restrictUnit g' : W →ₗ[K] W) v : V) =
        Matrix.toLin' (((g' : StatedSp n K).val) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) v.1 := by
      change ((restrict g') v : V) = _
      rw [restrict_apply]
      exact hcoe ((g' : StatedSp n K).val) v.1
    have hR : ((restrictUnit g : W →ₗ[K] W) (SW.symm v) : V) =
        Matrix.toLin' (((g : StatedSp n K).val) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (S.symm v.1) := by
      change ((restrict g) (SW.symm v) : V) = _
      rw [restrict_apply]
      exact hcoe ((g : StatedSp n K).val) (S.symm v.1)
    rw [hL, hR]
    have hmat : (((g' : StatedSp n K).val) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        (((g : StatedSp n K).val) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map
          (σ : K →+* K) := by
      simpa only [Matrix.GeneralLinearGroup.val_map_apply] using
        congrArg (fun w : GL (Fin n ⊕ Fin n) K =>
          (w : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hgg'
    rw [hmat, Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact map_mulVec_eq_vecMap σ
      (((g : StatedSp n K).val) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) v.1
  have hsq := toLin'_symm_conj_semilin b SW hSWsmul
    (restrictUnit g) (restrictUnit g') hpoint
  rw [heG_val g', heG_val g]
  exact hsq

end CFSG.StandardType
