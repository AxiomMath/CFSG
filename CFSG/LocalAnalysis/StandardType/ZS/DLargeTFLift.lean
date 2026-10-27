module

public import CFSG.LocalAnalysis.StandardType.ZS.ReflFrame
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtMatrices
import CFSG.LocalAnalysis.StandardType.ZS.AbsIrred
import CFSG.LocalAnalysis.StandardType.ZS.ExcMatricesRefl
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
import CFSG.LocalAnalysis.StandardType.ZS.ThroughRefl
import CFSG.LocalAnalysis.StandardType.ZS.NFourRelations
import Mathlib.RingTheory.ZMod.UnitsCyclic
import TauCeti.GroupTheory.Sylow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W] [Module (ZMod p) W]

private theorem eq_of_fixes_centralizer_of_agree
    {X : Subgroup (W ≃ₗ[ZMod p] W)} {l : ℕ} (hX : SplitSupport X l)
    {u v : W ≃ₗ[ZMod p] W}
    (huC : ∀ c ∈ centralizerSpace X, u c = c)
    (hvC : ∀ c ∈ centralizerSpace X, v c = c)
    (huv : ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace X, u w = v w) : u = v := by
  ext a
  have ha : a ∈ HardMathSupport.Kantor79.commutatorSpace X ⊔ centralizerSpace X := by
    rw [hX.1.sup_eq_top]; trivial
  obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp ha
  rw [map_add, map_add, huv w hw, huC c hc, hvC c hc]

private theorem blockSucc_lin {l : ℕ} {f : Module.Basis (Fin (l + 1)) (ZMod p) W}
    {M : Matrix (Fin l) (Fin l) (ZMod p)} {u : W ≃ₗ[ZMod p] W}
    (hu : LinearMap.toMatrix f f (u : W →ₗ[ZMod p] W) = Matrix.blockSucc M) :
    (u : W →ₗ[ZMod p] W) = Matrix.toLin f f (Matrix.blockSucc M) := by
  rw [← hu]
  exact (Matrix.toLin_toMatrix (v₁ := f) (v₂ := f) (u : W →ₗ[ZMod p] W)).symm

private theorem blockSucc_hlast {l : ℕ} {f : Module.Basis (Fin (l + 1)) (ZMod p) W}
    {M : Matrix (Fin l) (Fin l) (ZMod p)} {u : W ≃ₗ[ZMod p] W}
    (hu : LinearMap.toMatrix f f (u : W →ₗ[ZMod p] W) = Matrix.blockSucc M) :
    u (f (Fin.last l)) = f (Fin.last l) := by
  show (u : W →ₗ[ZMod p] W) (f (Fin.last l)) = f (Fin.last l)
  rw [blockSucc_lin hu, Matrix.toLin_self, Fin.sum_univ_castSucc]
  simp

private theorem blockSucc_fixes [Module.Finite (ZMod p) W]
    {l : ℕ} {X : Subgroup (W ≃ₗ[ZMod p] W)} (hX : SplitSupport X l)
    (hW : Module.finrank (ZMod p) W = l + 1)
    {f : Module.Basis (Fin (l + 1)) (ZMod p) W}
    (hflast : f (Fin.last l) ∈ centralizerSpace X)
    {u : W ≃ₗ[ZMod p] W} (hlast : u (f (Fin.last l)) = f (Fin.last l)) :
    ∀ c ∈ centralizerSpace X, u c = c := by
  have hCdim : Module.finrank (ZMod p) (centralizerSpace X) = 1 := by
    have h := Submodule.finrank_add_eq_of_isCompl hX.1
    rw [hX.2.1, hW] at h
    omega
  have hCspan : centralizerSpace X = Submodule.span (ZMod p) {f (Fin.last l)} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hCdim hflast
      (f.linearIndependent.ne_zero (Fin.last l))
  intro c hc
  rw [hCspan] at hc
  obtain ⟨ζ, hζ⟩ := Submodule.mem_span_singleton.mp hc
  rw [← hζ, map_smul, hlast]

private theorem blockSucc_restrict {l : ℕ}
    {X : Subgroup (W ≃ₗ[ZMod p] W)}
    {g : Module.Basis (Fin l) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X)}
    {f : Module.Basis (Fin (l + 1)) (ZMod p) W}
    (hf : ∀ i, f (Fin.castSucc i) = (g i : W))
    {M : Matrix (Fin l) (Fin l) (ZMod p)} {u : W ≃ₗ[ZMod p] W}
    (hu : LinearMap.toMatrix f f (u : W →ₗ[ZMod p] W) = Matrix.blockSucc M) :
    ∀ v : HardMathSupport.Kantor79.commutatorSpace X,
      u (v : W) = (Matrix.toLin g g M v : W) := by
  have hlin := blockSucc_lin hu
  intro v
  have hmap : (u : W →ₗ[ZMod p] W).comp
        (HardMathSupport.Kantor79.commutatorSpace X).subtype =
      (HardMathSupport.Kantor79.commutatorSpace X).subtype.comp (Matrix.toLin g g M) := by
    apply g.ext
    intro i
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    have h1 : (u : W →ₗ[ZMod p] W) (g i : W) = ∑ j, M j i • (g j : W) := by
      rw [← hf i]
      show (u : W →ₗ[ZMod p] W) (f (Fin.castSucc i)) = ∑ j, M j i • (g j : W)
      rw [hlin, Matrix.toLin_self, Fin.sum_univ_castSucc]
      simp only [Matrix.blockSucc_castSucc_castSucc, Matrix.blockSucc_last_castSucc, zero_smul,
        add_zero]
      exact Finset.sum_congr rfl (fun j _ => by rw [hf j])
    have h2 : (Matrix.toLin g g M (g i) : W) = ∑ j, M j i • (g j : W) := by
      have h := Matrix.toLin_self (v₁ := g) (v₂ := g) M i
      rw [h]
      simp
    change (u : W →ₗ[ZMod p] W) (g i : W) = (Matrix.toLin g g M (g i) : W)
    rw [h1, h2]
  have hval := congrArg (fun f' : HardMathSupport.Kantor79.commutatorSpace X →ₗ[ZMod p] W =>
    f' v) hmap
  simpa [LinearMap.comp_apply] using hval

private theorem blockSucc_data [Module.Finite (ZMod p) W]
    {l : ℕ} {X : Subgroup (W ≃ₗ[ZMod p] W)} (hX : SplitSupport X l)
    (hW : Module.finrank (ZMod p) W = l + 1)
    {g : Module.Basis (Fin l) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X)}
    {f : Module.Basis (Fin (l + 1)) (ZMod p) W}
    (hf : ∀ i, f (Fin.castSucc i) = (g i : W))
    (hflast : f (Fin.last l) ∈ centralizerSpace X)
    {M : Matrix (Fin l) (Fin l) (ZMod p)} {u : W ≃ₗ[ZMod p] W}
    (hu : LinearMap.toMatrix f f (u : W →ₗ[ZMod p] W) = Matrix.blockSucc M) :
    (∀ c ∈ centralizerSpace X, u c = c) ∧
      (∀ v : HardMathSupport.Kantor79.commutatorSpace X,
        u (v : W) = (Matrix.toLin g g M v : W)) :=
  ⟨blockSucc_fixes hX hW hflast (blockSucc_hlast hu),
    blockSucc_restrict hf hu⟩

private theorem blockSucc_le [Module.Finite (ZMod p) W]
    {X : Subgroup (W ≃ₗ[ZMod p] W)} {l : ℕ} (hX : SplitSupport X l)
    (hW : Module.finrank (ZMod p) W = l + 1)
    {g : Module.Basis (Fin l) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X)}
    {S : Set (Matrix (Fin l) (Fin l) (ZMod p))} (hS : movedGroup X = basisClosure g S)
    {f : Module.Basis (Fin (l + 1)) (ZMod p) W}
    (hf : ∀ i, f (Fin.castSucc i) = (g i : W))
    (hflast : f (Fin.last l) ∈ centralizerSpace X) :
    basisClosure f (Matrix.blockSucc '' S) ≤ X := by
  rw [basisClosure, Subgroup.closure_le]
  rintro u hu
  rw [Set.mem_setOf_eq] at hu
  obtain ⟨M, hM, huM⟩ := hu
  have huM' : LinearMap.toMatrix f f (u : W →ₗ[ZMod p] W) = Matrix.blockSucc M := huM.symm
  obtain ⟨huC, huV⟩ := blockSucc_data hX hW hf hflast huM'
  have hdetM : IsUnit M.det := by
    rw [← Matrix.det_blockSucc, ← huM']
    exact LinearEquiv.isUnit_det u f f
  let mapV : HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X := Matrix.toLinearEquiv g M hdetM
  have hmapVlin : (mapV : HardMathSupport.Kantor79.commutatorSpace X →ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X) = Matrix.toLin g g M := rfl
  have hmapV_mem : mapV ∈ basisClosure g S := by
    rw [basisClosure]
    refine Subgroup.subset_closure ?_
    show LinearMap.toMatrix g g (mapV : HardMathSupport.Kantor79.commutatorSpace X →ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X) ∈ S
    simpa [hmapVlin] using hM
  have hmemMG : mapV ∈ movedGroup X := by rw [hS]; exact hmapV_mem
  obtain ⟨x, hxφ⟩ := MonoidHom.mem_range.mp hmemMG
  have hxu : (x : W ≃ₗ[ZMod p] W) = u := by
    apply eq_of_fixes_centralizer_of_agree hX
    · intro c hc
      exact mem_centralizerSpace.mp hc (x : W ≃ₗ[ZMod p] W) x.2
    · exact huC
    · intro w hw
      have hxw : (x : W ≃ₗ[ZMod p] W) w = (mapV ⟨w, hw⟩ : W) := by
        have h := congrArg (fun e : HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
          HardMathSupport.Kantor79.commutatorSpace X => ((e ⟨w, hw⟩ : _) : W)) hxφ
        simpa [mapV, restrictHom_apply] using h
      have huw : u w = (mapV ⟨w, hw⟩ : W) := by
        simpa [mapV, hmapVlin] using huV ⟨w, hw⟩
      rw [hxw, huw]
  rw [← hxu]
  exact x.2

private def liftProp {X : Subgroup (W ≃ₗ[ZMod p] W)}
    (L : Subgroup (W ≃ₗ[ZMod p] W))
    (y : HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X) : Prop :=
  ∃ l ∈ L, (∀ c ∈ centralizerSpace X, l c = c) ∧
    (∀ v : HardMathSupport.Kantor79.commutatorSpace X, l (v : W) = (y v : W))

private theorem liftProp_one {X : Subgroup (W ≃ₗ[ZMod p] W)}
    (L : Subgroup (W ≃ₗ[ZMod p] W)) :
    liftProp L
      (1 : HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
        HardMathSupport.Kantor79.commutatorSpace X) :=
  ⟨1, Subgroup.one_mem L, (by intro c hc; rfl), (by intro v; rfl)⟩

private theorem liftProp_mul {X : Subgroup (W ≃ₗ[ZMod p] W)}
    (L : Subgroup (W ≃ₗ[ZMod p] W))
    {y z : HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X}
    (hy : liftProp L y) (hz : liftProp L z) :
    liftProp L (y * z) := by
  obtain ⟨l₁, hl₁, hc₁, hv₁⟩ := hy
  obtain ⟨l₂, hl₂, hc₂, hv₂⟩ := hz
  refine ⟨l₁ * l₂, Subgroup.mul_mem L hl₁ hl₂, ?_, ?_⟩
  · intro c hc
    rw [LinearEquiv.mul_apply, hc₂ c hc, hc₁ c hc]
  · intro v
    rw [LinearEquiv.mul_apply, hv₂ v, hv₁ (z v), LinearEquiv.mul_apply]

private theorem liftProp_inv {X : Subgroup (W ≃ₗ[ZMod p] W)}
    (L : Subgroup (W ≃ₗ[ZMod p] W))
    {y : HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X}
    (hy : liftProp L y) : liftProp L y⁻¹ := by
  obtain ⟨l, hl, hc, hv⟩ := hy
  refine ⟨l⁻¹, Subgroup.inv_mem L hl, ?_, ?_⟩
  · intro c hmem
    apply l.injective
    change l (l.symm c) = l c
    rw [LinearEquiv.apply_symm_apply, hc c hmem]
  · intro v
    have h1 : l (l⁻¹ (v : W)) =
        l ((y⁻¹ v : HardMathSupport.Kantor79.commutatorSpace X) : W) := by
      change l (l.symm (v : W)) = l ((y.symm v : _) : W)
      rw [LinearEquiv.apply_symm_apply, hv (y.symm v), LinearEquiv.apply_symm_apply]
    exact l.injective h1

private theorem liftProp_generator [Module.Finite (ZMod p) W]
    {l : ℕ} {X : Subgroup (W ≃ₗ[ZMod p] W)} (hX : SplitSupport X l)
    (hW : Module.finrank (ZMod p) W = l + 1)
    {g : Module.Basis (Fin l) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X)}
    {S : Set (Matrix (Fin l) (Fin l) (ZMod p))}
    {f : Module.Basis (Fin (l + 1)) (ZMod p) W}
    (hf : ∀ i, f (Fin.castSucc i) = (g i : W))
    (hflast : f (Fin.last l) ∈ centralizerSpace X)
    {y : HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X}
    (hy : LinearMap.toMatrix g g (y : HardMathSupport.Kantor79.commutatorSpace X →ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X) ∈ S) :
    liftProp (basisClosure f (Matrix.blockSucc '' S)) y := by
  let M : Matrix (Fin l) (Fin l) (ZMod p) := LinearMap.toMatrix g g
    (y : HardMathSupport.Kantor79.commutatorSpace X →ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X)
  have hy' : y = Matrix.toLin g g M :=
    (Matrix.toLin_toMatrix (v₁ := g) (v₂ := g) (y : HardMathSupport.Kantor79.commutatorSpace X
      →ₗ[ZMod p] HardMathSupport.Kantor79.commutatorSpace X)).symm
  have hdetM : IsUnit M.det := LinearEquiv.isUnit_det y g g
  have hdetBM : IsUnit (Matrix.blockSucc M).det := by
    rwa [Matrix.det_blockSucc]
  let lift : W ≃ₗ[ZMod p] W := Matrix.toLinearEquiv f (Matrix.blockSucc M) hdetBM
  have hliftlin : (lift : W →ₗ[ZMod p] W) = Matrix.toLin f f (Matrix.blockSucc M) := rfl
  have hliftmat : LinearMap.toMatrix f f (lift : W →ₗ[ZMod p] W) = Matrix.blockSucc M := by
    rw [hliftlin, LinearMap.toMatrix_toLin]
  have hlift_mem : lift ∈ basisClosure f (Matrix.blockSucc '' S) := by
    rw [basisClosure]
    refine Subgroup.subset_closure ?_
    show LinearMap.toMatrix f f (lift : W →ₗ[ZMod p] W) ∈ Matrix.blockSucc '' S
    exact ⟨M, hy, hliftmat.symm⟩
  obtain ⟨hliftC, hliftV⟩ := blockSucc_data hX hW hf hflast hliftmat
  refine ⟨lift, hlift_mem, hliftC, ?_⟩
  intro v
  rw [hliftV v]
  exact (congrArg (fun e : HardMathSupport.Kantor79.commutatorSpace X →ₗ[ZMod p]
    HardMathSupport.Kantor79.commutatorSpace X => ((e v : _) : W)) hy').symm

private theorem le_basisClosure_blockSucc [Module.Finite (ZMod p) W]
    {X : Subgroup (W ≃ₗ[ZMod p] W)} {l : ℕ} (hX : SplitSupport X l)
    (hW : Module.finrank (ZMod p) W = l + 1)
    {g : Module.Basis (Fin l) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X)}
    {S : Set (Matrix (Fin l) (Fin l) (ZMod p))} (hS : movedGroup X = basisClosure g S)
    {f : Module.Basis (Fin (l + 1)) (ZMod p) W}
    (hf : ∀ i, f (Fin.castSucc i) = (g i : W))
    (hflast : f (Fin.last l) ∈ centralizerSpace X) :
    X ≤ basisClosure f (Matrix.blockSucc '' S) := by
  intro x hx
  let L := basisClosure f (Matrix.blockSucc '' S)
  let φ := restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
    (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hxmg : φ ⟨x, hx⟩ ∈ basisClosure g S := by
    rw [← hS]
    exact MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩
  have hQ : liftProp L (φ ⟨x, hx⟩) := by
    refine Subgroup.closure_induction (p := fun y _ => liftProp L y) ?_ ?_ ?_ ?_ hxmg
    · intro y hy
      exact liftProp_generator hX hW hf hflast hy
    · exact liftProp_one L
    · intro y z _ _ hy hz
      exact liftProp_mul L hy hz
    · intro y _ hy
      exact liftProp_inv L hy
  obtain ⟨l, hl, hlc, hlv⟩ := hQ
  have hxl : (x : W ≃ₗ[ZMod p] W) = l := by
    apply eq_of_fixes_centralizer_of_agree hX
    · intro c hc
      exact mem_centralizerSpace.mp hc (x : W ≃ₗ[ZMod p] W) hx
    · exact hlc
    · intro w hw
      have hxw : (x : W ≃ₗ[ZMod p] W) w = (φ ⟨x, hx⟩ ⟨w, hw⟩ : W) := by
        simp [φ, restrictHom_apply]
      rw [hxw, hlv ⟨w, hw⟩]
  rw [hxl]
  exact hl

private noncomputable def centerScalar {A : Subgroup (W ≃ₗ[ZMod p] W)}
    (hA : AbsIrred p A) (z : Subgroup.center A) : ZMod p :=
  Classical.choose (AbsIrred.exists_eq_smul_of_mem_center hA z.2)

private theorem centerScalar_spec {A : Subgroup (W ≃ₗ[ZMod p] W)}
    (hA : AbsIrred p A) (z : Subgroup.center A) :
    (((z : A) : W ≃ₗ[ZMod p] W) : W →ₗ[ZMod p] W) =
      centerScalar hA z • LinearMap.id :=
  Classical.choose_spec (AbsIrred.exists_eq_smul_of_mem_center hA z.2)

private theorem centerScalar_eq_of {A : Subgroup (W ≃ₗ[ZMod p] W)}
    (hA : AbsIrred p A) {v : W} (hv : v ≠ 0) {z : Subgroup.center A} {c : ZMod p}
    (hc : (((z : A) : W ≃ₗ[ZMod p] W) : W →ₗ[ZMod p] W) = c • LinearMap.id) :
    centerScalar hA z = c := by
  have h : centerScalar hA z • v = c • v :=
    congrArg (fun f : W →ₗ[ZMod p] W => f v) ((centerScalar_spec hA z).symm.trans hc)
  have h2 : (centerScalar hA z - c) • v = 0 := by
    rw [sub_smul, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv)

private theorem centerScalar_ne_zero {A : Subgroup (W ≃ₗ[ZMod p] W)}
    (hA : AbsIrred p A) {v : W} (hv : v ≠ 0) (z : Subgroup.center A) :
    centerScalar hA z ≠ 0 := by
  intro h0
  have h := centerScalar_spec hA z
  rw [h0, zero_smul] at h
  have hvz : ((z : A) : W ≃ₗ[ZMod p] W) v = 0 :=
    congrArg (fun f : W →ₗ[ZMod p] W => f v) h
  exact hv (((z : A) : W ≃ₗ[ZMod p] W).injective (by rw [hvz, map_zero]))

private theorem centerScalar_one {A : Subgroup (W ≃ₗ[ZMod p] W)}
    (hA : AbsIrred p A) {v : W} (hv : v ≠ 0) :
    centerScalar hA (1 : Subgroup.center A) = 1 := by
  refine centerScalar_eq_of hA hv ?_
  simp

private theorem centerScalar_mul {A : Subgroup (W ≃ₗ[ZMod p] W)}
    (hA : AbsIrred p A) {v : W} (hv : v ≠ 0) (z₁ z₂ : Subgroup.center A) :
    centerScalar hA (z₁ * z₂) =
      centerScalar hA z₁ * centerScalar hA z₂ := by
  refine centerScalar_eq_of hA hv ?_
  have hmul : (((z₁ * z₂ : Subgroup.center A) : A) : W ≃ₗ[ZMod p] W) =
      (((z₁ : Subgroup.center A) : A) : W ≃ₗ[ZMod p] W) *
        (((z₂ : Subgroup.center A) : A) : W ≃ₗ[ZMod p] W) := rfl
  rw [hmul, LinearEquiv.coe_toLinearMap_mul, centerScalar_spec hA z₁, centerScalar_spec hA z₂]
  ext w
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]

private noncomputable def centerHom {A : Subgroup (W ≃ₗ[ZMod p] W)}
    (hA : AbsIrred p A) {v : W} (hv : v ≠ 0) : Subgroup.center A →* (ZMod p)ˣ where
  toFun z := Units.mk0 (centerScalar hA z) (centerScalar_ne_zero hA hv z)
  map_one' := Units.ext (centerScalar_one hA hv)
  map_mul' z w := Units.ext (centerScalar_mul hA hv z w)

private theorem centerHom_injective {A : Subgroup (W ≃ₗ[ZMod p] W)}
    (hA : AbsIrred p A) {v : W} (hv : v ≠ 0) :
    Function.Injective (centerHom hA hv) := by
  intro z w hzw
  have h : centerScalar hA z = centerScalar hA w := by
    have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hzw
    simpa [centerHom] using this
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro a
  rw [centerScalar_spec hA z, centerScalar_spec hA w, h]

theorem exists_basis_eq_basisClosure_blockSucc_of_movedGroup [Module.Finite (ZMod p) W]
    {X : Subgroup (W ≃ₗ[ZMod p] W)} {l : ℕ} (hX : SplitSupport X l)
    (hW : Module.finrank (ZMod p) W = l + 1)
    {g : Module.Basis (Fin l) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X)}
    {S : Set (Matrix (Fin l) (Fin l) (ZMod p))} (hS : movedGroup X = basisClosure g S) :
    ∃ f : Module.Basis (Fin (l + 1)) (ZMod p) W, X = basisClosure f (Matrix.blockSucc '' S) := by
  classical
  let V := HardMathSupport.Kantor79.commutatorSpace X
  have hvli : LinearIndependent (ZMod p) (fun i => (g i : W)) := by
    simpa [Function.comp_def] using
      (g.linearIndependent).map' V.subtype (by simp)
  have hvV : ∀ i, (g i : W) ∈ V := fun i => (g i).2
  obtain ⟨f, hf, hflast⟩ := exists_basis_snoc_of_splitSupport hX hW hvli hvV
  exact ⟨f, le_antisymm
    (le_basisClosure_blockSucc hX hW hS hf hflast)
    (blockSucc_le hX hW hS hf hflast)⟩

theorem exists_central_orderOf_eq_of_movedGroup {X : Subgroup (W ≃ₗ[ZMod p] W)} {l : ℕ}
    (hX : SplitSupport X l)
    {z : HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X} (hz : z ∈ movedGroup X)
    (hc : ∀ x ∈ movedGroup X, z * x = x * z) :
    ∃ z' ∈ X, (∀ x ∈ X, z' * x = x * z') ∧ orderOf z' = orderOf z := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hinj : Function.Injective φ := restrictHom_injective_of_splitSupport hX
  obtain ⟨z', hz'⟩ := MonoidHom.mem_range.mp hz
  refine ⟨z', z'.2, ?_, ?_⟩
  · intro x hx
    let x' : X := ⟨x, hx⟩
    have hxmg : φ x' ∈ movedGroup X := MonoidHom.mem_range.mpr ⟨x', rfl⟩
    have hmem : z' * x' = x' * z' := hinj (by
      rw [map_mul, map_mul, hz']
      exact hc (φ x') hxmg)
    have hval : (x' : W ≃ₗ[ZMod p] W) = x := rfl
    rw [← hval]
    exact congrArg (fun w : X => (w : W ≃ₗ[ZMod p] W)) hmem
  · have h := orderOf_injective φ hinj z'
    rw [hz'] at h
    rw [Subgroup.orderOf_coe]
    exact h.symm

theorem exists_orderOf_eq_card_center_of_absIrred [Module.Finite (ZMod p) W]
    {A : Subgroup (W ≃ₗ[ZMod p] W)} (hA : AbsIrred p A) :
    ∃ z ∈ A, (∀ x ∈ A, z * x = x * z) ∧ orderOf z = Nat.card (Subgroup.center A) := by
  by_cases hsub : Subsingleton W
  · have hsubC : Subsingleton ↥(Subgroup.center A) :=
      ⟨fun a b => Subtype.ext (Subtype.ext (LinearEquiv.ext fun _ => hsub.elim _ _))⟩
    refine ⟨1, A.one_mem, fun x _ => by simp, ?_⟩
    rw [orderOf_one, Nat.card_eq_one_iff_unique.mpr ⟨hsubC, ⟨1⟩⟩]
  · have hnt : Nontrivial W := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨v, hv⟩ := (nontrivial_iff_exists_ne (0 : W)).mp hnt
    have hcycUnits : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime (Fact.out)
    have hcyc : IsCyclic (Subgroup.center A) :=
      @isCyclic_of_injective (↥(Subgroup.center A)) ((ZMod p)ˣ) _ _ hcycUnits
        (centerHom hA hv) (centerHom_injective hA hv)
    obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (Subgroup.center A)).mp hcyc
    have hgmem : g ∈ Subgroup.center A := by
      rw [← hg]
      exact Subgroup.mem_zpowers g
    refine ⟨(g : W ≃ₗ[ZMod p] W), g.2, ?_, ?_⟩
    · intro x hx
      have hcomm := Subgroup.mem_center_iff.mp hgmem ⟨x, hx⟩
      exact (congrArg (fun w : A => (w : W ≃ₗ[ZMod p] W)) hcomm).symm
    · have horder : orderOf g = Nat.card (Subgroup.center A) := by
        rw [← Nat.card_zpowers, hg]
      rw [Subgroup.orderOf_coe, horder]

private lemma orderOf_smul_one_of_sq_eq_neg_one (hp : p ≠ 2) {t : ZMod p} (ht : t ^ 2 = -1) :
    orderOf (t • (1 : Matrix (Fin 4) (Fin 4) (ZMod p))) = 4 := by
  have hneg : (-1 : ZMod p) ≠ 1 :=
    Ring.neg_one_ne_one_of_char_ne_two (by rw [ZMod.ringChar_zmod_n]; exact hp)
  have h4 : (t • (1 : Matrix (Fin 4) (Fin 4) (ZMod p))) ^ 4 = 1 := by
    rw [smul_pow, one_pow]
    have ht4 : t ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, ht]
      ring
    rw [ht4, one_smul]
  have h2ne : (t • (1 : Matrix (Fin 4) (Fin 4) (ZMod p))) ^ 2 ≠ 1 := by
    rw [smul_pow, one_pow, ht]
    intro h
    exact hneg (by simpa using congrFun (congrFun h 0) 0)
  simpa using orderOf_eq_prime_pow (p := 2) (n := 1)
    (by simpa using h2ne) (by simpa using h4)

private lemma scalar_mem_basisClosure_weylN4Mats (hp : p ≠ 2)
    (f : Module.Basis (Fin 4) (ZMod p) W) {t : ZMod p} (ht : t ^ 2 = -1) :
    ∃ z ∈ basisClosure f (weylN4Mats t),
      automorphismToMatrix f z = t • 1 ∧ orderOf z = 4 := by
  classical
  have hp2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨s, hs, hcl, -, -⟩ := exists_n4_tuple hp2 ht f
  have hmat : ∀ i, automorphismToMatrix f (s i) = n4Mat t i :=
    fun i => by rw [automorphismToMatrix_apply]; exact hs i
  let z : W ≃ₗ[ZMod p] W := (n4Word.map s).prod
  have hzmat : automorphismToMatrix f z = (n4Word.map (n4Mat t)).prod := by
    dsimp only [z]
    rw [map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun i _ => hmat i)
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [← hcl]
    exact Subgroup.list_prod_mem (Subgroup.closure (Set.range s)) fun x hx =>
      Subgroup.subset_closure ((List.mem_map.mp hx).imp fun _ hi => hi.2)
  · rw [hzmat, prod_n4Mat_n4Word hp2 ht]
  · rw [← orderOf_injective (automorphismToMatrix f) (automorphismToMatrix_injective f) z,
      hzmat, prod_n4Mat_n4Word hp2 ht]
    exact orderOf_smul_one_of_sq_eq_neg_one hp ht

private lemma central_of_automorphismToMatrix_eq_smul_one (f : Module.Basis (Fin 4) (ZMod p) W)
    {z : W ≃ₗ[ZMod p] W} {t : ZMod p} (hzmat : automorphismToMatrix f z = t • 1)
    (x : W ≃ₗ[ZMod p] W) : z * x = x * z := by
  apply automorphismToMatrix_injective f
  rw [map_mul, map_mul, hzmat]
  simp

theorem exists_central_orderOf_four_basisClosure_weylN4Mats (hp : p ≠ 2)
    (f : Module.Basis (Fin 4) (ZMod p) W) {t : ZMod p} (ht : t ^ 2 = -1) :
    ∃ z ∈ basisClosure f (weylN4Mats t),
      (∀ x ∈ basisClosure f (weylN4Mats t), z * x = x * z) ∧ orderOf z = 4 := by
  obtain ⟨z, hz, hzmat, ho⟩ := scalar_mem_basisClosure_weylN4Mats hp f ht
  exact ⟨z, hz, fun x _ => central_of_automorphismToMatrix_eq_smul_one f hzmat x, ho⟩

theorem exists_central_orderOf_four_basisClosure_weylEN4Mats (hp : p ≠ 2)
    (f : Module.Basis (Fin 4) (ZMod p) W) {t : ZMod p} (ht : t ^ 2 = -1) :
    ∃ z ∈ basisClosure f (weylEN4Mats t),
      (∀ x ∈ basisClosure f (weylEN4Mats t), z * x = x * z) ∧ orderOf z = 4 := by
  obtain ⟨z, hz, hzmat, ho⟩ := scalar_mem_basisClosure_weylN4Mats hp f ht
  have hsub : basisClosure f (weylN4Mats t) ≤ basisClosure f (weylEN4Mats t) :=
    Subgroup.closure_mono fun g hg => Set.mem_insert_of_mem (diagSignMat 3) hg
  exact ⟨z, hsub hz, fun x _ => central_of_automorphismToMatrix_eq_smul_one f hzmat x, ho⟩

end CFSG.StandardType.ZS

end
