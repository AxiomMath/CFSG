module

public import CFSG.Quasithin.Background.SmithCurtisBasic
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ExtendScalars
import Mathlib.LinearAlgebra.TensorProduct.Pi
import TauCeti.LinearAlgebra.TensorProduct.Kernel
import TauCeti.LinearAlgebra.TensorProduct.Range

public section

namespace CFSG.Theory.Representation

open _root_.Representation
open Module
open scoped TensorProduct
open CFSG.Quasithin.SmithCurtis

variable {F G V M : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [Group M] (F' : Type*) [Field F'] [Algebra F F']

private noncomputable def fixSubDefect (ρ : Representation F G V) (N : Subgroup G) :
    V →ₗ[F] (N → V) :=
  LinearMap.pi fun n => ρ n - LinearMap.id

private theorem fixSub_eq_ker_fixSubDefect (ρ : Representation F G V) (N : Subgroup G) :
    fixSub ρ N = LinearMap.ker (fixSubDefect ρ N) := by
  ext v
  rw [mem_fixSub, LinearMap.mem_ker]
  constructor
  · intro hv
    ext n
    exact sub_eq_zero.mpr (hv n n.2)
  · intro hv n hn
    have := congrFun hv ⟨n, hn⟩
    simpa [fixSubDefect, sub_eq_zero] using this

private noncomputable def fixSubDefectExtendScalars (ρ : Representation F G V)
    (N : Subgroup G) : (F' ⊗[F] V) →ₗ[F'] (N → F' ⊗[F] V) :=
  LinearMap.pi fun n => extendScalars F' ρ n - LinearMap.id

private theorem fixSub_extendScalars_eq_ker (ρ : Representation F G V) (N : Subgroup G) :
    fixSub (extendScalars F' ρ) N = LinearMap.ker (fixSubDefectExtendScalars F' ρ N) := by
  ext v
  rw [mem_fixSub, LinearMap.mem_ker]
  constructor
  · intro hv
    ext n
    exact sub_eq_zero.mpr (hv n n.2)
  · intro hv n hn
    have := congrFun hv ⟨n, hn⟩
    simpa [fixSubDefectExtendScalars, sub_eq_zero] using this

private theorem fixSubDefectExtendScalars_eq (ρ : Representation F G V) (N : Subgroup G)
    [Fintype N] [DecidableEq N] :
    fixSubDefectExtendScalars F' ρ N =
      (TensorProduct.piRight F F' F' (fun _ : N => V)).toLinearMap ∘ₗ
        (fixSubDefect ρ N).baseChange F' := by
  apply LinearMap.ext
  intro x
  funext n
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp [fixSubDefectExtendScalars, fixSubDefect, TensorProduct.tmul_sub]
  | add x y hx hy => simp [map_add, hx, hy]

theorem fixSub_extendScalars_eq_range (ρ : Representation F G V) (N : Subgroup G) [Finite N] :
    fixSub (extendScalars F' ρ) N =
      LinearMap.range ((fixSub ρ N).subtype.baseChange F') := by
  classical
  let _ : Fintype N := Fintype.ofFinite N
  have hker : LinearMap.ker (fixSubDefectExtendScalars F' ρ N) =
      LinearMap.ker ((fixSubDefect ρ N).baseChange F') := by
    rw [fixSubDefectExtendScalars_eq F' ρ N]
    exact (TensorProduct.piRight F F' F' (fun _ : N => V)).ker_comp _
  calc
    fixSub (extendScalars F' ρ) N =
        LinearMap.ker (fixSubDefectExtendScalars F' ρ N) :=
      fixSub_extendScalars_eq_ker F' ρ N
    _ = LinearMap.ker ((fixSubDefect ρ N).baseChange F') := hker
    _ = (LinearMap.ker (fixSubDefect ρ N)).baseChange F' :=
      LinearMap.ker_baseChange_of_flat F' _
    _ = (fixSub ρ N).baseChange F' := by rw [fixSub_eq_ker_fixSubDefect]
    _ = LinearMap.range ((fixSub ρ N).subtype.baseChange F') := rfl

noncomputable def fixSubBaseChangeEquiv (ρ : Representation F G V) (N : Subgroup G)
    [Finite N] : F' ⊗[F] fixSub ρ N ≃ₗ[F'] fixSub (extendScalars F' ρ) N :=
  (Submodule.toBaseChange.toLinearEquiv F' (fixSub ρ N)).trans
    (LinearEquiv.ofEq _ _ (fixSub_extendScalars_eq_range F' ρ N).symm)

theorem coe_fixSubBaseChangeEquiv_tmul (ρ : Representation F G V) (N : Subgroup G)
    [Finite N] (a : F') (v : fixSub ρ N) :
    (fixSubBaseChangeEquiv F' ρ N (a ⊗ₜ v) : F' ⊗[F] V) = a ⊗ₜ (v : V) := by
  change ((Submodule.toBaseChange F' (fixSub ρ N)) (a ⊗ₜ v) : F' ⊗[F] V) = a ⊗ₜ (v : V)
  exact Submodule.coe_toBaseChange_tmul F' (fixSub ρ N) a v

private theorem inv_conj_mem_of_conj_mem (N : Subgroup G) [Finite N] (ι : M →* G) {m : M}
    (hι : ∀ m : M, ∀ n ∈ N, ι m * n * (ι m)⁻¹ ∈ N) {n : G} (hn : n ∈ N) :
    (ι m)⁻¹ * n * ι m ∈ N := by
  let c : N → N := fun x => ⟨ι m * (x : G) * (ι m)⁻¹, hι m x x.2⟩
  have hc : Function.Injective c := by
    intro x y hxy
    apply Subtype.ext
    have h := congrArg (fun z : G => (ι m)⁻¹ * z * ι m) (congrArg Subtype.val hxy)
    simpa [c, mul_assoc] using h
  obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.mp hc (⟨n, hn⟩ : N)
  have hxval : ι m * (x : G) * (ι m)⁻¹ = n := congrArg Subtype.val hx
  have hx' : (ι m)⁻¹ * n * ι m = (x : G) := by
    rw [← hxval]
    group
  rw [hx']
  exact x.2

theorem fixSub_stable_of_normalizes (ρ : Representation F G V)
    (N : Subgroup G) [Finite N] (ι : M →* G)
    (hι : ∀ m : M, ∀ n ∈ N, ι m * n * (ι m)⁻¹ ∈ N) (m : M) :
    ∀ v ∈ fixSub ρ N, (ρ.comp ι) m v ∈ fixSub ρ N := by
  intro v hv
  change ρ (ι m) v ∈ fixSub ρ N
  exact act_mem_fixSub ρ (fun n hn => inv_conj_mem_of_conj_mem N ι hι hn) hv

@[expose] noncomputable def sectionRep (ρ : Representation F G V) (N : Subgroup G) [Finite N]
    (ι : M →* G) (hι : ∀ m : M, ∀ n ∈ N, ι m * n * (ι m)⁻¹ ∈ N) :
    Representation F M (fixSub ρ N) :=
  restrictRep (ρ.comp ι) (fixSub ρ N)
    (fun m v hv => fixSub_stable_of_normalizes ρ N ι hι m v hv)

@[simp]
theorem sectionRep_apply (ρ : Representation F G V) (N : Subgroup G) [Finite N]
    (ι : M →* G) (hι : ∀ m : M, ∀ n ∈ N, ι m * n * (ι m)⁻¹ ∈ N) (m : M)
    (x : fixSub ρ N) :
    ((sectionRep ρ N ι hι m x : fixSub ρ N) : V) = ρ (ι m) x := rfl

theorem sectionRep_extendScalars (ρ : Representation F G V) (N : Subgroup G) [Finite N]
    (ι : M →* G) (hι : ∀ m : M, ∀ n ∈ N, ι m * n * (ι m)⁻¹ ∈ N) :
    ∀ (m : M) (x : F' ⊗[F] fixSub ρ N),
      fixSubBaseChangeEquiv F' ρ N (extendScalars F' (sectionRep ρ N ι hι) m x) =
        sectionRep (extendScalars F' ρ) N ι hι m (fixSubBaseChangeEquiv F' ρ N x) := by
  intro m x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
      apply Subtype.ext
      simp [extendScalars_apply, sectionRep_apply, coe_fixSubBaseChangeEquiv_tmul]
  | add x y hx hy =>
      simp only [map_add]
      rw [hx, hy]

noncomputable def sectionRepExtendScalarsEquiv (ρ : Representation F G V) (N : Subgroup G)
    [Finite N] (ι : M →* G)
    (hι : ∀ m : M, ∀ n ∈ N, ι m * n * (ι m)⁻¹ ∈ N) :
    RepEquiv (extendScalars F' (sectionRep ρ N ι hι))
      (sectionRep (extendScalars F' ρ) N ι hι) :=
  RepEquiv.mk (fixSubBaseChangeEquiv F' ρ N) (by
    intro m
    apply LinearMap.ext
    intro x
    exact sectionRep_extendScalars F' ρ N ι hι m x)

theorem isSimpleRep_sectionRep_of_extendScalars (ρ : Representation F G V) (N : Subgroup G)
    [Finite N] (ι : M →* G)
    (hι : ∀ m : M, ∀ n ∈ N, ι m * n * (ι m)⁻¹ ∈ N)
    (h : @IsSimpleRep F' M (fixSub (extendScalars F' ρ) N)
      inferInstance inferInstance inferInstance inferInstance
      (sectionRep (extendScalars F' ρ) N ι hι)) :
    @IsSimpleRep F M (fixSub ρ N)
      inferInstance inferInstance inferInstance inferInstance
      (sectionRep ρ N ι hι) := by
  classical
  let e := fixSubBaseChangeEquiv F' ρ N
  let eL : F' ⊗[F] fixSub ρ N →ₗ[F'] fixSub (extendScalars F' ρ) N :=
    e.toLinearMap
  have hnt : Nontrivial (fixSub ρ N) := by
    have hnt' : Nontrivial (fixSub (extendScalars F' ρ) N) := h.1
    have hntT : Nontrivial (F' ⊗[F] fixSub ρ N) :=
      e.nontrivial_congr.mpr hnt' 
    exact (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right (R := F) (M := F')).mp
      hntT
  refine ⟨hnt, ?_⟩
  intro W hW
  let Wb : Submodule F' (F' ⊗[F] fixSub ρ N) := W.baseChange F'
  have hWb_inv : ∀ m : M, ∀ y ∈ Wb,
      (sectionRep ρ N ι hι m).baseChange F' y ∈ Wb := by
    intro m y hy
    change y ∈ W.baseChange F' at hy
    change (sectionRep ρ N ι hι m).baseChange F' y ∈ W.baseChange F'
    rw [Submodule.baseChange_eq_span] at hy ⊢
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨w, hw, rfl⟩ := hy
        rw [TensorProduct.mk_apply, LinearMap.baseChange_tmul]
        exact Submodule.subset_span ⟨sectionRep ρ N ι hι m w, hW m w hw, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ ihy ihz => rw [map_add]; exact Submodule.add_mem _ ihy ihz
    | smul a y _ ihy => rw [map_smul]; exact Submodule.smul_mem _ a ihy
  let W' : Submodule F' (fixSub (extendScalars F' ρ) N) :=
    Wb.map eL
  have hW'_inv : ∀ m : M, ∀ y ∈ W',
      sectionRep (extendScalars F' ρ) N ι hι m y ∈ W' := by
    intro m y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    change sectionRep (extendScalars F' ρ) N ι hι m
      (fixSubBaseChangeEquiv F' ρ N x) ∈ W'
    rw [← sectionRep_extendScalars F' ρ N ι hι m x]
    exact Submodule.mem_map_of_mem (f := eL) (hWb_inv m x hx)
  rcases h.2 W' hW'_inv with hbot | htop
  · left
    have hWb_bot : Wb = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro y hy
      have hy' : eL y ∈ Wb.map eL :=
        Submodule.mem_map_of_mem (f := eL) hy
      rw [show Wb.map eL = ⊥ from hbot] at hy'
      have hy0 : e y = 0 := by simpa [eL] using hy'
      exact e.injective (by simpa using hy0)
    have hsub : Subsingleton (F' ⊗[F] W) := by
      rw [(Submodule.toBaseChange.toLinearEquiv F' W).toEquiv.subsingleton_congr]
      rw [show W.baseChange F' = Wb from rfl, hWb_bot]
      infer_instance
    have hsubW : Subsingleton W :=
      (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right (R := F) (M := F')).mp
        hsub
    exact Submodule.subsingleton_iff_eq_bot.mp hsubW
  · right
    have hWb_top : Wb = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy' : eL y ∈ Wb.map eL := by
        rw [show Wb.map eL = W' from rfl, htop]
        exact Submodule.mem_top
      obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy'
      have hxy' : x = y := e.injective (by simpa [eL] using hxy)
      rw [hxy'] at hx
      exact hx
    rw [eq_top_iff]
    intro x _
    have hmem : (1 : F') ⊗ₜ[F] x ∈ W.baseChange F' := by
      rw [show W.baseChange F' = Wb from rfl, hWb_top]
      exact Submodule.mem_top
    exact (Submodule.one_tmul_mem_baseChange_iff (A := F') (p := W) (m := x)).mp hmem

theorem sectionRep_eq_one_iff (ρ : Representation F G V) (N : Subgroup G) [Finite N]
    (ι : M →* G) (hι : ∀ m : M, ∀ n ∈ N, ι m * n * (ι m)⁻¹ ∈ N) (m : M) :
    sectionRep (extendScalars F' ρ) N ι hι m = 1 ↔
      sectionRep ρ N ι hι m = 1 := by
  classical
  let e := fixSubBaseChangeEquiv F' ρ N
  constructor
  · intro h
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have heq : e (extendScalars F' (sectionRep ρ N ι hι) m ((1 : F') ⊗ₜ[F] v)) =
        e ((1 : F') ⊗ₜ[F] v) := by
      rw [sectionRep_extendScalars F' ρ N ι hι m ((1 : F') ⊗ₜ[F] v)]
      exact congrArg (fun f : fixSub (extendScalars F' ρ) N →ₗ[F']
          fixSub (extendScalars F' ρ) N => f (e ((1 : F') ⊗ₜ[F] v))) h
    have h2 : (1 : F') ⊗ₜ[F] sectionRep ρ N ι hι m v = (1 : F') ⊗ₜ[F] v := by
      apply e.injective
      simpa [extendScalars_apply] using heq
    have h3 : (1 : F') ⊗ₜ[F] (sectionRep ρ N ι hι m v - v) = 0 := by
      rw [TensorProduct.tmul_sub, h2, sub_self]
    have hsub : sectionRep ρ N ι hι m v - v = 0 :=
      (Module.FaithfullyFlat.one_tmul_eq_zero_iff F (fixSub ρ N)
        (sectionRep ρ N ι hι m v - v)).mp h3
    exact congrArg Subtype.val (sub_eq_zero.mp hsub)
  · intro h
    ext y
    obtain ⟨z, rfl⟩ := e.surjective y
    have hz : extendScalars F' (sectionRep ρ N ι hι) m z = z := by
      rw [extendScalars_apply, h, LinearMap.baseChange_one]
      rfl
    rw [← sectionRep_extendScalars F' ρ N ι hι m z, hz]
    rfl

theorem fixSub_mapsTo (ρ : Representation F G V) (N : Subgroup G)
    (T : V →ₗ[F] V) (α : MulAut G)
    (hT : ∀ g v, T (ρ g v) = ρ (α g) (T v))
    (hN : N.map α.toMonoidHom = N) :
    ∀ v ∈ fixSub ρ N, T v ∈ fixSub ρ N := by
  intro v hv n hn
  have hpre : α.symm n ∈ N := by
    have hn' : n ∈ N.map (α : G ≃* G).toMonoidHom := by rw [hN]; exact hn
    exact (Subgroup.mem_map_equiv (f := α)).mp hn'
  have h := hT (α.symm n) v
  rw [hv _ hpre, MulEquiv.apply_symm_apply] at h
  exact h.symm

@[expose] noncomputable def fixSubMap (ρ : Representation F G V) (N : Subgroup G)
    (T : V →ₗ[F] V) (α : MulAut G)
    (hT : ∀ g v, T (ρ g v) = ρ (α g) (T v))
    (hN : N.map α.toMonoidHom = N) :
    fixSub ρ N →ₗ[F] fixSub ρ N :=
  T.restrict (fixSub_mapsTo ρ N T α hT hN)

@[simp]
theorem fixSubMap_apply (ρ : Representation F G V) (N : Subgroup G)
    (T : V →ₗ[F] V) (α : MulAut G)
    (hT : ∀ g v, T (ρ g v) = ρ (α g) (T v))
    (hN : N.map α.toMonoidHom = N) (x : fixSub ρ N) :
    ((fixSubMap ρ N T α hT hN x : fixSub ρ N) : V) = T x := rfl

theorem baseChange_intertwines (ρ : Representation F G V) (T : V →ₗ[F] V)
    (α : MulAut G) (hT : ∀ g v, T (ρ g v) = ρ (α g) (T v)) :
    ∀ g v, T.baseChange F' (extendScalars F' ρ g v) =
      extendScalars F' ρ (α g) (T.baseChange F' v) := by
  intro g v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a w => simp [extendScalars_apply, hT]
  | add x y hx hy =>
      simp only [map_add]
      rw [hx, hy]

@[expose] noncomputable def fixSubBaseChangeMap (ρ : Representation F G V) (N : Subgroup G)
    (T : V →ₗ[F] V) (α : MulAut G)
    (hT : ∀ g v, T (ρ g v) = ρ (α g) (T v))
    (hN : N.map α.toMonoidHom = N) :
    fixSub (extendScalars F' ρ) N →ₗ[F'] fixSub (extendScalars F' ρ) N :=
  fixSubMap (extendScalars F' ρ) N (T.baseChange F') α
    (baseChange_intertwines F' ρ T α hT) hN

@[simp]
theorem fixSubBaseChangeMap_apply (ρ : Representation F G V) (N : Subgroup G)
    (T : V →ₗ[F] V) (α : MulAut G)
    (hT : ∀ g v, T (ρ g v) = ρ (α g) (T v))
    (hN : N.map α.toMonoidHom = N)
    (x : fixSub (extendScalars F' ρ) N) :
    ((fixSubBaseChangeMap F' ρ N T α hT hN x :
      fixSub (extendScalars F' ρ) N) : F' ⊗[F] V) = T.baseChange F' x := rfl

theorem symm_intertwines (ρ : Representation F G V) (T : V ≃ₗ[F] V) (α : MulAut G)
    (hT : ∀ g v, T (ρ g v) = ρ (α g) (T v)) :
    ∀ g v, T.symm (ρ g v) = ρ (α.symm g) (T.symm v) := by
  intro g v
  apply T.injective
  simp [hT, MulEquiv.apply_symm_apply]

theorem map_symm_eq (N : Subgroup G) (α : MulAut G)
    (hN : N.map α.toMonoidHom = N) : N.map α.symm.toMonoidHom = N :=
  (Subgroup.map_symm_eq_iff_map_eq N).mpr hN

@[expose] noncomputable def fixSubEquiv (ρ : Representation F G V) (N : Subgroup G)
    (T : V ≃ₗ[F] V) (α : MulAut G)
    (hT : ∀ g v, T (ρ g v) = ρ (α g) (T v))
    (hN : N.map α.toMonoidHom = N) :
    fixSub ρ N ≃ₗ[F] fixSub ρ N :=
  LinearEquiv.ofLinearMap
    (fixSubMap ρ N T.toLinearMap α hT hN)
    (fixSubMap ρ N T.symm.toLinearMap α.symm (symm_intertwines ρ T α hT)
      (map_symm_eq N α hN))
    (by ext x; simp [fixSubMap_apply])
    (by ext x; simp [fixSubMap_apply])

@[simp]
theorem fixSubEquiv_apply (ρ : Representation F G V) (N : Subgroup G)
    (T : V ≃ₗ[F] V) (α : MulAut G)
    (hT : ∀ g v, T (ρ g v) = ρ (α g) (T v))
    (hN : N.map α.toMonoidHom = N) (x : fixSub ρ N) :
    ((fixSubEquiv ρ N T α hT hN x : fixSub ρ N) : V) = T x := rfl

@[simp]
theorem fixSubEquiv_symm_apply (ρ : Representation F G V) (N : Subgroup G)
    (T : V ≃ₗ[F] V) (α : MulAut G)
    (hT : ∀ g v, T (ρ g v) = ρ (α g) (T v))
    (hN : N.map α.toMonoidHom = N) (x : fixSub ρ N) :
    (((fixSubEquiv ρ N T α hT hN).symm x : fixSub ρ N) : V) = T.symm x := rfl

@[expose] noncomputable def fixSubBaseChangeLinearEquiv (ρ : Representation F G V) (N : Subgroup G)
    (T : V ≃ₗ[F] V) (α : MulAut G)
    (hT : ∀ g v, T (ρ g v) = ρ (α g) (T v))
    (hN : N.map α.toMonoidHom = N) :
    fixSub (extendScalars F' ρ) N ≃ₗ[F'] fixSub (extendScalars F' ρ) N :=
  fixSubEquiv (extendScalars F' ρ) N (T.baseChange F F' V V) α
    (baseChange_intertwines F' ρ T.toLinearMap α hT) hN

@[simp]
theorem fixSubBaseChangeLinearEquiv_apply (ρ : Representation F G V) (N : Subgroup G)
    (T : V ≃ₗ[F] V) (α : MulAut G)
    (hT : ∀ g v, T (ρ g v) = ρ (α g) (T v))
    (hN : N.map α.toMonoidHom = N)
    (x : fixSub (extendScalars F' ρ) N) :
    ((fixSubBaseChangeLinearEquiv F' ρ N T α hT hN x :
      fixSub (extendScalars F' ρ) N) : F' ⊗[F] V) =
        (T.baseChange F F' V V) x := rfl

theorem finrank_fixSub_extendScalars (ρ : Representation F G V) (N : Subgroup G)
    [Finite N] :
    finrank F' (fixSub (extendScalars F' ρ) N) = finrank F (fixSub ρ N) := by
  calc
    finrank F' (fixSub (extendScalars F' ρ) N) =
        finrank F' (F' ⊗[F] fixSub ρ N) :=
      (fixSubBaseChangeEquiv F' ρ N).finrank_eq.symm
    _ = finrank F (fixSub ρ N) := Module.finrank_baseChange

theorem card_fixSub_eq_card_pow_finrank [Finite F] [FiniteDimensional F V]
    (ρ : Representation F G V) (N : Subgroup G) [Finite N] :
    Nat.card (fixSub ρ N) =
      Nat.card F ^ finrank F' (fixSub (extendScalars F' ρ) N) := by
  rw [Module.natCard_eq_pow_finrank (K := F) (V := fixSub ρ N),
    ← finrank_fixSub_extendScalars F' ρ N]

end CFSG.Theory.Representation

end
