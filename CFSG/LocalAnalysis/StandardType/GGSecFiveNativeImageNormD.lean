module

public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGSignedCoordRefl
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEven
import CFSG.LocalAnalysis.StandardType.GGTorusDWeyl
import CFSG.LocalAnalysis.StandardType.GGTBJTypeBFrameChange
import CFSG.LocalAnalysis.StandardType.GGSignedPermCount
import CFSG.LocalAnalysis.StandardType.GGTBWNormOrth

public section

namespace CFSG.StandardType

open SpCoord Multiplicative

private abbrev V4 (p : ℕ) := Fin 4 → Multiplicative (ZMod p)

private abbrev CIdx (i0 : Fin 4) := {k : Fin 4 // k ≠ i0}

private abbrev VC (p : ℕ) (i0 : Fin 4) := CIdx i0 → Multiplicative (ZMod p)

private def onAxis {p : ℕ} (i0 : Fin 4) (f : V4 p) : Prop := ∀ k, k ≠ i0 → f k = 1

private theorem onAxis_iff_fixed {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i0 : Fin 4)
    (f : V4 p) :
    (∀ w ∈ dCoordinateBlock 4 p i0, w f = f) ↔ onAxis i0 f :=
  forall_dCoordinateBlock_fix_iff hp hp2 (by norm_num : 3 ≤ 4) i0 f

private theorem inv_normalizes_dCoordinateBlock {p : ℕ} (hp : p.Prime) (i0 : Fin 4)
    {u : MulAut (V4 p)}
    (hu : ∀ w ∈ dCoordinateBlock 4 p i0, u * w * u⁻¹ ∈ dCoordinateBlock 4 p i0) :
    ∀ w ∈ dCoordinateBlock 4 p i0, u⁻¹ * w * u ∈ dCoordinateBlock 4 p i0 := by
  classical
  intro w hw
  let W := dCoordinateBlock 4 p i0
  let F : ↥W → ↥W := fun x => ⟨u * x.1 * u⁻¹, hu x.1 x.2⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite (V4 p) := inferInstance
  haveI : Finite (MulAut (V4 p)) := MulEquiv.finite_left
  have hFin : Finite ↥W := Subtype.finite
  have hinj : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    have h := congrArg Subtype.val hxy
    exact mul_left_cancel (mul_right_cancel h)
  obtain ⟨x, hx⟩ := (Function.Injective.bijective_of_finite hinj).2 ⟨w, hw⟩
  have hxval : x.1 = u⁻¹ * w * u := by
    have h : u * x.1 * u⁻¹ = w := by
      have := congrArg Subtype.val hx
      simpa [F] using this
    calc x.1 = u⁻¹ * (u * x.1 * u⁻¹) * u := by group
      _ = u⁻¹ * w * u := by rw [h]
  rw [← hxval]
  exact x.2

private theorem onAxis_map_of_normalizes {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i0 : Fin 4)
    {v : MulAut (V4 p)}
    (hv : ∀ w ∈ dCoordinateBlock 4 p i0, v * w * v⁻¹ ∈ dCoordinateBlock 4 p i0)
    (hv' : ∀ w ∈ dCoordinateBlock 4 p i0, v⁻¹ * w * v ∈ dCoordinateBlock 4 p i0)
    {f : V4 p} (hf : onAxis i0 f) : onAxis i0 (v f) := by
  intro k hk
  have hfix : ∀ w ∈ dCoordinateBlock 4 p i0, w (v f) = v f := by
    intro w hw
    have hw' := hv' w hw
    calc w (v f) = v ((v⁻¹ * w * v) f) := by simp [MulAut.mul_apply]
      _ = v f := by
        rw [(onAxis_iff_fixed hp hp2 i0 f).mpr hf (v⁻¹ * w * v) hw']
  exact ((onAxis_iff_fixed hp hp2 i0 (v f)).mp hfix) k hk

private def extFun {p : ℕ} (i0 : Fin 4) (f : VC p i0) : V4 p :=
  fun k => if h : k = i0 then 1 else f ⟨k, h⟩

private def resFun {p : ℕ} (i0 : Fin 4) (F : V4 p) : VC p i0 :=
  fun k => F k.1

@[simp] private theorem resFun_extFun {p : ℕ} (i0 : Fin 4) (f : VC p i0) :
    resFun i0 (extFun i0 f) = f := by
  funext k
  simp only [resFun, extFun, dif_neg k.2]

private theorem extFun_mul {p : ℕ} (i0 : Fin 4) (f g : VC p i0) :
    extFun i0 (f * g) = extFun i0 f * extFun i0 g := by
  funext k
  by_cases h : k = i0
  · subst h
    simp [extFun]
  · simp [extFun, h]

private theorem exists_onAxis_mul_extFun_resFun {p : ℕ} (i0 : Fin 4) (F : V4 p) :
    ∃ l : V4 p, onAxis i0 l ∧ F = l * extFun i0 (resFun i0 F) := by
  refine ⟨fun k => if k = i0 then F k else 1, ?_, ?_⟩
  · intro k hk
    simp [hk]
  · funext k
    by_cases hk : k = i0
    · subst hk
      simp [extFun]
    · simp [extFun, resFun, hk]

private theorem resFun_eq_of_mul_onAxis {p : ℕ} (i0 : Fin 4) {l F : V4 p}
    (hl : onAxis i0 l) : resFun i0 (l * F) = resFun i0 F := by
  funext k
  simp only [resFun, Pi.mul_apply, hl k.1 k.2, one_mul]

private noncomputable def transportAut {p : ℕ} (i0 : Fin 4) (u : MulAut (V4 p))
    (hu : ∀ f, onAxis i0 f → onAxis i0 (u f))
    (hu' : ∀ f, onAxis i0 f → onAxis i0 (u⁻¹ f)) : MulAut (VC p i0) where
  toFun f := resFun i0 (u (extFun i0 f))
  invFun f := resFun i0 (u⁻¹ (extFun i0 f))
  left_inv f := by
    obtain ⟨l, hl, hF⟩ := exists_onAxis_mul_extFun_resFun i0 (u (extFun i0 f))
    have h1 : extFun i0 f =
        u⁻¹ l * u⁻¹ (extFun i0 (resFun i0 (u (extFun i0 f)))) := by
      calc extFun i0 f = u⁻¹ (u (extFun i0 f)) :=
            (MulAut.inv_apply_self (M := V4 p) u (extFun i0 f)).symm
        _ = u⁻¹ (l * extFun i0 (resFun i0 (u (extFun i0 f)))) :=
              congrArg (fun x : V4 p => (u⁻¹ : MulAut (V4 p)) x) hF
        _ = u⁻¹ l * u⁻¹ (extFun i0 (resFun i0 (u (extFun i0 f)))) := by rw [map_mul]
    have h2 := congrArg (resFun i0) h1
    rw [resFun_eq_of_mul_onAxis i0 (hu' l hl), resFun_extFun] at h2
    exact h2.symm
  right_inv f := by
    obtain ⟨l, hl, hF⟩ := exists_onAxis_mul_extFun_resFun i0 (u⁻¹ (extFun i0 f))
    have h1 : extFun i0 f =
        u l * u (extFun i0 (resFun i0 (u⁻¹ (extFun i0 f)))) := by
      calc extFun i0 f = u (u⁻¹ (extFun i0 f)) :=
            (MulAut.apply_inv_self (M := V4 p) u (extFun i0 f)).symm
        _ = u (l * extFun i0 (resFun i0 (u⁻¹ (extFun i0 f)))) :=
              congrArg (fun x : V4 p => (u : MulAut (V4 p)) x) hF
        _ = u l * u (extFun i0 (resFun i0 (u⁻¹ (extFun i0 f)))) := by rw [map_mul]
    have h2 := congrArg (resFun i0) h1
    rw [resFun_eq_of_mul_onAxis i0 (hu l hl), resFun_extFun] at h2
    exact h2.symm
  map_mul' f g := by
    change resFun i0 (u (extFun i0 (f * g))) =
      resFun i0 (u (extFun i0 f)) * resFun i0 (u (extFun i0 g))
    rw [extFun_mul, map_mul]
    rfl

private noncomputable def restrictHom {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i0 : Fin 4) :
    ↥(dCoordinateBlock 4 p i0) →* MulAut (VC p i0) where
  toFun w := transportAut i0 w.1
    (fun f hf => by
      rw [(onAxis_iff_fixed hp hp2 i0 f).mpr hf w.1 w.2]
      exact hf)
    (fun f hf => by
      rw [(onAxis_iff_fixed hp hp2 i0 f).mpr hf w.1⁻¹ (Subgroup.inv_mem _ w.2)]
      exact hf)
  map_one' := by
    refine MulEquiv.ext fun f => ?_
    change resFun i0 ((1 : MulAut (V4 p)) (extFun i0 f)) = (1 : MulAut (VC p i0)) f
    simp
  map_mul' w v := by
    refine MulEquiv.ext fun f => ?_
    change resFun i0 ((w.1 * v.1) (extFun i0 f)) =
      resFun i0 (w.1 (extFun i0 (resFun i0 (v.1 (extFun i0 f)))))
    obtain ⟨l, hl, hF⟩ := exists_onAxis_mul_extFun_resFun i0 (v.1 (extFun i0 f))
    have hwl : w.1 l = l := (onAxis_iff_fixed hp hp2 i0 l).mpr hl w.1 w.2
    calc resFun i0 ((w.1 * v.1) (extFun i0 f))
        = resFun i0 (w.1 (v.1 (extFun i0 f))) := by rw [MulAut.mul_apply]
      _ = resFun i0 (w.1 (l * extFun i0 (resFun i0 (v.1 (extFun i0 f))))) :=
            congrArg (fun x : V4 p => resFun i0 (w.1 x)) hF
      _ = resFun i0 (w.1 l * w.1 (extFun i0 (resFun i0 (v.1 (extFun i0 f))))) := by rw [map_mul]
      _ = resFun i0 (l * w.1 (extFun i0 (resFun i0 (v.1 (extFun i0 f))))) := by rw [hwl]
      _ = resFun i0 (w.1 (extFun i0 (resFun i0 (v.1 (extFun i0 f))))) :=
            resFun_eq_of_mul_onAxis i0 hl

@[simp] private theorem restrictHom_apply {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i0 : Fin 4)
    (w : ↥(dCoordinateBlock 4 p i0)) (f : VC p i0) :
    (restrictHom hp hp2 i0 w) f = resFun i0 (w.1 (extFun i0 f)) :=
  rfl

private noncomputable def coordEquiv (i0 : Fin 4) : Fin 3 ≃ CIdx i0 := by
  classical
  have hcard : Fintype.card (CIdx i0) = 3 := by
    change Fintype.card {x : Fin 4 | x ≠ i0} = 3
    rw [Set.card_ne_eq]
    norm_num
  exact (Fintype.equivFinOfCardEq hcard).symm

private noncomputable def coordMulEquiv (p : ℕ) (i0 : Fin 4) :
    VC p i0 ≃* (Fin 3 → Multiplicative (ZMod p)) where
  toFun f := f ∘ coordEquiv i0
  invFun g := g ∘ (coordEquiv i0).symm
  left_inv f := by funext c; simp
  right_inv g := by funext i; simp
  map_mul' f g := rfl

private noncomputable def sgnAutC {p : ℕ} (i0 : Fin 4) (a : CIdx i0) :
    MulAut (VC p i0) where
  toFun f := Function.update f a (f a)⁻¹
  invFun f := Function.update f a (f a)⁻¹
  left_inv f := by
    funext c
    by_cases hc : c = a
    · subst hc; simp
    · simp [Function.update_of_ne hc]
  right_inv f := by
    funext c
    by_cases hc : c = a
    · subst hc; simp
    · simp [Function.update_of_ne hc]
  map_mul' f g := by
    funext c
    by_cases hc : c = a
    · subst hc; simp [mul_comm]
    · simp [Function.update_of_ne hc]

private noncomputable def permAutC {p : ℕ} (i0 : Fin 4) (σ : Equiv.Perm (CIdx i0)) :
    MulAut (VC p i0) where
  toFun f := f ∘ ⇑σ⁻¹
  invFun f := f ∘ ⇑σ
  left_inv f := by funext c; simp
  right_inv f := by funext c; simp
  map_mul' f g := rfl

@[simp] private theorem sgnAutC_apply {p : ℕ} (i0 : Fin 4) (a : CIdx i0) (f : VC p i0) :
    sgnAutC i0 a f = Function.update f a (f a)⁻¹ :=
  rfl

@[simp] private theorem permAutC_apply {p : ℕ} (i0 : Fin 4) (σ : Equiv.Perm (CIdx i0))
    (f : VC p i0) : permAutC i0 σ f = f ∘ ⇑σ⁻¹ :=
  rfl

private theorem resFun_sgnAut {p : ℕ} (i0 : Fin 4) {a : CIdx i0} (f : V4 p) :
    resFun i0 (sgnAut a.1 f) = sgnAutC i0 a (resFun i0 f) := by
  funext c
  by_cases hca : c = a
  · subst hca
    simp [resFun, sgnAutC_apply, sgnAut_apply, Function.update_self]
  · have hca' : c.1 ≠ a.1 := fun h => hca (Subtype.ext h)
    simp [resFun, sgnAutC_apply, sgnAut_apply, Function.update_of_ne hca', hca]

private theorem coe_swap_subtype {i0 : Fin 4} {a b c : CIdx i0} :
    ((Equiv.swap a b c : CIdx i0) : Fin 4) = Equiv.swap a.1 b.1 c.1 := by
  by_cases hca : c = a
  · subst hca
    simp [Equiv.swap_apply_left]
  · by_cases hcb : c = b
    · subst hcb
      simp [Equiv.swap_apply_right, hca]
    · have h1 : c.1 ≠ a.1 := fun h => hca (Subtype.ext h)
      have h2 : c.1 ≠ b.1 := fun h => hcb (Subtype.ext h)
      simp [Equiv.swap_apply_of_ne_of_ne hca hcb,
        Equiv.swap_apply_of_ne_of_ne h1 h2]

private theorem resFun_permAut_swap {p : ℕ} (i0 : Fin 4) {a b : CIdx i0} (f : V4 p) :
    resFun i0 (permAut (Equiv.swap a.1 b.1) f) =
      permAutC i0 (Equiv.swap a b) (resFun i0 f) := by
  funext c
  simp only [resFun, permAutC_apply, permAut_apply, Function.comp_apply, Equiv.swap_inv]
  rw [coe_swap_subtype]

private theorem restrictHom_permAut_swap {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i0 : Fin 4)
    {a b : CIdx i0} (hab : a ≠ b) :
    restrictHom hp hp2 i0 ⟨permAut (Equiv.swap a.1 b.1),
        Subgroup.subset_closure (Or.inl ⟨a.1, b.1, fun h => hab (Subtype.ext h), a.2, b.2, rfl⟩)⟩ =
      permAutC i0 (Equiv.swap a b) := by
  refine MulEquiv.ext fun f => ?_
  rw [restrictHom_apply, resFun_permAut_swap, resFun_extFun]

private theorem permAut_swap_mul_negTrans {p : ℕ} {a b : Fin 4} (hab : a ≠ b) :
    (permAut (Equiv.swap a b) : MulAut (V4 p)) *
        (sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹) = sgnAut a * sgnAut b := by
  refine MulEquiv.ext fun f => funext fun i => ?_
  rw [MulAut.mul_apply, permAut_apply, Function.comp_apply, Equiv.swap_inv,
    negTrans_apply (p := p) a b hab f (Equiv.swap a b i)]
  by_cases hia : i = a
  · subst hia
    simp_all [MulAut.mul_apply, sgnAut_apply, Function.update_self]
  · by_cases hib : i = b
    · subst hib
      simp_all [MulAut.mul_apply, sgnAut_apply, Function.update_self]
    · have hsw_a : Equiv.swap a b i ≠ a := by
        intro h
        exact hib (by
          calc i = Equiv.swap a b (Equiv.swap a b i) := (Equiv.swap_apply_self a b i).symm
            _ = Equiv.swap a b a := by rw [h]
            _ = b := Equiv.swap_apply_left a b)
      have hsw_b : Equiv.swap a b i ≠ b := by
        intro h
        exact hia (by
          calc i = Equiv.swap a b (Equiv.swap a b i) := (Equiv.swap_apply_self a b i).symm
            _ = Equiv.swap a b b := by rw [h]
            _ = a := Equiv.swap_apply_right a b)
      simp [hsw_a, hsw_b, hia, hib, Equiv.swap_apply_of_ne_of_ne hia hib, MulAut.mul_apply,
        sgnAut_apply, Function.update_of_ne hia, Function.update_of_ne hib]

private theorem sgnAut_mul_mem_dCoordinateBlock {p : ℕ} (i0 : Fin 4) {a b : Fin 4}
    (hab : a ≠ b) (ha : a ≠ i0) (hb : b ≠ i0) :
    (sgnAut a * sgnAut b : MulAut (V4 p)) ∈ dCoordinateBlock 4 p i0 := by
  let W := dCoordinateBlock 4 p i0
  have ht : (permAut (p := p) (Equiv.swap a b) : MulAut (V4 p)) ∈ W :=
    Subgroup.subset_closure (Or.inl ⟨a, b, hab, ha, hb, rfl⟩)
  have hnt : (sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹ : MulAut (V4 p)) ∈ W :=
    Subgroup.subset_closure (Or.inr ⟨a, b, hab, ha, hb, rfl⟩)
  have h := W.mul_mem ht hnt
  rwa [permAut_swap_mul_negTrans hab] at h

private theorem restrictHom_sgnAut_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i0 : Fin 4)
    {a b : CIdx i0} (hab : a ≠ b) :
    restrictHom hp hp2 i0 ⟨sgnAut a.1 * sgnAut b.1,
        sgnAut_mul_mem_dCoordinateBlock (p := p) i0
          (fun h => hab (Subtype.ext h)) a.2 b.2⟩ =
      sgnAutC i0 a * sgnAutC i0 b := by
  refine MulEquiv.ext fun f => ?_
  rw [restrictHom_apply, MulAut.mul_apply, MulAut.mul_apply, resFun_sgnAut,
    resFun_sgnAut, resFun_extFun]

private noncomputable def D3 (p : ℕ) (hp : p.Prime) :
    Subgroup (MulAut (Fin 3 → Multiplicative (ZMod p))) :=
  letI : Fact p.Prime := ⟨hp⟩
  DScalarTorus.evenSignedGroup (p := p) (N := 3)

private noncomputable def DC {p : ℕ} (hp : p.Prime) (i0 : Fin 4) :
    Subgroup (MulAut (VC p i0)) :=
  (D3 p hp).map (MulAut.congr (coordMulEquiv p i0).symm).toMonoidHom

private theorem mulAut_congr_apply_apply {M N : Type*} [Group M] [Group N]
    (e : M ≃* N) (u : MulAut M) (x : M) :
    MulAut.congr e u (e x) = e (u x) := by
  simp [MulAut.congr_apply]

private theorem mulAut_congr_symm_congr {M N : Type*} [Group M] [Group N]
    (e : M ≃* N) (u : MulAut M) :
    MulAut.congr e.symm (MulAut.congr e u) = u := by
  refine MulEquiv.ext fun x => ?_
  simp [MulAut.congr_apply, MulEquiv.trans_apply]

private theorem mulAut_congr_congr_symm {M N : Type*} [Group M] [Group N]
    (e : M ≃* N) (u : MulAut N) :
    MulAut.congr e (MulAut.congr e.symm u) = u := by
  refine MulEquiv.ext fun x => ?_
  simp [MulAut.congr_apply, MulEquiv.trans_apply]

private theorem mem_DC_iff {p : ℕ} (hp : p.Prime) (i0 : Fin 4)
    (x : MulAut (VC p i0)) :
    x ∈ DC hp i0 ↔ MulAut.congr (coordMulEquiv p i0) x ∈ D3 p hp := by
  constructor
  · rintro ⟨d, hd, hEq⟩
    have h : MulAut.congr (coordMulEquiv p i0) x = d := by
      rw [← hEq]
      simpa only [MulEquiv.coe_toMonoidHom] using
        (mulAut_congr_congr_symm (coordMulEquiv p i0) d)
    rw [h]
    exact hd
  · intro hx
    exact ⟨MulAut.congr (coordMulEquiv p i0) x, hx,
      mulAut_congr_symm_congr _ _⟩

private theorem congr_sgnAutC {p : ℕ} (i0 : Fin 4) (a : CIdx i0) :
    MulAut.congr (coordMulEquiv p i0) (sgnAutC i0 a) =
      sgnAut (p := p) ((coordEquiv i0).symm a) := by
  refine MulEquiv.ext fun g => funext fun i => ?_
  by_cases hi : i = (coordEquiv i0).symm a
  · subst hi
    simp [MulAut.congr_apply, coordMulEquiv, sgnAutC_apply, sgnAut_apply,
      Function.update_self]
  · have hne : coordEquiv i0 i ≠ a := by
      intro h
      exact hi ((coordEquiv i0).injective (h.trans (Equiv.apply_symm_apply (coordEquiv i0) a).symm))
    simp [MulAut.congr_apply, coordMulEquiv, sgnAutC_apply, sgnAut_apply,
      Function.update_of_ne hne, Function.update_of_ne hi]

private theorem congr_permAutC {p : ℕ} (i0 : Fin 4) (σ : Equiv.Perm (CIdx i0)) :
    MulAut.congr (coordMulEquiv p i0) (permAutC i0 σ) =
      permAut (p := p) ((coordEquiv i0).trans (σ.trans (coordEquiv i0).symm)) := by
  refine MulEquiv.ext fun g => funext fun i => ?_
  simp [MulAut.congr_apply, coordMulEquiv, permAutC_apply, permAut_apply,
    Function.comp_apply, Equiv.trans_assoc]

private noncomputable def permAutCHom {p : ℕ} (i0 : Fin 4) :
    Equiv.Perm (CIdx i0) →* MulAut (VC p i0) where
  toFun := permAutC i0
  map_one' := by
    refine MulEquiv.ext fun f => funext fun c => ?_
    simp [permAutC_apply]
  map_mul' σ τ := by
    refine MulEquiv.ext fun f => funext fun c => ?_
    simp [permAutC_apply, Equiv.Perm.mul_apply]

private noncomputable def HC {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i0 : Fin 4) :
    Subgroup (MulAut (VC p i0)) :=
  (⊤ : Subgroup ↥(dCoordinateBlock 4 p i0)).map (restrictHom hp hp2 i0)

private theorem restrictHom_permAut_swap_mem_HC {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (i0 : Fin 4) {a b : CIdx i0} (hab : a ≠ b) :
    restrictHom hp hp2 i0 ⟨permAut (Equiv.swap a.1 b.1),
        Subgroup.subset_closure (Or.inl ⟨a.1, b.1, fun h => hab (Subtype.ext h), a.2, b.2, rfl⟩)⟩ ∈
      HC hp hp2 i0 :=
  Subgroup.mem_map.mpr ⟨_, Subgroup.mem_top _, rfl⟩

private theorem restrictHom_sgnAut_mul_mem_HC {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (i0 : Fin 4) {a b : CIdx i0} (hab : a ≠ b) :
    restrictHom hp hp2 i0 ⟨sgnAut a.1 * sgnAut b.1,
        sgnAut_mul_mem_dCoordinateBlock (p := p) i0
          (fun h => hab (Subtype.ext h)) a.2 b.2⟩ ∈ HC hp hp2 i0 :=
  Subgroup.mem_map.mpr ⟨_, Subgroup.mem_top _, rfl⟩

private theorem restrictHom_permAut_swap_mem_DC {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (i0 : Fin 4) {a b : CIdx i0} (hab : a ≠ b) :
    restrictHom hp hp2 i0 ⟨permAut (Equiv.swap a.1 b.1),
        Subgroup.subset_closure (Or.inl ⟨a.1, b.1, fun h => hab (Subtype.ext h), a.2, b.2, rfl⟩)⟩ ∈
      DC hp i0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [mem_DC_iff, restrictHom_permAut_swap hp hp2 i0 (a := a) (b := b) hab, congr_permAutC]
  have hmem : permAut (p := p) ((coordEquiv i0).trans
      ((Equiv.swap a b).trans (coordEquiv i0).symm)) ∈
      DScalarTorus.evenSignedGroup (p := p) (N := 3) :=
    DScalarTorus.permAut_mem_evenSignedGroup _
  simpa [D3] using hmem

private theorem restrictHom_sgnAut_mul_mem_DC {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (i0 : Fin 4) {a b : CIdx i0} (hab : a ≠ b) :
    restrictHom hp hp2 i0 ⟨sgnAut a.1 * sgnAut b.1,
        sgnAut_mul_mem_dCoordinateBlock (p := p) i0
          (fun h => hab (Subtype.ext h)) a.2 b.2⟩ ∈ DC hp i0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [mem_DC_iff, restrictHom_sgnAut_mul hp hp2 i0 (a := a) (b := b) hab, map_mul,
    congr_sgnAutC, congr_sgnAutC]
  have hne : (coordEquiv i0).symm a ≠ (coordEquiv i0).symm b := by
    intro h
    exact hab ((coordEquiv i0).symm.injective h)
  have hmem : sgnAut (p := p) ((coordEquiv i0).symm a) *
      sgnAut (p := p) ((coordEquiv i0).symm b) ∈
      DScalarTorus.evenSignedGroup (p := p) (N := 3) :=
    DScalarTorus.sgnAut_pair_mem_evenSignedGroup hne
  simpa [D3] using hmem

private theorem resFun_ext_res_eq_of_onAxis {p : ℕ} (i0 : Fin 4) {v : MulAut (V4 p)}
    (hv : ∀ l, onAxis i0 l → onAxis i0 (v l)) (F : V4 p) :
    resFun i0 (v (extFun i0 (resFun i0 F))) = resFun i0 (v F) := by
  obtain ⟨l, hl, hF⟩ := exists_onAxis_mul_extFun_resFun i0 F
  have hright : resFun i0 (v F) = resFun i0 (v (extFun i0 (resFun i0 F))) := by
    conv_lhs => rw [hF]
    rw [map_mul, resFun_eq_of_mul_onAxis i0 (hv l hl)]
  exact hright.symm

private theorem transportAut_mul_restrictHom {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i0 : Fin 4)
    {u : MulAut (V4 p)}
    (hu : ∀ f, onAxis i0 f → onAxis i0 (u f))
    (hu' : ∀ f, onAxis i0 f → onAxis i0 (u⁻¹ f))
    (hnorm : ∀ w ∈ dCoordinateBlock 4 p i0, u * w * u⁻¹ ∈ dCoordinateBlock 4 p i0)
    {w : MulAut (V4 p)} (hw : w ∈ dCoordinateBlock 4 p i0) :
    transportAut i0 u hu hu' * restrictHom hp hp2 i0 ⟨w, hw⟩ =
      restrictHom hp hp2 i0 ⟨u * w * u⁻¹, hnorm w hw⟩ * transportAut i0 u hu hu' := by
  refine MulEquiv.ext fun f => ?_
  change resFun i0 (u (extFun i0 (resFun i0 (w (extFun i0 f))))) =
    resFun i0 ((u * w * u⁻¹) (extFun i0 (resFun i0 (u (extFun i0 f)))))
  rw [resFun_ext_res_eq_of_onAxis i0 hu (w (extFun i0 f))]
  have hv : ∀ (l : V4 p), onAxis i0 l → onAxis i0 ((u * w * u⁻¹) l) := by
    intro l hl
    rw [(onAxis_iff_fixed hp hp2 i0 l).mpr hl (u * w * u⁻¹) (hnorm w hw)]
    exact hl
  rw [resFun_ext_res_eq_of_onAxis i0 hv (u (extFun i0 f))]
  congr 1
  simp [MulAut.mul_apply]

private theorem transportAut_conj_restrictHom_mem_HC {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (i0 : Fin 4) {u : MulAut (V4 p)}
    (hu : ∀ f, onAxis i0 f → onAxis i0 (u f))
    (hu' : ∀ f, onAxis i0 f → onAxis i0 (u⁻¹ f))
    (hnorm : ∀ w ∈ dCoordinateBlock 4 p i0, u * w * u⁻¹ ∈ dCoordinateBlock 4 p i0)
    {w : MulAut (V4 p)} (hw : w ∈ dCoordinateBlock 4 p i0) :
    transportAut i0 u hu hu' * restrictHom hp hp2 i0 ⟨w, hw⟩ *
        (transportAut i0 u hu hu')⁻¹ ∈ HC hp hp2 i0 := by
  rw [transportAut_mul_restrictHom hp hp2 i0 hu hu' hnorm hw]
  rw [mul_assoc, mul_inv_cancel, mul_one]
  exact Subgroup.mem_map.mpr ⟨⟨u * w * u⁻¹, hnorm w hw⟩, Subgroup.mem_top _, rfl⟩

private theorem restrictHom_negTrans_mem_DC {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (i0 : Fin 4) {a b : Fin 4} (hab : a ≠ b) (ha : a ≠ i0) (hb : b ≠ i0) :
    restrictHom hp hp2 i0
        ⟨sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹,
          Subgroup.subset_closure (Or.inr ⟨a, b, hab, ha, hb, rfl⟩)⟩ ∈ DC hp i0 := by
  let W := dCoordinateBlock 4 p i0
  let t : ↥W := ⟨permAut (Equiv.swap a b),
    Subgroup.subset_closure (Or.inl ⟨a, b, hab, ha, hb, rfl⟩)⟩
  let s : ↥W := ⟨sgnAut a * sgnAut b,
    sgnAut_mul_mem_dCoordinateBlock (p := p) i0 hab ha hb⟩
  let nt : ↥W := ⟨sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹,
    Subgroup.subset_closure (Or.inr ⟨a, b, hab, ha, hb, rfl⟩)⟩
  have haC : (⟨a, ha⟩ : CIdx i0) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Subtype.val h)
  have ht : restrictHom hp hp2 i0 t ∈ DC hp i0 := by
    simpa [t, W] using restrictHom_permAut_swap_mem_DC hp hp2 i0
      (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) haC
  have hs : restrictHom hp hp2 i0 s ∈ DC hp i0 := by
    simpa [s, W] using restrictHom_sgnAut_mul_mem_DC hp hp2 i0
      (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) haC
  have hrepr : nt = t⁻¹ * s := by
    apply Subtype.ext
    change sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹ =
      (permAut (Equiv.swap a b))⁻¹ * (sgnAut a * sgnAut b)
    rw [← permAut_swap_mul_negTrans (p := p) hab]
    group
  have hnt : restrictHom hp hp2 i0 nt = (restrictHom hp hp2 i0 t)⁻¹ *
      (restrictHom hp hp2 i0 s) := by
    rw [hrepr, map_mul, map_inv]
  change restrictHom hp hp2 i0 nt ∈ DC hp i0
  rw [hnt]
  exact (DC hp i0).mul_mem ((DC hp i0).inv_mem ht) hs

private theorem restrictHom_mem_DC_of_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (i0 : Fin 4) {w : MulAut (V4 p)} (hw : w ∈ dCoordinateBlock 4 p i0) :
    restrictHom hp hp2 i0 ⟨w, hw⟩ ∈ DC hp i0 := by
  dsimp [dCoordinateBlock] at hw
  induction hw using Subgroup.closure_induction with
  | mem r hr =>
      rcases hr with ⟨a, b, hab, ha, hb, rfl⟩ | ⟨a, b, hab, ha, hb, rfl⟩
      · exact restrictHom_permAut_swap_mem_DC hp hp2 i0
          (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (fun h => hab (congrArg Subtype.val h))
      · exact restrictHom_negTrans_mem_DC hp hp2 i0 hab ha hb
  | one =>
      change restrictHom hp hp2 i0 (1 : ↥(dCoordinateBlock 4 p i0)) ∈ DC hp i0
      rw [map_one]
      exact (DC hp i0).one_mem
  | mul x y hx hy ihx ihy =>
      have hEq : (⟨x * y, Subgroup.mul_mem (dCoordinateBlock 4 p i0) hx hy⟩ :
          ↥(dCoordinateBlock 4 p i0)) =
          (⟨x, hx⟩ : ↥(dCoordinateBlock 4 p i0)) * ⟨y, hy⟩ := rfl
      rw [hEq, map_mul]
      exact (DC hp i0).mul_mem ihx ihy
  | inv x hx ih =>
      have hEq : (⟨x⁻¹, Subgroup.inv_mem (dCoordinateBlock 4 p i0) hx⟩ :
          ↥(dCoordinateBlock 4 p i0)) =
          (⟨x, hx⟩ : ↥(dCoordinateBlock 4 p i0))⁻¹ := rfl
      rw [hEq, map_inv]
      exact (DC hp i0).inv_mem ih

private theorem HC_le_DC {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i0 : Fin 4) :
    HC hp hp2 i0 ≤ DC hp i0 := by
  rw [HC, Subgroup.map_le_iff_le_comap]
  intro w _
  exact restrictHom_mem_DC_of_mem hp hp2 i0 w.2

private theorem permAutC_mem_HC {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i0 : Fin 4)
    (σ : Equiv.Perm (CIdx i0)) : permAutC i0 σ ∈ HC hp hp2 i0 := by
  have hK : Subgroup.closure {τ : Equiv.Perm (CIdx i0) | τ.IsSwap} ≤
      (HC hp hp2 i0).comap (permAutCHom i0) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro τ ⟨a, b, hab, rfl⟩
    change permAutC i0 (Equiv.swap a b) ∈ HC hp hp2 i0
    rw [← restrictHom_permAut_swap hp hp2 i0 (a := a) (b := b) hab]
    exact restrictHom_permAut_swap_mem_HC hp hp2 i0 hab
  have htop : Subgroup.closure {τ : Equiv.Perm (CIdx i0) | τ.IsSwap} = ⊤ :=
    Equiv.Perm.closure_isSwap
  have hσ : σ ∈ Subgroup.closure {τ : Equiv.Perm (CIdx i0) | τ.IsSwap} := by
    rw [htop]
    exact Subgroup.mem_top σ
  exact hK hσ

private theorem D3_le_HC_map {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i0 : Fin 4) :
    D3 p hp ≤ (HC hp hp2 i0).map (MulAut.congr (coordMulEquiv p i0)).toMonoidHom := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hle : DScalarTorus.evenSignedGroup (p := p) (N := 3) ≤
      (HC hp hp2 i0).map (MulAut.congr (coordMulEquiv p i0)).toMonoidHom := by
    refine DScalarTorus.evenSignedGroup_le hp2 ?_ ?_
    · intro i j hij
      let a : CIdx i0 := (coordEquiv i0) i
      let b : CIdx i0 := (coordEquiv i0) j
      have hab : a ≠ b := fun h => hij ((coordEquiv i0).injective h)
      let w : ↥(dCoordinateBlock 4 p i0) := ⟨sgnAut a.1 * sgnAut b.1,
        sgnAut_mul_mem_dCoordinateBlock (p := p) i0
          (fun h => hab (Subtype.ext h)) a.2 b.2⟩
      have hwHC : restrictHom hp hp2 i0 w ∈ HC hp hp2 i0 := by
        simpa [w] using restrictHom_sgnAut_mul_mem_HC hp hp2 i0 hab
      refine Subgroup.mem_map.mpr ⟨restrictHom hp hp2 i0 w, hwHC, ?_⟩
      have hval : restrictHom hp hp2 i0 w = sgnAutC i0 a * sgnAutC i0 b := by
        simpa [w] using restrictHom_sgnAut_mul hp hp2 i0 (a := a) (b := b) hab
      rw [hval]
      change MulAut.congr (coordMulEquiv p i0) (sgnAutC i0 a * sgnAutC i0 b) =
        sgnAut i * sgnAut j
      rw [map_mul, congr_sgnAutC, congr_sgnAutC]
      simp [a, b]
    · intro σ
      let σC : Equiv.Perm (CIdx i0) := (coordEquiv i0).symm.trans (σ.trans (coordEquiv i0))
      refine Subgroup.mem_map.mpr ⟨permAutC i0 σC, permAutC_mem_HC hp hp2 i0 σC, ?_⟩
      change MulAut.congr (coordMulEquiv p i0) (permAutC i0 σC) = permAut σ
      rw [congr_permAutC]
      congr 1
      ext i
      simp [σC, Equiv.trans_assoc]
  simpa [D3] using hle

private theorem DC_le_HC {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i0 : Fin 4) :
    DC hp i0 ≤ HC hp hp2 i0 := by
  intro x hx
  rw [mem_DC_iff] at hx
  have hxH := D3_le_HC_map hp hp2 i0 hx
  rw [Subgroup.mem_map] at hxH
  obtain ⟨y, hy, hEq⟩ := hxH
  have hyx : y = x := (MulAut.congr (coordMulEquiv p i0)).injective hEq
  rwa [← hyx]

private theorem HC_eq_DC {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i0 : Fin 4) :
    HC hp hp2 i0 = DC hp i0 :=
  le_antisymm (HC_le_DC hp hp2 i0) (DC_le_HC hp hp2 i0)

private theorem inv_conj_mem_of_forall_conj_mem {G : Type*} [Group G] {H : Subgroup G}
    [Finite ↥H] {g : G} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    ∀ x ∈ H, g⁻¹ * x * g ∈ H := by
  intro x hx
  let F : ↥H → ↥H := fun y => ⟨g * y.1 * g⁻¹, h y.1 y.2⟩
  have hinj : Function.Injective F := by
    intro y z hyz
    apply Subtype.ext
    have h' := congrArg Subtype.val hyz
    exact mul_left_cancel (mul_right_cancel h')
  obtain ⟨y, hy⟩ := (Function.Injective.bijective_of_finite hinj).2 ⟨x, hx⟩
  have hyval : y.1 = g⁻¹ * x * g := by
    have h' : g * y.1 * g⁻¹ = x := by simpa [F] using congrArg Subtype.val hy
    calc y.1 = g⁻¹ * (g * y.1 * g⁻¹) * g := by group
      _ = g⁻¹ * x * g := by rw [h']
  rw [← hyval]
  exact y.2

private theorem isSignedPerm_of_mem_D3 {p : ℕ} (hp : p.Prime) {u : MulAut (Fin 3 → Multiplicative (ZMod p))}
    (hu : u ∈ D3 p hp) : IsSignedPerm ⇑u := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨π, ε, hε, -, hdata⟩ := hu
  exact ⟨π, ε, hε, hdata⟩

private theorem isSignedPerm_negAut_fin3 {p : ℕ} :
    IsSignedPerm ⇑(OrthExcEven.negAut (p := p) (k := 3)) := by
  refine ⟨1, fun _ => -1, fun _ => Or.inr rfl, fun f i => ?_⟩
  rw [OrthExcEven.negAut_apply, Equiv.Perm.one_apply, toAdd_inv_apply]
  ring

private theorem normalize_signed_of_normalize_D3 {p : ℕ} (hp : p.Prime)
    {Φ : MulAut (Fin 3 → Multiplicative (ZMod p))}
    (hΦ : ∀ d ∈ D3 p hp, Φ * d * Φ⁻¹ ∈ D3 p hp)
    (hΦinv : ∀ d ∈ D3 p hp, Φ⁻¹ * d * Φ ∈ D3 p hp) :
    (∀ u : MulAut (Fin 3 → Multiplicative (ZMod p)),
        IsSignedPerm ⇑u → IsSignedPerm ⇑(Φ * u * Φ⁻¹)) ∧
      (∀ u : MulAut (Fin 3 → Multiplicative (ZMod p)),
        IsSignedPerm ⇑u → IsSignedPerm ⇑(Φ⁻¹ * u * Φ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hd : ∀ i j : Fin 3, i ≠ j → sgnAut i * sgnAut j ∈ D3 p hp := fun i j hij => by
    simpa [D3] using DScalarTorus.sgnAut_pair_mem_evenSignedGroup (p := p) (N := 3) hij
  have ht : ∀ σ : Equiv.Perm (Fin 3), permAut σ ∈ D3 p hp := fun σ => by
    simpa [D3] using DScalarTorus.permAut_mem_evenSignedGroup (p := p) (N := 3) σ
  have hneg : OrthExcEven.negAut (p := p) (k := 3) *
      sgnAut (0 : Fin 3) ∈ D3 p hp := by
    simpa [D3] using OrthExcEven.negAut_mul_sgnAut_mem (p := p) (k := 3) hd
      (by decide : Odd 3) (0 : Fin 3)
  have hneg0 : OrthExcEven.negAut (p := p) (k := 3) *
      OrthExcEven.negAut (p := p) (k := 3) = 1 := OrthExcEven.negAut_mul_self
  have hconjneg (Ψ : MulAut (Fin 3 → Multiplicative (ZMod p))) :
      Ψ * OrthExcEven.negAut (p := p) (k := 3) * Ψ⁻¹ =
        OrthExcEven.negAut (p := p) (k := 3) := by
    rw [← OrthExcEven.negAut_mul_comm Ψ]
    group
  constructor
  · intro u hu
    rcases OrthExcEven.mem_or_mul_mem_of_isSignedPerm hd
      (fun a b _ => ht (Equiv.swap a b)) (0 : Fin 3) hu with h | h
    · exact isSignedPerm_of_mem_D3 hp (hΦ u h)
    · have hd' : u * sgnAut (0 : Fin 3) ∈ D3 p hp := h
      have hs0 : (sgnAut (0 : Fin 3) : MulAut (Fin 3 → Multiplicative (ZMod p))) =
          OrthExcEven.negAut (p := p) (k := 3) *
            (OrthExcEven.negAut (p := p) (k := 3) * sgnAut (0 : Fin 3)) := by
        rw [← mul_assoc, hneg0, one_mul]
      have hu_eq : u = (u * sgnAut (0 : Fin 3)) *
          OrthExcEven.negAut (p := p) (k := 3) *
          (OrthExcEven.negAut (p := p) (k := 3) * sgnAut (0 : Fin 3)) := by
        calc u = u * (sgnAut (0 : Fin 3) * sgnAut (0 : Fin 3)) := by
              rw [OrthExcEven.sgnAut_mul_self, mul_one]
          _ = u * sgnAut (0 : Fin 3) * sgnAut (0 : Fin 3) := by group
          _ = u * sgnAut (0 : Fin 3) *
              (OrthExcEven.negAut (p := p) (k := 3) *
                (OrthExcEven.negAut (p := p) (k := 3) * sgnAut (0 : Fin 3))) := by
              nth_rewrite 2 [hs0]
              rfl
          _ = (u * sgnAut (0 : Fin 3)) * OrthExcEven.negAut (p := p) (k := 3) *
              (OrthExcEven.negAut (p := p) (k := 3) * sgnAut (0 : Fin 3)) := by group
      rw [hu_eq]
      have h1 := isSignedPerm_of_mem_D3 hp (hΦ _ hd')
      have h2 : IsSignedPerm ⇑(OrthExcEven.negAut (p := p) (k := 3)) :=
        isSignedPerm_negAut_fin3
      have h3 := isSignedPerm_of_mem_D3 hp (hΦ _ hneg)
      have hconj := hconjneg Φ
      rw [show Φ * ((u * sgnAut (0 : Fin 3)) * OrthExcEven.negAut (p := p) (k := 3) *
            (OrthExcEven.negAut (p := p) (k := 3) * sgnAut (0 : Fin 3))) * Φ⁻¹ =
          (Φ * (u * sgnAut (0 : Fin 3)) * Φ⁻¹) *
            (Φ * OrthExcEven.negAut (p := p) (k := 3) * Φ⁻¹) *
            (Φ * (OrthExcEven.negAut (p := p) (k := 3) * sgnAut (0 : Fin 3)) * Φ⁻¹)
        by group]
      rw [hconj]
      exact SignedPermCount.isSignedPerm_mul
        (u := (Φ * (u * sgnAut (0 : Fin 3)) * Φ⁻¹) * OrthExcEven.negAut (p := p) (k := 3))
        (v := Φ * (OrthExcEven.negAut (p := p) (k := 3) * sgnAut (0 : Fin 3)) * Φ⁻¹)
        (SignedPermCount.isSignedPerm_mul
          (u := Φ * (u * sgnAut (0 : Fin 3)) * Φ⁻¹)
          (v := OrthExcEven.negAut (p := p) (k := 3)) h1 h2) h3
  · intro u hu
    rcases OrthExcEven.mem_or_mul_mem_of_isSignedPerm hd
      (fun a b _ => ht (Equiv.swap a b)) (0 : Fin 3) hu with h | h
    · exact isSignedPerm_of_mem_D3 hp (hΦinv u h)
    · have hd' : u * sgnAut (0 : Fin 3) ∈ D3 p hp := h
      have hs0 : (sgnAut (0 : Fin 3) : MulAut (Fin 3 → Multiplicative (ZMod p))) =
          OrthExcEven.negAut (p := p) (k := 3) *
            (OrthExcEven.negAut (p := p) (k := 3) * sgnAut (0 : Fin 3)) := by
        rw [← mul_assoc, hneg0, one_mul]
      have hu_eq : u = (u * sgnAut (0 : Fin 3)) *
          OrthExcEven.negAut (p := p) (k := 3) *
          (OrthExcEven.negAut (p := p) (k := 3) * sgnAut (0 : Fin 3)) := by
        calc u = u * (sgnAut (0 : Fin 3) * sgnAut (0 : Fin 3)) := by
              rw [OrthExcEven.sgnAut_mul_self, mul_one]
          _ = u * sgnAut (0 : Fin 3) * sgnAut (0 : Fin 3) := by group
          _ = u * sgnAut (0 : Fin 3) *
              (OrthExcEven.negAut (p := p) (k := 3) *
                (OrthExcEven.negAut (p := p) (k := 3) * sgnAut (0 : Fin 3))) := by
              nth_rewrite 2 [hs0]
              rfl
          _ = (u * sgnAut (0 : Fin 3)) * OrthExcEven.negAut (p := p) (k := 3) *
              (OrthExcEven.negAut (p := p) (k := 3) * sgnAut (0 : Fin 3)) := by group
      rw [hu_eq]
      have h1 := isSignedPerm_of_mem_D3 hp (hΦinv _ hd')
      have h2 : IsSignedPerm ⇑(OrthExcEven.negAut (p := p) (k := 3)) :=
        isSignedPerm_negAut_fin3
      have h3 := isSignedPerm_of_mem_D3 hp (hΦinv _ hneg)
      have hconj : Φ⁻¹ * OrthExcEven.negAut (p := p) (k := 3) * Φ =
          OrthExcEven.negAut (p := p) (k := 3) := by
        simpa using hconjneg Φ⁻¹
      rw [show Φ⁻¹ * ((u * sgnAut (0 : Fin 3)) * OrthExcEven.negAut (p := p) (k := 3) *
            (OrthExcEven.negAut (p := p) (k := 3) * sgnAut (0 : Fin 3))) * Φ =
          (Φ⁻¹ * (u * sgnAut (0 : Fin 3)) * Φ) *
            (Φ⁻¹ * OrthExcEven.negAut (p := p) (k := 3) * Φ) *
            (Φ⁻¹ * (OrthExcEven.negAut (p := p) (k := 3) * sgnAut (0 : Fin 3)) * Φ)
        by group]
      rw [hconj]
      exact SignedPermCount.isSignedPerm_mul
        (u := (Φ⁻¹ * (u * sgnAut (0 : Fin 3)) * Φ) * OrthExcEven.negAut (p := p) (k := 3))
        (v := Φ⁻¹ * (OrthExcEven.negAut (p := p) (k := 3) * sgnAut (0 : Fin 3)) * Φ)
        (SignedPermCount.isSignedPerm_mul
          (u := Φ⁻¹ * (u * sgnAut (0 : Fin 3)) * Φ)
          (v := OrthExcEven.negAut (p := p) (k := 3)) h1 h2) h3

private theorem prod_signs_eq_one_or_neg_one {p : ℕ} {ε : Fin 3 → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    (∏ i : Fin 3, ε i) = 1 ∨ (∏ i : Fin 3, ε i) = -1 := by
  classical
  induction (Finset.univ : Finset (Fin 3)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      rcases hε a with ha1 | ha1 <;> rcases ih with hs | hs <;> simp [ha1, hs]

theorem exists_smul_mem_dCoordinateBlock_four_of_normalizes {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (i0 : Fin 4) {u : MulAut (Fin 4 → Multiplicative (ZMod p))}
    (hu : ∀ w ∈ dCoordinateBlock 4 p i0, u * w * u⁻¹ ∈ dCoordinateBlock 4 p i0) :
    ∃ (γ : ZMod p) (w : MulAut (Fin 4 → Multiplicative (ZMod p))),
      w ∈ dCoordinateBlock 4 p i0 ∧
        ∀ (f : Fin 4 → Multiplicative (ZMod p)) (k : Fin 4), k ≠ i0 →
          toAdd (u f k) = γ * toAdd (w f k) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let W := dCoordinateBlock 4 p i0
  have hu_inv : ∀ w ∈ W, u⁻¹ * w * u ∈ W :=
    inv_normalizes_dCoordinateBlock hp i0 hu
  have hu_axis : ∀ f, onAxis i0 f → onAxis i0 (u f) :=
    fun f hf => onAxis_map_of_normalizes hp hp2 i0 hu hu_inv hf
  have huinv_axis : ∀ f, onAxis i0 f → onAxis i0 (u⁻¹ f) :=
    fun f hf => onAxis_map_of_normalizes hp hp2 i0 hu_inv hu hf
  let φ : MulAut (VC p i0) := transportAut i0 u hu_axis huinv_axis
  let Θ : VC p i0 ≃* (Fin 3 → Multiplicative (ZMod p)) := coordMulEquiv p i0
  let Φ : MulAut (Fin 3 → Multiplicative (ZMod p)) := MulAut.congr Θ φ
  have hφDC : ∀ d ∈ DC hp i0, φ * d * φ⁻¹ ∈ DC hp i0 := by
    intro d hd
    rw [← HC_eq_DC hp hp2 i0] at hd ⊢
    rw [HC, Subgroup.mem_map] at hd
    obtain ⟨w, -, hw_eq⟩ := hd
    rw [← hw_eq]
    simpa [φ] using transportAut_conj_restrictHom_mem_HC hp hp2 i0
      hu_axis huinv_axis hu (w := w.1) w.2
  have hΦD3 : ∀ d ∈ D3 p hp, Φ * d * Φ⁻¹ ∈ D3 p hp := by
    intro d hd
    let x : MulAut (VC p i0) := MulAut.congr Θ.symm d
    have hxDC : x ∈ DC hp i0 := by
      rw [mem_DC_iff]
      dsimp [x]
      rw [mulAut_congr_congr_symm]
      exact hd
    have hx := hφDC x hxDC
    rw [mem_DC_iff] at hx
    have hxeq : MulAut.congr Θ x = d := by
      dsimp [x]
      exact mulAut_congr_congr_symm Θ d
    have heq : MulAut.congr Θ (φ * x * φ⁻¹) = Φ * d * Φ⁻¹ := by
      dsimp [Φ]
      rw [map_mul, map_mul, map_inv, hxeq]
    rwa [heq] at hx
  have hΦD3inv : ∀ d ∈ D3 p hp, Φ⁻¹ * d * Φ ∈ D3 p hp :=
    inv_conj_mem_of_forall_conj_mem hΦD3
  have hSigned := normalize_signed_of_normalize_D3 hp hΦD3 hΦD3inv
  obtain ⟨w3, hw3, n, hc⟩ :=
    exists_isSignedPerm_pow hp hp2 (by norm_num : 3 ≤ 3) hSigned.1 hSigned.2
  obtain ⟨π3, ε3, hε3, hdata3⟩ := hw3
  have key : ∀ (n : ℕ) (wE : MulAut (Fin 3 → Multiplicative (ZMod p))),
      wE ∈ D3 p hp → (∀ g, Φ g = (wE g) ^ n) →
      ∃ w4 : MulAut (V4 p), w4 ∈ W ∧
        ∀ (f : V4 p) (k : Fin 4), k ≠ i0 →
          toAdd (u f k) = (n : ZMod p) * toAdd (w4 f k) := by
    intro n wE hwE hexp
    let wC : MulAut (VC p i0) := MulAut.congr Θ.symm wE
    have hwC_DC : wC ∈ DC hp i0 := by
      rw [mem_DC_iff]
      dsimp [wC]
      rw [mulAut_congr_congr_symm]
      exact hwE
    have hwC_HC : wC ∈ HC hp hp2 i0 := by rwa [HC_eq_DC hp hp2 i0]
    obtain ⟨w4, -, hw4_eq⟩ := Subgroup.mem_map.mp hwC_HC
    refine ⟨w4.1, w4.2, ?_⟩
    intro f k hk
    let c0 : CIdx i0 := ⟨k, hk⟩
    let fC : VC p i0 := resFun i0 f
    have hφ : φ fC = (wC fC) ^ n := by
      have h := hexp (Θ fC)
      have h1 : Φ (Θ fC) = Θ (φ fC) := by
        dsimp [Φ]
        exact mulAut_congr_apply_apply Θ φ fC
      have h2 : wE (Θ fC) = Θ (wC fC) := by
        have h2' : wC fC = Θ.symm (wE (Θ fC)) := by
          dsimp [wC]
          simpa using mulAut_congr_apply_apply Θ.symm wE (Θ fC)
        have := congrArg Θ h2'
        simpa using this.symm
      rw [h1, h2] at h
      rw [← map_pow] at h
      exact Θ.injective h
    have hwC_eq : wC fC = resFun i0 (w4.1 (extFun i0 fC)) := by
      rw [← hw4_eq, restrictHom_apply]
    have h_u_res : resFun i0 (u f) = resFun i0 (u (extFun i0 fC)) := by
      obtain ⟨l, hl, hF⟩ := exists_onAxis_mul_extFun_resFun i0 f
      rw [hF, map_mul, resFun_eq_of_mul_onAxis i0 (hu_axis l hl)]
    have h_w_res : resFun i0 (w4.1 f) = resFun i0 (w4.1 (extFun i0 fC)) := by
      obtain ⟨l, hl, hF⟩ := exists_onAxis_mul_extFun_resFun i0 f
      rw [hF, map_mul]
      have hwl : w4.1 l = l := (onAxis_iff_fixed hp hp2 i0 l).mpr hl w4.1 w4.2
      rw [hwl, resFun_eq_of_mul_onAxis i0 hl]
    calc
      toAdd (u f k) = toAdd (u (extFun i0 fC) k) := by
        have := congrArg (fun g : VC p i0 => toAdd (g c0)) h_u_res
        simpa [resFun, c0] using this
      _ = toAdd (φ fC c0) := rfl
      _ = toAdd (((wC fC) ^ n) c0) := by rw [hφ]
      _ = (n : ZMod p) * toAdd (wC fC c0) := by
        rw [Pi.pow_apply, toAdd_pow, nsmul_eq_mul]
      _ = (n : ZMod p) * toAdd (resFun i0 (w4.1 (extFun i0 fC)) c0) := by rw [hwC_eq]
      _ = (n : ZMod p) * toAdd (w4.1 f k) := by
        have := congrArg (fun g : VC p i0 => toAdd (g c0)) h_w_res
        rw [show toAdd (resFun i0 (w4.1 (extFun i0 fC)) c0) = toAdd (w4.1 f k) by
          simpa [resFun, c0] using this.symm]
  by_cases hprod : (∏ i : Fin 3, ε3 i) = 1
  · have hwE : w3 ∈ D3 p hp := by
      haveI : Fact p.Prime := ⟨hp⟩
      have hmem : w3 ∈ DScalarTorus.evenSignedGroup (p := p) (N := 3) :=
        ⟨π3, ε3, hε3, hprod, hdata3⟩
      simpa [D3] using hmem
    obtain ⟨w4, hw4, hconv⟩ := key n w3 hwE hc
    exact ⟨(n : ZMod p), w4, hw4, hconv⟩
  · have hprod_pm : (∏ i : Fin 3, ε3 i) = 1 ∨ (∏ i : Fin 3, ε3 i) = -1 :=
      prod_signs_eq_one_or_neg_one hε3
    have hprod_neg : (∏ i : Fin 3, ε3 i) = -1 := hprod_pm.resolve_left hprod
    let wE : MulAut (Fin 3 → Multiplicative (ZMod p)) :=
      OrthExcEven.negAut (p := p) (k := 3) * w3
    have hdataE : ∀ f i, toAdd (wE f (π3 i)) = (-ε3 i) * toAdd (f i) := by
      intro f i
      dsimp [wE]
      rw [OrthExcEven.negAut_apply, toAdd_inv_apply, hdata3]
      ring
    have hprodE : (∏ i : Fin 3, (-ε3 i)) = 1 := by
      have h1 : (∏ i : Fin 3, (-ε3 i)) = (-1 : ZMod p) ^ 3 * ∏ i, ε3 i := by
        rw [show (fun i : Fin 3 => -ε3 i) = (fun i => (-1 : ZMod p) * ε3 i) by
          funext i; ring]
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        simp
      rw [h1, hprod_neg]
      norm_num
    have hwE : wE ∈ D3 p hp := by
      haveI : Fact p.Prime := ⟨hp⟩
      have hmem : wE ∈ DScalarTorus.evenSignedGroup (p := p) (N := 3) := by
        refine ⟨π3, fun i => -ε3 i, ?_, hprodE, hdataE⟩
        intro i
        rcases hε3 i with h | h
        · right; simp [h]
        · left; simp [h]
      simpa [D3] using hmem
    have hw3_eq : w3 = OrthExcEven.negAut (p := p) (k := 3) * wE := by
      dsimp [wE]
      rw [← mul_assoc, OrthExcEven.negAut_mul_self, one_mul]
    have hexp : ∀ g, Φ g = (wE g) ^ (n * (p - 1)) := by
      intro g
      rw [hc g, hw3_eq, MulAut.mul_apply, OrthExcEven.negAut_apply]
      simpa using (OrthExcEven.inv_pow_mul_pred_eq (p := p) hp (x := (wE g)⁻¹) n).symm
    obtain ⟨w4, hw4, hconv⟩ := key (n * (p - 1)) wE hwE hexp
    exact ⟨((n * (p - 1) : ℕ) : ZMod p), w4, hw4, hconv⟩

end CFSG.StandardType
