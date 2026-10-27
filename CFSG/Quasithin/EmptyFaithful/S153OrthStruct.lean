module

public import CFSG.Quasithin.EmptyFaithful.S1417Orth

public section

namespace CFSG.Quasithin

structure OfourStruct {W : Type*} [CommGroup W] (X L₁ L₂ : Subgroup (MulAut W)) (t : MulAut W) :
    Prop where
  nat₁ : ActsAsNaturalL2 L₁ (commV L₁)
  nat₂ : ActsAsNaturalL2 L₂ (commV L₂)
  comm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a
  Linf : L₁ ⊓ L₂ = ⊥
  inf : commV L₁ ⊓ commV L₂ = ⊥
  sup : commV L₁ ⊔ commV L₂ = ⊤
  swap₁ : ∀ u ∈ commV L₁, t u ∈ commV L₂
  swap₂ : ∀ u ∈ commV L₂, t u ∈ commV L₁
  conj₁ : B1.conjAut t L₁ = L₂
  conj₂ : B1.conjAut t L₂ = L₁
  tsq : t * t = 1
  eq : X = (L₁ ⊔ L₂) ⊔ Subgroup.zpowers t

namespace S153

open S1417

section Coord

variable {W : Type*} [CommGroup W] {U₁ U₂ : Subgroup W}
  (hinf : U₁ ⊓ U₂ = ⊥) (hsup : U₁ ⊔ U₂ = ⊤) (φ₁ : ↥U₁ ≃* F2sq) (φ₂ : ↥U₂ ≃* F2sq)

private theorem coord_of_mem_fst {u : W} (hu : u ∈ U₁) :
    coordEquiv hinf hsup φ₁ φ₂ u = (φ₁ ⟨u, hu⟩, 1) := by
  have h := coordEquiv_mul hinf hsup φ₁ φ₂ hu (U₂.one_mem)
  have h1 : (⟨1, U₂.one_mem⟩ : U₂) = 1 := rfl
  rw [h1, map_one, mul_one] at h
  exact h

private theorem coord_of_mem_snd {u : W} (hu : u ∈ U₂) :
    coordEquiv hinf hsup φ₁ φ₂ u = (1, φ₂ ⟨u, hu⟩) := by
  have h := coordEquiv_mul hinf hsup φ₁ φ₂ (U₁.one_mem) hu
  have h1 : (⟨1, U₁.one_mem⟩ : U₁) = 1 := rfl
  rw [h1, map_one, one_mul] at h
  exact h

private theorem mem_fst_iff {w : W} : w ∈ U₁ ↔ (coordEquiv hinf hsup φ₁ φ₂ w).2 = 1 := by
  constructor
  · intro hw
    rw [coord_of_mem_fst hinf hsup φ₁ φ₂ hw]
  · intro h
    obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq hsup w
    rw [coordEquiv_mul hinf hsup φ₁ φ₂ hy hz] at h
    have h1 : (⟨z, hz⟩ : U₂) = 1 := φ₂.injective (by simpa using h)
    have h2 : z = 1 := congrArg Subtype.val h1
    rw [h2, mul_one]
    exact hy

private theorem mem_snd_iff {w : W} : w ∈ U₂ ↔ (coordEquiv hinf hsup φ₁ φ₂ w).1 = 1 := by
  constructor
  · intro hw
    rw [coord_of_mem_snd hinf hsup φ₁ φ₂ hw]
  · intro h
    obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq hsup w
    rw [coordEquiv_mul hinf hsup φ₁ φ₂ hy hz] at h
    have h1 : (⟨y, hy⟩ : U₁) = 1 := φ₁.injective (by simpa using h)
    have h2 : y = 1 := congrArg Subtype.val h1
    rw [h2, one_mul]
    exact hz

end Coord

section Homs

private def fstAut : MulAut F2sq →* MulAut (F2sq × F2sq) where
  toFun a := MulEquiv.prodCongr a (MulEquiv.refl F2sq)
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' _ _ := MulEquiv.ext fun _ => rfl

private def sndAut : MulAut F2sq →* MulAut (F2sq × F2sq) where
  toFun a := MulEquiv.prodCongr (MulEquiv.refl F2sq) a
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' _ _ := MulEquiv.ext fun _ => rfl

private theorem fstAut_apply (a : MulAut F2sq) (x y : F2sq) : fstAut a (x, y) = (a x, y) := rfl
private theorem sndAut_apply (a : MulAut F2sq) (x y : F2sq) : sndAut a (x, y) = (x, a y) := rfl

private def swapAut : MulAut (F2sq × F2sq) := MulEquiv.prodComm

private theorem swapAut_apply (x y : F2sq) : swapAut (x, y) = (y, x) := rfl

variable {W : Type*} [CommGroup W] {U₁ U₂ : Subgroup W}
  (hinf : U₁ ⊓ U₂ = ⊥) (hsup : U₁ ⊔ U₂ = ⊤) (φ₁ : ↥U₁ ≃* F2sq) (φ₂ : ↥U₂ ≃* F2sq)

private noncomputable def toW : MulAut (F2sq × F2sq) ≃* MulAut W :=
  (MulAut.congr (coordEquiv hinf hsup φ₁ φ₂)).symm

private theorem coord_toW (σ : MulAut (F2sq × F2sq)) (w : W) :
    coordEquiv hinf hsup φ₁ φ₂ (toW hinf hsup φ₁ φ₂ σ w) = σ (coordEquiv hinf hsup φ₁ φ₂ w) := by
  simp [toW]

private noncomputable def lam₁ : SL2 →* MulAut W :=
  (toW hinf hsup φ₁ φ₂).toMonoidHom.comp (fstAut.comp B1.slHom)

private noncomputable def lam₂ : SL2 →* MulAut W :=
  (toW hinf hsup φ₁ φ₂).toMonoidHom.comp (sndAut.comp B1.slHom)

private noncomputable def swapW : MulAut W := toW hinf hsup φ₁ φ₂ swapAut

private theorem coord_lam₁ (g : SL2) (w : W) :
    coordEquiv hinf hsup φ₁ φ₂ (lam₁ hinf hsup φ₁ φ₂ g w) =
      (B1.slHom g (coordEquiv hinf hsup φ₁ φ₂ w).1, (coordEquiv hinf hsup φ₁ φ₂ w).2) := by
  show coordEquiv hinf hsup φ₁ φ₂ (toW hinf hsup φ₁ φ₂ (fstAut (B1.slHom g)) w) = _
  rw [coord_toW]
  rfl

private theorem coord_lam₂ (g : SL2) (w : W) :
    coordEquiv hinf hsup φ₁ φ₂ (lam₂ hinf hsup φ₁ φ₂ g w) =
      ((coordEquiv hinf hsup φ₁ φ₂ w).1, B1.slHom g (coordEquiv hinf hsup φ₁ φ₂ w).2) := by
  show coordEquiv hinf hsup φ₁ φ₂ (toW hinf hsup φ₁ φ₂ (sndAut (B1.slHom g)) w) = _
  rw [coord_toW]
  rfl

private theorem coord_swapW (w : W) :
    coordEquiv hinf hsup φ₁ φ₂ (swapW hinf hsup φ₁ φ₂ w) =
      ((coordEquiv hinf hsup φ₁ φ₂ w).2, (coordEquiv hinf hsup φ₁ φ₂ w).1) := by
  show coordEquiv hinf hsup φ₁ φ₂ (toW hinf hsup φ₁ φ₂ swapAut w) = _
  rw [coord_toW]
  rfl

private theorem lam₁_injective : Function.Injective (lam₁ hinf hsup φ₁ φ₂) := by
  intro g h hgh
  apply B1.slHom_injective
  refine MulEquiv.ext fun x => ?_
  have e := congrArg (fun a : MulAut W => coordEquiv hinf hsup φ₁ φ₂
    (a ((coordEquiv hinf hsup φ₁ φ₂).symm (x, 1)))) hgh
  simp only [coord_lam₁, MulEquiv.apply_symm_apply, Prod.mk.injEq] at e
  exact e.1

private theorem lam₂_injective : Function.Injective (lam₂ hinf hsup φ₁ φ₂) := by
  intro g h hgh
  apply B1.slHom_injective
  refine MulEquiv.ext fun x => ?_
  have e := congrArg (fun a : MulAut W => coordEquiv hinf hsup φ₁ φ₂
    (a ((coordEquiv hinf hsup φ₁ φ₂).symm (1, x)))) hgh
  simp only [coord_lam₂, MulEquiv.apply_symm_apply, Prod.mk.injEq] at e
  exact e.2

private noncomputable abbrev LL₁ : Subgroup (MulAut W) := (lam₁ hinf hsup φ₁ φ₂).range

private noncomputable abbrev LL₂ : Subgroup (MulAut W) := (lam₂ hinf hsup φ₁ φ₂).range

private theorem mem_LL₁ {x : MulAut W} : x ∈ LL₁ hinf hsup φ₁ φ₂ ↔ ∃ g, lam₁ hinf hsup φ₁ φ₂ g = x :=
  MonoidHom.mem_range

private theorem mem_LL₂ {x : MulAut W} : x ∈ LL₂ hinf hsup φ₁ φ₂ ↔ ∃ g, lam₂ hinf hsup φ₁ φ₂ g = x :=
  MonoidHom.mem_range

private theorem exists_slHom_eq : ∀ a : F2sq, ∃ (g : SL2) (a' : F2sq), B1.slHom g a' * a'⁻¹ = a := by
  decide

private theorem commV_LL₁ : commV (LL₁ hinf hsup φ₁ φ₂) = U₁ := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨g, rfl⟩ := (mem_LL₁ hinf hsup φ₁ φ₂).1 hx
    show _ ∈ U₁
    rw [mem_fst_iff hinf hsup φ₁ φ₂, map_mul, map_inv, coord_lam₁]
    simp only [Prod.snd_mul, Prod.snd_inv]
    exact mul_inv_cancel _
  · intro u hu
    have hcu := coord_of_mem_fst hinf hsup φ₁ φ₂ hu
    obtain ⟨g, a', hga⟩ := exists_slHom_eq (φ₁ ⟨u, hu⟩)
    refine Subgroup.subset_closure ⟨lam₁ hinf hsup φ₁ φ₂ g, ⟨g, rfl⟩,
      (coordEquiv hinf hsup φ₁ φ₂).symm (a', 1), ?_⟩
    apply (coordEquiv hinf hsup φ₁ φ₂).injective
    rw [map_mul, map_inv, coord_lam₁, hcu]
    simp [hga]
    exact inv_one

private theorem commV_LL₂ : commV (LL₂ hinf hsup φ₁ φ₂) = U₂ := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨g, rfl⟩ := (mem_LL₂ hinf hsup φ₁ φ₂).1 hx
    show _ ∈ U₂
    rw [mem_snd_iff hinf hsup φ₁ φ₂, map_mul, map_inv, coord_lam₂]
    simp only [Prod.fst_mul, Prod.fst_inv]
    exact mul_inv_cancel _
  · intro u hu
    have hcu := coord_of_mem_snd hinf hsup φ₁ φ₂ hu
    obtain ⟨g, a', hga⟩ := exists_slHom_eq (φ₂ ⟨u, hu⟩)
    refine Subgroup.subset_closure ⟨lam₂ hinf hsup φ₁ φ₂ g, ⟨g, rfl⟩,
      (coordEquiv hinf hsup φ₁ φ₂).symm (1, a'), ?_⟩
    apply (coordEquiv hinf hsup φ₁ φ₂).injective
    rw [map_mul, map_inv, coord_lam₂, hcu]
    simp [hga]
    exact inv_one

private theorem natural₁ : ActsAsNaturalL2 (LL₁ hinf hsup φ₁ φ₂) (commV (LL₁ hinf hsup φ₁ φ₂)) := by
  have hc := commV_LL₁ hinf hsup φ₁ φ₂
  refine ⟨(MonoidHom.ofInjective (lam₁_injective hinf hsup φ₁ φ₂)).symm,
    (MulEquiv.subgroupCongr hc).trans φ₁, ?_⟩
  intro h u hu
  obtain ⟨g, hg⟩ := (mem_LL₁ hinf hsup φ₁ φ₂).1 h.2
  have heg : (MonoidHom.ofInjective (lam₁_injective hinf hsup φ₁ φ₂)).symm h = g := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hg.symm
  rw [heg]
  have e1 : ∀ x : ↥(commV (LL₁ hinf hsup φ₁ φ₂)),
      ((MulEquiv.subgroupCongr hc).trans φ₁) x = (coordEquiv hinf hsup φ₁ φ₂ (x : W)).1 := by
    intro x
    have hx : (x : W) ∈ U₁ := (SetLike.ext_iff.mp hc (x : W)).1 x.2
    rw [coord_of_mem_fst hinf hsup φ₁ φ₂ hx]
    rfl
  rw [e1 ⟨_, hu⟩, e1 u]
  show (coordEquiv hinf hsup φ₁ φ₂ ((h : MulAut W) (u : W))).1 = _
  rw [← hg, coord_lam₁]
  rfl

private theorem natural₂ : ActsAsNaturalL2 (LL₂ hinf hsup φ₁ φ₂) (commV (LL₂ hinf hsup φ₁ φ₂)) := by
  have hc := commV_LL₂ hinf hsup φ₁ φ₂
  refine ⟨(MonoidHom.ofInjective (lam₂_injective hinf hsup φ₁ φ₂)).symm,
    (MulEquiv.subgroupCongr hc).trans φ₂, ?_⟩
  intro h u hu
  obtain ⟨g, hg⟩ := (mem_LL₂ hinf hsup φ₁ φ₂).1 h.2
  have heg : (MonoidHom.ofInjective (lam₂_injective hinf hsup φ₁ φ₂)).symm h = g := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hg.symm
  rw [heg]
  have e1 : ∀ x : ↥(commV (LL₂ hinf hsup φ₁ φ₂)),
      ((MulEquiv.subgroupCongr hc).trans φ₂) x = (coordEquiv hinf hsup φ₁ φ₂ (x : W)).2 := by
    intro x
    have hx : (x : W) ∈ U₂ := (SetLike.ext_iff.mp hc (x : W)).1 x.2
    rw [coord_of_mem_snd hinf hsup φ₁ φ₂ hx]
    rfl
  rw [e1 ⟨_, hu⟩, e1 u]
  show (coordEquiv hinf hsup φ₁ φ₂ ((h : MulAut W) (u : W))).2 = _
  rw [← hg, coord_lam₂]
  rfl

private theorem lam_comm (g g' : SL2) :
    lam₁ hinf hsup φ₁ φ₂ g * lam₂ hinf hsup φ₁ φ₂ g' =
      lam₂ hinf hsup φ₁ φ₂ g' * lam₁ hinf hsup φ₁ φ₂ g := by
  refine MulEquiv.ext fun w => (coordEquiv hinf hsup φ₁ φ₂).injective ?_
  simp only [MulAut.mul_apply, coord_lam₁, coord_lam₂]

private theorem LL_comm : ∀ a ∈ LL₁ hinf hsup φ₁ φ₂, ∀ b ∈ LL₂ hinf hsup φ₁ φ₂, a * b = b * a := by
  rintro _ ⟨g, rfl⟩ _ ⟨g', rfl⟩
  exact lam_comm hinf hsup φ₁ φ₂ g g'

private theorem LL_inf : LL₁ hinf hsup φ₁ φ₂ ⊓ LL₂ hinf hsup φ₁ φ₂ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨g, rfl⟩, ⟨g', hg'⟩⟩
  rw [Subgroup.mem_bot]
  have h1 : g = 1 := by
    apply B1.slHom_injective
    refine MulEquiv.ext fun a => ?_
    have e := congrArg (fun y : MulAut W => (coordEquiv hinf hsup φ₁ φ₂)
      (y ((coordEquiv hinf hsup φ₁ φ₂).symm (a, 1)))) hg'
    simp only [coord_lam₁, coord_lam₂, MulEquiv.apply_symm_apply, Prod.mk.injEq] at e
    rw [map_one]
    exact e.1.symm.trans (by rfl)
  rw [h1, map_one]

private theorem swapW_mem_snd {u : W} (hu : u ∈ U₁) : swapW hinf hsup φ₁ φ₂ u ∈ U₂ := by
  rw [mem_snd_iff hinf hsup φ₁ φ₂, coord_swapW]
  exact (mem_fst_iff hinf hsup φ₁ φ₂).1 hu

private theorem swapW_mem_fst {u : W} (hu : u ∈ U₂) : swapW hinf hsup φ₁ φ₂ u ∈ U₁ := by
  rw [mem_fst_iff hinf hsup φ₁ φ₂, coord_swapW]
  exact (mem_snd_iff hinf hsup φ₁ φ₂).1 hu

private theorem swapW_mul_self : swapW hinf hsup φ₁ φ₂ * swapW hinf hsup φ₁ φ₂ = 1 := by
  refine MulEquiv.ext fun w => (coordEquiv hinf hsup φ₁ φ₂).injective ?_
  simp only [MulAut.mul_apply, coord_swapW, MulAut.one_apply]

private theorem swapW_inv : (swapW hinf hsup φ₁ φ₂)⁻¹ = swapW hinf hsup φ₁ φ₂ :=
  inv_eq_of_mul_eq_one_right (swapW_mul_self hinf hsup φ₁ φ₂)

private theorem swapW_lam₁ (g : SL2) :
    swapW hinf hsup φ₁ φ₂ * lam₁ hinf hsup φ₁ φ₂ g * swapW hinf hsup φ₁ φ₂ =
      lam₂ hinf hsup φ₁ φ₂ g := by
  refine MulEquiv.ext fun w => (coordEquiv hinf hsup φ₁ φ₂).injective ?_
  simp only [MulAut.mul_apply, coord_swapW, coord_lam₁, coord_lam₂]

private theorem swapW_lam₂ (g : SL2) :
    swapW hinf hsup φ₁ φ₂ * lam₂ hinf hsup φ₁ φ₂ g * swapW hinf hsup φ₁ φ₂ =
      lam₁ hinf hsup φ₁ φ₂ g := by
  refine MulEquiv.ext fun w => (coordEquiv hinf hsup φ₁ φ₂).injective ?_
  simp only [MulAut.mul_apply, coord_swapW, coord_lam₁, coord_lam₂]

private theorem conjAut_swapW_LL₁ : B1.conjAut (swapW hinf hsup φ₁ φ₂) (LL₁ hinf hsup φ₁ φ₂) =
    LL₂ hinf hsup φ₁ φ₂ := by
  have hss := swapW_mul_self hinf hsup φ₁ φ₂
  ext x
  rw [B1.mem_conjAut, swapW_inv]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    rw [← swapW_lam₁ hinf hsup φ₁ φ₂ g, hg]
    calc swapW hinf hsup φ₁ φ₂ * (swapW hinf hsup φ₁ φ₂ * x * swapW hinf hsup φ₁ φ₂) *
          swapW hinf hsup φ₁ φ₂
        = (swapW hinf hsup φ₁ φ₂ * swapW hinf hsup φ₁ φ₂) * x *
          (swapW hinf hsup φ₁ φ₂ * swapW hinf hsup φ₁ φ₂) := by simp only [mul_assoc]
      _ = x := by rw [hss]; simp
  · rintro ⟨g, rfl⟩
    exact ⟨g, (swapW_lam₂ hinf hsup φ₁ φ₂ g).symm ▸ rfl⟩

private theorem conjAut_swapW_LL₂ : B1.conjAut (swapW hinf hsup φ₁ φ₂) (LL₂ hinf hsup φ₁ φ₂) =
    LL₁ hinf hsup φ₁ φ₂ := by
  have hss := swapW_mul_self hinf hsup φ₁ φ₂
  ext x
  rw [B1.mem_conjAut, swapW_inv]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    rw [← swapW_lam₂ hinf hsup φ₁ φ₂ g, hg]
    calc swapW hinf hsup φ₁ φ₂ * (swapW hinf hsup φ₁ φ₂ * x * swapW hinf hsup φ₁ φ₂) *
          swapW hinf hsup φ₁ φ₂
        = (swapW hinf hsup φ₁ φ₂ * swapW hinf hsup φ₁ φ₂) * x *
          (swapW hinf hsup φ₁ φ₂ * swapW hinf hsup φ₁ φ₂) := by simp only [mul_assoc]
      _ = x := by rw [hss]; simp
  · rintro ⟨g, rfl⟩
    exact ⟨g, (swapW_lam₁ hinf hsup φ₁ φ₂ g).symm ▸ rfl⟩

private theorem lam₁_apply_of_mem_snd (g : SL2) {u : W} (hu : u ∈ U₂) :
    lam₁ hinf hsup φ₁ φ₂ g u = u := by
  apply (coordEquiv hinf hsup φ₁ φ₂).injective
  rw [coord_lam₁, coord_of_mem_snd hinf hsup φ₁ φ₂ hu]
  simp

private theorem lam₂_apply_of_mem_fst (g : SL2) {u : W} (hu : u ∈ U₁) :
    lam₂ hinf hsup φ₁ φ₂ g u = u := by
  apply (coordEquiv hinf hsup φ₁ φ₂).injective
  rw [coord_lam₂, coord_of_mem_fst hinf hsup φ₁ φ₂ hu]
  simp

private theorem lam₁_mem_fst (g : SL2) {u : W} (hu : u ∈ U₁) : lam₁ hinf hsup φ₁ φ₂ g u ∈ U₁ := by
  rw [mem_fst_iff hinf hsup φ₁ φ₂, coord_lam₁]
  exact (mem_fst_iff hinf hsup φ₁ φ₂).1 hu

private theorem lam₂_mem_snd (g : SL2) {u : W} (hu : u ∈ U₂) : lam₂ hinf hsup φ₁ φ₂ g u ∈ U₂ := by
  rw [mem_snd_iff hinf hsup φ₁ φ₂, coord_lam₂]
  exact (mem_snd_iff hinf hsup φ₁ φ₂).1 hu

private theorem exists_ne_one_mem_fst (φ₁ : ↥U₁ ≃* F2sq) : ∃ a ∈ U₁, a ≠ 1 := by
  refine ⟨(φ₁.symm (Multiplicative.ofAdd (Pi.single 0 1)) : W), (φ₁.symm _).2, fun h => ?_⟩
  have h1 : φ₁.symm (Multiplicative.ofAdd (Pi.single 0 1)) = 1 := Subtype.ext h
  have h2 : (Multiplicative.ofAdd (Pi.single 0 1) : F2sq) = 1 := by
    have := congrArg φ₁ h1
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  have h3 := congrFun (Multiplicative.ofAdd.injective h2) 0
  simp at h3

private theorem orthogonal_eq [Finite W] :
    orthogonalGroupOf (quadOf hinf hsup φ₁ φ₂) =
      (LL₁ hinf hsup φ₁ φ₂ ⊔ LL₂ hinf hsup φ₁ φ₂) ⊔ Subgroup.zpowers (swapW hinf hsup φ₁ φ₂) := by
  have hc₁ := commV_LL₁ hinf hsup φ₁ φ₂
  have hc₂ := commV_LL₂ hinf hsup φ₁ φ₂
  have hinfV : commV (LL₁ hinf hsup φ₁ φ₂) ⊓ commV (LL₂ hinf hsup φ₁ φ₂) = ⊥ := by
    rw [hc₁, hc₂]; exact hinf
  have hsupV : commV (LL₁ hinf hsup φ₁ φ₂) ⊔ commV (LL₂ hinf hsup φ₁ φ₂) = ⊤ := by
    rw [hc₁, hc₂]; exact hsup
  apply le_antisymm
  · intro g hg
    have hg' : ∀ w, quadOf hinf hsup φ₁ φ₂ (g w) = quadOf hinf hsup φ₁ φ₂ w := hg
    have key : ∀ g : MulAut W, (∀ u ∈ U₁, g u ∈ U₁) → (∀ u ∈ U₂, g u ∈ U₂) →
        g ∈ LL₁ hinf hsup φ₁ φ₂ ⊔ LL₂ hinf hsup φ₁ φ₂ := by
      intro g h₁ h₂
      have h₁' : ∀ u ∈ commV (LL₁ hinf hsup φ₁ φ₂), g u ∈ commV (LL₁ hinf hsup φ₁ φ₂) := by
        intro u hu
        rw [hc₁] at hu ⊢
        exact h₁ u hu
      have h₂' : ∀ u ∈ commV (LL₂ hinf hsup φ₁ φ₂), g u ∈ commV (LL₂ hinf hsup φ₁ φ₂) := by
        intro u hu
        rw [hc₂] at hu ⊢
        exact h₂ u hu
      obtain ⟨y, hy, hgy⟩ := exists_mem_sup_apply_eq (natural₁ hinf hsup φ₁ φ₂)
        (natural₂ hinf hsup φ₁ φ₂) (LL_comm hinf hsup φ₁ φ₂) hinfV
        (mem_stabSub_of_forall_le h₁') (mem_stabSub_of_forall_le h₂')
      have : g = y := MulEquiv.ext fun w => hgy w (by rw [hsupV]; exact Subgroup.mem_top w)
      rw [this]
      exact hy
    rcases perm_of_mem_orthogonal hinf hsup φ₁ φ₂ (exists_ne_one_mem_fst φ₁) hg' with
      ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Subgroup.mem_sup_left (key g h₁ h₂)
    · have hgt : g * swapW hinf hsup φ₁ φ₂ ∈ LL₁ hinf hsup φ₁ φ₂ ⊔ LL₂ hinf hsup φ₁ φ₂ :=
        key _ (fun u hu => h₂ _ (swapW_mem_snd hinf hsup φ₁ φ₂ hu))
          (fun u hu => h₁ _ (swapW_mem_fst hinf hsup φ₁ φ₂ hu))
      have : g = (g * swapW hinf hsup φ₁ φ₂) * (swapW hinf hsup φ₁ φ₂)⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hgt)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)))
  · refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨g, rfl⟩ v
      exact quadOf_apply_of_stab hinf hsup φ₁ φ₂ (fun u hu => lam₁_mem_fst hinf hsup φ₁ φ₂ g hu)
        (fun u hu => by rw [lam₁_apply_of_mem_snd hinf hsup φ₁ φ₂ g hu]; exact hu) v
    · rintro _ ⟨g, rfl⟩ v
      exact quadOf_apply_of_stab hinf hsup φ₁ φ₂
        (fun u hu => by rw [lam₂_apply_of_mem_fst hinf hsup φ₁ φ₂ g hu]; exact hu)
        (fun u hu => lam₂_mem_snd hinf hsup φ₁ φ₂ g hu) v
    · rw [Subgroup.zpowers_le]
      intro v
      exact quadOf_apply_of_swap hinf hsup φ₁ φ₂ (fun u hu => swapW_mem_snd hinf hsup φ₁ φ₂ hu)
        (fun u hu => swapW_mem_fst hinf hsup φ₁ φ₂ hu) v

end Homs

theorem exists_ofourStruct {W : Type*} [CommGroup W] [Finite W] {U₁ U₂ : Subgroup W}
    (hinf : U₁ ⊓ U₂ = ⊥) (hsup : U₁ ⊔ U₂ = ⊤) (φ₁ : ↥U₁ ≃* F2sq) (φ₂ : ↥U₂ ≃* F2sq) :
    ∃ (L₁ L₂ : Subgroup (MulAut W)) (t : MulAut W),
      OfourStruct (orthogonalGroupOf (quadOf hinf hsup φ₁ φ₂)) L₁ L₂ t ∧
        commV L₁ = U₁ ∧ commV L₂ = U₂ := by
  have hc₁ := commV_LL₁ hinf hsup φ₁ φ₂
  have hc₂ := commV_LL₂ hinf hsup φ₁ φ₂
  refine ⟨LL₁ hinf hsup φ₁ φ₂, LL₂ hinf hsup φ₁ φ₂, swapW hinf hsup φ₁ φ₂, ⟨natural₁ hinf hsup φ₁ φ₂,
    natural₂ hinf hsup φ₁ φ₂, LL_comm hinf hsup φ₁ φ₂, LL_inf hinf hsup φ₁ φ₂, ?_, ?_,
    fun u hu => ?_, fun u hu => ?_, conjAut_swapW_LL₁ hinf hsup φ₁ φ₂,
    conjAut_swapW_LL₂ hinf hsup φ₁ φ₂, swapW_mul_self hinf hsup φ₁ φ₂,
    orthogonal_eq hinf hsup φ₁ φ₂⟩, hc₁, hc₂⟩
  · rw [hc₁, hc₂]
    exact hinf
  · rw [hc₁, hc₂]
    exact hsup
  · rw [hc₁] at hu
    rw [hc₂]
    exact swapW_mem_snd hinf hsup φ₁ φ₂ hu
  · rw [hc₂] at hu
    rw [hc₁]
    exact swapW_mem_fst hinf hsup φ₁ φ₂ hu

end S153

end CFSG.Quasithin
