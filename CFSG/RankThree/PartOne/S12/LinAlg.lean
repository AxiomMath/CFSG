module

public import CFSG.RankThree.PartOne.S12.Skeleton
public import CFSG.RankThree.SubgroupLists.SchurCommutant

public section

namespace CFSG.RankThree.PartOne.LinAlg

open CFSG
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G]

section ExistsCoords

open scoped IsMulCommutative

theorem exists_coords (E : Subgroup G) [Finite E] [IsElementaryAbelian p E] {n : ℕ}
    (hcard : Nat.card E = p ^ n) : Nonempty (Multiplicative (Fin n → ZMod p) ≃* E) := by
  classical
  have hfin : Module.finrank (ZMod p) (Additive E) = n := by
    have h := FiniteField.pow_finrank_eq_natCard p (Additive E)
    have h' : Nat.card (Additive E) = p ^ n := hcard
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le (h.trans h')
  let b := Module.finBasisOfFinrankEq (ZMod p) (Additive E) hfin
  exact ⟨MulEquiv.toAdditiveRight.symm b.equivFun.symm.toAddEquiv⟩

end ExistsCoords

section Coords

variable {n : ℕ} {E : Subgroup G} (f : Multiplicative (Fin n → ZMod p) ≃* E)

@[expose] def coordAdd (σ : MulAut E) : (Fin n → ZMod p) ≃+ (Fin n → ZMod p) :=
  MulEquiv.toAdditive ((f.trans σ).trans f.symm)

@[expose] def coordLin (σ : MulAut E) : (Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p) :=
  (coordAdd f σ).toLinearEquiv fun c v => by
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

theorem coordLin_apply (σ : MulAut E) (v : Fin n → ZMod p) :
    coordLin f σ v = Multiplicative.toAdd (f.symm (σ (f (Multiplicative.ofAdd v)))) :=
  rfl

theorem apply_coordLin (σ : MulAut E) (v : Fin n → ZMod p) :
    f (Multiplicative.ofAdd (coordLin f σ v)) = σ (f (Multiplicative.ofAdd v)) := by
  rw [coordLin_apply, ofAdd_toAdd, MulEquiv.apply_symm_apply]

@[expose] def coordHom : MulAut E →* ((Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)) where
  toFun := coordLin f
  map_one' := by
    ext v
    simp [coordLin_apply]
  map_mul' σ τ := by
    ext v
    simp [coordLin_apply]

theorem coordHom_apply (σ : MulAut E) (v : Fin n → ZMod p) :
    coordHom f σ v = Multiplicative.toAdd (f.symm (σ (f (Multiplicative.ofAdd v)))) :=
  rfl

theorem coordHom_injective : Function.Injective (coordHom f) := by
  intro σ τ h
  ext a
  have := congrArg (fun φ => f (Multiplicative.ofAdd (φ (Multiplicative.toAdd (f.symm a))))) h
  simpa [coordHom_apply] using congrArg Subtype.val this

@[expose] noncomputable def wAction :
    Subgroup.normalizer (E : Set G) →* ((Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)) :=
  (coordHom f).comp E.normalizerMonoidHom

theorem wAction_apply (g : Subgroup.normalizer (E : Set G)) (v : Fin n → ZMod p) :
    ((f (Multiplicative.ofAdd (wAction f g v)) : E) : G) =
      (g : G) * (f (Multiplicative.ofAdd v) : G) * (g : G)⁻¹ := by
  simp [wAction, coordHom_apply]

theorem range_wAction : (wAction f).range = (torusWeyl E).map (coordHom f) := by
  rw [wAction, MonoidHom.range_comp, torusWeyl]

end Coords


section Subspaces

variable {n : ℕ} {E : Subgroup G} (f : Multiplicative (Fin n → ZMod p) ≃* E)

@[expose] def subSpace (B : Subgroup E) : Submodule (ZMod p) (Fin n → ZMod p) where
  carrier := {v | f (Multiplicative.ofAdd v) ∈ B}
  add_mem' {a b} ha hb := by
    change f (Multiplicative.ofAdd (a + b)) ∈ B
    rw [ofAdd_add, map_mul]
    exact B.mul_mem ha hb
  zero_mem' := by
    change f (Multiplicative.ofAdd 0) ∈ B
    rw [ofAdd_zero, map_one]
    exact B.one_mem
  smul_mem' c v hv := by
    change f (Multiplicative.ofAdd (c • v)) ∈ B
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, ofAdd_nsmul, map_pow]
    exact B.pow_mem hv _

@[expose] def spaceSubgroup (U : Submodule (ZMod p) (Fin n → ZMod p)) : Subgroup E where
  carrier := {x | Multiplicative.toAdd (f.symm x) ∈ U}
  mul_mem' {a b} ha hb := by
    change Multiplicative.toAdd (f.symm (a * b)) ∈ U
    rw [map_mul, toAdd_mul]
    exact U.add_mem ha hb
  one_mem' := by
    change Multiplicative.toAdd (f.symm 1) ∈ U
    rw [map_one, toAdd_one]
    exact U.zero_mem
  inv_mem' {a} ha := by
    change Multiplicative.toAdd (f.symm a⁻¹) ∈ U
    rw [map_inv, toAdd_inv]
    exact U.neg_mem ha

theorem mem_subSpace (B : Subgroup E) (v : Fin n → ZMod p) :
    v ∈ subSpace f B ↔ f (Multiplicative.ofAdd v) ∈ B :=
  Iff.rfl

theorem mem_spaceSubgroup (U : Submodule (ZMod p) (Fin n → ZMod p)) (x : E) :
    x ∈ spaceSubgroup f U ↔ Multiplicative.toAdd (f.symm x) ∈ U :=
  Iff.rfl

theorem toAdd_symm_mem_subSpace_iff (B : Subgroup E) (x : E) :
    Multiplicative.toAdd (f.symm x) ∈ subSpace f B ↔ x ∈ B := by
  rw [mem_subSpace, ofAdd_toAdd, MulEquiv.apply_symm_apply]

@[expose] def subSpaceEquiv : Subgroup E ≃o Submodule (ZMod p) (Fin n → ZMod p) where
  toFun := subSpace f
  invFun := spaceSubgroup f
  left_inv B := by
    ext x
    exact toAdd_symm_mem_subSpace_iff f B x
  right_inv U := by
    ext v
    change Multiplicative.toAdd (f.symm (f (Multiplicative.ofAdd v))) ∈ U ↔ v ∈ U
    rw [MulEquiv.symm_apply_apply, toAdd_ofAdd]
  map_rel_iff' := by
    intro B B'
    constructor
    · intro h x hx
      exact (toAdd_symm_mem_subSpace_iff f B' x).mp
        (h ((toAdd_symm_mem_subSpace_iff f B x).mpr hx))
    · intro h v hv
      exact h hv

theorem subSpaceEquiv_apply (B : Subgroup E) : subSpaceEquiv f B = subSpace f B :=
  rfl

theorem natCard_subSpace (B : Subgroup E) : Nat.card (subSpace f B) = Nat.card B :=
  Nat.card_congr
    { toFun := fun v => ⟨f (Multiplicative.ofAdd v.1), v.2⟩
      invFun := fun x => ⟨Multiplicative.toAdd (f.symm x.1),
        (toAdd_symm_mem_subSpace_iff f B x.1).mpr x.2⟩
      left_inv := fun v => by
        apply Subtype.ext
        change Multiplicative.toAdd (f.symm (f (Multiplicative.ofAdd v.1))) = v.1
        rw [MulEquiv.symm_apply_apply, toAdd_ofAdd]
      right_inv := fun x => by
        apply Subtype.ext
        exact MulEquiv.apply_symm_apply f _ }

theorem natCard_submodule_eq_pow_finrank {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    [Finite M] (U : Submodule (ZMod p) M) : Nat.card U = p ^ Module.finrank (ZMod p) U :=
  (FiniteField.pow_finrank_eq_natCard p U).symm

theorem natCard_eq_pow_finrank_subSpace (B : Subgroup E) :
    Nat.card B = p ^ Module.finrank (ZMod p) (subSpace f B) := by
  rw [← natCard_subSpace f B]
  exact natCard_submodule_eq_pow_finrank (subSpace f B)


@[expose] def bsub (B : Subgroup G) : Submodule (ZMod p) (Fin n → ZMod p) :=
  subSpace f (B.subgroupOf E)

theorem mem_bsub (B : Subgroup G) (v : Fin n → ZMod p) :
    v ∈ bsub f B ↔ ((f (Multiplicative.ofAdd v) : E) : G) ∈ B :=
  Iff.rfl

@[expose] def bsubEquiv : {B : Subgroup G // B ≤ E} ≃o Submodule (ZMod p) (Fin n → ZMod p) :=
  (Subgroup.MapSubtype.orderIso E).symm.trans (subSpaceEquiv f)

theorem bsubEquiv_apply (B : {B : Subgroup G // B ≤ E}) : bsubEquiv f B = bsub f B.1 :=
  rfl

theorem bsub_le_bsub_iff {B B' : Subgroup G} (hB : B ≤ E) (hB' : B' ≤ E) :
    bsub f B ≤ bsub f B' ↔ B ≤ B' :=
  (bsubEquiv f).le_iff_le (x := ⟨B, hB⟩) (y := ⟨B', hB'⟩)

theorem bsub_injective {B B' : Subgroup G} (hB : B ≤ E) (hB' : B' ≤ E) :
    bsub f B = bsub f B' ↔ B = B' := by
  have h := (bsubEquiv f).apply_eq_iff_eq (x := ⟨B, hB⟩) (y := ⟨B', hB'⟩)
  rw [Subtype.mk.injEq] at h
  exact h

theorem exists_bsub_eq (U : Submodule (ZMod p) (Fin n → ZMod p)) :
    ∃ B : Subgroup G, B ≤ E ∧ bsub f B = U :=
  ⟨((bsubEquiv f).symm U).1, ((bsubEquiv f).symm U).2, (bsubEquiv f).apply_symm_apply U⟩

theorem bsub_bot : bsub f (⊥ : Subgroup G) = ⊥ := by
  ext v
  simp [mem_bsub]

theorem bsub_self : bsub f E = ⊤ := by
  ext v
  simp [mem_bsub]

theorem natCard_eq_pow_finrank_bsub {B : Subgroup G} (hB : B ≤ E) :
    Nat.card B = p ^ Module.finrank (ZMod p) (bsub f B) := by
  rw [bsub, ← natCard_eq_pow_finrank_subSpace]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv).symm

end Subspaces

section Invariance

variable {n : ℕ} {E : Subgroup G} (f : Multiplicative (Fin n → ZMod p) ≃* E)

theorem preserves_iff_map_coordLin_le (φ : MulAut E) {B : Subgroup G} (hB : B ≤ E) :
    (∀ b (hb : b ∈ B), ((φ ⟨b, hB hb⟩ : E) : G) ∈ B) ↔
      (bsub f B).map (coordLin f φ).toLinearMap ≤ bsub f B := by
  constructor
  · intro h w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    have hv' : ((f (Multiplicative.ofAdd v) : E) : G) ∈ B := hv
    show ((f (Multiplicative.ofAdd (coordLin f φ v)) : E) : G) ∈ B
    rw [apply_coordLin]
    exact h _ hv'
  · intro h b hb
    have hfx : f (Multiplicative.ofAdd (Multiplicative.toAdd (f.symm ⟨b, hB hb⟩))) =
        ⟨b, hB hb⟩ := by
      rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]
    have hv : Multiplicative.toAdd (f.symm ⟨b, hB hb⟩) ∈ bsub f B := by
      rw [mem_bsub, hfx]
      exact hb
    have hw : ((f (Multiplicative.ofAdd (coordLin f φ (Multiplicative.toAdd (f.symm ⟨b, hB hb⟩))))
        : E) : G) ∈ B :=
      h (Submodule.mem_map_of_mem hv)
    rwa [apply_coordLin, hfx] at hw

theorem preserves_iff_map_coordLin_le_of_subgroup (Γ : Subgroup (MulAut E)) {B : Subgroup G}
    (hB : B ≤ E) :
    (∀ φ ∈ Γ, ∀ b (hb : b ∈ B), ((φ ⟨b, hB hb⟩ : E) : G) ∈ B) ↔
      ∀ φ ∈ Γ, (bsub f B).map (coordLin f φ).toLinearMap ≤ bsub f B :=
  forall₂_congr fun φ _ => preserves_iff_map_coordLin_le f φ hB

theorem torusInvariant_iff_forall_torusImage (Y : Subgroup G) {B : Subgroup G} (hB : B ≤ E) :
    torusInvariant E Y B ↔
      ∀ φ ∈ torusImage E Y, ∀ b (hb : b ∈ B), ((φ ⟨b, hB hb⟩ : E) : G) ∈ B := by
  constructor
  · intro h φ hφ b hb
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hφ
    exact h (w : G) ⟨hw, w.2⟩ b hb
  · intro h w hw b hb
    exact h (E.normalizerMonoidHom ⟨w, hw.2⟩)
      (Subgroup.mem_map_of_mem _ (show (⟨w, hw.2⟩ : Subgroup.normalizer (E : Set G)) ∈
        Y.subgroupOf (Subgroup.normalizer (E : Set G)) from hw.1)) b hb

theorem torusInvariant_iff (Y : Subgroup G) {B : Subgroup G} (hB : B ≤ E) :
    torusInvariant E Y B ↔
      ∀ φ ∈ torusImage E Y, (bsub f B).map (coordLin f φ).toLinearMap ≤ bsub f B :=
  (torusInvariant_iff_forall_torusImage Y hB).trans
    (preserves_iff_map_coordLin_le_of_subgroup f (torusImage E Y) hB)

theorem torusImage_top : torusImage E ⊤ = torusWeyl E := by
  rw [torusImage, torusWeyl, Subgroup.top_subgroupOf, MonoidHom.range_eq_map]

theorem torusInvariant_top_iff_forall_torusWeyl {B : Subgroup G} (hB : B ≤ E) :
    torusInvariant E ⊤ B ↔ ∀ φ ∈ torusWeyl E, ∀ b (hb : b ∈ B), ((φ ⟨b, hB hb⟩ : E) : G) ∈ B := by
  rw [torusInvariant_iff_forall_torusImage ⊤ hB, torusImage_top]

theorem torusInvariant_top_iff {B : Subgroup G} (hB : B ≤ E) :
    torusInvariant E ⊤ B ↔
      ∀ φ ∈ torusWeyl E, (bsub f B).map (coordLin f φ).toLinearMap ≤ bsub f B := by
  rw [torusInvariant_iff f ⊤ hB, torusImage_top]

end Invariance

section Commutator

variable {n : ℕ} {E : Subgroup G} (f : Multiplicative (Fin n → ZMod p) ≃* E)

@[expose] def coordSub (φ : MulAut E) : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p) :=
  (coordLin f φ : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)) - 1

theorem coordSub_apply (φ : MulAut E) (v : Fin n → ZMod p) :
    coordSub f φ v = coordLin f φ v - v :=
  rfl

theorem coordSub_eq (φ : MulAut E) :
    coordSub f φ = (coordLin f φ : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)) - 1 :=
  rfl

theorem apply_coordSub (φ : MulAut E) (v : Fin n → ZMod p) :
    f (Multiplicative.ofAdd (coordSub f φ v)) = φ (f (Multiplicative.ofAdd v)) *
      (f (Multiplicative.ofAdd v))⁻¹ := by
  rw [coordSub_apply, ofAdd_sub, map_div, apply_coordLin, div_eq_mul_inv]

theorem autMoved_eq_spaceSubgroup (φ : MulAut E) :
    autMoved E φ = spaceSubgroup f (LinearMap.range (coordSub f φ)) := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨e, rfl⟩
    refine ⟨Multiplicative.toAdd (f.symm e), ?_⟩
    have h := apply_coordSub f φ (Multiplicative.toAdd (f.symm e))
    rw [ofAdd_toAdd, MulEquiv.apply_symm_apply] at h
    show coordSub f φ (Multiplicative.toAdd (f.symm e)) = Multiplicative.toAdd (f.symm (φ e * e⁻¹))
    rw [← h, MulEquiv.symm_apply_apply, toAdd_ofAdd]
  · intro x hx
    obtain ⟨w, hw⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨f (Multiplicative.ofAdd w), ?_⟩
    have h := apply_coordSub f φ w
    have hw' : coordSub f φ w = Multiplicative.toAdd (f.symm x) := hw
    rw [hw', ofAdd_toAdd, MulEquiv.apply_symm_apply] at h
    exact h.symm

theorem autFixed_eq_spaceSubgroup (φ : MulAut E) :
    autFixed E φ = spaceSubgroup f (LinearMap.ker (coordSub f φ)) := by
  ext x
  have hx : f (Multiplicative.ofAdd (Multiplicative.toAdd (f.symm x))) = x := by
    rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]
  show φ x = x ↔ coordSub f φ (Multiplicative.toAdd (f.symm x)) = 0
  rw [coordSub_apply, sub_eq_zero, coordLin_apply, hx, Multiplicative.toAdd.injective.eq_iff,
    f.symm.injective.eq_iff]

theorem subSpace_autMoved (φ : MulAut E) :
    subSpace f (autMoved E φ) = LinearMap.range (coordSub f φ) := by
  rw [autMoved_eq_spaceSubgroup f]
  exact (subSpaceEquiv f).apply_symm_apply _

theorem subSpace_autFixed (φ : MulAut E) :
    subSpace f (autFixed E φ) = LinearMap.ker (coordSub f φ) := by
  rw [autFixed_eq_spaceSubgroup f]
  exact (subSpaceEquiv f).apply_symm_apply _

theorem natCard_autMoved (φ : MulAut E) :
    Nat.card (autMoved E φ) = p ^ Module.finrank (ZMod p) (LinearMap.range (coordSub f φ)) := by
  rw [natCard_eq_pow_finrank_subSpace f, subSpace_autMoved f]

theorem natCard_autFixed (φ : MulAut E) :
    Nat.card (autFixed E φ) = p ^ Module.finrank (ZMod p) (LinearMap.ker (coordSub f φ)) := by
  rw [natCard_eq_pow_finrank_subSpace f, subSpace_autFixed f]

theorem bsub_autMovedInG (φ : MulAut E) :
    bsub f (autMovedInG E φ) = LinearMap.range (coordSub f φ) := by
  rw [bsub, autMovedInG, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
    E.subtype_injective]
  exact subSpace_autMoved f φ

theorem bsub_autFixedInG (φ : MulAut E) :
    bsub f (autFixedInG E φ) = LinearMap.ker (coordSub f φ) := by
  rw [bsub, autFixedInG, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
    E.subtype_injective]
  exact subSpace_autFixed f φ

theorem finrank_range_add_finrank_ker (φ : MulAut E) :
    Module.finrank (ZMod p) (LinearMap.range (coordSub f φ)) +
      Module.finrank (ZMod p) (LinearMap.ker (coordSub f φ)) = n := by
  have h := LinearMap.finrank_range_add_finrank_ker (coordSub f φ)
  rwa [Module.finrank_fin_fun] at h

include f in
theorem natCard_eq_pow_of_coords : Nat.card E = p ^ n := by
  rw [← Nat.card_congr f.toEquiv]
  change Nat.card (Fin n → ZMod p) = p ^ n
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

include f in
theorem natCard_autMoved_mul_natCard_autFixed (φ : MulAut E) :
    Nat.card (autMoved E φ) * Nat.card (autFixed E φ) = Nat.card E := by
  rw [natCard_autMoved f, natCard_autFixed f, ← pow_add, finrank_range_add_finrank_ker f,
    natCard_eq_pow_of_coords f]

theorem autMoved_le_autFixed_iff (φ : MulAut E) :
    autMoved E φ ≤ autFixed E φ ↔ coordSub f φ ∘ₗ coordSub f φ = 0 := by
  rw [← (subSpaceEquiv f).le_iff_le, subSpaceEquiv_apply, subSpaceEquiv_apply,
    subSpace_autMoved f, subSpace_autFixed f, LinearMap.range_le_ker_iff]

theorem isAutReflection_iff (φ : MulAut E) :
    IsAutReflection p E φ ↔ orderOf (coordHom f φ) = 2 ∧
      Module.finrank (ZMod p) (LinearMap.range (coordSub f φ)) = 1 := by
  rw [IsAutReflection, orderOf_injective (coordHom f) (coordHom_injective f) φ, natCard_autMoved f,
    Nat.pow_eq_self_iff (Fact.out : p.Prime).one_lt]

theorem isAutTransvection_iff (φ : MulAut E) :
    IsAutTransvection p E φ ↔ coordHom f φ ≠ 1 ∧
      Module.finrank (ZMod p) (LinearMap.range (coordSub f φ)) = 1 ∧
      coordSub f φ ∘ₗ coordSub f φ = 0 := by
  rw [IsAutTransvection, natCard_autMoved f, Nat.pow_eq_self_iff (Fact.out : p.Prime).one_lt,
    autMoved_le_autFixed_iff f, ← map_one (coordHom f), (coordHom_injective f).ne_iff]

theorem isAutTransvection_iff_of_rank (φ : MulAut E) :
    IsAutTransvection p E φ ↔
      Module.finrank (ZMod p) (LinearMap.range (coordSub f φ)) = 1 ∧
      coordSub f φ ∘ₗ coordSub f φ = 0 := by
  rw [isAutTransvection_iff f]
  refine ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨fun h1 => ?_, h.1, h.2⟩⟩
  have h0 : coordSub f φ = 0 := LinearMap.ext fun v => by
    rw [coordSub_apply, LinearMap.zero_apply]
    have hv : coordLin f φ v = v := by
      simpa [coordHom_apply, coordLin_apply] using congrArg (fun L => L v) h1
    rw [hv, sub_self]
  have h2 := h.1
  rw [h0, LinearMap.range_zero, finrank_bot] at h2
  exact zero_ne_one h2

end Commutator


section MatrixForm

variable {n : ℕ}

@[expose] noncomputable def toGL :
    ((Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)) ≃* GL (Fin n) (ZMod p) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Fin n → ZMod p)).symm.trans
    Matrix.GeneralLinearGroup.toLin.symm

theorem toGL_mulVec (g : (Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)) (v : Fin n → ZMod p) :
    (toGL g : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ v = g v := by
  have h1 : Matrix.GeneralLinearGroup.toLin (toGL g) =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Fin n → ZMod p)).symm g :=
    MulEquiv.apply_symm_apply _ _
  have h2 := congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod p) (Fin n → ZMod p) =>
    (u : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)) v) h1
  simp only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply] at h2
  exact h2

variable {E : Subgroup G} (f : Multiplicative (Fin n → ZMod p) ≃* E)

@[expose] noncomputable def coordGL : MulAut E →* GL (Fin n) (ZMod p) :=
  (toGL (p := p) (n := n)).toMonoidHom.comp (coordHom f)

theorem coordGL_apply (σ : MulAut E) : coordGL f σ = toGL (coordHom f σ) :=
  rfl

theorem coordGL_mulVec (σ : MulAut E) (v : Fin n → ZMod p) :
    (coordGL f σ : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ v =
      coordLin f σ v :=
  toGL_mulVec _ v

theorem coordGL_injective : Function.Injective (coordGL f) :=
  (toGL (p := p) (n := n)).injective.comp (coordHom_injective f)

@[expose] noncomputable def torusWeylGL : Subgroup (GL (Fin n) (ZMod p)) :=
  (torusWeyl E).map (coordGL f)

theorem mem_torusWeylGL_iff (g : GL (Fin n) (ZMod p)) :
    g ∈ torusWeylGL f ↔ ∃ φ ∈ torusWeyl E, coordGL f φ = g :=
  Subgroup.mem_map

theorem coordGL_mem_torusWeylGL_iff (φ : MulAut E) :
    coordGL f φ ∈ torusWeylGL f ↔ φ ∈ torusWeyl E :=
  Subgroup.mem_map_iff_mem (coordGL_injective f)

@[expose] noncomputable def wActionGL : Subgroup.normalizer (E : Set G) →* GL (Fin n) (ZMod p) :=
  (coordGL f).comp E.normalizerMonoidHom

theorem range_wActionGL : (wActionGL f).range = torusWeylGL f := by
  rw [wActionGL, MonoidHom.range_comp, torusWeylGL, torusWeyl]

theorem mulVecLin_coordGL_sub_one (φ : MulAut E) :
    ((coordGL f φ : Matrix (Fin n) (Fin n) (ZMod p)) - 1).mulVecLin =
      coordSub f φ :=
  LinearMap.ext fun v => by
    rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, coordGL_mulVec]
    rfl

theorem rank_coordGL_sub_one (φ : MulAut E) :
    ((coordGL f φ : Matrix (Fin n) (Fin n) (ZMod p)) - 1).rank =
      Module.finrank (ZMod p) (LinearMap.range (coordSub f φ)) := by
  rw [Matrix.rank, mulVecLin_coordGL_sub_one f]

theorem coordGL_sub_one_mul_self_eq_zero_iff (φ : MulAut E) :
    ((coordGL f φ : Matrix (Fin n) (Fin n) (ZMod p)) - 1) *
        ((coordGL f φ : Matrix (Fin n) (Fin n) (ZMod p)) - 1) = 0 ↔
      coordSub f φ ∘ₗ coordSub f φ = 0 := by
  rw [← Matrix.toLin'.injective.eq_iff, map_zero, Matrix.toLin'_mul, Matrix.toLin'_apply',
    mulVecLin_coordGL_sub_one f]

theorem isAutReflection_iff_matrix (φ : MulAut E) :
    IsAutReflection p E φ ↔ orderOf (coordGL f φ) = 2 ∧
      ((coordGL f φ : Matrix (Fin n) (Fin n) (ZMod p)) - 1).rank = 1 := by
  rw [isAutReflection_iff f, rank_coordGL_sub_one f,
    orderOf_injective (coordHom f) (coordHom_injective f) φ,
    orderOf_injective (coordGL f) (coordGL_injective f) φ]

theorem isAutTransvection_iff_matrix (φ : MulAut E) :
    IsAutTransvection p E φ ↔ coordGL f φ ≠ 1 ∧
      ((coordGL f φ : Matrix (Fin n) (Fin n) (ZMod p)) - 1).rank = 1 ∧
      ((coordGL f φ : Matrix (Fin n) (Fin n) (ZMod p)) - 1) *
        ((coordGL f φ : Matrix (Fin n) (Fin n) (ZMod p)) - 1) = 0 := by
  rw [isAutTransvection_iff f, rank_coordGL_sub_one f, coordGL_sub_one_mul_self_eq_zero_iff f,
    ← map_one (coordGL f), (coordGL_injective f).ne_iff, ← map_one (coordHom f),
    (coordHom_injective f).ne_iff]

theorem isAutTransvection_iff_matrix_of_rank (φ : MulAut E) :
    IsAutTransvection p E φ ↔
      ((coordGL f φ : Matrix (Fin n) (Fin n) (ZMod p)) - 1).rank = 1 ∧
      ((coordGL f φ : Matrix (Fin n) (Fin n) (ZMod p)) - 1) *
        ((coordGL f φ : Matrix (Fin n) (Fin n) (ZMod p)) - 1) = 0 := by
  rw [isAutTransvection_iff_of_rank f, rank_coordGL_sub_one f,
    coordGL_sub_one_mul_self_eq_zero_iff f]

end MatrixForm


section Transport

variable {n : ℕ} {E : Subgroup G} (f : Multiplicative (Fin n → ZMod p) ≃* E)

theorem isIrreducibleMatrixRep_map_coordGL_iff (Γ : Subgroup (MulAut E)) :
    (∀ B : Subgroup G, ∀ hB : B ≤ E,
        (∀ φ ∈ Γ, ∀ b (hb : b ∈ B), ((φ ⟨b, hB hb⟩ : E) : G) ∈ B) → B = ⊥ ∨ B = E) ↔
      CFSG.RepresentationTheory.IsIrreducibleMatrixRep (Γ.map (coordGL f)).subtype := by
  constructor
  · intro hirr W hW
    obtain ⟨B, hBE, rfl⟩ := exists_bsub_eq f W
    have hinv : ∀ φ ∈ Γ, ∀ b (hb : b ∈ B), ((φ ⟨b, hBE hb⟩ : E) : G) ∈ B := by
      refine (preserves_iff_map_coordLin_le_of_subgroup f Γ hBE).mpr fun φ hφ w hw => ?_
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
      have h : (coordGL f φ : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ v ∈
          bsub f B := hW ⟨coordGL f φ, Subgroup.mem_map_of_mem _ hφ⟩ v hv
      rwa [coordGL_mulVec] at h
    rcases hirr B hBE hinv with rfl | rfl
    · exact Or.inl (bsub_bot f)
    · exact Or.inr (bsub_self f)
  · intro hirr B hBE hinv
    have hW : ∀ g : Γ.map (coordGL f), ∀ w ∈ bsub f B,
        ((g : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ w ∈ bsub f B := by
      rintro ⟨g, hg⟩ w hw
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hg
      have h := (preserves_iff_map_coordLin_le_of_subgroup f Γ hBE).mp hinv φ hφ
        (Submodule.mem_map_of_mem hw)
      show (coordGL f φ : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ w ∈
        bsub f B
      rwa [coordGL_mulVec]
    rcases hirr (bsub f B) hW with h | h
    · exact Or.inl ((bsub_injective f hBE bot_le).mp (h.trans (bsub_bot f).symm))
    · exact Or.inr ((bsub_injective f hBE le_rfl).mp (h.trans (bsub_self f).symm))

theorem torusIrreducible_iff :
    torusIrreducible E ↔
      CFSG.RepresentationTheory.IsIrreducibleMatrixRep (torusWeylGL f).subtype := by
  refine Iff.trans ?_ (isIrreducibleMatrixRep_map_coordGL_iff f (torusWeyl E))
  refine forall_congr' fun B => forall_congr' fun hB => ?_
  rw [torusInvariant_top_iff_forall_torusWeyl hB]

theorem torusIrreducible_iff_isIrreducibleOn :
    torusIrreducible E ↔ CFSG.RankThree.SubgroupLists.IsIrreducibleOn (torusWeylGL f) :=
  (torusIrreducible_iff f).trans CFSG.RankThree.SubgroupLists.isIrreducibleOn_iff.symm

@[expose] noncomputable def torusWeylEquiv : torusWeyl E ≃* torusWeylGL f :=
  Subgroup.equivMapOfInjective (torusWeyl E) (coordGL f) (coordGL_injective f)

theorem natCard_torusWeylGL : Nat.card (torusWeylGL f) = Nat.card (torusWeyl E) :=
  (Nat.card_congr (torusWeylEquiv f).toEquiv).symm

theorem pCore_eq_bot_iff_of_mulEquiv {H K : Type*} [Group H] [Group K] (p : ℕ) (e : H ≃* K) :
    CFSG.pCore p H = ⊥ ↔ CFSG.pCore p K = ⊥ := by
  rw [← CFSG.pCore_map_iso p e]
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).symm

theorem torusWeylHasPCore_iff :
    torusWeylHasPCore p E ↔ CFSG.pCore p ↥(torusWeylGL f) ≠ ⊥ :=
  not_congr (pCore_eq_bot_iff_of_mulEquiv p (torusWeylEquiv f))

theorem torusHasTransvection_iff :
    torusHasTransvection p E ↔ ∃ g ∈ torusWeylGL f, g ≠ 1 ∧
      ((g : Matrix (Fin n) (Fin n) (ZMod p)) - 1).rank = 1 ∧
      ((g : Matrix (Fin n) (Fin n) (ZMod p)) - 1) * ((g : Matrix (Fin n) (Fin n) (ZMod p)) - 1) =
        0 := by
  constructor
  · rintro ⟨φ, hφ, ht⟩
    exact ⟨coordGL f φ, (coordGL_mem_torusWeylGL_iff f φ).mpr hφ,
      (isAutTransvection_iff_matrix f φ).mp ht⟩
  · rintro ⟨g, hg, h⟩
    obtain ⟨φ, hφ, rfl⟩ := (mem_torusWeylGL_iff f g).mp hg
    exact ⟨φ, hφ, (isAutTransvection_iff_matrix f φ).mpr h⟩

end Transport

end CFSG.RankThree.PartOne.LinAlg
