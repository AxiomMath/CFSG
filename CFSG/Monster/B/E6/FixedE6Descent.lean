module

public import CFSG.Monster.B.E6.FixedE6Basis
public import CFSG.LieType.Chevalley.C2E6FieldExtensionStar
public import CFSG.Monster.B.Classical.E6AdjointGroup

public noncomputable section

namespace CFSG.Monster.B.E6.FixedE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap (K ω bar barHom t0 t0_add t0_smul t0_coe)
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.Monster.B.Classical.E6Adjoint

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem sq_algebraMap (c : ZMod 2) : algebraMap (ZMod 2) K c ^ 2 = algebraMap (ZMod 2) K c := by
  rw [← map_pow]
  congr 1
  revert c
  decide

theorem eq_zero_or_one_of_sq_eq {a : K} (h : a ^ 2 = a) : a = 0 ∨ a = 1 := by
  have : a * (a - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.1 h1)

theorem algebraMap_t0 {a : K} (h : a ^ 2 = a) : algebraMap (ZMod 2) K (t0 a) = a := by
  rcases eq_zero_or_one_of_sq_eq h with rfl | rfl
  · rw [show (0 : K) = algebraMap (ZMod 2) K 0 from (map_zero _).symm, t0_coe]
  · rw [show (1 : K) = algebraMap (ZMod 2) K 1 from (map_one _).symm, t0_coe]

@[expose] def fixedL : Submodule (ZMod 2) V where
  carrier := {u | fixedMap u = u}
  add_mem' {u v} hu hv := by
    change fixedMap (u + v) = u + v
    rw [fixedMap_add, hu, hv]
  zero_mem' := by
    change fixedMap 0 = 0
    have h := fixedMap_smul (0 : K) 0
    rwa [zero_smul, zero_pow two_ne_zero, zero_smul] at h
  smul_mem' c u hu := by
    change fixedMap (c • u) = c • u
    rw [← algebraMap_smul K c u, fixedMap_smul, hu, sq_algebraMap]

theorem mem_fixedL {u : V} : u ∈ fixedL ↔ fixedMap u = u := Iff.rfl

theorem basisVec_mem_fixedL (l : Label Tag.E6) : basisVec l ∈ fixedL := fixedMap_basisVec l

theorem mem_fixedL_iff_coordK
    {u : V} : u ∈ fixedL ↔ ∀ l, coordK u l ^ 2 = coordK u l :=
  fixedMap_eq_self_iff u

theorem sum_t0_smul
    {u : V} (hu : u ∈ fixedL) : ∑ l, t0 (coordK u l) • basisVec l = u := by
  conv_rhs => rw [← sum_coordK_smul u]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← algebraMap_smul K, algebraMap_t0 (mem_fixedL_iff_coordK.1 hu l)]

@[expose] def basisVecL (l : Label Tag.E6) : fixedL := ⟨basisVec l, basisVec_mem_fixedL l⟩

theorem linearIndependent_basisVecL :
    LinearIndependent (ZMod 2) basisVecL := by
  have hli : LinearIndependent (ZMod 2) basisVec := by
    refine linearIndependent_basisVec.restrict_scalars ?_
    intro a b h
    have h' : algebraMap (ZMod 2) K a = algebraMap (ZMod 2) K b := by
      simpa [Algebra.smul_def] using h
    exact (algebraMap (ZMod 2) K).injective h'
  exact LinearIndependent.of_comp fixedL.subtype hli

theorem span_basisVecL :
    ⊤ ≤ Submodule.span (ZMod 2) (Set.range basisVecL) := by
  rintro ⟨u, hu⟩ -
  have h : ∑ l, t0 (coordK u l) • basisVecL l = ⟨u, hu⟩ :=
    Subtype.ext (by simpa [basisVecL] using sum_t0_smul hu)
  rw [← h]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

@[expose] def basisL :
    Module.Basis (Label Tag.E6) (ZMod 2) fixedL :=
  Module.Basis.mk linearIndependent_basisVecL span_basisVecL

theorem basisL_apply
    (l : Label Tag.E6) : (basisL l : V) = basisVec l := by
  rw [basisL, Module.Basis.mk_apply]
  rfl

theorem card_label_E6 : Fintype.card (Label Tag.E6) = 78 := by
  rw [Fintype.card_sum, Fintype.card_fin, card_isRoot]
  rfl

theorem finrank_fixedL :
    Module.finrank (ZMod 2) fixedL = 78 := by
  rw [Module.finrank_eq_card_basis basisL, card_label_E6]

theorem span_K_fixedL :
    Submodule.span K (fixedL : Set V) = ⊤ := by
  refine eq_top_iff.2 ((span_basisVec).ge.trans (Submodule.span_mono ?_))
  rintro _ ⟨l, rfl⟩
  exact basisVec_mem_fixedL l

@[expose] def tensorEquiv :
    TensorProduct (ZMod 2) K fixedL ≃ₗ[K] V :=
  (Algebra.TensorProduct.basis K basisL).equiv basisK (Equiv.refl _)

theorem tensorEquiv_one_tmul
    (u : fixedL) : tensorEquiv ((1 : K) ⊗ₜ u) = (u : V) := by
  have key : (tensorEquiv.toLinearMap.restrictScalars (ZMod 2)).comp
      (TensorProduct.mk (ZMod 2) K fixedL 1) = fixedL.subtype := by
    refine basisL.ext fun l => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
      LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, Submodule.subtype_apply]
    rw [basisL_apply, ← basisK_apply, ← Algebra.TensorProduct.basis_apply, tensorEquiv,
      Module.Basis.equiv_apply, Equiv.refl_apply]
  exact congrArg (fun φ => φ u) key

theorem tensorEquiv_tmul
    (c : K) (u : fixedL) : tensorEquiv (c ⊗ₜ u) = c • (u : V) := by
  rw [show c ⊗ₜ[ZMod 2] u = c • ((1 : K) ⊗ₜ[ZMod 2] u) by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, tensorEquiv_one_tmul]

theorem sqV_eq_mapRange (v : V) :
    sqV v = Finsupp.mapRange (fun x : K => x ^ 2) (zero_pow two_ne_zero) v := rfl

theorem fixedMap_bracket (u v : V) :
    fixedMap (bracket K u v) = bracket K (fixedMap u) (fixedMap v) := by
  rw [fixedMap, fixedMap, fixedMap, sqV_eq_mapRange, sqV_eq_mapRange, sqV_eq_mapRange,
    sq_bracket]
  exact diagramMap_bracket _ _

theorem form_fixedMap (u v : V) : form K (fixedMap u) (fixedMap v) = form K u v ^ 2 := by
  rw [fixedMap, fixedMap]
  have h := diagramMap_form (sqV u) (sqV v)
  rw [← sq_form]
  exact h

theorem bracket_mem_fixedL {u v : V} (hu : u ∈ fixedL) (hv : v ∈ fixedL) :
    bracket K u v ∈ fixedL := by
  rw [mem_fixedL, fixedMap_bracket, hu, hv]

@[expose] def bracketL (u v : fixedL) : fixedL := ⟨bracket K u v, bracket_mem_fixedL u.2 v.2⟩

theorem form_sq_eq (u v : fixedL) : form K u v ^ 2 = form K u v := by
  rw [← form_fixedMap, u.2, v.2]

theorem form_smul_left_zmod (c : ZMod 2) (u v : V) : form K (c • u) v = c • form K u v := by
  rw [← algebraMap_smul K c u, map_smul, LinearMap.smul_apply, smul_eq_mul, Algebra.smul_def]

theorem form_smul_right_zmod (c : ZMod 2) (u v : V) : form K u (c • v) = c • form K u v := by
  rw [← algebraMap_smul K c v, map_smul, smul_eq_mul, Algebra.smul_def]

@[expose] def formL : LinearMap.BilinForm (ZMod 2) fixedL :=
  LinearMap.mk₂ (ZMod 2) (fun u v => t0 (form K u v))
    (fun u u' v => by
      simp only [Submodule.coe_add, map_add, LinearMap.add_apply, t0_add])
    (fun c u v => by
      simp only [Submodule.coe_smul, form_smul_left_zmod, t0_smul, smul_eq_mul])
    (fun u v v' => by simp only [Submodule.coe_add, map_add, t0_add])
    (fun c u v => by
      simp only [Submodule.coe_smul, form_smul_right_zmod, t0_smul, smul_eq_mul])

theorem formL_apply (u v : fixedL) : formL u v = t0 (form K u v) := rfl

theorem algebraMap_formL (u v : fixedL) : algebraMap (ZMod 2) K (formL u v) = form K u v :=
  algebraMap_t0 (form_sq_eq u v)

theorem t0_zero : t0 (0 : K) = 0 := by
  rw [show (0 : K) = algebraMap (ZMod 2) K 0 from (map_zero _).symm, t0_coe]

theorem formL_self
    (u : fixedL) : formL u u = 0 := by
  rw [formL_apply, form_self, t0_zero]

theorem formL_bracketL
    (u v w : fixedL) : formL (bracketL u v) w = formL u (bracketL v w) := by
  rw [formL_apply, formL_apply]
  exact congrArg t0 (form_bracket (u : V) v w)

theorem form_eq_zero_of_forall
    {u : V} (hu : ∀ v ∈ fixedL, form K u v = 0) (w : V) :
    form K u w = 0 := by
  have hw : w ∈ Submodule.span K (fixedL : Set V) := span_K_fixedL ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact hu x hx
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

theorem formL_nondegenerate :
    formL.Nondegenerate := by
  refine ⟨fun u hu => ?_, fun v hv => ?_⟩
  · refine Subtype.ext (form_separatingLeft (R := K) _ fun w => ?_)
    refine form_eq_zero_of_forall (fun x hx => ?_) w
    rw [← algebraMap_formL u ⟨x, hx⟩, hu, map_zero]
  · refine Subtype.ext (form_separatingLeft (R := K) _ fun w => ?_)
    refine form_eq_zero_of_forall (fun x hx => ?_) w
    rw [form_comm, ← algebraMap_formL ⟨x, hx⟩ v, hv, map_zero]

theorem sqV_apply_end (A : Module.End K V) (v : V) :
    sqV (A v) = entrywise barHom A (sqV v) :=
  (entrywise_apply_mapRange barHom A v).symm

abbrev gEnd
    (g : stdGroup) : Module.End K V := ((g : ModGL Tag.E6 K) : Module.End K V)

theorem twistHom_stdGroup
    (g : stdGroup) : twistHom TwistTag.E6 K barHom g.1 = g.1 :=
  ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).1
    (graphFixedRootGroup_le _ _ _ g.2)).2

theorem fixedMap_stdGroup
    (g : stdGroup) (v : V) : fixedMap (gEnd g v) = gEnd g (fixedMap v) := by
  have h := twistHom_stdGroup g
  rw [twistHom_eq_conj] at h
  have h' : diagE6GL * betaGL g.1 = g.1 * diagE6GL := by
    rw [← mul_inv_eq_iff_eq_mul]
    exact h
  rw [fixedMap, fixedMap, sqV_apply_end]
  have := congrArg (fun A : ModGL Tag.E6 K => (A : Module.End K V) (sqV v)) h'
  exact this

theorem stdGroup_mem_fixedL
    (g : stdGroup) {u : V} (hu : u ∈ fixedL) : gEnd g u ∈ fixedL := by
  rw [mem_fixedL, fixedMap_stdGroup, hu]

theorem stdGroup_mem_adjointGroup
    (g : stdGroup) : g.1 ∈ adjointGroup Tag.E6 K :=
  ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).1
    (graphFixedRootGroup_le _ _ _ g.2)).1

theorem eq_of_forall_mem_fixedL
    {g h : stdGroup} (H : ∀ u ∈ fixedL, gEnd g u = gEnd h u) :
    g = h := by
  have hl : gEnd g = gEnd h :=
    basisK.ext fun l => by rw [basisK_apply]; exact H _ (basisVec_mem_fixedL l)
  exact Subtype.ext (Units.ext hl)

theorem fixedMap_sqV (v : V) : fixedMap (sqV v) = sqV (fixedMap v) := by
  ext l
  rw [fixedMap_apply, sqV_apply, sqV_apply, fixedMap_apply]

theorem sqV_mem_fixedL {u : V} (hu : u ∈ fixedL) : sqV u ∈ fixedL := by
  rw [mem_fixedL, fixedMap_sqV, hu]

theorem sqV_gEnd
    (g : stdGroup) (v : V) : sqV (gEnd g v) = gEnd (betaG g) (sqV v) := by
  rw [sqV_apply_end]
  rfl

open _root_.Classical in
@[expose] def sigmaPow
    (b : betaGroup) (v : V) : V :=
  if (b : MulAut stdGroup) = 1 then v else sqV v

theorem sigmaPow_of_eq_one
    {b : betaGroup} (h : (b : MulAut stdGroup) = 1) (v : V) :
    sigmaPow b v = v := by
  rw [sigmaPow, ite_eq_left h]

theorem sigmaPow_of_eq_betaG
    {b : betaGroup} (h : (b : MulAut stdGroup) = betaG) (v : V) :
    sigmaPow b v = sqV v := by
  rw [sigmaPow, ite_eq_right (by rw [h]; exact betaG_ne_one)]

theorem sigmaPow_mul
    (b b' : betaGroup) (v : V) :
    sigmaPow (b * b') v = sigmaPow b (sigmaPow b' v) := by
  rcases mem_betaGroup_iff.mp b.2 with h | h <;> rcases mem_betaGroup_iff.mp b'.2 with h' | h'
  · rw [sigmaPow_of_eq_one (by rw [Subgroup.coe_mul, h, h', one_mul]), sigmaPow_of_eq_one h,
      sigmaPow_of_eq_one h']
  · rw [sigmaPow_of_eq_betaG (by rw [Subgroup.coe_mul, h, h', one_mul]), sigmaPow_of_eq_one h,
      sigmaPow_of_eq_betaG h']
  · rw [sigmaPow_of_eq_betaG (by rw [Subgroup.coe_mul, h, h', mul_one]),
      sigmaPow_of_eq_betaG h, sigmaPow_of_eq_one h']
  · rw [sigmaPow_of_eq_one (by rw [Subgroup.coe_mul, h, h', betaG_mul_self]),
      sigmaPow_of_eq_betaG h, sigmaPow_of_eq_betaG h', sqV_sqV]

theorem sigmaPow_gEnd
    (b : betaGroup) (g : stdGroup) (v : V) :
    sigmaPow b (gEnd g v) = gEnd ((b : MulAut stdGroup) g) (sigmaPow b v) := by
  rcases mem_betaGroup_iff.mp b.2 with h | h
  · rw [sigmaPow_of_eq_one h, sigmaPow_of_eq_one h, h]
    rfl
  · rw [sigmaPow_of_eq_betaG h, sigmaPow_of_eq_betaG h, h, sqV_gEnd]

theorem sigmaPow_mem
    (b : betaGroup) {u : V} (hu : u ∈ fixedL) : sigmaPow b u ∈ fixedL := by
  rcases mem_betaGroup_iff.mp b.2 with h | h
  · rwa [sigmaPow_of_eq_one h]
  · rw [sigmaPow_of_eq_betaG h]
    exact sqV_mem_fixedL hu

@[expose] def actV
    (γ : GStar) (v : V) : V := gEnd γ.left (sigmaPow γ.right v)

theorem actV_mul
    (γ γ' : GStar) (v : V) : actV (γ * γ') v = actV γ (actV γ' v) := by
  simp only [actV, SemidirectProduct.mul_left, SemidirectProduct.mul_right]
  rw [sigmaPow_mul, sigmaPow_gEnd]
  rfl

theorem actV_one
    (v : V) : actV 1 v = v := by
  rw [actV, SemidirectProduct.one_left, SemidirectProduct.one_right,
    sigmaPow_of_eq_one (by rfl)]
  rfl

theorem actV_mem
    (γ : GStar) {u : V} (hu : u ∈ fixedL) : actV γ u ∈ fixedL :=
  stdGroup_mem_fixedL _ (sigmaPow_mem _ hu)

@[expose] def actL
    (γ : GStar) (u : fixedL) : fixedL := ⟨actV γ u, actV_mem γ u.2⟩

theorem actL_mul
    (γ γ' : GStar) (u : fixedL) : actL (γ * γ') u = actL γ (actL γ' u) :=
  Subtype.ext (actV_mul γ γ' u)

theorem actL_one
    (u : fixedL) : actL 1 u = u := Subtype.ext (actV_one u)

@[expose] def actStar :
    GStar →* Equiv.Perm fixedL where
  toFun γ :=
    { toFun := actL γ
      invFun := actL γ⁻¹
      left_inv := fun u => by rw [← actL_mul, inv_mul_cancel, actL_one]
      right_inv := fun u => by rw [← actL_mul, mul_inv_cancel, actL_one] }
  map_one' := Equiv.ext actL_one
  map_mul' γ γ' := Equiv.ext fun u => actL_mul γ γ' u

theorem coe_actStar_apply
    (γ : GStar) (u : fixedL) :
    (actStar γ u : V) = gEnd γ.left (sigmaPow γ.right u) := rfl

theorem actStar_inl
    (g : stdGroup) (u : fixedL) :
    (actStar (SemidirectProduct.inl g) u : V) = gEnd g u := by
  rw [coe_actStar_apply, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
    sigmaPow_of_eq_one (by rfl)]

abbrev betaB :
    betaGroup := ⟨betaG, Subgroup.mem_zpowers betaG⟩

theorem actStar_inr_betaB
    (u : fixedL) :
    (actStar (SemidirectProduct.inr betaB) u : V) = sqV u := by
  rw [coe_actStar_apply, SemidirectProduct.left_inr, SemidirectProduct.right_inr,
    sigmaPow_of_eq_betaG rfl]
  rfl

theorem gEnd_betaG
    (g : stdGroup) (v : V) : gEnd (betaG g) v = sqV (gEnd g (sqV v)) := by
  rw [sqV_gEnd, sqV_sqV]

theorem gEnd_mul
    (x y : stdGroup) : gEnd (x * y) = gEnd x * gEnd y := rfl

theorem gEnd_one_apply
    (v : V) : gEnd 1 v = v := rfl

theorem actStar_injective :
    Function.Injective actStar := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  have htriv : ∀ u ∈ fixedL, gEnd γ.left (sigmaPow γ.right u) = u := fun u hu =>
    congrArg Subtype.val (Equiv.ext_iff.1 hγ ⟨u, hu⟩)
  rcases mem_betaGroup_iff.mp γ.right.2 with h | h
  · have hl : γ.left = 1 := eq_of_forall_mem_fixedL fun u hu => by
      have := htriv u hu
      rw [sigmaPow_of_eq_one h u] at this
      rw [this, gEnd_one_apply]
    exact SemidirectProduct.ext hl (Subtype.ext h)
  · exfalso
    set n := γ.left
    have hσ : ∀ u ∈ fixedL, gEnd n (sqV u) = u := fun u hu => by
      rw [← sigmaPow_of_eq_betaG h u]
      exact htriv u hu
    have hσ' : ∀ u ∈ fixedL, sqV u = gEnd n⁻¹ u := fun u hu => by
      have := congrArg (gEnd n⁻¹) (hσ u hu)
      rwa [← Module.End.mul_apply, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
        Subgroup.coe_one, Units.val_one, Module.End.one_apply] at this
    have hn : n⁻¹ = n := by
      have hsq : n⁻¹ * n⁻¹ = 1 := eq_of_forall_mem_fixedL fun u hu => by
        have h1 := hσ' (sqV u) (sqV_mem_fixedL hu)
        rw [sqV_sqV, hσ' u hu] at h1
        rw [gEnd_mul, Module.End.mul_apply, ← h1, gEnd_one_apply]
      have := mul_eq_one_iff_eq_inv.1 hsq
      rwa [inv_inv] at this
    have hβ : ∀ x : stdGroup, betaG x = n⁻¹ * x * n := fun x =>
      eq_of_forall_mem_fixedL fun u hu => by
        rw [gEnd_betaG, hσ' u hu, hσ' _ (stdGroup_mem_fixedL x (stdGroup_mem_fixedL _ hu))]
        conv_lhs => rw [show gEnd n⁻¹ u = gEnd n u by rw [hn]]
        rfl
    exact betaG_ne_conj n⁻¹ (MulEquiv.ext fun x => by
      rw [hβ x, MulAut.conj_apply, inv_inv])

@[expose] def FixedLabel : Label Tag.E6 → Prop
  | .inl i => rhoE6 i = i
  | .inr α => permLattice rhoE6 α.1 = α.1

instance : DecidablePred FixedLabel := fun l => by
  cases l <;> unfold FixedLabel <;> infer_instance

theorem labelRho_eq_iff_fixedLabel (l : Label Tag.E6) : labelRho l = l ↔ FixedLabel l := by
  rcases l with i | α
  · rw [labelRho_inl]
    exact ⟨fun h => Sum.inl_injective h, fun h => by rw [show rhoE6 i = i from h]⟩
  · rw [labelRho_inr]
    exact ⟨fun h => congrArg Subtype.val (Sum.inr_injective h),
      fun h => congrArg Sum.inr (Subtype.ext h)⟩

set_option maxRecDepth 20000 in
theorem card_fixedLabel :
    (Finset.univ.filter FixedLabel).card = 26 := by
  have h : (∑ i : Fin Tag.E6.rank, if FixedLabel (Sum.inl i) then 1 else 0) +
      ∑ v ∈ rootFinset Tag.E6, (if permLattice rhoE6 v = v then 1 else 0) = 26 := by
    decide +kernel
  rw [Finset.sum_subtype (F := inferInstance) (rootFinset Tag.E6) (fun _ => mem_rootFinset)] at h
  rw [Finset.card_filter, Fintype.sum_sum_type]
  exact h

set_option maxRecDepth 20000 in
theorem card_not_fixedLabel :
    (Finset.univ.filter fun l => ¬FixedLabel l).card = 52 := by
  have h : (∑ i : Fin Tag.E6.rank, if ¬FixedLabel (Sum.inl i) then 1 else 0) +
      ∑ v ∈ rootFinset Tag.E6, (if ¬permLattice rhoE6 v = v then 1 else 0) = 52 := by
    decide +kernel
  rw [Finset.sum_subtype (F := inferInstance) (rootFinset Tag.E6) (fun _ => mem_rootFinset)] at h
  rw [Finset.card_filter, Fintype.sum_sum_type]
  exact h

theorem card_fixed_labels :
    (Finset.univ.filter fun l : Label Tag.E6 => labelRho l = l).card = 26 ∧
      (Finset.univ.filter fun l : Label Tag.E6 => labelRho l ≠ l).card = 52 := by
  simp only [labelRho_eq_iff_fixedLabel, ne_eq]
  exact ⟨card_fixedLabel, card_not_fixedLabel⟩

theorem fixed_E6_binary_adjoint_descent :
    (∀ u : V, u ∈ fixedL ↔ PV (sqV u) = u) ∧
    Module.finrank (ZMod 2) fixedL = 78 ∧
    Submodule.span K (fixedL : Set V) = ⊤ ∧
    (∃ e : TensorProduct (ZMod 2) K fixedL ≃ₗ[K] V,
      ∀ (c : K) (u : fixedL), e (c ⊗ₜ u) = c • (u : V)) ∧
    (∀ u ∈ fixedL, ∀ v ∈ fixedL, bracket K u v ∈ fixedL) ∧
    (∀ u v : fixedL, (bracketL u v : V) = bracket K u v) ∧
    (∀ u v : fixedL, algebraMap (ZMod 2) K (formL u v) = form K u v) ∧
    formL.Nondegenerate ∧ (∀ u : fixedL, formL u u = 0) ∧
    (∀ u v w : fixedL, formL (bracketL u v) w = formL u (bracketL v w)) ∧
    (∀ l : Label Tag.E6, labelRho l = l → basisVec l = Finsupp.single l 1) ∧
    (∀ l : Label Tag.E6, labelRho l ≠ l → (IsFirst l ↔ ¬IsFirst (labelRho l))) ∧
    (∀ l : Label Tag.E6, labelRho l ≠ l → IsFirst l →
      basisVec l = Finsupp.single l 1 + Finsupp.single (labelRho l) 1 ∧
      basisVec (labelRho l) = ω • Finsupp.single l 1 + ω ^ 2 • Finsupp.single (labelRho l) 1) ∧
    (Finset.univ.filter fun l : Label Tag.E6 => labelRho l = l).card = 26 ∧
    (Finset.univ.filter fun l : Label Tag.E6 => labelRho l ≠ l).card = 52 ∧
    (∀ l, (basisL l : V) = basisVec l) ∧
    (∀ (g : stdGroup) (u : V), u ∈ fixedL → gEnd g u ∈ fixedL) ∧
    (∀ (g : stdGroup) (u v : V), gEnd g (bracket K u v) = bracket K (gEnd g u) (gEnd g v) ∧
      form K (gEnd g u) (gEnd g v) = form K u v) ∧
    (∀ (g : stdGroup) (u : fixedL), (actStar (SemidirectProduct.inl g) u : V) = gEnd g u) ∧
    (∀ u : fixedL, (actStar (SemidirectProduct.inr betaB) u : V) = sqV u) ∧
    Function.Injective (actStar.comp SemidirectProduct.inl) ∧ Function.Injective actStar := by
  refine ⟨fun u => Iff.rfl, finrank_fixedL, span_K_fixedL, ⟨tensorEquiv, tensorEquiv_tmul⟩,
    fun u hu v hv => bracket_mem_fixedL hu hv, fun u v => rfl, algebraMap_formL,
    formL_nondegenerate, formL_self, formL_bracketL, fun l h => basisVec_of_fixed h,
    fun l h => isFirst_iff_not_isFirst h, fun l h hf => ?_, card_fixed_labels.1,
    card_fixed_labels.2, basisL_apply, fun g u hu => stdGroup_mem_fixedL g hu,
    fun g u v => ⟨adjointGroup_bracket (stdGroup_mem_adjointGroup g) u v,
      adjointGroup_form (stdGroup_mem_adjointGroup g) u v⟩, actStar_inl, actStar_inr_betaB,
    actStar_injective.comp SemidirectProduct.inl_injective, actStar_injective⟩
  have h' : labelRho (labelRho l) ≠ labelRho l := labelRho_ne_iff.2 h
  refine ⟨basisVec_of_first h hf, ?_⟩
  rw [basisVec_of_second h' ((isFirst_iff_not_isFirst h).1 hf), labelRho_labelRho]

end CFSG.Monster.B.E6.FixedE6
