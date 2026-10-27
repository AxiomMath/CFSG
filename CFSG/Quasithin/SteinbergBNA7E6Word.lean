module

public import CFSG.Quasithin.SteinbergBNA7Transvection
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSectionRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public noncomputable section

namespace CFSG.Quasithin.SteinbergBN

open scoped Pointwise

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}

@[expose] def tripleHom (X : Fin 3 → V) (hX : Function.Injective X) :
    MulAction.stabilizer (LinearMap.GeneralLinearGroup (ZMod 2) V) (Set.range X) →*
      Equiv.Perm (Fin 3) :=
  (Equiv.ofInjective X hX).symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom _ _)

theorem tripleHom_spec (X : Fin 3 → V) (hX : Function.Injective X)
    (g : MulAction.stabilizer (LinearMap.GeneralLinearGroup (ZMod 2) V) (Set.range X))
    (k : Fin 3) :
    X (tripleHom X hX g k) =
      ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) (X k) := by
  simp only [tripleHom, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_symm, MulAction.toPermHom_apply,
    MulAction.toPerm_apply, Equiv.apply_ofInjective_symm hX]
  rfl

theorem tripleHom_eq_iff (X : Fin 3 → V) (hX : Function.Injective X)
    (g : MulAction.stabilizer (LinearMap.GeneralLinearGroup (ZMod 2) V) (Set.range X))
    (σ : Equiv.Perm (Fin 3)) :
    tripleHom X hX g = σ ↔
      ∀ k, ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) (X k) = X (σ k) := by
  constructor
  · rintro rfl k
    exact (tripleHom_spec X hX g k).symm
  · intro h
    exact Equiv.ext fun k => hX ((tripleHom_spec X hX g k).trans (h k))

theorem mem_stabilizer_range_of_involution {g : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hg : g * g = 1) {X : Fin 3 → V} (h : ∀ k, ∃ l, (g : V →ₗ[ZMod 2] V) (X k) = X l) :
    g ∈ MulAction.stabilizer (LinearMap.GeneralLinearGroup (ZMod 2) V) (Set.range X) := by
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
    obtain ⟨l, hl⟩ := h k
    exact ⟨l, hl.symm⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨l, hl⟩ := h k
    refine ⟨X l, ⟨l, rfl⟩, ?_⟩
    rw [← hl]
    change ((g * g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) (X k) = X k
    rw [hg]
    rfl

theorem perm_three_mem_closure (K : Subgroup (Equiv.Perm (Fin 3)))
    (h12 : Equiv.swap 1 2 ∈ K) (h02 : Equiv.swap 0 2 ∈ K) (σ : Equiv.Perm (Fin 3)) : σ ∈ K := by
  have hσ : ∀ σ : Equiv.Perm (Fin 3), σ = 1 ∨ σ = Equiv.swap 1 2 ∨ σ = Equiv.swap 0 2 ∨
      σ = Equiv.swap 1 2 * Equiv.swap 0 2 ∨ σ = Equiv.swap 0 2 * Equiv.swap 1 2 ∨
      σ = Equiv.swap 1 2 * Equiv.swap 0 2 * Equiv.swap 1 2 := by decide
  rcases hσ σ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact K.one_mem
  · exact h12
  · exact h02
  · exact K.mul_mem h12 h02
  · exact K.mul_mem h02 h12
  · exact K.mul_mem (K.mul_mem h12 h02) h12

theorem pair_span_eq_zero {S T : Set V} (h : ∀ x ∈ S, ∀ y ∈ T, β x y = 0) :
    ∀ x ∈ Submodule.span (ZMod 2) S, ∀ y ∈ Submodule.span (ZMod 2) T, β x y = 0 := by
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => exact map_zero _
    | add y y' _ _ h1 h2 => rw [map_add, h1, h2, add_zero]
    | smul c y _ h1 => rw [map_smul, h1, smul_zero]
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add x x' _ _ h1 h2 => rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
  | smul c x _ h1 => rw [map_smul, LinearMap.smul_apply, h1, smul_zero]

theorem fix_span {g : V →ₗ[ZMod 2] V} {S : Set V} (h : ∀ x ∈ S, g x = x) :
    ∀ x ∈ Submodule.span (ZMod 2) S, g x = x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact map_zero g
  | add x x' _ _ h1 h2 => rw [map_add, h1, h2]
  | smul c x _ h1 => rw [map_smul, h1]

theorem gl_eq_one_of_fix {g : LinearMap.GeneralLinearGroup (ZMod 2) V} {U W : Submodule (ZMod 2) V}
    (hUW : U ⊔ W = ⊤) (hU : ∀ x ∈ U, (g : V →ₗ[ZMod 2] V) x = x)
    (hW : ∀ x ∈ W, (g : V →ₗ[ZMod 2] V) x = x) : g = 1 := by
  refine Units.ext (LinearMap.ext fun x => ?_)
  have hx : x ∈ U ⊔ W := hUW ▸ Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add, hU u hu, hW w hw]
  rfl

theorem fin3_cases {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ k, P k := by
  intro k
  fin_cases k
  exacts [h0, h1, h2]

section Plane

variable (hβ : β.IsAlt) {p q : V}

theorem triple_injective (hβ : β.IsAlt) (hpq : β p q = 1) :
    Function.Injective ![p, q, p + q] := by
  have hp : p ≠ 0 := by
    rintro rfl
    simp at hpq
  have hq : q ≠ 0 := by
    rintro rfl
    simp at hpq
  have hne : p ≠ q := by
    rintro rfl
    rw [hβ.self_eq_zero] at hpq
    exact zero_ne_one hpq
  intro k l h
  fin_cases k <;> fin_cases l <;> simp_all

theorem transv_triple_left (hpq : β p q = 1) (k : Fin 3) :
    (transv hβ p : V →ₗ[ZMod 2] V) (![p, q, p + q] k) = ![p, q, p + q] (Equiv.swap 1 2 k) := by
  have h0 := transv_apply_self hβ p
  have h1 : (transv hβ p : V →ₗ[ZMod 2] V) q = p + q := by
    rw [transv_apply, hpq, one_smul, add_comm]
  have h2 : (transv hβ p : V →ₗ[ZMod 2] V) (p + q) = q := by
    rw [transv_apply, map_add, hβ.self_eq_zero, hpq, zero_add, one_smul, add_comm p q, add_assoc,
      zmod_two_add_self, add_zero]
  revert k
  refine fin3_cases ?_ ?_ ?_
  · rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    exact h0
  · rw [Equiv.swap_apply_left]
    exact h1
  · rw [Equiv.swap_apply_right]
    exact h2

theorem transv_triple_right (hpq : β p q = 1) (k : Fin 3) :
    (transv hβ q : V →ₗ[ZMod 2] V) (![p, q, p + q] k) = ![p, q, p + q] (Equiv.swap 0 2 k) := by
  have hqp : β q p = 1 := (isAlt_apply_comm hβ q p).trans hpq
  have h0 : (transv hβ q : V →ₗ[ZMod 2] V) p = p + q := by
    rw [transv_apply, hqp, one_smul]
  have h1 := transv_apply_self hβ q
  have h2 : (transv hβ q : V →ₗ[ZMod 2] V) (p + q) = p := by
    rw [transv_apply, map_add, hβ.self_eq_zero, hqp, add_zero, one_smul, add_assoc,
      zmod_two_add_self, add_zero]
  revert k
  refine fin3_cases ?_ ?_ ?_
  · rw [Equiv.swap_apply_left]
    exact h0
  · rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    exact h1
  · rw [Equiv.swap_apply_right]
    exact h2

end Plane

section Planes

variable (hβ : β.IsAlt) (pa pb : Fin 3 → V)

@[expose] def triples (i : Fin 3) : Fin 3 → V := ![pa i, pb i, pa i + pb i]

@[expose] def factor (i : Fin 3) : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
  Subgroup.closure {transv hβ (pa i), transv hβ (pb i)}

@[expose] def tripleStab : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
  ⨅ i, MulAction.stabilizer (LinearMap.GeneralLinearGroup (ZMod 2) V) (Set.range (triples pa pb i))

@[expose] def prodGroup : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
  factor hβ pa pb 0 ⊔ factor hβ pa pb 1 ⊔ factor hβ pa pb 2

variable {pa pb} (h1 : ∀ i, β (pa i) (pb i) = 1)
  (h2 : ∀ i j, i ≠ j → β (pa i) (pa j) = 0 ∧ β (pa i) (pb j) = 0 ∧ β (pb i) (pa j) = 0 ∧
    β (pb i) (pb j) = 0)

@[expose] def planeHom :
    tripleStab pa pb →* (Fin 3 → Equiv.Perm (Fin 3)) :=
  MonoidHom.pi fun j => (tripleHom (triples pa pb j) (triple_injective hβ (h1 j))).comp
    (Subgroup.inclusion (iInf_le (fun i => MulAction.stabilizer
      (LinearMap.GeneralLinearGroup (ZMod 2) V) (Set.range (triples pa pb i))) j))

include h1 in
theorem planeHom_apply_eq_iff (g : tripleStab pa pb) (j : Fin 3) (σ : Equiv.Perm (Fin 3)) :
    planeHom hβ h1 g j = σ ↔ ∀ k, ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) (triples pa pb j k) = triples pa pb j (σ k) :=
  tripleHom_eq_iff _ _ _ σ

include h1 in
theorem planeHom_spec (g : tripleStab pa pb) (j k : Fin 3) :
    triples pa pb j (planeHom hβ h1 g j k) = ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) (triples pa pb j k) :=
  tripleHom_spec _ _ _ k

include h2 in
theorem transv_pa_triples_of_ne {i j : Fin 3} (hij : i ≠ j) (k : Fin 3) :
    (transv hβ (pa i) : V →ₗ[ZMod 2] V) (triples pa pb j k) = triples pa pb j k := by
  obtain ⟨ha, hb, -, -⟩ := h2 i j hij
  apply transv_apply_of_orth hβ
  fin_cases k <;> simp [triples, ha, hb]

include h2 in
theorem transv_pb_triples_of_ne {i j : Fin 3} (hij : i ≠ j) (k : Fin 3) :
    (transv hβ (pb i) : V →ₗ[ZMod 2] V) (triples pa pb j k) = triples pa pb j k := by
  obtain ⟨-, -, ha, hb⟩ := h2 i j hij
  apply transv_apply_of_orth hβ
  fin_cases k <;> simp [triples, ha, hb]

include h1 h2 in
theorem transv_pa_mem_tripleStab (i : Fin 3) : transv hβ (pa i) ∈ tripleStab pa pb := by
  refine Subgroup.mem_iInf.2 fun j => mem_stabilizer_range_of_involution
    (transv_mul_self hβ _) fun k => ?_
  by_cases hij : i = j
  · subst hij
    exact ⟨_, transv_triple_left hβ (h1 i) k⟩
  · exact ⟨k, transv_pa_triples_of_ne hβ h2 hij k⟩

include h1 h2 in
theorem transv_pb_mem_tripleStab (i : Fin 3) : transv hβ (pb i) ∈ tripleStab pa pb := by
  refine Subgroup.mem_iInf.2 fun j => mem_stabilizer_range_of_involution
    (transv_mul_self hβ _) fun k => ?_
  by_cases hij : i = j
  · subst hij
    exact ⟨_, transv_triple_right hβ (h1 i) k⟩
  · exact ⟨k, transv_pb_triples_of_ne hβ h2 hij k⟩

include h1 h2 in
theorem factor_le_tripleStab (i : Fin 3) : factor hβ pa pb i ≤ tripleStab pa pb := by
  rw [factor, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact transv_pa_mem_tripleStab hβ h1 h2 i
  · exact transv_pb_mem_tripleStab hβ h1 h2 i

theorem factor_le_prodGroup (i : Fin 3) : factor hβ pa pb i ≤ prodGroup hβ pa pb := by
  fin_cases i
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

include h1 h2 in
theorem prodGroup_le_tripleStab : prodGroup hβ pa pb ≤ tripleStab pa pb :=
  sup_le (sup_le (factor_le_tripleStab hβ h1 h2 0) (factor_le_tripleStab hβ h1 h2 1))
    (factor_le_tripleStab hβ h1 h2 2)

include h2 in
theorem factor_le_fixingSubgroup_plane {i j : Fin 3} (hij : i ≠ j) :
    factor hβ pa pb i ≤ fixingSubgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)
      (Submodule.span (ZMod 2) {pa j, pb j} : Set V) := by
  obtain ⟨haa, hab, hba, hbb⟩ := h2 i j hij
  rw [factor, Subgroup.closure_le]
  rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, mem_fixingSubgroup_iff] <;> intro x hx <;>
    apply transv_apply_of_orth hβ
  · refine pair_span_eq_zero (S := {pa i}) ?_ _ (Submodule.subset_span rfl) x hx
    rintro _ rfl _ (rfl | rfl)
    · exact haa
    · exact hab
  · refine pair_span_eq_zero (S := {pb i}) ?_ _ (Submodule.subset_span rfl) x hx
    rintro _ rfl _ (rfl | rfl)
    · exact hba
    · exact hbb

theorem factor_le_fixingSubgroup (W : Submodule (ZMod 2) V)
    (hW : ∀ i, ∀ x ∈ W, β (pa i) x = 0 ∧ β (pb i) x = 0) (i : Fin 3) :
    factor hβ pa pb i ≤ fixingSubgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) (W : Set V) := by
  rw [factor, Subgroup.closure_le]
  rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, mem_fixingSubgroup_iff] <;> intro x hx
  · exact transv_apply_of_orth hβ (hW i x hx).1
  · exact transv_apply_of_orth hβ (hW i x hx).2

theorem prodGroup_le_fixingSubgroup (W : Submodule (ZMod 2) V)
    (hW : ∀ i, ∀ x ∈ W, β (pa i) x = 0 ∧ β (pb i) x = 0) :
    prodGroup hβ pa pb ≤ fixingSubgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) (W : Set V) :=
  sup_le (sup_le (factor_le_fixingSubgroup hβ W hW 0) (factor_le_fixingSubgroup hβ W hW 1))
    (factor_le_fixingSubgroup hβ W hW 2)

include h1 h2 in
theorem planeHom_transv_pa (i : Fin 3) :
    planeHom hβ h1 ⟨transv hβ (pa i), transv_pa_mem_tripleStab hβ h1 h2 i⟩ =
      Pi.mulSingle i (Equiv.swap 1 2) := by
  funext j
  rw [planeHom_apply_eq_iff]
  intro k
  by_cases hij : j = i
  · subst hij
    rw [Pi.mulSingle_eq_same]
    exact transv_triple_left hβ (h1 j) k
  · rw [Pi.mulSingle_eq_of_ne hij, Equiv.Perm.one_apply]
    exact transv_pa_triples_of_ne hβ h2 (Ne.symm hij) k

include h1 h2 in
theorem planeHom_transv_pb (i : Fin 3) :
    planeHom hβ h1 ⟨transv hβ (pb i), transv_pb_mem_tripleStab hβ h1 h2 i⟩ =
      Pi.mulSingle i (Equiv.swap 0 2) := by
  funext j
  rw [planeHom_apply_eq_iff]
  intro k
  by_cases hij : j = i
  · subst hij
    rw [Pi.mulSingle_eq_same]
    exact transv_triple_right hβ (h1 j) k
  · rw [Pi.mulSingle_eq_of_ne hij, Equiv.Perm.one_apply]
    exact transv_pb_triples_of_ne hβ h2 (Ne.symm hij) k

include h1 h2 in
theorem planeHom_factor_of_ne {i j : Fin 3} (hij : j ≠ i) {g : LinearMap.GeneralLinearGroup
    (ZMod 2) V} (hg : g ∈ factor hβ pa pb i) :
    planeHom hβ h1 ⟨g, factor_le_tripleStab hβ h1 h2 i hg⟩ j = 1 := by
  let φ : tripleStab pa pb →* Equiv.Perm (Fin 3) := (Pi.evalMonoidHom _ j).comp (planeHom hβ h1)
  have hle : factor hβ pa pb i ≤ φ.ker.map (tripleStab pa pb).subtype := by
    rw [factor, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · refine ⟨⟨_, transv_pa_mem_tripleStab hβ h1 h2 i⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      change planeHom hβ h1 _ j = 1
      rw [planeHom_transv_pa hβ h1 h2, Pi.mulSingle_eq_of_ne hij]
    · refine ⟨⟨_, transv_pb_mem_tripleStab hβ h1 h2 i⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      change planeHom hβ h1 _ j = 1
      rw [planeHom_transv_pb hβ h1 h2, Pi.mulSingle_eq_of_ne hij]
  obtain ⟨g', hg', rfl⟩ := hle hg
  exact hg'

include h1 h2 in
theorem planeHom_factor {i : Fin 3} {g : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hg : g ∈ factor hβ pa pb i) :
    planeHom hβ h1 ⟨g, factor_le_tripleStab hβ h1 h2 i hg⟩ =
      Pi.mulSingle i (planeHom hβ h1 ⟨g, factor_le_tripleStab hβ h1 h2 i hg⟩ i) := by
  funext j
  by_cases hij : j = i
  · subst hij
    rw [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hij, planeHom_factor_of_ne hβ h1 h2 hij hg]

include h1 in
theorem eq_one_of_planeHom_eq_one {W : Submodule (ZMod 2) V}
    (hspan : Submodule.span (ZMod 2) (Set.range pa ∪ Set.range pb) ⊔ W = ⊤)
    (g : tripleStab pa pb) (hg : planeHom hβ h1 g = 1)
    (hgW : ∀ x ∈ W, ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) x = x) :
    g = 1 := by
  have hfix : ∀ j k, ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
      (triples pa pb j k) = triples pa pb j k := fun j k =>
    ((planeHom_apply_eq_iff hβ h1 g j 1).1 (congrFun hg j) k)
  refine Subtype.ext (gl_eq_one_of_fix hspan (fix_span ?_) hgW)
  rintro x (⟨j, rfl⟩ | ⟨j, rfl⟩)
  · exact hfix j 0
  · exact hfix j 1

variable (W : Submodule (ZMod 2) V)
  (hspan : Submodule.span (ZMod 2) (Set.range pa ∪ Set.range pb) ⊔ W = ⊤)
  (hW : ∀ i, ∀ x ∈ W, β (pa i) x = 0 ∧ β (pb i) x = 0)

@[expose] def prodHom : prodGroup hβ pa pb →* (Fin 3 → Equiv.Perm (Fin 3)) :=
  (planeHom hβ h1).comp (Subgroup.inclusion (prodGroup_le_tripleStab hβ h1 h2))

include h1 h2 hspan hW in
theorem prodHom_injective : Function.Injective (prodHom hβ h1 h2) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have := eq_one_of_planeHom_eq_one hβ h1 hspan
    (Subgroup.inclusion (prodGroup_le_tripleStab hβ h1 h2) g) hg fun x hx =>
      (mem_fixingSubgroup_iff _).1 (prodGroup_le_fixingSubgroup hβ W hW g.2) x hx
  have h' : (g : LinearMap.GeneralLinearGroup (ZMod 2) V) = 1 := congrArg Subtype.val this
  exact Subtype.ext h'

theorem prodHom_surjective : Function.Surjective (prodHom hβ h1 h2) := by
  rw [← MonoidHom.range_eq_top]
  have hsingle : ∀ i σ, Pi.mulSingle i σ ∈ (prodHom hβ h1 h2).range := by
    intro i
    let K : Subgroup (Equiv.Perm (Fin 3)) :=
      (prodHom hβ h1 h2).range.comap (MonoidHom.mulSingle (fun _ : Fin 3 => Equiv.Perm (Fin 3)) i)
    refine perm_three_mem_closure K ?_ ?_
    · refine ⟨⟨transv hβ (pa i), factor_le_prodGroup hβ i (Subgroup.subset_closure (Or.inl rfl))⟩,
        ?_⟩
      exact planeHom_transv_pa hβ h1 h2 i
    · refine ⟨⟨transv hβ (pb i), factor_le_prodGroup hβ i (Subgroup.subset_closure (Or.inr rfl))⟩,
        ?_⟩
      exact planeHom_transv_pb hβ h1 h2 i
  rw [eq_top_iff]
  intro f _
  have hf : f = Pi.mulSingle 0 (f 0) * Pi.mulSingle 1 (f 1) * Pi.mulSingle 2 (f 2) := by
    funext j
    fin_cases j <;> simp
  rw [hf]
  exact mul_mem (mul_mem (hsingle 0 _) (hsingle 1 _)) (hsingle 2 _)

include h1 h2 hspan hW in
theorem prodGroup_card : Nat.card (prodGroup hβ pa pb) = 216 := by
  rw [Nat.card_congr (MulEquiv.ofBijective (prodHom hβ h1 h2)
    ⟨prodHom_injective hβ h1 h2 W hspan hW, prodHom_surjective hβ h1 h2⟩).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_pi, Fintype.card_perm]
  rfl

include h1 h2 hspan hW in
theorem factor_eq_one {i : Fin 3} {g : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hg : g ∈ factor hβ pa pb i)
    (h : planeHom hβ h1 ⟨g, factor_le_tripleStab hβ h1 h2 i hg⟩ i = 1) : g = 1 := by
  have hpg := factor_le_prodGroup hβ i hg
  have key : prodHom hβ h1 h2 ⟨g, hpg⟩ = 1 := by
    change planeHom hβ h1 ⟨g, factor_le_tripleStab hβ h1 h2 i hg⟩ = 1
    rw [planeHom_factor hβ h1 h2 hg, h, Pi.mulSingle_one]
  have := prodHom_injective hβ h1 h2 W hspan hW (key.trans (map_one _).symm)
  exact congrArg Subtype.val this

include h1 h2 hspan hW in
theorem factor_equiv_perm (i : Fin 3) : Nonempty (factor hβ pa pb i ≃* Equiv.Perm (Fin 3)) := by
  let θ : factor hβ pa pb i →* Equiv.Perm (Fin 3) := (Pi.evalMonoidHom _ i).comp
    ((planeHom hβ h1).comp (Subgroup.inclusion (factor_le_tripleStab hβ h1 h2 i)))
  refine ⟨MulEquiv.ofBijective θ ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (factor_eq_one hβ h1 h2 W hspan hW g.2 hg)
  · intro σ
    let K : Subgroup (Equiv.Perm (Fin 3)) := θ.range
    have hK : σ ∈ K := by
      refine perm_three_mem_closure K ⟨⟨transv hβ (pa i), Subgroup.subset_closure (Or.inl rfl)⟩,
        ?_⟩ ⟨⟨transv hβ (pb i), Subgroup.subset_closure (Or.inr rfl)⟩, ?_⟩ σ
      · change planeHom hβ h1 ⟨transv hβ (pa i), transv_pa_mem_tripleStab hβ h1 h2 i⟩ i = _
        rw [planeHom_transv_pa hβ h1 h2, Pi.mulSingle_eq_same]
      · change planeHom hβ h1 ⟨transv hβ (pb i), transv_pb_mem_tripleStab hβ h1 h2 i⟩ i = _
        rw [planeHom_transv_pb hβ h1 h2, Pi.mulSingle_eq_same]
    exact hK

include h1 h2 hspan hW in
theorem factor_commute {i j : Fin 3} (hij : i ≠ j) {g h : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hg : g ∈ factor hβ pa pb i) (hh : h ∈ factor hβ pa pb j) : g * h = h * g := by
  have hpg := factor_le_prodGroup hβ i hg
  have hph := factor_le_prodGroup hβ j hh
  have key : prodHom hβ h1 h2 (⟨g, hpg⟩ * ⟨h, hph⟩) = prodHom hβ h1 h2 (⟨h, hph⟩ * ⟨g, hpg⟩) := by
    rw [map_mul, map_mul]
    change planeHom hβ h1 ⟨g, factor_le_tripleStab hβ h1 h2 i hg⟩ *
        planeHom hβ h1 ⟨h, factor_le_tripleStab hβ h1 h2 j hh⟩ =
      planeHom hβ h1 ⟨h, factor_le_tripleStab hβ h1 h2 j hh⟩ *
        planeHom hβ h1 ⟨g, factor_le_tripleStab hβ h1 h2 i hg⟩
    rw [planeHom_factor hβ h1 h2 hg, planeHom_factor hβ h1 h2 hh]
    exact Pi.mulSingle_commute hij _ _
  exact congrArg Subtype.val (prodHom_injective hβ h1 h2 W hspan hW key)

include h1 h2 hspan hW in
theorem factor_prod_eq_one {g₀ g₁ g₂ : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (h₀ : g₀ ∈ factor hβ pa pb 0) (h₁ : g₁ ∈ factor hβ pa pb 1) (h₂ : g₂ ∈ factor hβ pa pb 2)
    (h : g₀ * g₁ * g₂ = 1) : g₀ = 1 ∧ g₁ = 1 ∧ g₂ = 1 := by
  have key : prodHom hβ h1 h2 (⟨g₀, factor_le_prodGroup hβ 0 h₀⟩ *
      ⟨g₁, factor_le_prodGroup hβ 1 h₁⟩ * ⟨g₂, factor_le_prodGroup hβ 2 h₂⟩) = 1 := by
    have : (⟨g₀, factor_le_prodGroup hβ 0 h₀⟩ * ⟨g₁, factor_le_prodGroup hβ 1 h₁⟩ *
        ⟨g₂, factor_le_prodGroup hβ 2 h₂⟩ : prodGroup hβ pa pb) = 1 := Subtype.ext h
    rw [this, map_one]
  rw [map_mul, map_mul] at key
  change planeHom hβ h1 ⟨g₀, factor_le_tripleStab hβ h1 h2 0 h₀⟩ *
      planeHom hβ h1 ⟨g₁, factor_le_tripleStab hβ h1 h2 1 h₁⟩ *
      planeHom hβ h1 ⟨g₂, factor_le_tripleStab hβ h1 h2 2 h₂⟩ = 1 at key
  rw [planeHom_factor hβ h1 h2 h₀, planeHom_factor hβ h1 h2 h₁,
    planeHom_factor hβ h1 h2 h₂] at key
  have k0 := congrFun key 0
  have k1 := congrFun key 1
  have k2 := congrFun key 2
  simp only [Pi.mul_apply, Pi.one_apply, Pi.mulSingle_eq_same,
    Pi.mulSingle_eq_of_ne (show (1 : Fin 3) ≠ 0 by decide),
    Pi.mulSingle_eq_of_ne (show (2 : Fin 3) ≠ 0 by decide),
    Pi.mulSingle_eq_of_ne (show (0 : Fin 3) ≠ 1 by decide),
    Pi.mulSingle_eq_of_ne (show (2 : Fin 3) ≠ 1 by decide),
    Pi.mulSingle_eq_of_ne (show (0 : Fin 3) ≠ 2 by decide),
    Pi.mulSingle_eq_of_ne (show (1 : Fin 3) ≠ 2 by decide), mul_one, one_mul] at k0 k1 k2
  exact ⟨factor_eq_one hβ h1 h2 W hspan hW h₀ k0, factor_eq_one hβ h1 h2 W hspan hW h₁ k1,
    factor_eq_one hβ h1 h2 W hspan hW h₂ k2⟩

theorem triples_mem_span (i k : Fin 3) :
    triples pa pb i k ∈ Submodule.span (ZMod 2) ({pa i, pb i} : Set V) := by
  have ha : pa i ∈ Submodule.span (ZMod 2) ({pa i, pb i} : Set V) :=
    Submodule.subset_span (Or.inl rfl)
  have hb : pb i ∈ Submodule.span (ZMod 2) ({pa i, pb i} : Set V) :=
    Submodule.subset_span (Or.inr rfl)
  fin_cases k
  · exact ha
  · exact hb
  · exact Submodule.add_mem _ ha hb

include h1 h2 in
theorem factor_apply_mem_plane {i : Fin 3} {g : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hg : g ∈ factor hβ pa pb i) {x : V} (hx : x ∈ Submodule.span (ZMod 2) ({pa i, pb i} : Set V)) :
    (g : V →ₗ[ZMod 2] V) x ∈ Submodule.span (ZMod 2) ({pa i, pb i} : Set V) := by
  have hle : Submodule.span (ZMod 2) ({pa i, pb i} : Set V) ≤
      (Submodule.span (ZMod 2) ({pa i, pb i} : Set V)).comap (g : V →ₗ[ZMod 2] V) := by
    rw [Submodule.span_le]
    have hk : ∀ k, (g : V →ₗ[ZMod 2] V) (triples pa pb i k) ∈
        Submodule.span (ZMod 2) ({pa i, pb i} : Set V) := fun k => by
      rw [← planeHom_spec hβ h1 ⟨g, factor_le_tripleStab hβ h1 h2 i hg⟩ i k]
      exact triples_mem_span i _
    rintro _ (rfl | rfl)
    · exact hk 0
    · exact hk 1
  exact hle hx

include h1 h2 hspan hW in
theorem factor_faithful {i : Fin 3} {g : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hg : g ∈ factor hβ pa pb i)
    (hfix : ∀ x ∈ Submodule.span (ZMod 2) ({pa i, pb i} : Set V), (g : V →ₗ[ZMod 2] V) x = x) :
    g = 1 := by
  refine factor_eq_one hβ h1 h2 W hspan hW hg ?_
  rw [planeHom_apply_eq_iff]
  intro k
  exact hfix _ (triples_mem_span i k)

end Planes

@[expose] def e6Mat : Fin 6 → Fin 6 → ZMod 2 :=
  ![![0, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![0, 1, 0, 1, 0, 1], ![0, 0, 1, 0, 1, 0],
    ![0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0]]

theorem e6Mat_eq (i j : Fin 6) : e6Mat i j = if e6Tree.Adj i j then 1 else 0 := by
  revert i j
  decide

@[expose] def e6Form (x y : Fin 6 → ZMod 2) : ZMod 2 := ∑ i, ∑ j, x i * y j * e6Mat i j

@[expose] def e6Tr (y x : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 := x + e6Form y x • y

theorem e6Form_nondeg : ∀ x : Fin 6 → ZMod 2, (∀ j, e6Form x (Pi.single j 1) = 0) → x = 0 := by
  decide

section Config

variable (hβ : β.IsAlt) {e : Fin 6 → V} (he : pairGraph hβ e = e6Tree)
include he

theorem pair_e6 (i j : Fin 6) : β (e i) (e j) = e6Mat i j := by
  rw [e6Mat_eq]
  split_ifs with h
  · rw [← he] at h
    exact h
  · rw [← he] at h
    exact (pairGraph_not_adj hβ e).1 h

theorem pair_vec (x y : Fin 6 → ZMod 2) :
    β (Fintype.linearCombination (ZMod 2) e x) (Fintype.linearCombination (ZMod 2) e y) =
      e6Form x y := by
  simp only [Fintype.linearCombination_apply, LinearMap.BilinForm.sum_left,
    LinearMap.BilinForm.sum_right, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    pair_e6 hβ he, e6Form, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem transv_vec (x y : Fin 6 → ZMod 2) :
    (transv hβ (Fintype.linearCombination (ZMod 2) e y) : V →ₗ[ZMod 2] V)
      (Fintype.linearCombination (ZMod 2) e x) =
      Fintype.linearCombination (ZMod 2) e (e6Tr y x) := by
  rw [transv_apply, pair_vec hβ he, e6Tr, map_add, map_smul]

end Config

theorem e_eq_vec (e : Fin 6 → V) (j : Fin 6) :
    e j = Fintype.linearCombination (ZMod 2) e (Pi.single j 1) := by
  rw [Fintype.linearCombination_apply_single, one_smul]

@[expose] def e6Ga : Fin 3 → Fin 6 → ZMod 2 := ![Pi.single 0 1, Pi.single 3 1, ![1, 0, 1, 0, 1, 0]]

@[expose] def e6Gb : Fin 3 → Fin 6 → ZMod 2 := ![Pi.single 1 1, Pi.single 4 1, Pi.single 5 1]

theorem e6Form_ga_gb : ∀ i, e6Form (e6Ga i) (e6Gb i) = 1 := by
  decide

theorem e6Form_planes_orth : ∀ i j, i ≠ j → e6Form (e6Ga i) (e6Ga j) = 0 ∧
    e6Form (e6Ga i) (e6Gb j) = 0 ∧ e6Form (e6Gb i) (e6Ga j) = 0 ∧
    e6Form (e6Gb i) (e6Gb j) = 0 := by
  decide

theorem e6Tr_word :
    e6Tr (Pi.single 5 1) (e6Tr (Pi.single 2 1) (e6Tr (Pi.single 3 1) (e6Tr (Pi.single 1 1)
      (e6Tr (Pi.single 2 1) (e6Tr (Pi.single 5 1) (e6Tr (Pi.single 4 1) (e6Tr (Pi.single 3 1)
        (e6Tr (Pi.single 2 1) (e6Tr (Pi.single 1 1) (Pi.single 0 1)))))))))) =
      ![1, 0, 1, 0, 1, 0] := by
  decide

theorem e6_transvection_word_three_S3_factors [FiniteDimensional (ZMod 2) V] (hβ : β.IsAlt)
    (e : Fin 6 → V) (he : pairGraph hβ e = e6Tree) :
    let t : Fin 6 → LinearMap.GeneralLinearGroup (ZMod 2) V := fun k => transv hβ (e k)
    let N := Subgroup.closure (Set.range t)
    let U := Submodule.span (ZMod 2) (Set.range e)
    let c := e 0 + e 2 + e 4
    let w := t 5 * t 2 * t 3 * t 1 * t 2 * t 5 * t 4 * t 3 * t 2 * t 1
    let L : Fin 3 → Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
      ![Subgroup.closure {t 0, t 1}, Subgroup.closure {t 3, t 4},
        Subgroup.closure {transv hβ c, t 5}]
    let P : Fin 3 → Submodule (ZMod 2) V :=
      ![Submodule.span (ZMod 2) {e 0, e 1}, Submodule.span (ZMod 2) {e 3, e 4},
        Submodule.span (ZMod 2) {c, e 5}]
    LinearIndependent (ZMod 2) e ∧ (β.restrict U).Nondegenerate ∧
      IsCompl U (β.orthogonal U) ∧
      (w : V →ₗ[ZMod 2] V) (e 0) = c ∧ transv hβ c = w * t 0 * w⁻¹ ∧ transv hβ c ∈ N ∧
      (∀ i, Nonempty (L i ≃* Equiv.Perm (Fin 3))) ∧
      (∀ i, ∀ g ∈ L i, ∀ x ∈ β.orthogonal U, (g : V →ₗ[ZMod 2] V) x = x) ∧
      (∀ i j, i ≠ j → ∀ g ∈ L i, ∀ h ∈ L j, g * h = h * g) ∧
      (∀ g₀ ∈ L 0, ∀ g₁ ∈ L 1, ∀ g₂ ∈ L 2, g₀ * g₁ * g₂ = 1 → g₀ = 1 ∧ g₁ = 1 ∧ g₂ = 1) ∧
      L 0 ⊔ L 1 ⊔ L 2 ≤ N ∧ Nat.card ↥(L 0 ⊔ L 1 ⊔ L 2) = 216 ∧
      (∀ i j, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, β x y = 0) ∧
      (∀ i, ∀ g ∈ L i, ∀ x ∈ P i, (g : V →ₗ[ZMod 2] V) x ∈ P i) ∧
      (∀ i, ∀ g ∈ L i, (∀ x ∈ P i, (g : V →ₗ[ZMod 2] V) x = x) → g = 1) ∧
      (∀ i j, i ≠ j → ∀ g ∈ L i, ∀ x ∈ P j, (g : V →ₗ[ZMod 2] V) x = x) ∧
      ∀ (G : Type*) [Group G] [Finite G],
        (∀ E : Subgroup G, CFSG.IsElementaryAbelian 3 E → Nat.card E ≤ 9) →
        ∀ (Y : Subgroup G) (H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
          (π : Y →* H), Function.Surjective π → ¬ ∀ k, t k ∈ H := by
  intro t N U c w L P
  have hev := e_eq_vec e
  have hc : c = Fintype.linearCombination (ZMod 2) e ![1, 0, 1, 0, 1, 0] := by
    simp [c, Fintype.linearCombination_apply, Fin.sum_univ_six]
  have ht : ∀ k, t k ∈ N := fun k => Subgroup.subset_closure ⟨k, rfl⟩
  have heU : ∀ j, e j ∈ U := fun j => Submodule.subset_span ⟨j, rfl⟩
  have hsep : ∀ x ∈ U, (∀ j, β x (e j) = 0) → x = 0 := by
    intro x hx h
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hx
    have hg : g = 0 := e6Form_nondeg g fun j => by
      rw [← pair_vec hβ he, ← hev j, Fintype.linearCombination_apply]
      exact h j
    simp [hg]
  have hind : LinearIndependent (ZMod 2) e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : g = 0 := e6Form_nondeg g fun j => by
      rw [← pair_vec hβ he, ← hev j, Fintype.linearCombination_apply, hg, map_zero,
        LinearMap.zero_apply]
    intro i
    rw [h0, Pi.zero_apply]
  have hnd : (β.restrict U).Nondegenerate := by
    refine ⟨fun x hx => Subtype.ext (hsep x x.2 fun j => hx ⟨e j, heU j⟩),
      fun y hy => Subtype.ext (hsep y y.2 fun j => ?_)⟩
    rw [isAlt_apply_comm hβ]
    exact hy ⟨e j, heU j⟩
  have hcompl : IsCompl U (β.orthogonal U) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hβ.isRefl hnd
  have hiso : N ≤ isometryGroup β := (Subgroup.closure_le _).2 (by
    rintro _ ⟨k, rfl⟩
    exact transv_mem_isometryGroup hβ (e k))
  have hwN : w ∈ N := mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (mul_mem (ht 5) (ht 2)) (ht 3)) (ht 1)) (ht 2)) (ht 5)) (ht 4)) (ht 3)) (ht 2)) (ht 1)
  have hw : (w : V →ₗ[ZMod 2] V) (e 0) = c := by
    simp only [w, t, Units.val_mul, Module.End.mul_apply]
    rw [hc]
    simp only [hev]
    simp only [transv_vec hβ he]
    rw [e6Tr_word]
  have hconj : transv hβ c = w * t 0 * w⁻¹ := by
    rw [conj_transv hβ (hiso hwN), hw]
  have hcN : transv hβ c ∈ N := by
    rw [hconj]
    exact mul_mem (mul_mem hwN (ht 0)) (inv_mem hwN)
  let pa : Fin 3 → V := ![e 0, e 3, c]
  let pb : Fin 3 → V := ![e 1, e 4, e 5]
  have hpa : ∀ i, pa i = Fintype.linearCombination (ZMod 2) e (e6Ga i) := by
    intro i
    fin_cases i
    exacts [hev 0, hev 3, hc]
  have hpb : ∀ i, pb i = Fintype.linearCombination (ZMod 2) e (e6Gb i) := by
    intro i
    fin_cases i
    exacts [hev 1, hev 4, hev 5]
  have h1 : ∀ i, β (pa i) (pb i) = 1 := fun i => by
    rw [hpa, hpb, pair_vec hβ he]
    exact e6Form_ga_gb i
  have h2 : ∀ i j, i ≠ j → β (pa i) (pa j) = 0 ∧ β (pa i) (pb j) = 0 ∧ β (pb i) (pa j) = 0 ∧
      β (pb i) (pb j) = 0 := fun i j hij => by
    simp only [hpa, hpb, pair_vec hβ he]
    exact e6Form_planes_orth i j hij
  have hpaU : ∀ i, pa i ∈ U := by
    intro i
    fin_cases i
    · exact heU 0
    · exact heU 3
    · exact U.add_mem (U.add_mem (heU 0) (heU 2)) (heU 4)
  have hpbU : ∀ i, pb i ∈ U := by
    intro i
    fin_cases i
    exacts [heU 1, heU 4, heU 5]
  have hUS : U ≤ Submodule.span (ZMod 2) (Set.range pa ∪ Set.range pb) := by
    rw [Submodule.span_le]
    have ha : ∀ i, pa i ∈ Submodule.span (ZMod 2) (Set.range pa ∪ Set.range pb) := fun i =>
      Submodule.subset_span (Or.inl ⟨i, rfl⟩)
    have hb : ∀ i, pb i ∈ Submodule.span (ZMod 2) (Set.range pa ∪ Set.range pb) := fun i =>
      Submodule.subset_span (Or.inr ⟨i, rfl⟩)
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · exact ha 0
    · exact hb 0
    · have h2e : e 2 = pa 2 + pa 0 + pb 1 := by
        change e 2 = e 0 + e 2 + e 4 + e 0 + e 4
        rw [show e 0 + e 2 + e 4 + e 0 + e 4 = e 2 + (e 0 + e 0) + (e 4 + e 4) by abel,
          zmod_two_add_self, zmod_two_add_self, add_zero, add_zero]
      simp only [Fin.reduceFinMk, Fin.isValue]
      rw [h2e]
      exact Submodule.add_mem _ (Submodule.add_mem _ (ha 2) (ha 0)) (hb 1)
    · exact ha 1
    · exact hb 1
    · exact hb 2
  have hspan : Submodule.span (ZMod 2) (Set.range pa ∪ Set.range pb) ⊔ β.orthogonal U = ⊤ :=
    eq_top_iff.2 (hcompl.sup_eq_top.ge.trans (sup_le_sup_right hUS _))
  have hW : ∀ i, ∀ x ∈ β.orthogonal U, β (pa i) x = 0 ∧ β (pb i) x = 0 := fun i x hx =>
    ⟨(LinearMap.BilinForm.mem_orthogonal_iff.1 hx) _ (hpaU i),
      (LinearMap.BilinForm.mem_orthogonal_iff.1 hx) _ (hpbU i)⟩
  have hL : ∀ i, L i = factor hβ pa pb i := by
    intro i
    fin_cases i <;> rfl
  have hP : ∀ i, P i = Submodule.span (ZMod 2) ({pa i, pb i} : Set V) := by
    intro i
    fin_cases i <;> rfl
  have hprod : L 0 ⊔ L 1 ⊔ L 2 = prodGroup hβ pa pb := by
    rw [hL 0, hL 1, hL 2]
    rfl
  have hLN : ∀ i, L i ≤ N := by
    intro i
    rw [hL, factor, Subgroup.closure_le]
    fin_cases i <;> rintro _ (rfl | rfl)
    exacts [ht 0, ht 1, ht 3, ht 4, hcN, ht 5]
  refine ⟨hind, hnd, hcompl, hw, hconj, hcN, fun i => ?_, fun i g hg x hx => ?_,
    fun i j hij g hg h hh => ?_, fun g₀ h₀ g₁ h₁ g₂ h₂ h => ?_,
    sup_le (sup_le (hLN 0) (hLN 1)) (hLN 2), ?_, fun i j hij x hx y hy => ?_,
    fun i g hg x hx => ?_, fun i g hg hfix => ?_, fun i j hij g hg x hx => ?_, ?_⟩
  · rw [hL]
    exact factor_equiv_perm hβ h1 h2 _ hspan hW i
  · rw [hL] at hg
    exact (mem_fixingSubgroup_iff _).1 (factor_le_fixingSubgroup hβ _ hW i hg) x hx
  · rw [hL] at hg hh
    exact factor_commute hβ h1 h2 _ hspan hW hij hg hh
  · rw [hL] at h₀ h₁ h₂
    exact factor_prod_eq_one hβ h1 h2 _ hspan hW h₀ h₁ h₂ h
  · rw [hprod]
    exact prodGroup_card hβ h1 h2 _ hspan hW
  · rw [hP] at hx hy
    refine pair_span_eq_zero ?_ x hx y hy
    obtain ⟨haa, hab, hba, hbb⟩ := h2 i j hij
    rintro _ (rfl | rfl) _ (rfl | rfl)
    exacts [haa, hab, hba, hbb]
  · rw [hL] at hg
    rw [hP] at hx ⊢
    exact factor_apply_mem_plane hβ h1 h2 hg hx
  · rw [hL] at hg
    rw [hP] at hfix
    exact factor_faithful hβ h1 h2 _ hspan hW hg hfix
  · rw [hL] at hg
    rw [hP] at hx
    exact (mem_fixingSubgroup_iff _).1 (factor_le_fixingSubgroup_plane hβ h2 hij hg) x hx
  · intro G _ _ hG Y H π hπ hall
    have hNH : N ≤ H := (Subgroup.closure_le _).2 (by
      rintro _ ⟨k, rfl⟩
      exact hall k)
    have hLH : prodGroup hβ pa pb ≤ H := hprod ▸ (sup_le (sup_le (hLN 0) (hLN 1)) (hLN 2)).trans hNH
    let K : Subgroup Y := (prodGroup hβ pa pb).comap (H.subtype.comp π)
    let Y₀ : Subgroup G := K.map Y.subtype
    let e₁ : K ≃* Y₀ := K.equivMapOfInjective Y.subtype Y.subtype_injective
    let πK : K →* prodGroup hβ pa pb :=
      ((H.subtype.comp π).comp K.subtype).codRestrict _ fun k => k.2
    let f : Y₀ →* (Fin 3 → Equiv.Perm (Fin 3)) :=
      (prodHom hβ h1 h2).comp (πK.comp e₁.symm.toMonoidHom)
    have hf : Function.Surjective f := by
      intro σ
      obtain ⟨l, rfl⟩ := prodHom_surjective hβ h1 h2 σ
      obtain ⟨y, hy⟩ := hπ ⟨l, hLH l.2⟩
      have hyK : y ∈ K := by
        change ((π y : H) : LinearMap.GeneralLinearGroup (ZMod 2) V) ∈ prodGroup hβ pa pb
        rw [hy]
        exact l.2
      refine ⟨e₁ ⟨y, hyK⟩, ?_⟩
      change prodHom hβ h1 h2 (πK (e₁.symm (e₁ ⟨y, hyK⟩))) = prodHom hβ h1 h2 l
      rw [MulEquiv.symm_apply_apply]
      congr 1
      apply Subtype.ext
      change ((π y : H) : LinearMap.GeneralLinearGroup (ZMod 2) V) = l
      rw [hy]
    have h3 := CFSG.QuasithinUnique.Setup.Lift.sym_three_pow_section_forces_three_rank 3 Y₀ f hf
    have h2' : CFSG.pRank 3 G ≤ 2 := by
      apply csSup_le'
      rintro r ⟨A, hA, hcard⟩
      have h9 := hG A hA
      rw [hcard] at h9
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (h9.trans (by norm_num))
    omega

end CFSG.Quasithin.SteinbergBN
