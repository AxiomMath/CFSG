module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.SteinbergCD

open Matrix
open scoped Pointwise

section Defs

variable (K : Type*) [Field K]

abbrev QGSpace : Type _ := ZMod 2 × K × K × K

abbrev QGAut : Type _ := Multiplicative (AddAut (QGSpace K))

@[expose] def qgT : QGSpace K := (1, 0, 0, 0)

@[expose] def qgOmega : Set (QGSpace K) := {e | e.1 = 1 ∧ e.2.2.2 = e.2.1 * e.2.2.1}

@[expose] def qgW : AddSubgroup (QGSpace K) where
  carrier := {e | e.1 = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Prod.fst_add] at *
    rw [ha, hb, add_zero]
  zero_mem' := rfl
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, Prod.fst_neg] at *
    rw [ha, neg_zero]

@[expose] def qgZ : AddSubgroup (QGSpace K) where
  carrier := {e | e.1 = 0 ∧ e.2.1 = 0 ∧ e.2.2.1 = 0}
  add_mem' {a b} ha hb := by
    obtain ⟨ha1, ha2, ha3⟩ := ha
    obtain ⟨hb1, hb2, hb3⟩ := hb
    exact ⟨by simp [ha1, hb1], by simp [ha2, hb2], by simp [ha3, hb3]⟩
  zero_mem' := ⟨rfl, rfl, rfl⟩
  neg_mem' {a} ha := by
    obtain ⟨ha1, ha2, ha3⟩ := ha
    exact ⟨by simp [ha1], by simp [ha2], by simp [ha3]⟩

@[expose] def qgStab : Subgroup (QGAut K) where
  carrier := {α | ⇑(Multiplicative.toAdd α) '' qgOmega K = qgOmega K}
  mul_mem' {α β} hα hβ := by
    simp only [Set.mem_ofPred_eq] at *
    change (⇑(Multiplicative.toAdd α) ∘ ⇑(Multiplicative.toAdd β)) '' qgOmega K = qgOmega K
    rw [Set.image_comp, hβ, hα]
  one_mem' := by
    simp only [Set.mem_ofPred_eq]
    exact Set.image_id _
  inv_mem' {α} hα := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hα]
    rw [← Set.image_comp]
    have h : ⇑(Multiplicative.toAdd α⁻¹) ∘ ⇑(Multiplicative.toAdd α) = id :=
      funext fun e => AddAut.neg_apply_self _ _ _
    rw [h, Set.image_id]

end Defs

section Points

variable {K : Type*} [Field K]

theorem zmod_two_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

@[expose] def qgPoint (v : Fin 2 → K) : QGSpace K := (1, v 0, v 1, v 0 * v 1)

theorem qgPoint_mem (v : Fin 2 → K) : qgPoint v ∈ qgOmega K := ⟨rfl, rfl⟩

theorem qgPoint_zero : qgPoint (0 : Fin 2 → K) = qgT K := by
  simp [qgPoint, qgT]

theorem mem_qgOmega_iff {e : QGSpace K} : e ∈ qgOmega K ↔ qgPoint ![e.2.1, e.2.2.1] = e := by
  obtain ⟨ε, x, y, z⟩ := e
  constructor
  · rintro ⟨h1, h2⟩
    simp only at h1 h2
    subst h1 h2
    simp [qgPoint]
  · intro h
    rw [← h]
    exact qgPoint_mem _

theorem mem_qgOmega_iff_exists {e : QGSpace K} : e ∈ qgOmega K ↔ ∃ v, qgPoint v = e :=
  ⟨fun h => ⟨_, mem_qgOmega_iff.1 h⟩, fun ⟨v, hv⟩ => hv ▸ qgPoint_mem v⟩

theorem qgPoint_injective : Function.Injective (qgPoint (K := K)) := by
  intro v w h
  simp only [qgPoint, Prod.mk.injEq] at h
  ext i
  fin_cases i
  · exact h.2.1
  · exact h.2.2.1

theorem toAdd_mem_qgOmega {α : QGAut K} (hα : α ∈ qgStab K) {e : QGSpace K}
    (he : e ∈ qgOmega K) : Multiplicative.toAdd α e ∈ qgOmega K := by
  have hα' : ⇑(Multiplicative.toAdd α) '' qgOmega K = qgOmega K := hα
  rw [← hα']
  exact ⟨e, he, rfl⟩

@[expose] def qgInduced (α : QGAut K) (v : Fin 2 → K) : Fin 2 → K :=
  ![(Multiplicative.toAdd α (qgPoint v)).2.1, (Multiplicative.toAdd α (qgPoint v)).2.2.1]

theorem qgPoint_qgInduced {α : QGAut K} (hα : α ∈ qgStab K) (v : Fin 2 → K) :
    qgPoint (qgInduced α v) = Multiplicative.toAdd α (qgPoint v) :=
  mem_qgOmega_iff.1 (toAdd_mem_qgOmega hα (qgPoint_mem v))

theorem qgInduced_mul {α β : QGAut K} (hα : α ∈ qgStab K) (hβ : β ∈ qgStab K)
    (v : Fin 2 → K) : qgInduced (α * β) v = qgInduced α (qgInduced β v) := by
  apply qgPoint_injective
  rw [qgPoint_qgInduced (mul_mem hα hβ), qgPoint_qgInduced hα, qgPoint_qgInduced hβ]
  rfl

theorem qgInduced_one (v : Fin 2 → K) : qgInduced 1 v = v :=
  qgPoint_injective (by rw [qgPoint_qgInduced (one_mem _)]; rfl)

@[expose] noncomputable def qgPerm : qgStab K →* Equiv.Perm (Fin 2 → K) where
  toFun α :=
    { toFun := qgInduced α
      invFun := qgInduced (α : QGAut K)⁻¹
      left_inv := fun v => by
        rw [← qgInduced_mul (inv_mem α.2) α.2, inv_mul_cancel, qgInduced_one]
      right_inv := fun v => by
        rw [← qgInduced_mul α.2 (inv_mem α.2), mul_inv_cancel, qgInduced_one] }
  map_one' := Equiv.ext qgInduced_one
  map_mul' α β := Equiv.ext fun v => qgInduced_mul α.2 β.2 v

theorem qgPerm_apply (α : qgStab K) (v : Fin 2 → K) : qgPerm α v = qgInduced α v :=
  rfl

end Points

section CharTwo

variable {K : Type*} [Field K] [CharP K 2]

theorem qgZ_mem_closure (z : K) :
    ((0, 0, 0, z) : QGSpace K) ∈ AddSubgroup.closure (qgOmega K) := by
  have e : ((0, 0, 0, z) : QGSpace K) =
      qgPoint ![0, z] + qgPoint ![1, z] - (qgPoint ![0, 0] + qgPoint ![1, 0]) := by
    simp only [qgPoint]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp [CharTwo.add_self_eq_zero]
  rw [e]
  have hP : ∀ v, qgPoint v ∈ AddSubgroup.closure (qgOmega K) :=
    fun v => AddSubgroup.subset_closure (qgPoint_mem v)
  exact AddSubgroup.sub_mem _ (AddSubgroup.add_mem _ (hP _) (hP _))
    (AddSubgroup.add_mem _ (hP _) (hP _))

theorem closure_qgOmega : AddSubgroup.closure (qgOmega K) = ⊤ := by
  have hP : ∀ v, qgPoint v ∈ AddSubgroup.closure (qgOmega K) :=
    fun v => AddSubgroup.subset_closure (qgPoint_mem v)
  rw [eq_top_iff]
  rintro ⟨ε, x, y, z⟩ -
  have hZ := qgZ_mem_closure (K := K) (z - x * y)
  have hε : ∀ ε : ZMod 2, ε = 0 ∨ ε = 1 := by decide
  rcases hε ε with rfl | rfl
  · have e : ((0, x, y, z) : QGSpace K) = qgPoint ![x, y] + (0, 0, 0, z - x * y) + qgPoint 0 := by
      simp only [qgPoint]
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp [zmod_two_one_add_one]
    rw [e]
    exact AddSubgroup.add_mem _ (AddSubgroup.add_mem _ (hP _) hZ) (hP _)
  · have e : ((1, x, y, z) : QGSpace K) = qgPoint ![x, y] + (0, 0, 0, z - x * y) := by
      simp only [qgPoint]
      ext <;> simp
    rw [e]
    exact AddSubgroup.add_mem _ (hP _) hZ

theorem qgOmega_add_qgOmega :
    qgOmega K + qgOmega K = {0} ∪ {e | e.1 = 0 ∧ (e.2.1, e.2.2.1) ≠ (0, 0)} := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext e
  rw [Set.mem_add]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨v, rfl⟩ := mem_qgOmega_iff_exists.1 ha
    obtain ⟨w, rfl⟩ := mem_qgOmega_iff_exists.1 hb
    by_cases hvw : (v 0 + w 0, v 1 + w 1) = (0, 0)
    · left
      simp only [Prod.mk.injEq] at hvw
      have h0 : w 0 = v 0 := by linear_combination hvw.1 - v 0 * h2
      have h1 : w 1 = v 1 := by linear_combination hvw.2 - v 1 * h2
      rw [Set.mem_singleton_iff]
      simp only [qgPoint]
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
      · simp [zmod_two_one_add_one]
      · simpa using hvw.1
      · simpa using hvw.2
      · simp only [Prod.snd_add, Prod.snd_zero]
        rw [h0, h1]
        linear_combination v 0 * v 1 * h2
    · right
      refine ⟨by simp only [qgPoint, Prod.fst_add, zmod_two_one_add_one], ?_⟩
      simpa [qgPoint] using hvw
  · rintro (h | ⟨h1, hne⟩)
    · rw [Set.mem_singleton_iff] at h
      subst h
      refine ⟨qgPoint 0, qgPoint_mem _, qgPoint 0, qgPoint_mem _, ?_⟩
      simp only [qgPoint]
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp [zmod_two_one_add_one]
    · obtain ⟨ε, x, y, z⟩ := e
      simp only at h1 hne
      subst h1
      obtain ⟨a, b, hab⟩ : ∃ a b : K, a * y + b * x = z + x * y := by
        by_cases hx : x = 0
        · have hy : y ≠ 0 := fun hy => hne (by rw [hx, hy])
          exact ⟨(z + x * y) / y, 0, by rw [zero_mul, add_zero, div_mul_cancel₀ _ hy]⟩
        · exact ⟨0, (z + x * y) / x, by rw [zero_mul, zero_add, div_mul_cancel₀ _ hx]⟩
      refine ⟨qgPoint ![a, b], qgPoint_mem _, qgPoint ![a + x, b + y], qgPoint_mem _, ?_⟩
      simp only [qgPoint]
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
      · simp [zmod_two_one_add_one]
      · simp only [Prod.snd_add, Prod.fst_add, Matrix.cons_val_zero]
        linear_combination a * h2
      · simp only [Prod.snd_add, Prod.fst_add, Matrix.cons_val_one, Matrix.cons_val_zero]
        linear_combination b * h2
      · simp only [Prod.snd_add, Matrix.cons_val_one, Matrix.cons_val_zero]
        linear_combination hab + (a * b + x * y) * h2

theorem fst_toAdd {α : QGAut K} (hα : α ∈ qgStab K) (e : QGSpace K) :
    (Multiplicative.toAdd α e).1 = e.1 := by
  have h := AddMonoidHom.eq_of_eqOn_dense (closure_qgOmega (K := K))
    (f := (AddMonoidHom.fst _ _).comp (Multiplicative.toAdd α).toAddMonoidHom)
    (g := AddMonoidHom.fst _ _) (fun e he => by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_fst,
        AddEquiv.coe_toAddMonoidHom]
      rw [(toAdd_mem_qgOmega hα he).1, he.1])
  exact DFunLike.congr_fun h e

theorem toAdd_mem_qgW {α : QGAut K} (hα : α ∈ qgStab K) {e : QGSpace K} (he : e ∈ qgW K) :
    Multiplicative.toAdd α e ∈ qgW K := by
  change (Multiplicative.toAdd α e).1 = 0
  rw [fst_toAdd hα]
  exact he

omit [CharP K 2] in
theorem toAdd_mem_add {α : QGAut K} (hα : α ∈ qgStab K) {e : QGSpace K}
    (he : e ∈ qgOmega K + qgOmega K) : Multiplicative.toAdd α e ∈ qgOmega K + qgOmega K := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 he
  exact Set.mem_add.2 ⟨_, toAdd_mem_qgOmega hα ha, _, toAdd_mem_qgOmega hα hb,
    (map_add _ _ _).symm⟩

theorem toAdd_mem_qgZ {α : QGAut K} (hα : α ∈ qgStab K) {e : QGSpace K} (he : e ∈ qgZ K) :
    Multiplicative.toAdd α e ∈ qgZ K := by
  have hW : Multiplicative.toAdd α e ∈ qgW K := toAdd_mem_qgW hα he.1
  by_contra hZ
  have hmem : Multiplicative.toAdd α e ∈ qgOmega K + qgOmega K := by
    rw [qgOmega_add_qgOmega]
    right
    refine ⟨hW, fun h => hZ ⟨hW, ?_, ?_⟩⟩
    · exact (Prod.mk.inj h).1
    · exact (Prod.mk.inj h).2
  have hmem' := toAdd_mem_add (inv_mem hα) hmem
  have hinv : Multiplicative.toAdd α⁻¹ (Multiplicative.toAdd α e) = e :=
    AddAut.neg_apply_self _ _ _
  rw [hinv, qgOmega_add_qgOmega] at hmem'
  rcases hmem' with h0 | ⟨-, hne⟩
  · rw [Set.mem_singleton_iff] at h0
    apply hZ
    rw [h0, map_zero]
    exact (qgZ K).zero_mem
  · exact hne (by rw [he.2.1, he.2.2])

theorem map_qgW {α : QGAut K} (hα : α ∈ qgStab K) :
    (qgW K).map (Multiplicative.toAdd α).toAddMonoidHom = qgW K := by
  apply le_antisymm
  · rintro _ ⟨e, he, rfl⟩
    exact toAdd_mem_qgW hα he
  · intro e he
    exact ⟨Multiplicative.toAdd α⁻¹ e, toAdd_mem_qgW (inv_mem hα) he, AddAut.apply_neg_self _ _ _⟩

theorem map_qgZ {α : QGAut K} (hα : α ∈ qgStab K) :
    (qgZ K).map (Multiplicative.toAdd α).toAddMonoidHom = qgZ K := by
  apply le_antisymm
  · rintro _ ⟨e, he, rfl⟩
    exact toAdd_mem_qgZ hα he
  · intro e he
    exact ⟨Multiplicative.toAdd α⁻¹ e, toAdd_mem_qgZ (inv_mem hα) he, AddAut.apply_neg_self _ _ _⟩

theorem eq_one_of_qgInduced {α : QGAut K} (hα : α ∈ qgStab K) (h : ∀ v, qgInduced α v = v) :
    α = 1 := by
  have h1 : Set.EqOn (Multiplicative.toAdd α).toAddMonoidHom (AddMonoidHom.id _) (qgOmega K) := by
    intro e he
    simp only [AddEquiv.coe_toAddMonoidHom, AddMonoidHom.id_apply]
    rw [← mem_qgOmega_iff.1 he, ← qgPoint_qgInduced hα, h]
  have h2 := AddMonoidHom.eq_of_eqOn_dense (closure_qgOmega (K := K)) h1
  apply Multiplicative.toAdd.injective
  exact AddEquiv.ext fun e => DFunLike.congr_fun h2 e

theorem qgPerm_injective : Function.Injective (qgPerm (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  exact Subtype.ext (eq_one_of_qgInduced α.2 fun v => by
    rw [← qgPerm_apply, hα]
    rfl)

omit [CharP K 2] in
theorem mem_qgStab_of_mapsTo [Finite K] {α : QGAut K}
    (h : ∀ e ∈ qgOmega K, Multiplicative.toAdd α e ∈ qgOmega K) : α ∈ qgStab K := by
  change ⇑(Multiplicative.toAdd α) '' qgOmega K = qgOmega K
  apply Set.eq_of_subset_of_ncard_le
  · rintro _ ⟨e, he, rfl⟩
    exact h e he
  · rw [Set.ncard_image_of_injective _ (Multiplicative.toAdd α).injective]
  · exact Set.toFinite _

variable (K) in
abbrev f2Cast : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K

@[expose] def qgTranslFun (a b : K) (e : QGSpace K) : QGSpace K :=
  (e.1, e.2.1 + f2Cast K e.1 * a, e.2.2.1 + f2Cast K e.1 * b,
    e.2.2.2 + b * e.2.1 + a * e.2.2.1 + f2Cast K e.1 * a * b)

theorem qgTranslFun_involutive (a b : K) (e : QGSpace K) :
    qgTranslFun a b (qgTranslFun a b e) = e := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨ε, x, y, z⟩ := e
  simp only [qgTranslFun]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
  · linear_combination (f2Cast K ε * a) * h2
  · linear_combination (f2Cast K ε * b) * h2
  · linear_combination (b * x + a * y + 2 * f2Cast K ε * a * b) * h2

theorem qgTranslFun_add (a b : K) (e e' : QGSpace K) :
    qgTranslFun a b (e + e') = qgTranslFun a b e + qgTranslFun a b e' := by
  obtain ⟨ε, x, y, z⟩ := e
  obtain ⟨ε', x', y', z'⟩ := e'
  simp only [qgTranslFun, Prod.mk_add_mk, map_add]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> ring

@[expose] def qgTransl (a b : K) : QGAut K :=
  Multiplicative.ofAdd
    { toFun := qgTranslFun a b
      invFun := qgTranslFun a b
      left_inv := qgTranslFun_involutive a b
      right_inv := qgTranslFun_involutive a b
      map_add' := qgTranslFun_add a b }

theorem toAdd_qgTransl_apply (a b : K) (e : QGSpace K) :
    Multiplicative.toAdd (qgTransl a b) e = qgTranslFun a b e :=
  rfl

theorem qgTranslFun_qgPoint (a b : K) (v : Fin 2 → K) :
    qgTranslFun a b (qgPoint v) = qgPoint (v + ![a, b]) := by
  simp only [qgTranslFun, qgPoint, map_one, one_mul]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp
  · simp
  · simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

theorem qgTransl_mem [Finite K] (a b : K) : qgTransl a b ∈ qgStab K :=
  mem_qgStab_of_mapsTo fun e he => by
    obtain ⟨v, rfl⟩ := mem_qgOmega_iff_exists.1 he
    rw [toAdd_qgTransl_apply, qgTranslFun_qgPoint]
    exact qgPoint_mem _

theorem qgInduced_qgTransl [Finite K] (a b : K) (v : Fin 2 → K) :
    qgInduced (qgTransl a b) v = v + ![a, b] := by
  apply qgPoint_injective
  rw [qgPoint_qgInduced (qgTransl_mem a b), toAdd_qgTransl_apply, qgTranslFun_qgPoint]

omit [CharP K 2] in
theorem vec_zero_two : (![0, 0] : Fin 2 → K) = 0 := by
  ext i
  fin_cases i <;> rfl

@[expose] def qgPolar (u w : Fin 2 → K) : K := u 0 * w 1 + w 0 * u 1

theorem qgPolar_mulVec (M : Matrix (Fin 2) (Fin 2) K) (a b : Fin 2 → K) :
    qgPolar (M *ᵥ a) (M *ᵥ b) = M.det * qgPolar a b := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [qgPolar, mulVec, dotProduct, Fin.sum_univ_two, det_fin_two]
  linear_combination (M 0 0 * M 1 0 * a 0 * b 0 + M 0 1 * M 1 1 * a 1 * b 1 +
    M 0 1 * M 1 0 * (a 0 * b 1 + a 1 * b 0)) * h2

@[expose] def qgSemiFun (M : Matrix (Fin 2) (Fin 2) K) (σ : K ≃+* K) (e : QGSpace K) :
    QGSpace K :=
  (e.1, (M *ᵥ ![σ e.2.1, σ e.2.2.1]) 0, (M *ᵥ ![σ e.2.1, σ e.2.2.1]) 1,
    (M *ᵥ ![σ e.2.1, σ e.2.2.1]) 0 * (M *ᵥ ![σ e.2.1, σ e.2.2.1]) 1 +
      M.det * σ (e.2.1 * e.2.2.1) + M.det * σ e.2.2.2)

theorem qgSemiFun_add (M : Matrix (Fin 2) (Fin 2) K) (σ : K ≃+* K) (e e' : QGSpace K) :
    qgSemiFun M σ (e + e') = qgSemiFun M σ e + qgSemiFun M σ e' := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨ε, x, y, z⟩ := e
  obtain ⟨ε', x', y', z'⟩ := e'
  have hv : (![σ (x + x'), σ (y + y')] : Fin 2 → K) = ![σ x, σ y] + ![σ x', σ y'] := by
    ext i
    fin_cases i <;> simp
  have hP := qgPolar_mulVec M ![σ x, σ y] ![σ x', σ y']
  simp only [qgPolar, Matrix.cons_val_zero, Matrix.cons_val_one] at hP
  simp only [qgSemiFun, Prod.mk_add_mk]
  rw [hv, mulVec_add]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · simp only [Pi.add_apply, map_add, map_mul]
    linear_combination hP + M.det * (σ x * σ y' + σ x' * σ y) * h2

theorem qgSemiFun_qgPoint (M : Matrix (Fin 2) (Fin 2) K) (σ : K ≃+* K) (v : Fin 2 → K) :
    qgSemiFun M σ (qgPoint v) = qgPoint (M *ᵥ fun i => σ (v i)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hv : (![σ (v 0), σ (v 1)] : Fin 2 → K) = fun i => σ (v i) := by
    ext i
    fin_cases i <;> simp
  simp only [qgSemiFun, qgPoint]
  rw [hv]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
  linear_combination M.det * σ (v 0 * v 1) * h2

variable [Finite K]

omit [Finite K] in
theorem qgSemiFun_injective (M : GL (Fin 2) K) (σ : K ≃+* K) :
    Function.Injective (qgSemiFun (M : Matrix (Fin 2) (Fin 2) K) σ) := by
  let f : QGSpace K →+ QGSpace K :=
    { toFun := qgSemiFun (M : Matrix (Fin 2) (Fin 2) K) σ
      map_zero' := by simp [qgSemiFun, vec_zero_two]
      map_add' := qgSemiFun_add _ σ }
  change Function.Injective f
  rw [injective_iff_map_eq_zero]
  rintro ⟨ε, x, y, z⟩ he
  simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, qgSemiFun, Prod.mk_eq_zero] at he
  obtain ⟨hε, h0, h1, h3⟩ := he
  have hMv : (M : Matrix (Fin 2) (Fin 2) K) *ᵥ ![σ x, σ y] = 0 := by
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have hinv : ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hv : (![σ x, σ y] : Fin 2 → K) = 0 := by
    have := congrArg (((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ ·) hMv
    simpa [mulVec_mulVec, hinv] using this
  have hx : x = 0 := by
    have := congrFun hv 0
    simpa using this
  have hy : y = 0 := by
    have := congrFun hv 1
    simpa using this
  subst hx hy
  have hdet : (M : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    have h := congrArg det hinv
    rw [det_mul, det_one] at h
    exact right_ne_zero_of_mul_eq_one h
  rw [hMv] at h3
  simp only [Pi.zero_apply, mul_zero, map_zero, zero_add, mul_eq_zero, hdet, false_or,
    map_eq_zero] at h3
  rw [hε, h3]
  rfl

@[expose] noncomputable def qgSemi (M : GL (Fin 2) K) (σ : K ≃+* K) : QGAut K :=
  Multiplicative.ofAdd (AddEquiv.ofBijective
    ({ toFun := qgSemiFun (M : Matrix (Fin 2) (Fin 2) K) σ
       map_zero' := by simp [qgSemiFun, vec_zero_two]
       map_add' := qgSemiFun_add _ σ } : QGSpace K →+ QGSpace K)
    (Finite.injective_iff_bijective.1 (qgSemiFun_injective M σ)))

theorem toAdd_qgSemi_apply (M : GL (Fin 2) K) (σ : K ≃+* K) (e : QGSpace K) :
    Multiplicative.toAdd (qgSemi M σ) e = qgSemiFun (M : Matrix (Fin 2) (Fin 2) K) σ e :=
  rfl

theorem qgSemi_mem (M : GL (Fin 2) K) (σ : K ≃+* K) : qgSemi M σ ∈ qgStab K :=
  mem_qgStab_of_mapsTo fun e he => by
    obtain ⟨v, rfl⟩ := mem_qgOmega_iff_exists.1 he
    rw [toAdd_qgSemi_apply, qgSemiFun_qgPoint]
    exact qgPoint_mem _

theorem qgInduced_qgSemi (M : GL (Fin 2) K) (σ : K ≃+* K) (v : Fin 2 → K) :
    qgInduced (qgSemi M σ) v = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => σ (v i) := by
  apply qgPoint_injective
  rw [qgPoint_qgInduced (qgSemi_mem M σ), toAdd_qgSemi_apply, qgSemiFun_qgPoint]

end CharTwo

end CFSG.LocalAnalysis.SteinbergCD
