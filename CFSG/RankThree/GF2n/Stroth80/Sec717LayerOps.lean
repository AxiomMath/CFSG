module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveOpm

public section

namespace CFSG.RankThree.GF2n.Stroth80

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

structure IsLayerLowering (T P : Submodule K E) (f : E →ₗ[K] E) : Prop where
  top : ∀ x, f x ∈ P
  mid : ∀ x ∈ P, f x ∈ T
  bot : ∀ x ∈ T, f x = 0

structure IsLayerCorner (T P : Submodule K E) (f : E →ₗ[K] E) : Prop where
  top : ∀ x, f x ∈ T
  mid : ∀ x ∈ P, f x = 0

variable {T P : Submodule K E} {f g h : E →ₗ[K] E}

theorem IsLayerLowering.comp_comp (hf : IsLayerLowering T P f) (hg : IsLayerLowering T P g)
    (hh : IsLayerLowering T P h) (x : E) : f (g (h x)) = 0 :=
  hf.bot _ (hg.mid _ (hh.top x))

theorem IsLayerCorner.isLayerLowering (hTP : T ≤ P) (hf : IsLayerCorner T P f) :
    IsLayerLowering T P f :=
  ⟨fun x => hTP (hf.top x), fun x hx => by rw [hf.mid x hx]; exact T.zero_mem,
    fun x hx => hf.mid x (hTP hx)⟩

theorem IsLayerCorner.apply_lowering (hf : IsLayerCorner T P f) (hg : IsLayerLowering T P g)
    (x : E) : f (g x) = 0 :=
  hf.mid _ (hg.top x)

theorem IsLayerLowering.apply_corner (hf : IsLayerLowering T P f) (hg : IsLayerCorner T P g)
    (x : E) : f (g x) = 0 :=
  hf.bot _ (hg.top x)

theorem opm_mul_apply_layer (a b : E ≃ₗ[K] E) (w : E) :
    opm (a * b) w = opm a w + opm b w + opm a (opm b w) := by
  simp only [opm_apply, LinearEquiv.mul_apply, map_sub]
  abel

theorem linearEquiv_apply_inv_apply (a : E ≃ₗ[K] E) (x : E) : a (a⁻¹ x) = x := by
  have h := DFunLike.congr_fun (mul_inv_cancel a) x
  rw [LinearEquiv.mul_apply] at h
  exact h

theorem linearEquiv_inv_apply_apply (a : E ≃ₗ[K] E) (x : E) : a⁻¹ (a x) = x := by
  have h := DFunLike.congr_fun (inv_mul_cancel a) x
  rw [LinearEquiv.mul_apply] at h
  exact h

theorem opm_inv_apply_of_lowering {a : E ≃ₗ[K] E} (ha : IsLayerLowering T P (opm a)) (x : E) :
    opm a⁻¹ x = -opm a x + opm a (opm a x) := by
  have hxy : a (a⁻¹ x) = x := linearEquiv_apply_inv_apply a x
  have hf : opm a (a⁻¹ x) = x - a⁻¹ x := by rw [opm_apply, hxy]
  have h2 : a⁻¹ x = x - opm a (a⁻¹ x) := by rw [hf]; abel
  have h3 : opm a (opm a (a⁻¹ x)) = opm a (opm a x) := by
    have e : opm a (opm a (a⁻¹ x)) = opm a (opm a (x - opm a (a⁻¹ x))) :=
      congrArg (fun y => opm a (opm a y)) h2
    rw [e, map_sub, map_sub, ha.comp_comp ha ha, sub_zero]
  have e1 : opm a (a⁻¹ x) = opm a x - opm a (opm a x) := by
    have e : opm a (a⁻¹ x) = opm a (x - opm a (a⁻¹ x)) := congrArg (opm a) h2
    rw [e, map_sub, h3]
  have e2 : opm a⁻¹ x = -opm a (a⁻¹ x) := by rw [opm_apply, hf]; abel
  rw [e2, e1]
  abel

theorem IsLayerLowering.opm_mul (hTP : T ≤ P) {a b : E ≃ₗ[K] E}
    (ha : IsLayerLowering T P (opm a)) (hb : IsLayerLowering T P (opm b)) :
    IsLayerLowering T P (opm (a * b)) := by
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [opm_mul_apply_layer]
    exact P.add_mem (P.add_mem (ha.top x) (hb.top x)) (hTP (ha.mid _ (hb.top x)))
  · rw [opm_mul_apply_layer, ha.bot _ (hb.mid x hx), add_zero]
    exact T.add_mem (ha.mid x hx) (hb.mid x hx)
  · rw [opm_mul_apply_layer, hb.bot x hx, ha.bot x hx, map_zero, add_zero, add_zero]

theorem IsLayerLowering.opm_inv (hTP : T ≤ P) {a : E ≃ₗ[K] E}
    (ha : IsLayerLowering T P (opm a)) : IsLayerLowering T P (opm a⁻¹) := by
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [opm_inv_apply_of_lowering ha]
    exact P.add_mem (P.neg_mem (ha.top x)) (hTP (ha.mid _ (ha.top x)))
  · rw [opm_inv_apply_of_lowering ha, ha.bot _ (ha.mid x hx), add_zero]
    exact T.neg_mem (ha.mid x hx)
  · rw [opm_inv_apply_of_lowering ha, ha.bot x hx, map_zero, neg_zero, add_zero]

theorem opm_commutator_of_lowering {a b : E ≃ₗ[K] E} (ha : IsLayerLowering T P (opm a))
    (hb : IsLayerLowering T P (opm b)) (x : E) :
    opm (a * b * a⁻¹ * b⁻¹) x = opm a (opm b x) - opm b (opm a x) := by
  have aaa := ha.comp_comp ha ha
  have aab := ha.comp_comp ha hb
  have aba := ha.comp_comp hb ha
  have abb := ha.comp_comp hb hb
  have baa := hb.comp_comp ha ha
  have bab := hb.comp_comp ha hb
  have bba := hb.comp_comp hb ha
  have bbb := hb.comp_comp hb hb
  simp only [opm_mul_apply_layer, opm_inv_apply_of_lowering ha,
    opm_inv_apply_of_lowering hb, map_add, map_neg, map_zero, aaa, aab, aba, abb, baa, bab, bba,
    bbb, neg_zero, add_zero, zero_add]
  abel

theorem opm_conj_apply (r a : E ≃ₗ[K] E) (x : E) :
    opm (r * a * r⁻¹) x = r (opm a (r⁻¹ x)) := by
  rw [opm_apply, opm_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_sub,
    linearEquiv_apply_inv_apply]

theorem IsLayerLowering.conj {r a : E ≃ₗ[K] E} (hrT : ∀ w ∈ T, r w ∈ T) (hrP : ∀ w ∈ P, r w ∈ P)
    (hrT' : ∀ w ∈ T, r⁻¹ w ∈ T) (hrP' : ∀ w ∈ P, r⁻¹ w ∈ P) (ha : IsLayerLowering T P (opm a)) :
    IsLayerLowering T P (opm (r * a * r⁻¹)) := by
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [opm_conj_apply]; exact hrP _ (ha.top _)
  · rw [opm_conj_apply]; exact hrT _ (ha.mid _ (hrP' x hx))
  · rw [opm_conj_apply, ha.bot _ (hrT' x hx), map_zero]

theorem eq_one_of_opm_eq_zero {a : E ≃ₗ[K] E} (h : ∀ x, opm a x = 0) : a = 1 := by
  ext x
  have hx := h x
  rw [opm_apply, sub_eq_zero] at hx
  exact hx

theorem commutator_eq_one_of_corner (hTP : T ≤ P) {a b : E ≃ₗ[K] E}
    (ha : IsLayerLowering T P (opm a)) (hb : IsLayerCorner T P (opm b)) :
    a * b * a⁻¹ * b⁻¹ = 1 := by
  apply eq_one_of_opm_eq_zero
  intro x
  rw [opm_commutator_of_lowering ha (hb.isLayerLowering hTP), ha.apply_corner hb,
    hb.apply_lowering ha, sub_zero]

end CFSG.RankThree.GF2n.Stroth80
