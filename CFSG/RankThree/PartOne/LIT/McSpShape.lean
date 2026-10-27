module

public import CFSG.RankThree.PartOne.LIT.McFrame

public section

namespace CFSG.RankThree.PartOne.LIT

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  (H : Subgroup (V ≃ₗ[ZMod p] V))

structure PlaneForms (ωU ωL : LinearMap.BilinForm (ZMod p) V) (U L : Submodule (ZMod p) V) :
    Prop where
  altU : ωU.IsAlt
  altL : ωL.IsAlt
  vanishU_left : ∀ y z, y ∈ L → ωU y z = 0
  vanishU_right : ∀ y z, z ∈ L → ωU y z = 0
  vanishL_left : ∀ y z, y ∈ U → ωL y z = 0
  vanishL_right : ∀ y z, z ∈ U → ωL y z = 0
  nondegU : ∀ u ∈ U, u ≠ 0 → ∃ z ∈ U, ωU u z ≠ 0
  nondegL : ∀ l ∈ L, l ≠ 0 → ∃ z ∈ L, ωL l z ≠ 0
  kerU : ∀ u ∈ U, u ≠ 0 → ∀ y ∈ U, ωU u y = 0 → y ∈ Submodule.span (ZMod p) {u}
  kerL : ∀ l ∈ L, l ≠ 0 → ∀ y ∈ L, ωL l y = 0 → y ∈ Submodule.span (ZMod p) {l}

private theorem exists_plane_form {W : Submodule (ZMod p) V}
    (hW : Module.finrank (ZMod p) W = 2) (π : V →ₗ[ZMod p] V) (hπ : ∀ x, π x ∈ W)
    (hπW : ∀ w ∈ W, π w = w) :
    ∃ ω : LinearMap.BilinForm (ZMod p) V, ω.IsAlt ∧ (∀ y z, π y = 0 → ω y z = 0) ∧
      (∀ y z, π z = 0 → ω y z = 0) ∧ (∀ w ∈ W, w ≠ 0 → ∃ z ∈ W, ω w z ≠ 0) ∧
      (∀ w ∈ W, w ≠ 0 → ∀ y ∈ W, ω w y = 0 → y ∈ Submodule.span (ZMod p) {w}) := by
  have : Module.Finite (ZMod p) W := Module.finite_of_finrank_pos (by omega)
  let b := Module.finBasisOfFinrankEq (ZMod p) W hW
  let c : Fin 2 → V →ₗ[ZMod p] ZMod p := fun i => b.coord i ∘ₗ π.codRestrict W hπ
  have hc0 : ∀ y, π y = 0 → ∀ i, c i y = 0 := fun y hy i => by
    have : π.codRestrict W hπ y = 0 := Subtype.ext hy
    simp [c, this]
  have hcW : ∀ (w : V) (hw : w ∈ W) i, c i w = b.repr ⟨w, hw⟩ i := fun w hw i => by
    have : π.codRestrict W hπ w = ⟨w, hw⟩ := Subtype.ext (hπW w hw)
    simp [c, this]
  have hcb : ∀ i j, c i (b j) = if i = j then 1 else 0 := fun i j => by
    rw [hcW _ (b j).2 i]
    simp [Finsupp.single_apply, eq_comm]
  have hzero : ∀ (w : V) (hw : w ∈ W), c 0 w = 0 → c 1 w = 0 → w = 0 := by
    intro w hw h0 h1
    have : (⟨w, hw⟩ : W) = 0 := b.ext_elem fun i => by
      rw [map_zero, Finsupp.zero_apply, ← hcW w hw]
      fin_cases i
      · exact h0
      · exact h1
    exact congrArg Subtype.val this
  let ω : LinearMap.BilinForm (ZMod p) V :=
    LinearMap.BilinForm.linMulLin (c 0) (c 1) - LinearMap.BilinForm.linMulLin (c 1) (c 0)
  have hω : ∀ y z, ω y z = c 0 y * c 1 z - c 1 y * c 0 z := fun y z => by simp [ω]
  refine ⟨ω, fun x => by rw [hω]; ring, fun y z hy => by simp [hω, hc0 y hy],
    fun y z hz => by simp [hω, hc0 z hz], ?_, ?_⟩
  · intro w hw hw0
    by_contra hcon
    push Not at hcon
    have h1 := hcon (b 1) (b 1).2
    have h0 := hcon (b 0) (b 0).2
    simp only [hω, hcb] at h1 h0
    simp at h1 h0
    exact hw0 (hzero w hw h1 h0)
  · intro w hw hw0 y hy hωwy
    rw [hω] at hωwy
    obtain ⟨s, hs0, hs1⟩ : ∃ s : ZMod p, c 0 y = s * c 0 w ∧ c 1 y = s * c 1 w := by
      by_cases ha : c 0 w = 0
      · have hb1 : c 1 w ≠ 0 := fun hb1 => hw0 (hzero w hw ha hb1)
        refine ⟨c 1 y / c 1 w, ?_, ?_⟩
        · rw [ha, mul_zero]
          rw [ha, zero_mul, zero_sub, neg_eq_zero] at hωwy
          exact (mul_eq_zero.mp hωwy).resolve_left hb1
        · field_simp
      · refine ⟨c 0 y / c 0 w, ?_, ?_⟩
        · field_simp
        · field_simp
          linear_combination hωwy
    have h := hzero (y - s • w) (W.sub_mem hy (W.smul_mem s hw))
      (by rw [map_sub, map_smul, hs0, smul_eq_mul, sub_self])
      (by rw [map_sub, map_smul, hs1, smul_eq_mul, sub_self])
    exact Submodule.mem_span_singleton.mpr ⟨s, (sub_eq_zero.mp h).symm⟩

theorem exists_planeForms {U L : Submodule (ZMod p) V} (hF : IsFrame H U L) :
    ∃ ωU ωL : LinearMap.BilinForm (ZMod p) V, PlaneForms ωU ωL U L := by
  obtain ⟨ωU, hωU, hU1, hU2, hU3, hU4⟩ :=
    exists_plane_form hF.2.1 hF.projU hF.projU_mem fun w hw => hF.projU_of_mem hw
  obtain ⟨ωL, hωL, hL1, hL2, hL3, hL4⟩ :=
    exists_plane_form hF.2.2.1 hF.projL hF.projL_mem fun w hw => hF.projL_of_mem hw
  exact ⟨ωU, ωL, hωU, hωL, fun y z hy => hU1 y z (hF.projU_of_mem_L hy),
    fun y z hz => hU2 y z (hF.projU_of_mem_L hz), fun y z hy => hL1 y z (hF.projL_of_mem_U hy),
    fun y z hz => hL2 y z (hF.projL_of_mem_U hz), hU3, hL3, hU4, hL4⟩

variable {H}

private theorem HasUniqueAxes.eq_zero_of_apply_eq_zero (hua : HasUniqueAxes H) {a b : V}
    {f g : Module.Dual (ZMod p) V} (ha : a ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfa : TrIn H a f) (hgb : TrIn H b g) (hga : g a = 0) : f b = 0 := by
  by_contra hfb
  obtain ⟨t, ht⟩ := hua a f (f b • g) ha hfa (TrIn.rule_R hfa hgb hga) hf
  have hb : f b * g b = t * f b := by
    simpa using congrArg (fun φ : Module.Dual (ZMod p) V => φ b) ht
  rw [hgb.1, mul_zero] at hb
  have ht0 : t = 0 := (mul_eq_zero.mp hb.symm).resolve_right hfb
  rw [ht0, zero_smul] at ht
  exact hg ((smul_eq_zero.mp ht).resolve_left hfb)

theorem HasUniqueAxes.reciprocal (hua : HasUniqueAxes H) {a b : V}
    {f g : Module.Dual (ZMod p) V}
    (ha : a ≠ 0) (hb : b ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0) (hfa : TrIn H a f) (hgb : TrIn H b g) :
    f b = 0 ↔ g a = 0 :=
  ⟨fun hfb => hua.eq_zero_of_apply_eq_zero hb hg hf hgb hfa hfb,
    hua.eq_zero_of_apply_eq_zero ha hf hg hfa hgb⟩

namespace PlaneForms

variable {ωU ωL : LinearMap.BilinForm (ZMod p) V} {U L : Submodule (ZMod p) V}

theorem left_projU (hP : PlaneForms ωU ωL U L) (hF : IsFrame H U L) (x z : V) :
    ωU x z = ωU (hF.projU x) z := by
  conv_lhs => rw [← hF.projU_add_projL x]
  rw [map_add, LinearMap.add_apply, hP.vanishU_left _ _ (hF.projL_mem x), add_zero]

theorem right_projU (hP : PlaneForms ωU ωL U L) (hF : IsFrame H U L) (y z : V) :
    ωU y z = ωU y (hF.projU z) := by
  conv_lhs => rw [← hF.projU_add_projL z]
  rw [map_add, hP.vanishU_right _ _ (hF.projL_mem z), add_zero]

theorem left_projL (hP : PlaneForms ωU ωL U L) (hF : IsFrame H U L) (x z : V) :
    ωL x z = ωL (hF.projL x) z := by
  conv_lhs => rw [← hF.projU_add_projL x]
  rw [map_add, LinearMap.add_apply, hP.vanishL_left _ _ (hF.projU_mem x), zero_add]

theorem right_projL (hP : PlaneForms ωU ωL U L) (hF : IsFrame H U L) (y z : V) :
    ωL y z = ωL y (hF.projL z) := by
  conv_lhs => rw [← hF.projU_add_projL z]
  rw [map_add, hP.vanishL_right _ _ (hF.projU_mem z), zero_add]

theorem trIn_axisU (hP : PlaneForms ωU ωL U L) (hF : IsFrame H U L) {c : V} (hc : c ∈ U) :
    TrIn H c (ωU c) :=
  hF.2.2.2 c hc (ωU c) (fun l hl => hP.vanishU_right c l hl) (hP.altU.self_eq_zero c)

theorem axisU_ne_zero (hP : PlaneForms ωU ωL U L) {c : V} (hc : c ∈ U) (hc0 : c ≠ 0) :
    ωU c ≠ 0 := by
  obtain ⟨z, -, hz⟩ := hP.nondegU c hc hc0
  intro h0
  exact hz (by rw [h0, LinearMap.zero_apply])

end PlaneForms

section Shape

variable {ωU ωL : LinearMap.BilinForm (ZMod p) V} {U L : Submodule (ZMod p) V}
  (hua : HasUniqueAxes H) (hF : IsFrame H U L) (hP : PlaneForms ωU ωL U L)
  {x : V} {h : Module.Dual (ZMod p) V} (hx : x ≠ 0) (hh : h ≠ 0) (hxh : TrIn H x h)

include hua hF hP hx hh hxh

private theorem shape_apply_eq_zero_iff {c : V} (hc : c ∈ U) :
    h c = 0 ↔ ωU c (hF.projU x) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc0
  · simp
  · rw [← hP.right_projU hF c x]
    exact (hua.reciprocal hc0 hx (hP.axisU_ne_zero hc hc0) hh (hP.trIn_axisU hF hc) hxh).symm

private theorem shape_vanish_U (h0 : hF.projU x = 0) {c : V} (hc : c ∈ U) : h c = 0 :=
  (shape_apply_eq_zero_iff hua hF hP hx hh hxh hc).mpr (by rw [h0, map_zero])

private theorem shape_projU (hU0 : hF.projU x ≠ 0) :
    h (hF.projU x) = 0 ∧ ∃ y ∈ U, h y ≠ 0 := by
  have key : ∀ c ∈ U, h c = 0 ↔ ωU c (hF.projU x) = 0 := fun c hc =>
    shape_apply_eq_zero_iff hua hF hP hx hh hxh hc
  refine ⟨(key _ (hF.projU_mem x)).mpr (hP.altU.self_eq_zero _), ?_⟩
  obtain ⟨z, hz, hωz⟩ := hP.nondegU _ (hF.projU_mem x) hU0
  refine ⟨z, hz, fun hz0 => hωz ?_⟩
  exact neg_eq_zero.mp ((hP.altU.neg_eq _ _).trans ((key z hz).mp hz0))

private theorem shape_apply_projL : h (hF.projL x) = 0 := by
  have h2 : h (hF.projU x) = 0 := by
    by_cases hU0 : hF.projU x = 0
    · rw [hU0, map_zero]
    · exact (shape_projU hua hF hP hx hh hxh hU0).1
  have h3 : h (hF.projU x) + h (hF.projL x) = h x := by
    rw [← map_add, hF.projU_add_projL]
  rwa [hxh.1, h2, zero_add] at h3

omit hh in
private theorem shape_vanish_L (hL0 : hF.projL x = 0) {c : V} (hc : c ∈ L) : h c = 0 := by
  have hxU : x ∈ U := by
    have := hF.projU_add_projL x
    rw [hL0, add_zero] at this
    rw [← this]
    exact hF.projU_mem x
  obtain ⟨t, ht⟩ := hua x (ωU x) h hx (hP.trIn_axisU hF hxU) hxh (hP.axisU_ne_zero hxU hx)
  rw [ht, LinearMap.smul_apply, hP.vanishU_right x c hc, smul_zero]

private theorem shape_exists_L (hL0 : hF.projL x ≠ 0) : ∃ y ∈ L, h y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  by_cases hU0 : hF.projU x = 0
  · apply hh
    ext y
    have : h (hF.projU y) + h (hF.projL y) = h y := by rw [← map_add, hF.projU_add_projL]
    rw [LinearMap.zero_apply, ← this, hcon _ (hF.projL_mem y),
      shape_vanish_U hua hF hP hx hh hxh hU0 (hF.projU_mem y), add_zero]
  · obtain ⟨hxU, c, hc, hhc⟩ := shape_projU hua hF hP hx hh hxh hU0
    have hxUtr : TrIn H (hF.projU x) h := hF.2.2.2 _ (hF.projU_mem x) h hcon hxU
    have hneg : TrIn H ((-1 : ZMod p) • hF.projU x) h :=
      TrIn.smul_center_iff.mpr (hxUtr.smul (-1))
    have hsum : x + (-1 : ZMod p) • hF.projU x = hF.projL x := by
      rw [neg_one_smul, ← sub_eq_add_neg]
      exact sub_eq_of_eq_add' (hF.projU_add_projL x).symm
    have hxLtr : TrIn H (hF.projL x) h := hsum ▸ TrIn.add_center hxh hneg
    have hc0 : c ≠ 0 := fun h0 => hhc (by rw [h0, map_zero])
    have := hua.reciprocal hL0 hc0 hh (hP.axisU_ne_zero hc hc0) hxLtr (hP.trIn_axisU hF hc)
    exact hhc (this.mpr (hP.vanishU_right c _ (hF.projL_mem x)))

private theorem shape_lam :
    ∃ lam : ZMod p, (∀ y, h (hF.projU y) = lam * ωU x y) ∧ (hF.projU x ≠ 0 → lam ≠ 0) := by
  by_cases hU0 : hF.projU x = 0
  · refine ⟨0, fun y => ?_, fun h' => absurd hU0 h'⟩
    rw [zero_mul, shape_vanish_U hua hF hP hx hh hxh hU0 (hF.projU_mem y)]
  · obtain ⟨hxU, y0, hy0, hhy0⟩ := shape_projU hua hF hP hx hh hxh hU0
    obtain ⟨lam, hlam⟩ := eq_smul_of_vanish_on_plane hF.2.1 (hF.projU_mem x) hU0 hxU
      (hP.altU.self_eq_zero _) (hP.nondegU _ (hF.projU_mem x) hU0)
    refine ⟨lam, fun y => ?_, fun _ hlam0 => hhy0 ?_⟩
    · rw [hlam _ (hF.projU_mem y), ← hP.right_projU hF, ← hP.left_projU hF]
    · rw [hlam _ hy0, hlam0, zero_mul]

private theorem shape_mu :
    ∃ mu : ZMod p, (∀ y, h (hF.projL y) = mu * ωL x y) ∧ (hF.projL x ≠ 0 → mu ≠ 0) := by
  by_cases hL0 : hF.projL x = 0
  · refine ⟨0, fun y => ?_, fun h' => absurd hL0 h'⟩
    rw [zero_mul, shape_vanish_L hua hF hP hx hxh hL0 (hF.projL_mem y)]
  · obtain ⟨mu, hmu⟩ := eq_smul_of_vanish_on_plane hF.2.2.1 (hF.projL_mem x) hL0
      (shape_apply_projL hua hF hP hx hh hxh) (hP.altL.self_eq_zero _)
      (hP.nondegL _ (hF.projL_mem x) hL0)
    refine ⟨mu, fun y => ?_, fun _ hmu0 => ?_⟩
    · rw [hmu _ (hF.projL_mem y), ← hP.right_projL hF, ← hP.left_projL hF]
    · obtain ⟨y, hy, hhy⟩ := shape_exists_L hua hF hP hx hh hxh hL0
      exact hhy (by rw [hmu y hy, hmu0, zero_mul])

end Shape

theorem HasUniqueAxes.shape_of_planeForms (hua : HasUniqueAxes H) {U L : Submodule (ZMod p) V}
    (hF : IsFrame H U L) {ωU ωL : LinearMap.BilinForm (ZMod p) V} (hP : PlaneForms ωU ωL U L)
    {x : V} {h : Module.Dual (ZMod p) V} (hx : x ≠ 0) (hh : h ≠ 0) (hxh : TrIn H x h) :
    ∃ lam mu : ZMod p, (∀ y, h y = lam * ωU x y + mu * ωL x y) ∧
      (hF.projU x ≠ 0 → lam ≠ 0) ∧ (hF.projL x ≠ 0 → mu ≠ 0) := by
  obtain ⟨lam, hlam, hlam0⟩ := shape_lam hua hF hP hx hh hxh
  obtain ⟨mu, hmu, hmu0⟩ := shape_mu hua hF hP hx hh hxh
  refine ⟨lam, mu, fun y => ?_, hlam0, hmu0⟩
  have : h (hF.projU y) + h (hF.projL y) = h y := by rw [← map_add, hF.projU_add_projL]
  rw [← this, hlam, hmu]

end CFSG.RankThree.PartOne.LIT
