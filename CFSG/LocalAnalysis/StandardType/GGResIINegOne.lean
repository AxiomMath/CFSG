module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Refl

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem ggResII_tv_of_coroot (hp2 : p ≠ 2) {r r' : V ≃ₗ[ZMod p] V} {hv : V}
    {α β : Module.Dual (ZMod p) V} (hr : ∀ w, r w = w - α w • hv) (hr' : ∀ w, r' w = w - β w • hv)
    (hα : α hv = 2) (hβ : β hv = 2) (hne : α ≠ β) :
    Module.finrank (ZMod p) (ggLinMove (r * r')) = 1 ∧
      ∀ w, (r * r') ((r * r') w - w) = (r * r') w - w := by
  have hmul : ∀ w, (r * r') w = w + (β w - α w) • hv := by
    intro w
    rw [LinearEquiv.mul_apply, hr, hr', map_sub, map_smul, smul_eq_mul, hα]
    module
  have hv0 : hv ≠ 0 := by
    rintro rfl
    rw [map_zero] at hα
    exact zmod_two_ne_zero hp2 hα.symm
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, (β - α) w₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (sub_eq_zero.mp (LinearMap.ext hc)).symm
  have hmove : ggLinMove (r * r') = Submodule.span (ZMod p) {hv} := by
    apply le_antisymm
    · rintro v ⟨w, rfl⟩
      rw [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, hmul, add_sub_cancel_left]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self hv)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      refine ⟨((β - α) w₀)⁻¹ • w₀, ?_⟩
      rw [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, hmul, add_sub_cancel_left,
        map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_sub]
      change (((β - α) w₀)⁻¹ * (β - α) w₀) • hv = hv
      rw [inv_mul_cancel₀ hw₀, one_smul]
  refine ⟨by rw [hmove]; exact finrank_span_singleton hv0, fun w => ?_⟩
  rw [hmul w, add_sub_cancel_left, hmul, map_smul, map_smul, hα, hβ, sub_self, zero_smul,
    add_zero]

theorem ggResII_tv_of_neg (hp2 : p ≠ 2) {ι : Type} (g : ι → (V ≃ₗ[ZMod p] V)) (h : ι → V)
    (α : ι → Module.Dual (ZMod p) V) (hg : ∀ o w, g o w = w - α o w • h o) {a : ι}
    (ha : α a (h a) = 2) {w : V ≃ₗ[ZMod p] V} (hw : w ∈ Subgroup.closure (Set.range g))
    (hwa : w (h a) = -h a) {z : V} (hwz : w z = z) (hz : α a z ≠ 0) :
    ∃ t ∈ Subgroup.closure (Set.range g),
      Module.finrank (ZMod p) (ggLinMove t) = 1 ∧ ∀ v, t (t v - v) = t v - v := by
  have hwi : ∀ v, w⁻¹ v = w.symm v := fun v => by rw [LinearEquiv.coe_inv]
  have hwa' : w⁻¹ (h a) = -h a := by
    rw [hwi, LinearEquiv.symm_apply_eq, map_neg, hwa, neg_neg]
  have hwz' : w⁻¹ z = z := by rw [hwi, LinearEquiv.symm_apply_eq, hwz]
  let β : Module.Dual (ZMod p) V := -((α a).comp (w⁻¹ : V ≃ₗ[ZMod p] V).toLinearMap)
  have hβv : ∀ v, β v = -α a (w⁻¹ v) := fun v => rfl
  have hconj : ∀ v, (w * g a * w⁻¹) v = v - β v • h a := by
    intro v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg, map_sub, map_smul, hwa, hβv, hwi,
      LinearEquiv.apply_symm_apply, smul_neg, neg_smul, sub_neg_eq_add]
  have hβ2 : β (h a) = 2 := by rw [hβv, hwa', map_neg, neg_neg, ha]
  have hne : α a ≠ β := by
    intro heq
    have h1 := congrArg (fun f : Module.Dual (ZMod p) V => f z) heq
    simp only [hβv, hwz'] at h1
    have h2 : (2 : ZMod p) * α a z = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact zmod_two_ne_zero hp2 h3
    · exact hz h3
  have hga : g a ∈ Subgroup.closure (Set.range g) := Subgroup.subset_closure ⟨a, rfl⟩
  refine ⟨g a * (w * g a * w⁻¹), Subgroup.mul_mem _ hga
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ hw hga) (Subgroup.inv_mem _ hw)), ?_⟩
  exact ggResII_tv_of_coroot hp2 (hg a) hconj ha hβ2 hne

end Refl

@[expose] def ggNegStep {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (c : List ℤ) : List ℤ :=
  List.ofFn fun k : Fin n =>
    if k = i then c.getD k 0 - (List.ofFn fun l : Fin n => c.getD l 0 * C i l).sum else c.getD k 0

@[expose] def ggNegWord {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ws : List (Fin n)) (c : List ℤ) :
    List ℤ :=
  ws.foldr (fun i acc => ggNegStep C i acc) c

@[expose] def ggNegUnit (n : ℕ) (j : Fin n) : List ℤ := List.ofFn fun k : Fin n => if k = j then 1 else 0

@[expose] def ggNegCox (n k : ℕ) : List (Fin n) := (List.replicate k (List.finRange n)).flatten

@[expose] def ggNegOneCheck {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) : Bool :=
  (List.finRange n).all fun j =>
    ggNegWord C (ggNegCox n k) (ggNegUnit n j) == (ggNegUnit n j).map (- ·)

section Sound

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}

@[expose] def ggNegVec (h : Fin n → V) (c : List ℤ) : V :=
  ∑ k : Fin n, ((c.getD k 0 : ℤ) : ZMod p) • h k

private theorem ggNeg_getD_ofFn (f : Fin n → ℤ) (k : Fin n) : (List.ofFn f).getD k 0 = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

theorem ggNegVec_step (h : Fin n → V) (α : Fin n → Module.Dual (ZMod p) V)
    (r : Fin n → (V ≃ₗ[ZMod p] V)) (C : Matrix (Fin n) (Fin n) ℤ)
    (hr : ∀ i w, r i w = w - α i w • h i) (hC : ∀ i k, α i (h k) = (C i k : ZMod p))
    (i : Fin n) (c : List ℤ) :
    r i (ggNegVec (p := p) h c) = ggNegVec (p := p) h (ggNegStep C i c) := by
  classical
  have hs : α i (ggNegVec (p := p) h c) =
      (((List.ofFn fun l : Fin n => c.getD l 0 * C i l).sum : ℤ) : ZMod p) := by
    rw [ggNegVec, map_sum, List.sum_ofFn]
    push_cast
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, hC, smul_eq_mul]
  set S : ℤ := (List.ofFn fun l : Fin n => c.getD l 0 * C i l).sum with hS
  rw [hr, hs, ggNegVec, ggNegVec]
  simp only [ggNegStep, ggNeg_getD_ofFn]
  have hrhs : ∀ k : Fin n, (((if k = i then c.getD k 0 - S else c.getD k 0 : ℤ)) : ZMod p) • h k =
      ((c.getD k 0 : ℤ) : ZMod p) • h k - (if k = i then ((S : ℤ) : ZMod p) • h i else 0) := by
    intro k
    split_ifs with hk
    · subst hk
      push_cast
      rw [sub_smul]
    · rw [sub_zero]
  rw [Finset.sum_congr rfl fun k _ => hrhs k, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp

theorem ggNegVec_word (h : Fin n → V) (α : Fin n → Module.Dual (ZMod p) V)
    (r : Fin n → (V ≃ₗ[ZMod p] V)) (C : Matrix (Fin n) (Fin n) ℤ)
    (hr : ∀ i w, r i w = w - α i w • h i) (hC : ∀ i k, α i (h k) = (C i k : ZMod p))
    (ws : List (Fin n)) (c : List ℤ) :
    (ws.map r).prod (ggNegVec (p := p) h c) = ggNegVec (p := p) h (ggNegWord C ws c) := by
  induction ws with
  | nil => rfl
  | cons i ws ih =>
    rw [List.map_cons, List.prod_cons, LinearEquiv.mul_apply, ih,
      ggNegVec_step h α r C hr hC]
    rfl

theorem ggNegVec_unit (h : Fin n → V) (j : Fin n) : ggNegVec (p := p) h (ggNegUnit n j) = h j := by
  classical
  simp only [ggNegVec, ggNegUnit, ggNeg_getD_ofFn]
  simp

theorem ggNegVec_neg (h : Fin n → V) (c : List ℤ) :
    ggNegVec (p := p) h (c.map (- ·)) = -ggNegVec (p := p) h c := by
  rw [ggNegVec, ggNegVec, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (c.map (- ·)).getD k 0 = -(c.getD k 0) := by
    rw [show (0 : ℤ) = -0 from neg_zero.symm, List.getD_map, neg_zero]
  rw [hk, Int.cast_neg, neg_smul]

theorem ggNegOneCheck_sound (h : Fin n → V) (α : Fin n → Module.Dual (ZMod p) V)
    (r : Fin n → (V ≃ₗ[ZMod p] V)) (C : Matrix (Fin n) (Fin n) ℤ)
    (hr : ∀ i w, r i w = w - α i w • h i) (hC : ∀ i k, α i (h k) = (C i k : ZMod p)) {k : ℕ}
    (hchk : ggNegOneCheck C k = true) (j : Fin n) :
    ((ggNegCox n k).map r).prod (h j) = -h j := by
  have hj : ggNegWord C (ggNegCox n k) (ggNegUnit n j) = (ggNegUnit n j).map (- ·) := by
    have := List.all_eq_true.mp hchk j (List.mem_finRange j)
    exact beq_iff_eq.mp this
  rw [← ggNegVec_unit (p := p) h j, ggNegVec_word h α r C hr hC, hj, ggNegVec_neg]

theorem ggNegOneCheck_negates_span (h : Fin n → V) (α : Fin n → Module.Dual (ZMod p) V)
    (r : Fin n → (V ≃ₗ[ZMod p] V)) (C : Matrix (Fin n) (Fin n) ℤ)
    (hr : ∀ i w, r i w = w - α i w • h i) (hC : ∀ i k, α i (h k) = (C i k : ZMod p))
    {k : ℕ} (hchk : ggNegOneCheck C k = true) {x : V} (hx : ∀ i, r i x = x) :
    ∃ z ∈ Subgroup.closure (Set.range r),
      (∀ s ∈ Submodule.span (ZMod p) (Set.range h), z s = -s) ∧ z x = x := by
  let z : V ≃ₗ[ZMod p] V := ((ggNegCox n k).map r).prod
  have hz : z ∈ Subgroup.closure (Set.range r) := by
    apply Subgroup.list_prod_mem
    intro g hg
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
    exact Subgroup.subset_closure (Set.mem_range_self i)
  refine ⟨z, hz, ?_, ?_⟩
  · intro s hs
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨i, rfl⟩ := hs
      exact ggNegOneCheck_sound h α r C hr hC hchk i
    | zero => simp
    | add a b ha hb iha ihb => simp only [map_add, iha, ihb, neg_add]
    | smul c a ha ih => simp only [map_smul, ih, smul_neg]
  · have hfix : Subgroup.closure (Set.range r) ≤
        MulAction.stabilizer (V ≃ₗ[ZMod p] V) x := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i, rfl⟩
      exact MulAction.mem_stabilizer_iff.mpr (hx i)
    exact MulAction.mem_stabilizer_iff.mp (hfix hz)

end Sound

theorem ggNegOneCheck_A_one : ggNegOneCheck (CartanMatrix.A 1) 1 = true := by decide +kernel

theorem ggNegOneCheck_B {n : ℕ} (h2 : 2 ≤ n) (h8 : n ≤ 8) :
    ggNegOneCheck (CartanMatrix.B n) n = true := by
  interval_cases n <;> decide +kernel

theorem ggNegOneCheck_C {n : ℕ} (h2 : 2 ≤ n) (h8 : n ≤ 8) :
    ggNegOneCheck (CartanMatrix.C n) n = true := by
  interval_cases n <;> decide +kernel

theorem ggNegOneCheck_D {n : ℕ} (h4 : 4 ≤ n) (h8 : n ≤ 8) (he : Even n) :
    ggNegOneCheck (CartanMatrix.D n) (n - 1) = true := by
  interval_cases n <;> first | decide +kernel | exact absurd he (by decide)

theorem ggNegOneCheck_E7 : ggNegOneCheck (CartanMatrix.E 7) 9 = true := by decide +kernel

theorem ggNegOneCheck_E8 : ggNegOneCheck (CartanMatrix.E 8) 15 = true := by decide +kernel

theorem ggNegOneCheck_F4 : ggNegOneCheck CartanMatrix.F₄ 6 = true ∧
    ggNegOneCheck CartanMatrix.F₄.transpose 6 = true := by
  constructor <;> decide +kernel

theorem ggNegOneCheck_G2 : ggNegOneCheck CartanMatrix.G₂ 3 = true ∧
    ggNegOneCheck CartanMatrix.G₂.transpose 3 = true := by
  constructor <;> decide +kernel

end CFSG.StandardType
