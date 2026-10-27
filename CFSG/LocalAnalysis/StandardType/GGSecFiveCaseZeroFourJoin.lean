module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroReflShape
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLLabel
import Mathlib.Tactic.Ring

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {V : Type} [AddCommGroup V] [Module (ZMod p) V]

private theorem ggCZWB_le_ggCZWF4 {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hp2 : p ≠ 2) (hd : GGCZDual e φ) : ggCZWB p e φ ≤ ggCZWF4 p e φ := by
  rw [ggCZWB]
  refine (Subgroup.closure_le (ggCZWF4 p e φ)).mpr ?_
  rintro r (⟨i, j, hij, hr⟩ | ⟨i, hi, hr⟩)
  · have hne : i ≠ j := by rintro rfl; omega
    refine ggCZ_subset_ggCZWF4 hp2 hd (Or.inl (Or.inl ⟨i, j, hne, 1, Or.inl rfl, ?_⟩))
    simpa using hr
  · exact ggCZ_subset_ggCZWF4 hp2 hd (Or.inl (Or.inr ⟨i, hr⟩))

private noncomputable def czRDRefl {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {i j : Fin 4} (hij : i ≠ j) : V ≃ₗ[ZMod p] V :=
  reflection (f := φ i - φ j) (x := e i - e j) (by
    have hd' : ∀ a b, φ a (e b) = if a = b then 1 else 0 := hd
    have hji : j ≠ i := fun h => hij h.symm
    simp [hd', hij, hji]
    ring)

private noncomputable def czSRefl {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (i : Fin 4) : V ≃ₗ[ZMod p] V :=
  reflection (f := (2 : ZMod p) • φ i) (x := e i) (by
    have hd' : ∀ a b, φ a (e b) = if a = b then 1 else 0 := hd
    simp [hd'])

private theorem czRDRefl_apply {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {i j : Fin 4} (hij : i ≠ j) (v : V) :
    czRDRefl (φ := φ) hd hij v = v - (φ i v - φ j v) • (e i - e j) := by
  unfold czRDRefl
  rw [reflection_apply]
  rfl

private theorem czSRefl_apply {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (i : Fin 4) (v : V) :
    czSRefl (e := e) hd i v = v - (2 * φ i v) • e i := by
  unfold czSRefl
  rw [reflection_apply]
  simp

private theorem czRDRefl_inv {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {i j : Fin 4} (hij : i ≠ j) :
    (czRDRefl (φ := φ) hd hij)⁻¹ = czRDRefl (φ := φ) hd hij := by
  unfold czRDRefl
  exact reflection_inv _

private theorem czSRefl_inv {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (i : Fin 4) : (czSRefl (e := e) hd i)⁻¹ = czSRefl (e := e) hd i := by
  unfold czSRefl
  exact reflection_inv _

private theorem czRDRefl_mem {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {i j : Fin 4} (hij : i ≠ j) :
    czRDRefl (φ := φ) hd hij ∈ ggCZRD e φ := by
  refine ⟨i, j, hij, 1, Or.inl rfl, fun v => ?_⟩
  rw [czRDRefl_apply]
  simp

private theorem czSRefl_mem {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (i : Fin 4) : czSRefl (e := e) hd i ∈ ggCZS e φ := by
  refine ⟨i, fun v => ?_⟩
  rw [czSRefl_apply]

private theorem czRDRefl_conj_czSRefl {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {i j : Fin 4} (hij : i ≠ j) :
    czRDRefl (φ := φ) hd hij * czSRefl (e := e) hd j *
        (czRDRefl (φ := φ) hd hij)⁻¹ = czSRefl (e := e) hd i := by
  ext v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, czRDRefl_inv]
  have hd' : ∀ a b, φ a (e b) = if a = b then 1 else 0 := hd
  have hji : j ≠ i := fun h => hij h.symm
  simp only [czRDRefl_apply, czSRefl_apply, map_sub, map_smul, hd', hij, hji, if_true,
    if_false]
  module

private def czHForm {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (w : Fin 4 → ZMod p) (v : V) : V :=
  v - ((2 : ZMod p)⁻¹ * ∑ k, w k * φ k v) • ∑ k, w k • e k

private theorem czSRefl_conj_czHForm {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {w : Fin 4 → ZMod p} (k : Fin 4)
    {r : V ≃ₗ[ZMod p] V} (hr : ∀ v, r v = czHForm (e := e) (φ := φ) w v) (v : V) :
    (czSRefl (e := e) hd k * r * (czSRefl (e := e) hd k)⁻¹) v =
      czHForm (e := e) (φ := φ) (Function.update w k (- w k)) v := by
  have hd' : ∀ i j, φ i (e j) = if i = j then 1 else 0 := hd
  rw [czSRefl_inv]
  simp only [LinearEquiv.mul_apply]
  rw [hr]
  fin_cases k <;>
    simp only [czHForm, czSRefl_apply, Fin.sum_univ_four, Function.update_apply,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, if_true, neg_mul, neg_smul, Fin.isValue] <;>
    simp [hd', map_sub, map_smul, map_add, smul_eq_mul] <;>
    module

private lemma neg_eq_of_ne_of_pm_one {p : ℕ} [Fact p.Prime] {a b : ZMod p}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hne : a ≠ b) : -a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

private def czW3 (p : ℕ) : Fin 4 → ZMod p := ![1, -1, -1, -1]

private lemma update_pm_one {p : ℕ} {w : Fin 4 → ZMod p} (hw : ∀ k, w k = 1 ∨ w k = -1)
    (k : Fin 4) (c : ZMod p) (hc : c = 1 ∨ c = -1) :
    ∀ j, Function.update w k c j = 1 ∨ Function.update w k c j = -1 := by
  intro j
  by_cases hj : j = k
  · subst hj
    simpa using hc
  · rw [Function.update_of_ne hj]
    exact hw j

private theorem czHForm_target {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hS : ∀ i, czSRefl (e := e) hd i ∈ A) {r : V ≃ₗ[ZMod p] V} {w : Fin 4 → ZMod p}
    (hw : ∀ k, w k = 1 ∨ w k = -1)
    (hr : ∀ v, r v = czHForm (e := e) (φ := φ) w v) (hrmem : r ∈ A)
    {u : Fin 4 → ZMod p} (hu : ∀ k, u k = 1 ∨ u k = -1) :
    ∃ r' ∈ A, ∀ v, r' v = czHForm (e := e) (φ := φ) u v := by
  have step : ∀ (k : Fin 4) (r : V ≃ₗ[ZMod p] V) (w : Fin 4 → ZMod p),
      (∀ j, w j = 1 ∨ w j = -1) → (∀ v, r v = czHForm (e := e) (φ := φ) w v) → r ∈ A →
      ∃ r' ∈ A, ∀ v, r' v = czHForm (e := e) (φ := φ) (Function.update w k (u k)) v := by
    intro k r w hw hr hrmem
    by_cases hwk : w k = u k
    · have hupd : Function.update w k (u k) = w := by
        funext j
        by_cases hj : j = k
        · subst hj
          rw [Function.update_self, hwk]
        · rw [Function.update_of_ne hj]
      exact ⟨r, hrmem, fun v => by rw [hr, hupd]⟩
    · refine ⟨czSRefl (e := e) hd k * r * (czSRefl (e := e) hd k)⁻¹,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (hS k) hrmem) (Subgroup.inv_mem _ (hS k)),
        fun v => ?_⟩
      rw [czSRefl_conj_czHForm hd k hr v,
        neg_eq_of_ne_of_pm_one (hw k) (hu k) hwk]
  obtain ⟨r1, h1mem, h1⟩ := step 0 r w hw hr hrmem
  obtain ⟨r2, h2mem, h2⟩ :=
    step 1 r1 (Function.update w 0 (u 0))
      (update_pm_one hw 0 (u 0) (hu 0)) h1 h1mem
  obtain ⟨r3, h3mem, h3⟩ :=
    step 2 r2 (Function.update (Function.update w 0 (u 0)) 1 (u 1))
      (update_pm_one (update_pm_one hw 0 _ (hu 0)) 1 _ (hu 1)) h2 h2mem
  obtain ⟨r4, h4mem, h4⟩ :=
    step 3 r3
      (Function.update (Function.update (Function.update w 0 (u 0)) 1 (u 1)) 2 (u 2))
      (update_pm_one (update_pm_one (update_pm_one hw 0 _ (hu 0)) 1 _ (hu 1)) 2 _
        (hu 2)) h3 h3mem
  have hw4eq :
      Function.update
        (Function.update (Function.update (Function.update w 0 (u 0)) 1 (u 1)) 2 (u 2)) 3
        (u 3) = u := by
    funext k
    fin_cases k <;> simp
  exact ⟨r4, h4mem, fun v => by rw [h4, hw4eq]⟩

private lemma zmod_half_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p)⁻¹ * 2 = 1 :=
  inv_mul_cancel₀ (zmod_two_ne_zero hp2)

private lemma zmod_half_four {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p)⁻¹ * 4 = 2 := by
  rw [show (4 : ZMod p) = 2 * 2 by ring, ← mul_assoc, inv_mul_cancel₀ (zmod_two_ne_zero hp2),
    one_mul]

private lemma zmod_half_sum_four {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p)⁻¹ * (1 + 1 + 1 + 1) = 2 := by
  rw [show (1 : ZMod p) + 1 + 1 + 1 = 4 by ring, zmod_half_four hp2]

private def czHvec (p : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (e : Fin 4 → V) : Fin 4 → V :=
  ![e 1 - e 2, e 2 - e 3, 2 • e 3, e 0 - e 1 - e 2 - e 3]

private def czAlpha (p : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (φ : Fin 4 → Module.Dual (ZMod p) V) : Fin 4 → Module.Dual (ZMod p) V :=
  ![(φ 1 - φ 2), (φ 2 - φ 3), φ 3, (2 : ZMod p)⁻¹ • (φ 0 - φ 1 - φ 2 - φ 3)]

private theorem czHvec_alpha_self {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hp2 : p ≠ 2) (hd : GGCZDual e φ) :
    ∀ i, czAlpha p φ i (czHvec p e i) = 2 := by
  have hd' : ∀ a b, φ a (e b) = if a = b then 1 else 0 := hd
  intro i
  fin_cases i <;>
    simp [czAlpha, czHvec, hd', zmod_half_sum_four hp2] <;>
    ring

private theorem czHvec_alpha_pair {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hp2 : p ≠ 2) (hd : GGCZDual e φ) :
    ∀ i j, czAlpha p φ i (czHvec p e j) = (CartanMatrix.F₄ i j : ZMod p) := by
  have hd' : ∀ a b, φ a (e b) = if a = b then 1 else 0 := hd
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [czAlpha, czHvec, hd', CartanMatrix.F₄, zmod_half_two hp2, zmod_half_sum_four hp2] <;>
    ring

private theorem czHForm_czW3_apply {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V} (v : V) :
    czHForm (e := e) (φ := φ) (czW3 p) v =
      v - ((2 : ZMod p)⁻¹ * (φ 0 v - φ 1 v - φ 2 v - φ 3 v)) •
        (e 0 - e 1 - e 2 - e 3) := by
  simp [czHForm, czW3, Fin.sum_univ_four]
  module

private theorem ggCZ_exists_sChange (h : GGCaseZeroData p B Bs x L D J 𝒦)
    (ιV : Additive ↥Bs ≃+ V) {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hA : Subgroup.map (ggLin (p := p) ιV) (ggAutomizerJoin L Bs 𝒦) = ggCZWB p e φ)
    (hne : ggAutomizerJoin L Bs 𝒦 ≠ ggAutomizer L Bs) (hm3 : 3 ≤ 4)
    (hF : GGCZFrameD p Bs (ggAutomizer L Bs) ιV e φ) :
    ∃ K₀ ∈ 𝒦, ∃ s₀ ∈ ggAutomizer K₀ Bs, GGIsReflection p s₀ ∧
      ggLin (p := p) ιV s₀ ∈ ggCZS e φ := by
  obtain ⟨-, hp2, -, -⟩ := h.basic
  have hd : GGCZDual e φ := hF.1
  have hRDpre : ∀ r ∈ ggCZRD e φ, ∃ a ∈ ggAutomizer L Bs, ggLin (p := p) ιV a = r :=
    hF.2.2.1
  by_contra hcon
  push Not at hcon
  have hjoin : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer L Bs := by
    rw [ggAutomizerJoin]
    refine sup_le le_rfl ?_
    refine iSup₂_le fun K' hK' => ?_
    obtain ⟨y', hy'⟩ := h.cfg.2.2.2.1.2 K' hK'
    rw [h.cfg.2.1 y' K' hy']
    refine (Subgroup.closure_le (ggAutomizer L Bs)).mpr ?_
    rintro r ⟨hrK, hrR⟩
    have hrInf : r ∈ ggAInf p B Bs x L D J := ggAutomizer_le_ggAInf_of_nbr hy' hrK
    have hshape := h.refl_shape hm3 ιV hF r hrInf hrR
    have hrWB : ggLin (p := p) ιV r ∈ ggCZWB p e φ := by
      rw [← hA]
      exact Subgroup.mem_map_of_mem _ (ggAutomizer_le_ggAutomizerJoin (Or.inr hK') hrK)
    rcases hshape with hR | hS | ⟨-, hH⟩
    · obtain ⟨a, haL, haeq⟩ := hRDpre (ggLin (p := p) ιV r) hR
      have har : a = r := ggLin_injective ιV haeq
      rwa [← har]
    · exact absurd hS (hcon K' hK' r hrK hrR)
    · exact absurd hH (ggCZWB_not_mem_H hp2 (by norm_num) hd hrWB)
  exact hne (le_antisymm hjoin le_sup_left)

private theorem ggCZ_exists_join_image (ιV : Additive ↥Bs ≃+ V)
    {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V} (hd : GGCZDual e φ)
    (hRDpre : ∀ r ∈ ggCZRD e φ, ∃ a ∈ ggAutomizer L Bs, ggLin (p := p) ιV a = r)
    {K : Subgroup G} {t : MulAut ↥Bs} (htK : t ∈ ggAutomizer K Bs)
    {K₀ : Subgroup G} {s₀ : MulAut ↥Bs} (hs₀K : s₀ ∈ ggAutomizer K₀ Bs)
    (hs₀S : ggLin (p := p) ιV s₀ ∈ ggCZS e φ) :
    ∃ A' : Subgroup (MulAut ↥Bs),
      A' = ggAutomizer L Bs ⊔ ggAutomizer K₀ Bs ⊔ ggAutomizer K Bs ∧
      t ∈ A' ∧
      (∀ r ∈ ggCZRD e φ, ∃ a ∈ A', ggLin (p := p) ιV a = r) ∧
      (∀ r ∈ ggCZS e φ, ∃ a ∈ A', ggLin (p := p) ιV a = r) := by
  classical
  let 𝒦' : Finset (Subgroup G) := {K₀, K}
  let A' : Subgroup (MulAut ↥Bs) := ggAutomizerJoin L Bs 𝒦'
  have hA'eq : A' = ggAutomizer L Bs ⊔ ggAutomizer K₀ Bs ⊔ ggAutomizer K Bs := by
    simp only [A', ggAutomizerJoin, 𝒦', Finset.iSup_insert, Finset.iSup_singleton]
    rw [sup_assoc]
  have hK₀mem' : K₀ ∈ 𝒦' := by simp [𝒦']
  have hKmem' : K ∈ 𝒦' := by simp [𝒦']
  have hs₀A' : s₀ ∈ A' := ggAutomizer_le_ggAutomizerJoin (Or.inr hK₀mem') hs₀K
  have htA' : t ∈ A' := ggAutomizer_le_ggAutomizerJoin (Or.inr hKmem') htK
  have hRD_map : ggCZRD e φ ⊆ Subgroup.map (ggLin (p := p) ιV) A' := by
    rintro r hr
    obtain ⟨a, haL, haeq⟩ := hRDpre r hr
    exact ⟨a, ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) haL, haeq⟩
  obtain ⟨j, hjform⟩ := hs₀S
  have hs₀_eq : ggLin (p := p) ιV s₀ = czSRefl (e := e) hd j := by
    ext v
    rw [hjform v, czSRefl_apply]
  have hS_map : ggCZS e φ ⊆ Subgroup.map (ggLin (p := p) ιV) A' := by
    rintro r ⟨i, hi⟩
    have hri : r = czSRefl (e := e) hd i := by
      ext v
      rw [hi, czSRefl_apply]
    by_cases hij : i = j
    · subst hij
      exact ⟨s₀, hs₀A', by rw [hs₀_eq, hri]⟩
    · obtain ⟨g, hgA', hgeq⟩ := hRD_map (czRDRefl_mem (p := p) hd hij)
      refine ⟨g * s₀ * g⁻¹,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hgA' hs₀A') (Subgroup.inv_mem _ hgA'), ?_⟩
      rw [map_mul, map_mul, map_inv, hgeq, hs₀_eq, czRDRefl_conj_czSRefl hd hij, hri]
  exact ⟨A', hA'eq, htA', hRD_map, hS_map⟩

private theorem ggCZ_map_automizer_le_F4 (h : GGCaseZeroData p B Bs x L D J 𝒦)
    (ιV : Additive ↥Bs ≃+ V) {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (hm3 : 3 ≤ 4) (hF : GGCZFrameD p Bs (ggAutomizer L Bs) ιV e φ)
    {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K) :
    Subgroup.map (ggLin (p := p) ιV) (ggAutomizer K Bs) ≤ ggCZWF4 p e φ := by
  obtain ⟨-, hp2, -, -⟩ := h.basic
  rw [Subgroup.map_le_iff_le_comap]
  rw [h.cfg.2.1 y K hK]
  refine (Subgroup.closure_le _).mpr ?_
  rintro r ⟨hrK, hrR⟩
  have hrInf : r ∈ ggAInf p B Bs x L D J := ggAutomizer_le_ggAInf_of_nbr hK hrK
  have hshape := h.refl_shape hm3 ιV hF r hrInf hrR
  rcases hshape with hR | hS | ⟨-, hH⟩
  · exact ggCZ_subset_ggCZWF4 hp2 hd (Or.inl (Or.inl hR))
  · exact ggCZ_subset_ggCZWF4 hp2 hd (Or.inl (Or.inr hS))
  · exact ggCZ_subset_ggCZWF4 hp2 hd (Or.inr hH)

private theorem ggCZ_map_le_F4 (h : GGCaseZeroData p B Bs x L D J 𝒦)
    (ιV : Additive ↥Bs ≃+ V) {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ)
    (hA : Subgroup.map (ggLin (p := p) ιV) (ggAutomizerJoin L Bs 𝒦) = ggCZWB p e φ)
    (hm3 : 3 ≤ 4) (hF : GGCZFrameD p Bs (ggAutomizer L Bs) ιV e φ)
    {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K)
    {K₀ : Subgroup G} {y₀ : G} (hK₀nbr : GGNbr p B x D J y₀ K₀)
    {A' : Subgroup (MulAut ↥Bs)}
    (hA'eq : A' = ggAutomizer L Bs ⊔ ggAutomizer K₀ Bs ⊔ ggAutomizer K Bs) :
    Subgroup.map (ggLin (p := p) ιV) A' ≤ ggCZWF4 p e φ := by
  obtain ⟨-, hp2, -, -⟩ := h.basic
  rw [hA'eq, Subgroup.map_sup, Subgroup.map_sup]
  refine sup_le (sup_le ?_ ?_) ?_
  · have h₁ : Subgroup.map (ggLin (p := p) ιV) (ggAutomizer L Bs) ≤
        Subgroup.map (ggLin (p := p) ιV) (ggAutomizerJoin L Bs 𝒦) :=
      Subgroup.map_mono (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl))
    exact h₁.trans (by rw [hA]; exact ggCZWB_le_ggCZWF4 hp2 hd)
  · exact ggCZ_map_automizer_le_F4 h ιV hd hm3 hF hK₀nbr
  · exact ggCZ_map_automizer_le_F4 h ιV hd hm3 hF hK

omit [Finite G] in
private theorem ggCZ_exists_hForm_and_map (ιV : Additive ↥Bs ≃+ V)
    {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V} (hd : GGCZDual e φ)
    {A' : Subgroup (MulAut ↥Bs)} {t : MulAut ↥Bs} (htA' : t ∈ A')
    (hS : ggCZS e φ ⊆ Subgroup.map (ggLin (p := p) ιV) A')
    (hH : ggLin (p := p) ιV t ∈ ggCZH e φ) :
    ∃ rH ∈ Subgroup.map (ggLin (p := p) ιV) A',
      (∀ v, rH v = czHForm (e := e) (φ := φ) (czW3 p) v) ∧
      ggCZH e φ ⊆ Subgroup.map (ggLin (p := p) ιV) A' := by
  have hw3 : ∀ k, czW3 p k = 1 ∨ czW3 p k = -1 := by
    intro k
    fin_cases k <;> simp [czW3]
  have hR3 : ∃ r3 ∈ Subgroup.map (ggLin (p := p) ιV) A',
      ∀ v, r3 v = czHForm (e := e) (φ := φ) (czW3 p) v := by
    obtain ⟨w₀, hw₀, hform₀⟩ := hH
    have htmap : ggLin (p := p) ιV t ∈ Subgroup.map (ggLin (p := p) ιV) A' :=
      Subgroup.mem_map_of_mem _ htA'
    exact czHForm_target (p := p) hd (A := Subgroup.map (ggLin (p := p) ιV) A')
      (fun i => hS (czSRefl_mem (p := p) hd i)) (w := w₀) hw₀ hform₀ htmap
      (u := czW3 p) hw3
  obtain ⟨rH, hrHmem, hrHform⟩ := hR3
  refine ⟨rH, hrHmem, hrHform, ?_⟩
  rintro r ⟨w, hw, hform⟩
  obtain ⟨r', hr'mem, hr'form⟩ :=
    czHForm_target (p := p) hd (A := Subgroup.map (ggLin (p := p) ιV) A')
      (fun i => hS (czSRefl_mem (p := p) hd i)) (w := czW3 p) hw3 hrHform hrHmem
      (u := w) hw
  have hrr : r = r' := by
    ext v
    rw [hform v, hr'form v]
    rfl
  rw [hrr]
  exact hr'mem

omit [Finite G] in
private theorem ggCZ_map_ge_F4 (ιV : Additive ↥Bs ≃+ V) {e : Fin 4 → V}
    {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {A' : Subgroup (MulAut ↥Bs)} {rH : V ≃ₗ[ZMod p] V}
    (hrHform : ∀ v, rH v = czHForm (e := e) (φ := φ) (czW3 p) v)
    (hRD : ggCZRD e φ ⊆ Subgroup.map (ggLin (p := p) ιV) A')
    (hS : ggCZS e φ ⊆ Subgroup.map (ggLin (p := p) ιV) A')
    (hH : ggCZH e φ ⊆ Subgroup.map (ggLin (p := p) ιV) A') :
    ggCZWF4 p e φ ≤ Subgroup.map (ggLin (p := p) ιV) A' := by
  have hw3 : ∀ k, czW3 p k = 1 ∨ czW3 p k = -1 := by
    intro k
    fin_cases k <;> simp [czW3]
  have hrHmem : rH ∈ Subgroup.map (ggLin (p := p) ιV) A' :=
    hH ⟨czW3 p, hw3, hrHform⟩
  rw [ggCZWF4]
  refine (Subgroup.closure_le _).mpr ?_
  rintro r ⟨i, hi⟩
  fin_cases i
  · have hr : r = czRDRefl (φ := φ) hd (by decide : (1 : Fin 4) ≠ 2) := by
      ext v
      rw [hi, czRDRefl_apply]
    rw [hr]
    exact hRD (czRDRefl_mem (p := p) hd (by decide : (1 : Fin 4) ≠ 2))
  · have hr : r = czRDRefl (φ := φ) hd (by decide : (2 : Fin 4) ≠ 3) := by
      ext v
      rw [hi, czRDRefl_apply]
    rw [hr]
    exact hRD (czRDRefl_mem (p := p) hd (by decide : (2 : Fin 4) ≠ 3))
  · have hr : r = czSRefl (e := e) hd 3 := by
      ext v
      rw [hi, czSRefl_apply]
    rw [hr]
    exact hS (czSRefl_mem (p := p) hd 3)
  · have hr : r = rH := by
      ext v
      rw [hi, hrHform v, czHForm_czW3_apply]
    rw [hr]
    exact hrHmem

omit [Finite G] in
private theorem ggCZ_exists_psi (hp2 : p ≠ 2) (ιV : Additive ↥Bs ≃+ V)
    {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V} (hd : GGCZDual e φ)
    {A' : Subgroup (MulAut ↥Bs)} (hA'le : A' ≤ ggAutomizer ⊤ Bs)
    (hRD : ggCZRD e φ ⊆ Subgroup.map (ggLin (p := p) ιV) A')
    (hS : ggCZS e φ ⊆ Subgroup.map (ggLin (p := p) ιV) A')
    {rH : V ≃ₗ[ZMod p] V} (hrHmem : rH ∈ Subgroup.map (ggLin (p := p) ιV) A')
    (hrHform : ∀ v, rH v = czHForm (e := e) (φ := φ) (czW3 p) v) :
    ∃ ψ : Fin 4 → MulAut ↥Bs,
      (∀ i, ψ i ∈ A') ∧
      (∀ i, ggLin (p := p) ιV (ψ i) =
        ![czRDRefl (φ := φ) hd (by decide : (1 : Fin 4) ≠ 2),
          czRDRefl (φ := φ) hd (by decide : (2 : Fin 4) ≠ 3),
          czSRefl (e := e) hd 3, rH] i) ∧
      (∀ i, ψ i ∈ ggInduced ⊤ Bs) ∧
      (∀ i, ggLin (p := p) ιV (ψ i) = reflection (czHvec_alpha_self hp2 hd i)) := by
  classical
  let rgen : Fin 4 → V ≃ₗ[ZMod p] V :=
    ![czRDRefl (φ := φ) hd (by decide : (1 : Fin 4) ≠ 2),
      czRDRefl (φ := φ) hd (by decide : (2 : Fin 4) ≠ 3),
      czSRefl (e := e) hd 3,
      rH]
  have hrgen_mem : ∀ i, rgen i ∈ Subgroup.map (ggLin (p := p) ιV) A' := by
    intro i
    fin_cases i
    · exact hRD (czRDRefl_mem (p := p) hd (by decide : (1 : Fin 4) ≠ 2))
    · exact hRD (czRDRefl_mem (p := p) hd (by decide : (2 : Fin 4) ≠ 3))
    · exact hS (czSRefl_mem (p := p) hd 3)
    · exact hrHmem
  let ψ : Fin 4 → MulAut ↥Bs := fun i =>
    Classical.choose (Subgroup.mem_map.mp (hrgen_mem i))
  have hψA' : ∀ i, ψ i ∈ A' := fun i =>
    (Classical.choose_spec (Subgroup.mem_map.mp (hrgen_mem i))).1
  have hψlin : ∀ i, ggLin (p := p) ιV (ψ i) = rgen i := fun i =>
    (Classical.choose_spec (Subgroup.mem_map.mp (hrgen_mem i))).2
  have hψ_ind : ∀ i, ψ i ∈ ggInduced ⊤ Bs := fun i =>
    mem_ggInduced_top_of_mem_ggAutomizer (hA'le (hψA' i))
  have hlin : ∀ i, ggLin (p := p) ιV (ψ i) = reflection (czHvec_alpha_self hp2 hd i) := by
    intro i
    rw [hψlin i]
    fin_cases i <;> ext v
    all_goals simp [rgen, czAlpha, czHvec, czRDRefl_apply, czSRefl_apply, czHForm_czW3_apply,
      hrHform, Module.reflection_apply]
    all_goals module
  exact ⟨ψ, hψA', hψlin, hψ_ind, hlin⟩

omit [Finite G] in
private theorem ggCZ_weyl_closure (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (ιV : Additive ↥Bs ≃+ V) {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {ψ : Fin 4 → MulAut ↥Bs}
    (hψ_ind : ∀ i, ψ i ∈ ggInduced ⊤ Bs)
    (hlin : ∀ i, ggLin (p := p) ιV (ψ i) = reflection (czHvec_alpha_self hp2 hd i)) :
    GGWeylReflectionGroup p (Subgroup.closure (Set.range ψ)) := by
  have hPall : ∀ i j, czAlpha p φ i (czHvec p e j) = (CartanMatrix.F₄ i j : ZMod p) :=
    czHvec_alpha_pair hp2 hd
  have hdet : (Matrix.of fun i j => czAlpha p φ i (czHvec p e j)).det ≠ 0 := by
    have hmat : (Matrix.of fun i j => czAlpha p φ i (czHvec p e j)) =
        (CartanMatrix.F₄.map (Int.castRingHom (ZMod p))) := by
      ext i j
      simpa [Matrix.of_apply, Matrix.map_apply] using hPall i j
    rw [hmat]
    change ((Int.castRingHom (ZMod p)).mapMatrix CartanMatrix.F₄).det ≠ 0
    rw [← RingHom.map_det]
    have h1 : CartanMatrix.F₄.det = 1 := by decide
    rw [h1, map_one]
    exact one_ne_zero
  have hind : LinearIndependent (ZMod p) (czHvec p e) :=
    linearIndependent_of_det_ne_zero (czHvec p e) (czAlpha p φ) hdet
  have hM : GGIsWeylMatrix (CoxeterMatrix.F₄) := by
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 4), ?_⟩))))
    exact (CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)).symm
  have hMfixed : GGIsWeylMatrixFixed (CoxeterMatrix.F₄) := by
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 4), ?_⟩))))
    exact (CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)).symm
  have hFT : TauCeti.IsFiniteType CartanMatrix.F₄ :=
    isFiniteType_of_ggIsWeylMatrixFixed hMfixed ggIntCartan_F₄
  exact ggWeylReflectionGroup_of_label_of_isFiniteType hp2 hNT hM ggIntCartan_F₄ hFT ψ
    hψ_ind ιV (czHvec p e) (czAlpha p φ) (czHvec_alpha_self hp2 hd) hlin hind 2 0
    (fun i j _ => hPall i j) (by decide)

omit [Finite G] in
private theorem ggCZ_weyl_A' (ιV : Additive ↥Bs ≃+ V) {e : Fin 4 → V}
    {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {A' : Subgroup (MulAut ↥Bs)} {rH : V ≃ₗ[ZMod p] V}
    (hrHform : ∀ v, rH v = czHForm (e := e) (φ := φ) (czW3 p) v)
    {ψ : Fin 4 → MulAut ↥Bs}
    (hψlin : ∀ i, ggLin (p := p) ιV (ψ i) =
      ![czRDRefl (φ := φ) hd (by decide : (1 : Fin 4) ≠ 2),
        czRDRefl (φ := φ) hd (by decide : (2 : Fin 4) ≠ 3),
        czSRefl (e := e) hd 3, rH] i)
    (hmapA' : Subgroup.map (ggLin (p := p) ιV) A' = ggCZWF4 p e φ)
    (hWeylψ : GGWeylReflectionGroup p (Subgroup.closure (Set.range ψ))) :
    GGWeylReflectionGroup p A' := by
  let rgen : Fin 4 → V ≃ₗ[ZMod p] V :=
    ![czRDRefl (φ := φ) hd (by decide : (1 : Fin 4) ≠ 2),
      czRDRefl (φ := φ) hd (by decide : (2 : Fin 4) ≠ 3),
      czSRefl (e := e) hd 3,
      rH]
  have hrgen_gens : ∀ i, GGCZGensF4 e φ i (rgen i) := by
    intro i
    fin_cases i <;> simp [rgen, GGCZGensF4, czRDRefl_apply, czSRefl_apply,
      czHForm_czW3_apply, hrHform]
  have hrgen_eq : ∀ {i : Fin 4} {r : V ≃ₗ[ZMod p] V}, GGCZGensF4 e φ i r → rgen i = r := by
    intro i r h
    ext v
    fin_cases i <;>
      simp_all [GGCZGensF4, rgen, czRDRefl_apply, czSRefl_apply, czHForm_czW3_apply]
  have himage : (ggLin (p := p) ιV) '' Set.range ψ = {r | ∃ i, GGCZGensF4 e φ i r} := by
    ext r
    constructor
    · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by rw [hψlin i]; exact hrgen_gens i⟩
    · rintro ⟨i, hi⟩
      exact ⟨ψ i, ⟨i, rfl⟩, by rw [hψlin i]; exact hrgen_eq hi⟩
  have hmapψ : Subgroup.map (ggLin (p := p) ιV) (Subgroup.closure (Set.range ψ)) =
      ggCZWF4 p e φ := by
    rw [ggCZWF4, MonoidHom.map_closure, himage]
  have hA'eqψ : A' = Subgroup.closure (Set.range ψ) :=
    Subgroup.map_injective (ggLin_injective ιV) (hmapA'.trans hmapψ.symm)
  rw [hA'eqψ]
  exact hWeylψ

private theorem ggCZ_false_of_weyl_A' (h : GGCaseZeroData p B Bs x L D J 𝒦)
    (ιV : Additive ↥Bs ≃+ V) {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ)
    (hA : Subgroup.map (ggLin (p := p) ιV) (ggAutomizerJoin L Bs 𝒦) = ggCZWB p e φ)
    {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K)
    {t : MulAut ↥Bs} (hH : ggLin (p := p) ιV t ∈ ggCZH e φ)
    {K₀ : Subgroup G} {y₀ : G} (hK₀nbr : GGNbr p B x D J y₀ K₀)
    {A' : Subgroup (MulAut ↥Bs)}
    (hA'eq : A' = ggAutomizer L Bs ⊔ ggAutomizer K₀ Bs ⊔ ggAutomizer K Bs)
    (hmapA' : Subgroup.map (ggLin (p := p) ιV) A' = ggCZWF4 p e φ)
    (htA' : t ∈ A') (hWeylA' : GGWeylReflectionGroup p A') : False := by
  classical
  obtain ⟨-, hp2, -, -⟩ := h.basic
  let 𝒦' : Finset (Subgroup G) := {K₀, K}
  have hA'join : A' = ggAutomizerJoin L Bs 𝒦' := by
    rw [hA'eq]
    simp only [ggAutomizerJoin, 𝒦', Finset.iSup_insert, Finset.iSup_singleton]
    rw [sup_assoc]
  have hWeylA'join : GGWeylReflectionGroup p (ggAutomizerJoin L Bs 𝒦') := by
    rw [← hA'join]
    exact hWeylA'
  have hleAK : ggAutomizerJoin L Bs 𝒦 ≤ A' := by
    refine (Subgroup.map_le_map_iff_of_injective (f := ggLin (p := p) ιV)
      (ggLin_injective ιV)).mp ?_
    rw [hmapA', hA]
    exact ggCZWB_le_ggCZWF4 hp2 hd
  have ht_not : t ∉ ggAutomizerJoin L Bs 𝒦 := by
    intro hmem
    have hmap_t : ggLin (p := p) ιV t ∈ ggCZWB p e φ := by
      rw [← hA]
      exact Subgroup.mem_map_of_mem _ hmem
    exact ggCZWB_not_mem_H hp2 (by norm_num) hd hmap_t hH
  have hset : GGNbrSet p B x D J 𝒦' := by
    refine ⟨?_, ?_⟩
    · rw [show 𝒦' = insert K₀ {K} from rfl]
      exact (Finset.card_insert_le _ _).trans (by simp)
    · intro X hX
      simp only [𝒦', Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl
      · exact ⟨y₀, hK₀nbr⟩
      · exact ⟨y, hK⟩
  have hcardmax : Nat.card A' ≤ Nat.card (ggAutomizerJoin L Bs 𝒦) := by
    rw [hA'join]
    exact h.cfg.2.2.2.2.2 𝒦' hset hWeylA'join
  have hEq : ggAutomizerJoin L Bs 𝒦 = A' :=
    Subgroup.eq_of_le_of_card_ge hleAK hcardmax
  exact ht_not (hEq.symm ▸ htA')

theorem GGCaseZeroData.false_of_B4_half (h : GGCaseZeroData p B Bs x L D J 𝒦)
    (ιV : Additive ↥Bs ≃+ V) {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ)
    (hA : Subgroup.map (ggLin (p := p) ιV) (ggAutomizerJoin L Bs 𝒦) = ggCZWB p e φ)
    (hne : ggAutomizerJoin L Bs 𝒦 ≠ ggAutomizer L Bs) {y : G} {K : Subgroup G}
    (hK : GGNbr p B x D J y K) {t : MulAut ↥Bs} (htK : t ∈ ggAutomizer K Bs)
    (ht : GGIsReflection p t) (hH : ggLin (p := p) ιV t ∈ ggCZH e φ) : False := by
  have _ := ht
  classical
  obtain ⟨hp, hp2, hBs, hNT⟩ := h.basic
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  obtain ⟨hm3, hF⟩ := h.frameD_of_B (by norm_num) ιV hd hA hne
  have hRDpre : ∀ r ∈ ggCZRD e φ, ∃ a ∈ ggAutomizer L Bs, ggLin (p := p) ιV a = r :=
    hF.2.2.1
  obtain ⟨K₀, hK₀mem, s₀, hs₀K, -, hs₀S⟩ :=
    ggCZ_exists_sChange h ιV hA hne hm3 hF
  obtain ⟨y₀, hK₀nbr⟩ := h.cfg.2.2.2.1.2 K₀ hK₀mem
  obtain ⟨A', hA'eq, htA', hRD_map, hS_map⟩ :=
    ggCZ_exists_join_image ιV hd hRDpre htK hs₀K hs₀S
  have hA'le : A' ≤ ggAutomizer ⊤ Bs := by
    rw [hA'eq]
    exact sup_le (sup_le (ggAutomizer_le_top L Bs) (ggAutomizer_le_top K₀ Bs))
      (ggAutomizer_le_top K Bs)
  have hmap_le : Subgroup.map (ggLin (p := p) ιV) A' ≤ ggCZWF4 p e φ :=
    ggCZ_map_le_F4 h ιV hd hA hm3 hF hK hK₀nbr hA'eq
  obtain ⟨rH, hrHmem, hrHform, hH_map⟩ :=
    ggCZ_exists_hForm_and_map ιV hd htA' hS_map hH
  have hmap_ge : ggCZWF4 p e φ ≤ Subgroup.map (ggLin (p := p) ιV) A' :=
    ggCZ_map_ge_F4 ιV hd hrHform hRD_map hS_map hH_map
  have hmapA' : Subgroup.map (ggLin (p := p) ιV) A' = ggCZWF4 p e φ :=
    le_antisymm hmap_le hmap_ge
  obtain ⟨ψ, hψA', hψlin, hψ_ind, hlin⟩ :=
    ggCZ_exists_psi hp2 ιV hd hA'le hRD_map hS_map hrHmem hrHform
  have hWeylψ : GGWeylReflectionGroup p (Subgroup.closure (Set.range ψ)) :=
    ggCZ_weyl_closure hp2 hNT ιV hd hψ_ind hlin
  have hWeylA' : GGWeylReflectionGroup p A' :=
    ggCZ_weyl_A' ιV hd hrHform hψlin hmapA' hWeylψ
  exact ggCZ_false_of_weyl_A' h ιV hd hA hK hH hK₀nbr hA'eq hmapA' htA' hWeylA'

end

end CFSG.StandardType

end
