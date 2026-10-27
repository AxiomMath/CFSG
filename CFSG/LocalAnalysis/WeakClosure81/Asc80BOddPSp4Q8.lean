module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSpAniso

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCSpFull CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

namespace SpSeitz

variable {r : ℕ} {K : Type} [Field K]

theorem spTransvection_mul_same (v : Fin r ⊕ Fin r → K) (s t : K) :
    spTransvection v s * spTransvection v t = spTransvection v (s + t) := by
  apply spLin_injective
  rw [map_mul]
  refine Units.ext (LinearMap.ext fun y => ?_)
  change spEnd (spTransvection v s) (spEnd (spTransvection v t) y) =
    spEnd (spTransvection v (s + t)) y
  simp only [spEnd_spTransvection, map_add, map_smul, spForm_isAlt.self_eq_zero,
    mul_zero, zero_smul, add_zero]
  module

theorem spTransvection_zero_right (v : Fin r ⊕ Fin r → K) : spTransvection v (0 : K) = 1 := by
  apply spLin_injective
  rw [map_one]
  refine Units.ext (LinearMap.ext fun y => ?_)
  change spEnd (spTransvection v 0) y = y
  rw [spEnd_spTransvection, zero_mul, zero_smul, add_zero]

theorem commute_spTransvection_of_orth {u v : Fin r ⊕ Fin r → K} (h : spForm r K u v = 0)
    (s t : K) : spTransvection u s * spTransvection v t = spTransvection v t * spTransvection u s :=
  commute_spTransvection (by rw [spEnd_spTransvection, h, mul_zero, zero_smul, add_zero]) s

theorem spTransvection_neg (v : Fin r ⊕ Fin r → K) (t : K) :
    spTransvection (-v) t = spTransvection v t := by
  rw [show -v = (-1 : K) • v by simp, spTransvection_smul]
  congr 1
  ring

theorem commute_pair {g : StatedSp r K} (hg : spEnd g * spEnd g = -1) {u : Fin r ⊕ Fin r → K}
    (hu : spForm r K u (spEnd g u) = 0) (t : K) :
    spTransvection u t * spTransvection (spEnd g u) t * g =
      g * (spTransvection u t * spTransvection (spEnd g u) t) := by
  have hgg : spEnd g (spEnd g u) = -u := by
    rw [← Module.End.mul_apply, hg, LinearMap.neg_apply, Module.End.one_apply]
  have h1 := spTransvection_conj g u t
  have h2 := spTransvection_conj g (spEnd g u) t
  rw [hgg, spTransvection_neg] at h2
  have key : g * (spTransvection u t * spTransvection (spEnd g u) t) * g⁻¹ =
      spTransvection u t * spTransvection (spEnd g u) t := by
    calc g * (spTransvection u t * spTransvection (spEnd g u) t) * g⁻¹
        = (g * spTransvection u t * g⁻¹) * (g * spTransvection (spEnd g u) t * g⁻¹) := by group
      _ = spTransvection (spEnd g u) t * spTransvection u t := by rw [h1, h2]
      _ = spTransvection u t * spTransvection (spEnd g u) t :=
          (commute_spTransvection_of_orth hu t t).symm
  calc spTransvection u t * spTransvection (spEnd g u) t * g
      = g * (spTransvection u t * spTransvection (spEnd g u) t) * g⁻¹ * g := by rw [key]
    _ = g * (spTransvection u t * spTransvection (spEnd g u) t) := by group

theorem transCenter_quat {E : Subgroup (StatedProj (StatedSp r K))} {a b : StatedSp r K}
    (ha : proj r K a ∈ E) (hb : proj r K b ∈ E) (ha1 : proj r K a ≠ 1) (hb1 : proj r K b ≠ 1)
    (haa : spEnd a * spEnd a = -1) (hbb : spEnd b * spEnd b = -1)
    (hc : spEnd a * spEnd b = -(spEnd b * spEnd a)) {c : Fin r ⊕ Fin r → K}
    (hca : spForm r K c (spEnd a c) = 0) (hcb : spForm r K c (spEnd b c) = 0)
    (hcc : spForm r K c (spEnd a (spEnd b c)) ≠ 0) {m : K} (hm0 : m ≠ 0) (hm1 : m * m ≠ 1)
    (hm2 : m * m ≠ -1) :
    TransCenter (cGen E) (spEnd a c + m • spEnd b c) := by
  set A := spEnd a with hAdef
  set B := spEnd b with hBdef
  have hAA : ∀ v, A (A v) = -v := fun v => by
    rw [← Module.End.mul_apply, haa, LinearMap.neg_apply, Module.End.one_apply]
  have hBB : ∀ v, B (B v) = -v := fun v => by
    rw [← Module.End.mul_apply, hbb, LinearMap.neg_apply, Module.End.one_apply]
  have hBA : ∀ v, B (A v) = -(A (B v)) := fun v => by
    rw [← Module.End.mul_apply, show B * A = -(A * B) by rw [hc, neg_neg],
      LinearMap.neg_apply, Module.End.mul_apply]
  have isoA : ∀ u v, spForm r K (A u) (A v) = spForm r K u v := spEnd_isometry a
  have isoB : ∀ u v, spForm r K (B u) (B v) = spForm r K u v := spEnd_isometry b
  have hsw := spForm_swap (r := r) (K := K)
  set κ := spForm r K (A c) (B c) with hκ
  have hκ' : κ = -spForm r K c (A (B c)) := by
    rw [hκ, ← isoA (A c) (B c), hAA, map_neg, LinearMap.neg_apply]
  have hκ0 : κ ≠ 0 := by rw [hκ']; exact neg_ne_zero.2 hcc
  have hABc_Ac : spForm r K (A (B c)) (A c) = 0 := by rw [isoA, hsw, hcb, neg_zero]
  have hABc_Bc : spForm r K (A (B c)) (B c) = 0 := by
    rw [← isoB]
    simp only [hBA, hBB, map_neg, neg_neg, hsw c (A c), hca, neg_zero]
  set x := A c + m • B c with hx
  set c' := c - m • A (B c) with hc'
  have hAc' : A c' = x := by
    rw [hc', map_sub, map_smul, hAA, hx, smul_neg, sub_neg_eq_add]
  have hc'x : spForm r K c' x = 0 := by
    rw [hc', hx]
    simp only [map_sub, map_add, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, hca, hcb, hABc_Ac, hABc_Bc]
    ring
  have hc'Ac : spForm r K c' (A c) = 0 := by
    rw [hc']
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hca,
      hABc_Ac]
    ring
  have hc'Bc : spForm r K c' (B c) = 0 := by
    rw [hc']
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hcb,
      hABc_Bc]
    ring
  set t := (m - m⁻¹) / κ with ht
  have hg₁ : spTransvection c t * spTransvection (A c) t ∈ cGen E :=
    mem_cGen_of_commute ha ha1 (commute_pair haa hca t)
  have hg₂ : spTransvection c t * spTransvection (B c) t ∈ cGen E :=
    mem_cGen_of_commute hb hb1 (commute_pair hbb hcb t)
  set P := spTransvection (A c) t * spTransvection (B c) (-t) with hP
  have hPmem : P ∈ cGen E := by
    have hcA := commute_spTransvection_of_orth hca t t
    have hcB := commute_spTransvection_of_orth hcb t (-t)
    have : P = (spTransvection c t * spTransvection (A c) t) *
        (spTransvection c t * spTransvection (B c) t)⁻¹ := by
      rw [mul_inv_rev, spTransvection_inv, spTransvection_inv, hP]
      calc spTransvection (A c) t * spTransvection (B c) (-t)
          = spTransvection (A c) t * spTransvection (B c) (-t) *
              (spTransvection c t * spTransvection c (-t)) := by
            rw [spTransvection_mul_same, add_neg_cancel, spTransvection_zero_right, mul_one]
        _ = spTransvection (A c) t * (spTransvection c t * spTransvection (B c) (-t)) *
              spTransvection c (-t) := by rw [hcB]; group
        _ = spTransvection c t * spTransvection (A c) t * spTransvection (B c) (-t) *
              spTransvection c (-t) := by rw [← mul_assoc (spTransvection (A c) t), ← hcA]
        _ = spTransvection c t * spTransvection (A c) t *
              (spTransvection (B c) (-t) * spTransvection c (-t)) := by group
    rw [this]
    exact (cGen E).mul_mem hg₁ ((cGen E).inv_mem hg₂)
  have hPc' : spEnd P c' = c' := by
    rw [hP, spEnd_mul, Module.End.mul_apply, spEnd_spTransvection, spEnd_spTransvection, hc'Bc,
      mul_zero, zero_smul, add_zero, hc'Ac, mul_zero, zero_smul, add_zero]
  have hPx : spEnd P x = (m⁻¹ * m⁻¹) • x := by
    rw [hP, spEnd_mul, Module.End.mul_apply, spEnd_spTransvection, spEnd_spTransvection]
    have e1 : spForm r K x (B c) = κ := by
      rw [hx, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        spForm_isAlt.self_eq_zero, smul_zero, add_zero]
    have e2 : spForm r K (B c) (A c) = -κ := by rw [hsw]
    rw [e1]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      spForm_isAlt.self_eq_zero, e2, hx]
    rw [ht]
    match_scalars <;> field_simp <;> ring
  have hlam : m⁻¹ * m⁻¹ * (m⁻¹ * m⁻¹) - 1 ≠ 0 := by
    intro h
    have h' : (m * m - 1) * (m * m + 1) = 0 := by
      field_simp at h
      linear_combination -h
    rcases mul_eq_zero.1 h' with h'' | h''
    · exact hm1 (sub_eq_zero.1 h'')
    · exact hm2 (eq_neg_of_add_eq_zero_left h'')
  intro w
  set D := m⁻¹ * m⁻¹ * (m⁻¹ * m⁻¹) - 1 with hD
  set s := w / D with hs
  have hg₃ : spTransvection c' s * spTransvection x s ∈ cGen E := by
    have := commute_pair haa (u := c') (by rw [hAc']; exact hc'x) s
    rw [hAc'] at this
    exact mem_cGen_of_commute ha ha1 this
  have hcomm : P * (spTransvection c' s * spTransvection x s) * P⁻¹ *
      (spTransvection c' s * spTransvection x s)⁻¹ = spTransvection x w := by
    have h1 := spTransvection_conj P c' s
    have h2 := spTransvection_conj P x s
    rw [hPc'] at h1
    rw [hPx, spTransvection_smul] at h2
    have h3 : P * (spTransvection c' s * spTransvection x s) * P⁻¹ =
        spTransvection c' s * spTransvection x (m⁻¹ * m⁻¹ * (m⁻¹ * m⁻¹) * s) := by
      rw [show P * (spTransvection c' s * spTransvection x s) * P⁻¹ =
          (P * spTransvection c' s * P⁻¹) * (P * spTransvection x s * P⁻¹) by group, h1, h2]
    rw [h3, mul_inv_rev, spTransvection_inv, spTransvection_inv]
    have hxc' : spForm r K x c' = 0 := by rw [hsw, hc'x, neg_zero]
    have h4 := spTransvection_conj (spTransvection c' s) x
      ((m⁻¹ * m⁻¹ * (m⁻¹ * m⁻¹)) * s + -s)
    rw [spEnd_spTransvection, hxc', mul_zero, zero_smul, add_zero] at h4
    have hw : m⁻¹ * m⁻¹ * (m⁻¹ * m⁻¹) * s + -s = w := by
      rw [show m⁻¹ * m⁻¹ * (m⁻¹ * m⁻¹) * s + -s = D * s by rw [hD]; ring, hs,
        mul_div_cancel₀ _ hlam]
    rw [hw] at h4
    rw [← h4, spTransvection_inv]
    calc spTransvection c' s * spTransvection x (m⁻¹ * m⁻¹ * (m⁻¹ * m⁻¹) * s) *
          (spTransvection x (-s) * spTransvection c' (-s))
        = spTransvection c' s * (spTransvection x (m⁻¹ * m⁻¹ * (m⁻¹ * m⁻¹) * s) *
            spTransvection x (-s)) * spTransvection c' (-s) := by group
      _ = _ := by rw [spTransvection_mul_same, hw]
  rw [← hcomm]
  exact (cGen E).mul_mem ((cGen E).mul_mem ((cGen E).mul_mem hPmem hg₃)
    ((cGen E).inv_mem hPmem)) ((cGen E).inv_mem hg₃)

section Structure

variable {E : Subgroup (StatedProj (StatedSp r K))} {a b : StatedSp r K}

theorem stab_of_ab (hr : 1 ≤ r) (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (ha : proj r K a ∈ E) (hb : proj r K b ∈ E) (ha1 : proj r K a ≠ 1) (hb1 : proj r K b ≠ 1)
    (hab : proj r K a ≠ proj r K b) {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hWa : ∀ w ∈ W, spEnd a w ∈ W) (hWb : ∀ w ∈ W, spEnd b w ∈ W) :
    ∀ g : StatedSp r K, proj r K g ∈ E → ∀ w ∈ W, spEnd g w ∈ W := by
  intro g hg w hw
  have key : ∀ c : StatedSp r K, proj r K g = proj r K c → spEnd c w ∈ W → spEnd g w ∈ W := by
    intro c hgc hcw
    rcases spEnd_eq_or_neg_of_proj_eq hr hgc with h | h
    · rw [h]; exact hcw
    · rw [h, LinearMap.neg_apply]; exact W.neg_mem hcw
  rcases mem_four hE h4 ha hb hg ha1 hb1 hab with h | h | h | h
  · exact key 1 (by rw [h, map_one]) (by rw [spEnd_one, Module.End.one_apply]; exact hw)
  · exact key a h (hWa w hw)
  · exact key b h (hWb w hw)
  · exact key (a * b) (by rw [h, map_mul])
      (by rw [spEnd_mul, Module.End.mul_apply]; exact hWa _ (hWb w hw))

variable (hAA : ∀ v, spEnd a (spEnd a v) = -v) (hBB : ∀ v, spEnd b (spEnd b v) = -v)
  (hBA : ∀ v, spEnd b (spEnd a v) = -(spEnd a (spEnd b v)))
include hAA hBB hBA

theorem exists_quat_eig (h2K : (2 : K) ≠ 0) {x₀ y₀ : K} (hxy : x₀ ^ 2 + y₀ ^ 2 + 1 = 0)
    {X : Submodule K (Fin r ⊕ Fin r → K)} (hXa : ∀ w ∈ X, spEnd a w ∈ X)
    (hXb : ∀ w ∈ X, spEnd b w ∈ X) (hX : X ≠ ⊥) :
    ∃ v ∈ X, v ≠ 0 ∧ spEnd b v = x₀ • v + y₀ • spEnd a v := by
  by_contra hcon
  push Not at hcon
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX
  set R : (Fin r ⊕ Fin r → K) → (Fin r ⊕ Fin r → K) :=
    fun z => -spEnd b z - x₀ • z + y₀ • spEnd a z with hR
  have hRX : ∀ z ∈ X, R z ∈ X := fun z hz =>
    X.add_mem (X.sub_mem (X.neg_mem (hXb z hz)) (X.smul_mem _ hz)) (X.smul_mem _ (hXa z hz))
  have hRe : ∀ z, spEnd b (R z) = x₀ • R z + y₀ • spEnd a (R z) := by
    intro z
    simp only [hR, map_add, map_sub, map_neg, map_smul, hBB, hBA, hAA]
    linear_combination (norm := module) hxy • z
  have hR0 : ∀ z ∈ X, R z = 0 := by
    intro z hz
    by_contra h
    exact hcon _ (hRX z hz) h (hRe z) |>.elim
  have hBz : ∀ z ∈ X, spEnd b z = -x₀ • z + y₀ • spEnd a z := by
    intro z hz
    have := hR0 z hz
    rw [hR] at this
    linear_combination (norm := module) -this
  have h1 := hBz _ (hXa w hw)
  have h2 := hBA w
  rw [h1, hBz w hw, map_add, map_smul, map_smul, hAA] at h2
  have e1 : x₀ • spEnd a w + y₀ • w = 0 := by
    have : (2 : K) • (x₀ • spEnd a w + y₀ • w) = 0 := by
      linear_combination (norm := module) -h2
    exact (smul_eq_zero.1 this).resolve_left h2K
  have e2 : y₀ • spEnd a w - x₀ • w = 0 := by
    have := congrArg (spEnd a) e1
    rw [map_add, map_smul, map_smul, hAA, map_zero] at this
    linear_combination (norm := module) this
  have e3 : spEnd a w = 0 := by
    have : (x₀ ^ 2 + y₀ ^ 2) • spEnd a w = 0 := by
      linear_combination (norm := module) x₀ • e1 + y₀ • e2
    rw [show x₀ ^ 2 + y₀ ^ 2 = -1 by linear_combination hxy, neg_one_smul, neg_eq_zero] at this
    exact this
  apply hw0
  have := hAA w
  rw [e3, map_zero] at this
  exact neg_eq_zero.1 this.symm

omit hAA hBB hBA in
theorem span_pair_stable (T : Module.End K (Fin r ⊕ Fin r → K)) {u w : Fin r ⊕ Fin r → K}
    (h1 : T u ∈ Submodule.span K {u, w}) (h2 : T w ∈ Submodule.span K {u, w}) :
    ∀ z ∈ Submodule.span K {u, w}, T z ∈ Submodule.span K {u, w} := by
  intro z hz
  have hle : Submodule.span K {u, w} ≤ (Submodule.span K {u, w}).comap T := by
    rw [Submodule.span_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact h1
    · exact h2
  exact hle hz

omit hBB in
theorem form_ne_zero_of_quat_eig (hr : 1 ≤ r) (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (ha : proj r K a ∈ E) (hb : proj r K b ∈ E) (ha1 : proj r K a ≠ 1) (hb1 : proj r K b ≠ 1)
    (hab : proj r K a ≠ proj r K b)
    (hani : ∀ W : Submodule K (Fin r ⊕ Fin r → K), (∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0) →
      (∀ g : StatedSp r K, proj r K g ∈ E → ∀ w ∈ W, spEnd g w ∈ W) → W = ⊥)
    {x₀ y₀ : K} {v : Fin r ⊕ Fin r → K} (hv0 : v ≠ 0)
    (hv : spEnd b v = x₀ • v + y₀ • spEnd a v) : spForm r K v (spEnd a v) ≠ 0 := by
  intro h0
  set W := Submodule.span K {v, spEnd a v} with hW
  have hvW : v ∈ W := Submodule.subset_span (by simp)
  have hAvW : spEnd a v ∈ W := Submodule.subset_span (by simp)
  have hAAv : spEnd a (spEnd a v) ∈ W := by rw [hAA]; exact W.neg_mem hvW
  have hWa := span_pair_stable (spEnd a) hAvW hAAv
  have hBv : spEnd b v ∈ W := by
    rw [hv]
    exact W.add_mem (W.smul_mem _ hvW) (W.smul_mem _ hAvW)
  have hBAv : spEnd b (spEnd a v) ∈ W := by
    rw [hBA, hv, map_add, map_smul, map_smul, hAA]
    exact W.neg_mem (W.add_mem (W.smul_mem _ hAvW) (W.smul_mem _ (W.neg_mem hvW)))
  have hWb := span_pair_stable (spEnd b) hBv hBAv
  have hti : ∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0 := by
    intro x hx y hy
    obtain ⟨c₁, d₁, rfl⟩ := Submodule.mem_span_pair.1 hx
    obtain ⟨c₂, d₂, rfl⟩ := Submodule.mem_span_pair.1 hy
    have h0' : spForm r K (spEnd a v) v = 0 := by rw [spForm_swap, h0, neg_zero]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      spForm_isAlt.self_eq_zero, h0, h0']
    ring
  have := hani W hti (stab_of_ab hr hE h4 ha hb ha1 hb1 hab hWa hWb)
  rw [this] at hvW
  exact hv0 ((Submodule.mem_bot K).1 hvW)

end Structure

theorem exists_sp_comb {a : StatedSp r K} (hAA : ∀ v, spEnd a (spEnd a v) = -v) {l μ : K}
    (h : l ^ 2 + μ ^ 2 = 1) :
    ∃ G : StatedSp r K, ∀ v, spEnd G v = l • v + μ • spEnd a v := by
  set T : Module.End K (Fin r ⊕ Fin r → K) := l • 1 + μ • spEnd a with hT
  set T' : Module.End K (Fin r ⊕ Fin r → K) := l • 1 - μ • spEnd a with hT'
  have hTv : ∀ v, T v = l • v + μ • spEnd a v := fun v => by simp [hT]
  have hT'v : ∀ v, T' v = l • v - μ • spEnd a v := fun v => by simp [hT']
  have h1 : T * T' = 1 := LinearMap.ext fun v => by
    rw [Module.End.mul_apply, hT'v, hTv, map_sub, map_smul, map_smul, hAA, Module.End.one_apply]
    linear_combination (norm := module) h • v
  have h2 : T' * T = 1 := LinearMap.ext fun v => by
    rw [Module.End.mul_apply, hTv, hT'v, map_add, map_smul, map_smul, hAA, Module.End.one_apply]
    linear_combination (norm := module) h • v
  set u : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K) := ⟨T, T', h1, h2⟩ with hu
  have hmem : u ∈ sesqUnitaryGroup (spForm r K) := by
    rw [mem_sesqUnitaryGroup]
    intro x y
    change spForm r K (T x) (T y) = spForm r K x y
    have isoA := spEnd_isometry a
    have e : spForm r K (spEnd a x) y = -spForm r K x (spEnd a y) := by
      rw [← isoA, hAA, map_neg, LinearMap.neg_apply]
    rw [hTv, hTv]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, e,
      isoA]
    linear_combination spForm r K x y * h
  have : u ∈ (spLin r K).range := by rw [range_spLin]; exact hmem
  obtain ⟨G, hG⟩ := this
  refine ⟨G, fun v => ?_⟩
  change ((spLin r K G : LinearMap.GeneralLinearGroup K _) : Module.End K _) v = _
  rw [hG]
  exact hTv v

theorem transCenter_sweep {H : Subgroup (StatedSp r K)} {e₁ e₂ z : Fin r ⊕ Fin r → K}
    (h12 : spForm r K e₁ e₂ ≠ 0) (hU : ∀ s t : K, TransCenter H (s • e₁ + t • e₂))
    (hz1 : spForm r K e₁ z = 0) (hz2 : spForm r K e₂ z = 0) {s₀ t₀ : K} (h0 : s₀ ≠ 0 ∨ t₀ ≠ 0)
    (hp : TransCenter H (s₀ • e₁ + t₀ • e₂ + z)) :
    ∀ s t : K, (s ≠ 0 ∨ t ≠ 0) → TransCenter H (s • e₁ + t • e₂ + z) := by
  have h21 : spForm r K e₂ e₁ = -spForm r K e₁ e₂ := spForm_swap e₁ e₂
  have hz1' : spForm r K z e₁ = 0 := by rw [spForm_swap, hz1, neg_zero]
  have hz2' : spForm r K z e₂ = 0 := by rw [spForm_swap, hz2, neg_zero]
  have step : ∀ s₁ t₁ s t : K, TransCenter H (s₁ • e₁ + t₁ • e₂ + z) → s₁ * t - t₁ * s ≠ 0 →
      TransCenter H (s • e₁ + t • e₂ + z) := by
    intro s₁ t₁ s t h1 hd
    have hadd := TransCenter.add h1 (hU (s - s₁) (t - t₁)) (by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        spForm_isAlt.self_eq_zero, h21, hz1', hz2']
      intro h
      apply hd
      have : (s₁ * t - t₁ * s) * spForm r K e₁ e₂ = 0 := by linear_combination h
      exact (mul_eq_zero.1 this).resolve_right h12)
    convert hadd using 1
    module
  intro s t hst
  by_cases hd : s₀ * t - t₀ * s ≠ 0
  · exact step s₀ t₀ s t hp hd
  push Not at hd
  rcases h0 with hs₀ | ht₀
  · have hs : s ≠ 0 := by
      rintro rfl
      rcases hst with h | h
      · exact h rfl
      · exact h ((mul_eq_zero.1 (by linear_combination hd : s₀ * t = 0)).resolve_left hs₀)
    have h1 := step s₀ t₀ 0 1 hp (by simpa using hs₀)
    exact step 0 1 s t h1 (by simpa using hs)
  · have ht : t ≠ 0 := by
      rintro rfl
      rcases hst with h | h
      · exact h ((mul_eq_zero.1 (by linear_combination -hd : t₀ * s = 0)).resolve_left ht₀)
      · exact h rfl
    have h1 := step s₀ t₀ 1 0 hp (by simpa using ht₀)
    exact step 1 0 s t h1 (by simpa using ht)

end SpSeitz

namespace SpSeitz

section Four

variable {K : Type} [Field K]

theorem isSquare_neg_of_not [Finite K] (hK : ¬ IsSquare (-1 : K)) {u : K} (hu0 : u ≠ 0)
    (hu : ¬ IsSquare u) : IsSquare (-u) := by
  classical
  have := Fintype.ofFinite K
  have h1 : quadraticChar K (-1) = -1 := quadraticChar_neg_one_iff_not_isSquare.2 hK
  have h2 : quadraticChar K u = -1 := quadraticChar_neg_one_iff_not_isSquare.2 hu
  rw [← quadraticChar_one_iff_isSquare (neg_ne_zero.2 hu0), neg_eq_neg_one_mul, map_mul, h1, h2]
  norm_num

theorem exists_ne_zero_one_neg_one [Finite K] (h2K : (2 : K) ≠ 0) (h3 : Nat.card K ≠ 3) :
    ∃ s : K, s ≠ 0 ∧ s ≠ 1 ∧ s ≠ -1 := by
  classical
  have := Fintype.ofFinite K
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1, -1} := by
    intro s _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases h0 : s = 0
    · exact Or.inl h0
    by_cases h1 : s = 1
    · exact Or.inr (Or.inl h1)
    exact Or.inr (Or.inr (hcon s h0 h1))
  have h1m : (1 : K) ≠ -1 := (neg_one_ne_one_of_two h2K).symm
  have h0m : (0 : K) ≠ -1 := fun h => one_ne_zero (neg_eq_zero.1 h.symm)
  have hcard : ({0, 1, -1} : Finset K).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h0m]), Finset.card_pair h1m]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ, hcard] at hle
  have hge : 3 ≤ Fintype.card K := by rw [← hcard]; exact Finset.card_le_univ _
  apply h3
  rw [Nat.card_eq_fintype_card]
  omega

theorem exists_quat_vec [Finite K] (h2K : (2 : K) ≠ 0) (hK : ¬ IsSquare (-1 : K))
    {E : Subgroup (StatedProj (StatedSp 2 K))} (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (hani : ∀ W : Submodule K (Fin 2 ⊕ Fin 2 → K), (∀ x ∈ W, ∀ y ∈ W, spForm 2 K x y = 0) →
      (∀ g : StatedSp 2 K, proj 2 K g ∈ E → ∀ w ∈ W, spEnd g w ∈ W) → W = ⊥)
    {a b : StatedSp 2 K} (ha : proj 2 K a ∈ E) (hb : proj 2 K b ∈ E) (ha1 : proj 2 K a ≠ 1)
    (hb1 : proj 2 K b ≠ 1) (hab : proj 2 K a ≠ proj 2 K b)
    (hAA : ∀ v, spEnd a (spEnd a v) = -v) (hBB : ∀ v, spEnd b (spEnd b v) = -v)
    (hBA : ∀ v, spEnd b (spEnd a v) = -(spEnd a (spEnd b v))) :
    ∃ c : Fin 2 ⊕ Fin 2 → K, spForm 2 K c (spEnd a c) = 0 ∧ spForm 2 K c (spEnd b c) = 0 ∧
      spForm 2 K c (spEnd a (spEnd b c)) ≠ 0 := by
  classical
  set A := spEnd a with hAdef
  set B := spEnd b with hBdef
  have isoA : ∀ u v, spForm 2 K (A u) (A v) = spForm 2 K u v := spEnd_isometry a
  have isoB : ∀ u v, spForm 2 K (B u) (B v) = spForm 2 K u v := spEnd_isometry b
  have hsw : ∀ x y : Fin 2 ⊕ Fin 2 → K, spForm 2 K y x = -spForm 2 K x y := spForm_swap
  have hself : ∀ x : Fin 2 ⊕ Fin 2 → K, spForm 2 K x x = 0 := spForm_isAlt.self_eq_zero
  obtain ⟨x₀, y₀, hxy'⟩ := exists_sq_add_sq h2K one_ne_zero one_ne_zero (1 : K)
  have hxy : x₀ ^ 2 + y₀ ^ 2 + 1 = 0 := by linear_combination hxy'
  have hx0 : x₀ ≠ 0 := by
    rintro rfl
    exact hK ⟨y₀, by linear_combination -hxy⟩
  have hfq : ∀ {v : Fin 2 ⊕ Fin 2 → K}, v ≠ 0 → B v = x₀ • v + y₀ • A v →
      spForm 2 K v (A v) ≠ 0 := fun hv0 hv =>
    form_ne_zero_of_quat_eig hAA hBA (r := 2) (by norm_num) hE h4 ha hb ha1 hb1 hab hani hv0 hv
  obtain ⟨v₀, -, hv₀0, hBv₀⟩ := exists_quat_eig hAA hBB hBA h2K hxy (X := ⊤)
    (fun _ _ => Submodule.mem_top) (fun _ _ => Submodule.mem_top) top_ne_bot
  rw [← hAdef, ← hBdef] at hBv₀
  have hω₀ := hfq hv₀0 hBv₀
  set ω₀ := spForm 2 K v₀ (A v₀) with hω₀def
  set W₁ : Submodule K (Fin 2 ⊕ Fin 2 → K) :=
    (spForm 2 K).orthogonal (Submodule.span K {v₀, A v₀}) with hW₁
  have hmem : ∀ w, w ∈ W₁ ↔ spForm 2 K v₀ w = 0 ∧ spForm 2 K (A v₀) w = 0 := by
    intro w
    rw [hW₁, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      exact ⟨h v₀ (Submodule.subset_span (by simp)), h (A v₀) (Submodule.subset_span (by simp))⟩
    · rintro ⟨h1, h2⟩ n hn
      obtain ⟨c₁, d₁, rfl⟩ := Submodule.mem_span_pair.1 hn
      change spForm 2 K (c₁ • v₀ + d₁ • A v₀) w = 0
      rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, h1, h2, smul_zero, smul_zero, add_zero]
  have hW₁a : ∀ w ∈ W₁, A w ∈ W₁ := by
    intro w hw
    obtain ⟨h1, h2⟩ := (hmem w).1 hw
    refine (hmem _).2 ⟨?_, ?_⟩
    · rw [← isoA, hAA, map_neg, h2, neg_zero]
    · rw [isoA, h1]
  have hW₁b : ∀ w ∈ W₁, B w ∈ W₁ := by
    intro w hw
    obtain ⟨h1, h2⟩ := (hmem w).1 hw
    refine (hmem _).2 ⟨?_, ?_⟩
    · rw [← isoB, hBB, hBv₀]
      simp only [map_neg, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        h1, h2, smul_zero, add_zero, neg_zero]
    · rw [← isoB, hBB, hBA, hBv₀]
      simp only [map_neg, map_add, map_smul, hAA, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.neg_apply, h1, h2, smul_zero, add_zero, neg_zero]
  have hW₁0 : W₁ ≠ ⊥ := by
    intro h
    have hf := LinearMap.BilinForm.finrank_orthogonal (spForm_nondegenerate (r := 2) (K := K))
      (Submodule.span K {v₀, A v₀})
    rw [← hW₁, h, finrank_bot] at hf
    have hle : Module.finrank K (Submodule.span K ({v₀, A v₀} : Set (Fin 2 ⊕ Fin 2 → K))) ≤ 2 := by
      have := finrank_span_finset_le_card (R := K) ({v₀, A v₀} : Finset (Fin 2 ⊕ Fin 2 → K))
      rw [Finset.coe_insert, Finset.coe_singleton] at this
      exact this.trans Finset.card_le_two
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at hf
    omega
  obtain ⟨v₁, hv₁W, hv₁0, hBv₁⟩ := exists_quat_eig hAA hBB hBA h2K hxy hW₁a hW₁b hW₁0
  rw [← hAdef, ← hBdef] at hBv₁
  have hω₁ := hfq hv₁0 hBv₁
  set ω₁ := spForm 2 K v₁ (A v₁) with hω₁def
  obtain ⟨g1, g2⟩ := (hmem v₁).1 hv₁W
  obtain ⟨g3, g4⟩ := (hmem _).1 (hW₁a v₁ hv₁W)
  have g1' : spForm 2 K v₁ v₀ = 0 := by rw [hsw, g1, neg_zero]
  have g2' : spForm 2 K v₁ (A v₀) = 0 := by rw [hsw, g2, neg_zero]
  have g3' : spForm 2 K (A v₁) v₀ = 0 := by rw [hsw, g3, neg_zero]
  have g4' : spForm 2 K (A v₁) (A v₀) = 0 := by rw [hsw, g4, neg_zero]
  have h00 : spForm 2 K (A v₀) v₀ = -ω₀ := by rw [hsw]
  have h11 : spForm 2 K (A v₁) v₁ = -ω₁ := by rw [hsw]
  have hμ : IsSquare (ω₁ / ω₀) := by
    by_contra hns
    obtain ⟨ν, hν⟩ := isSquare_neg_of_not hK (div_ne_zero hω₁ hω₀) hns
    have hz0 : ν • v₀ + v₁ ≠ 0 := by
      intro h
      have := congrArg (fun w => spForm 2 K w (A v₁)) h
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, g3,
        map_zero, LinearMap.zero_apply, mul_zero, zero_add] at this
      exact hω₁ this
    have hBz : B (ν • v₀ + v₁) = x₀ • (ν • v₀ + v₁) + y₀ • A (ν • v₀ + v₁) := by
      rw [map_add, map_smul, hBv₀, hBv₁, map_add, map_smul]
      module
    apply hfq hz0 hBz
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, g3,
      g2']
    rw [← hω₀def, ← hω₁def]
    have : ω₁ = -(ν * ν) * ω₀ := by
      rw [← hν]
      field_simp
    rw [this]
    ring
  obtain ⟨κ, hκ⟩ := hμ
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    rw [mul_zero, div_eq_zero_iff] at hκ
    exact hκ.elim hω₁ hω₀
  have hω₁κ : ω₁ = κ * κ * ω₀ := by
    rw [← hκ]
    field_simp
  refine ⟨v₀ + (κ⁻¹ * x₀) • A v₁ - (κ⁻¹ * y₀) • v₁, ?_, ?_, ?_⟩
  · have hAc : A (v₀ + (κ⁻¹ * x₀) • A v₁ - (κ⁻¹ * y₀) • v₁) =
        A v₀ - (κ⁻¹ * x₀) • v₁ - (κ⁻¹ * y₀) • A v₁ := by
      rw [map_sub, map_add, map_smul, map_smul, hAA]
      module
    rw [hAc]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, hself, g1, g3, g2', g4', h11]
    rw [← hω₀def, ← hω₁def, hω₁κ]
    field_simp
    linear_combination (κ * κ * ω₀) * hxy
  · have hBc : B (v₀ + (κ⁻¹ * x₀) • A v₁ - (κ⁻¹ * y₀) • v₁) =
        x₀ • v₀ + y₀ • A v₀ + κ⁻¹ • A v₁ := by
      rw [map_sub, map_add, map_smul, map_smul, hBv₀, hBA, hBv₁, map_add, map_smul, map_smul, hAA]
      linear_combination (norm := module) hxy • ((-κ⁻¹) • A v₁)
    rw [hBc]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, hself, g3, g1', g2', g3', g4']
    rw [← hω₀def, ← hω₁def, hω₁κ]
    field_simp
    ring
  · have hABc : A (B (v₀ + (κ⁻¹ * x₀) • A v₁ - (κ⁻¹ * y₀) • v₁)) =
        x₀ • A v₀ - y₀ • v₀ - κ⁻¹ • v₁ := by
      rw [map_sub, map_add, map_smul, map_smul, hBv₀, hBA, hBv₁, map_add, map_smul, map_smul, hAA]
      simp only [map_add, map_sub, map_neg, map_smul, hAA]
      linear_combination (norm := module) hxy • ((κ⁻¹) • v₁)
    rw [hABc]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, hself, g1, g1', g2', g3', g4', h11]
    rw [hω₁κ]
    intro h
    have hκκ : κ⁻¹ * κ = 1 := inv_mul_cancel₀ hκ0
    apply mul_ne_zero (mul_ne_zero h2K hx0) hω₀
    linear_combination h - x₀ * ω₀ * (1 + κ⁻¹ * κ) * hκκ

variable {E : Subgroup (StatedProj (StatedSp 2 K))} {a b : StatedSp 2 K}

theorem eq_zero_of_sq_add_sq (hK : ¬ IsSquare (-1 : K)) {s t : K} (h : s ^ 2 + t ^ 2 = 0) :
    s = 0 ∧ t = 0 := by
  by_cases ht : t = 0
  · rw [ht] at h
    exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by simpa using h), ht⟩
  · exact (hK ⟨s / t, by field_simp; linear_combination -h⟩).elim

theorem transCenter_span_ab (hK : ¬ IsSquare (-1 : K)) (ha : proj 2 K a ∈ E)
    (hb : proj 2 K b ∈ E) (ha1 : proj 2 K a ≠ 1) (hb1 : proj 2 K b ≠ 1)
    (haa : spEnd a * spEnd a = -1) (hbb : spEnd b * spEnd b = -1)
    (hc : spEnd a * spEnd b = -(spEnd b * spEnd a)) {c : Fin 2 ⊕ Fin 2 → K}
    (hca : spForm 2 K c (spEnd a c) = 0) (hcb : spForm 2 K c (spEnd b c) = 0)
    (hcc : spForm 2 K c (spEnd a (spEnd b c)) ≠ 0) {m : K} (hm0 : m ≠ 0) (hm1 : m * m ≠ 1)
    (hm2 : m * m ≠ -1) (α β : K) :
    TransCenter (cGen E) (α • spEnd a c + β • spEnd b c) := by
  have hAA : ∀ v, spEnd a (spEnd a v) = -v := fun v => by
    rw [← Module.End.mul_apply, haa, LinearMap.neg_apply, Module.End.one_apply]
  have hBB : ∀ v, spEnd b (spEnd b v) = -v := fun v => by
    rw [← Module.End.mul_apply, hbb, LinearMap.neg_apply, Module.End.one_apply]
  have hBA : ∀ v, spEnd b (spEnd a v) = -(spEnd a (spEnd b v)) := fun v => by
    rw [← Module.End.mul_apply, show spEnd b * spEnd a = -(spEnd a * spEnd b) by rw [hc, neg_neg],
      LinearMap.neg_apply, Module.End.mul_apply]
  set A := spEnd a with hAdef
  set B := spEnd b with hBdef
  have isoA : ∀ u v, spForm 2 K (A u) (A v) = spForm 2 K u v := spEnd_isometry a
  have isoB : ∀ u v, spForm 2 K (B u) (B v) = spForm 2 K u v := spEnd_isometry b
  have hsw : ∀ x y : Fin 2 ⊕ Fin 2 → K, spForm 2 K y x = -spForm 2 K x y := spForm_swap
  have hself : ∀ x : Fin 2 ⊕ Fin 2 → K, spForm 2 K x x = 0 := spForm_isAlt.self_eq_zero
  have f1 : spForm 2 K (A (B c)) (A c) = 0 := by rw [isoA, hsw, hcb, neg_zero]
  have f2 : spForm 2 K (A (B c)) (B c) = 0 := by
    rw [← isoB]
    simp only [hBA, hBB, map_neg, neg_neg, hsw c (A c), hca, neg_zero]
  have f4 : spForm 2 K (A (B c)) c = -spForm 2 K c (A (B c)) := by rw [hsw]
  have hd : 1 + m * m ≠ 0 := fun h => hm2 (by linear_combination h)
  by_cases h0 : α = 0 ∧ β = 0
  · rw [h0.1, h0.2, zero_smul, zero_smul, add_zero]
    exact transCenter_zero
  set s := (α + m * β) / (1 + m * m) with hs
  set t := (m * α - β) / (1 + m * m) with ht
  have hst : ¬ (s = 0 ∧ t = 0) := by
    rintro ⟨h1, h2⟩
    apply h0
    rw [hs, div_eq_zero_iff] at h1
    rw [ht, div_eq_zero_iff] at h2
    have e1 := h1.resolve_right hd
    have e2 := h2.resolve_right hd
    constructor
    · have : (1 + m * m) * α = 0 := by linear_combination e1 + m * e2
      exact (mul_eq_zero.1 this).resolve_left hd
    · have : (1 + m * m) * β = 0 := by linear_combination m * e1 - e2
      exact (mul_eq_zero.1 this).resolve_left hd
  set c'' := s • c + t • A (B c) with hc''
  have hAc'' : A c'' = s • A c - t • B c := by
    rw [hc'', map_add, map_smul, map_smul, hAA, smul_neg, sub_eq_add_neg]
  have hBc'' : B c'' = s • B c + t • A c := by
    rw [hc'', map_add, map_smul, map_smul, hBA, hBB, map_neg, neg_neg]
  have hABc'' : A (B c'') = s • A (B c) - t • c := by
    rw [hBc'', map_add, map_smul, map_smul, hAA, smul_neg, sub_eq_add_neg]
  have k1 : spForm 2 K c'' (A c'') = 0 := by
    rw [hAc'', hc'']
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, hca, hcb, f1, f2]
    ring
  have k2 : spForm 2 K c'' (B c'') = 0 := by
    rw [hBc'', hc'']
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hca,
      hcb, f1, f2]
    ring
  have k3 : spForm 2 K c'' (A (B c'')) ≠ 0 := by
    rw [hABc'', hc'']
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, hself, f4]
    intro h
    have : (s ^ 2 + t ^ 2) * spForm 2 K c (A (B c)) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · exact hst (eq_zero_of_sq_add_sq hK h')
    · exact hcc h'
  have key := transCenter_quat ha hb ha1 hb1 haa hbb hc k1 k2 k3 hm0 hm1 hm2
  have hd2 : 1 + m ^ 2 ≠ 0 := by rwa [sq]
  have e : α • A c + β • B c = A c'' + m • B c'' := by
    rw [hAc'', hBc'', hs, ht]
    match_scalars <;> field_simp <;> ring
  rw [e]
  exact key

theorem exists_comb_four (haa : spEnd a * spEnd a = -1) (hbb : spEnd b * spEnd b = -1)
    (hc : spEnd a * spEnd b = -(spEnd b * spEnd a)) {c : Fin 2 ⊕ Fin 2 → K}
    (hca : spForm 2 K c (spEnd a c) = 0) (hcb : spForm 2 K c (spEnd b c) = 0)
    (hcc : spForm 2 K c (spEnd a (spEnd b c)) ≠ 0) (v : Fin 2 ⊕ Fin 2 → K) :
    ∃ s t α β : K, v = s • c + t • spEnd a (spEnd b c) + (α • spEnd a c + β • spEnd b c) := by
  have hAA : ∀ v, spEnd a (spEnd a v) = -v := fun v => by
    rw [← Module.End.mul_apply, haa, LinearMap.neg_apply, Module.End.one_apply]
  have hBB : ∀ v, spEnd b (spEnd b v) = -v := fun v => by
    rw [← Module.End.mul_apply, hbb, LinearMap.neg_apply, Module.End.one_apply]
  have hBA : ∀ v, spEnd b (spEnd a v) = -(spEnd a (spEnd b v)) := fun v => by
    rw [← Module.End.mul_apply, show spEnd b * spEnd a = -(spEnd a * spEnd b) by rw [hc, neg_neg],
      LinearMap.neg_apply, Module.End.mul_apply]
  set A := spEnd a with hAdef
  set B := spEnd b with hBdef
  have isoA : ∀ u v, spForm 2 K (A u) (A v) = spForm 2 K u v := spEnd_isometry a
  have isoB : ∀ u v, spForm 2 K (B u) (B v) = spForm 2 K u v := spEnd_isometry b
  have hsw : ∀ x y : Fin 2 ⊕ Fin 2 → K, spForm 2 K y x = -spForm 2 K x y := spForm_swap
  have hself : ∀ x : Fin 2 ⊕ Fin 2 → K, spForm 2 K x x = 0 := spForm_isAlt.self_eq_zero
  set γ := spForm 2 K c (A (B c)) with hγ
  have f1 : spForm 2 K (A (B c)) (A c) = 0 := by rw [isoA, hsw, hcb, neg_zero]
  have f2 : spForm 2 K (A (B c)) (B c) = 0 := by
    rw [← isoB]
    simp only [hBA, hBB, map_neg, neg_neg, hsw c (A c), hca, neg_zero]
  have f3 : spForm 2 K (A c) (B c) = -γ := by
    rw [← isoA (A c) (B c), hAA, map_neg, LinearMap.neg_apply]
  have f1' : spForm 2 K (A c) (A (B c)) = 0 := by rw [hsw, f1, neg_zero]
  have f2' : spForm 2 K (B c) (A (B c)) = 0 := by rw [hsw, f2, neg_zero]
  have f3' : spForm 2 K (B c) (A c) = γ := by rw [hsw, f3, neg_neg]
  have f4 : spForm 2 K (A (B c)) c = -γ := by rw [hsw]
  have f5 : spForm 2 K (A c) c = 0 := by rw [hsw, hca, neg_zero]
  have f6 : spForm 2 K (B c) c = 0 := by rw [hsw, hcb, neg_zero]
  set L : (Fin 4 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
    Fintype.linearCombination K ![c, A (B c), A c, B c] with hL
  have hLapp : ∀ f, L f = f 0 • c + f 1 • A (B c) + (f 2 • A c + f 3 • B c) := by
    intro f
    rw [hL, Fintype.linearCombination_apply, Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]
    abel
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    rw [hLapp] at hf
    have e1 := congrArg (fun w => spForm 2 K w (A (B c))) hf
    have e2 := congrArg (fun w => spForm 2 K w c) hf
    have e3 := congrArg (fun w => spForm 2 K w (B c)) hf
    have e4 := congrArg (fun w => spForm 2 K w (A c)) hf
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hself, f1, f2, f1', f2', f3, f3', f4, f5, f6, hca, hcb, map_zero,
      LinearMap.zero_apply] at e1 e2 e3 e4
    funext i
    fin_cases i
    · have : f 0 * γ = 0 := by linear_combination e1
      exact (mul_eq_zero.1 this).resolve_right hcc
    · have : f 1 * γ = 0 := by linear_combination -e2
      exact (mul_eq_zero.1 this).resolve_right hcc
    · have : f 2 * γ = 0 := by linear_combination -e3
      exact (mul_eq_zero.1 this).resolve_right hcc
    · have : f 3 * γ = 0 := by linear_combination e4
      exact (mul_eq_zero.1 this).resolve_right hcc
  have hsurj : Function.Surjective L := by
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    simp [Module.finrank_fintype_fun_eq_card]
  obtain ⟨f, rfl⟩ := hsurj v
  exact ⟨f 0, f 1, f 2, f 3, hLapp f⟩

theorem cGen_eq_top_of_quat [Finite K] (h2K : (2 : K) ≠ 0) (h3 : Nat.card K ≠ 3)
    (hK : ¬ IsSquare (-1 : K)) (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (hani : ∀ W : Submodule K (Fin 2 ⊕ Fin 2 → K), (∀ x ∈ W, ∀ y ∈ W, spForm 2 K x y = 0) →
      (∀ g : StatedSp 2 K, proj 2 K g ∈ E → ∀ w ∈ W, spEnd g w ∈ W) → W = ⊥)
    (ha : proj 2 K a ∈ E) (hb : proj 2 K b ∈ E) (ha1 : proj 2 K a ≠ 1)
    (hb1 : proj 2 K b ≠ 1) (hab : proj 2 K a ≠ proj 2 K b) (haa : spEnd a * spEnd a = -1)
    (hbb : spEnd b * spEnd b = -1) (hc : spEnd a * spEnd b = -(spEnd b * spEnd a)) :
    cGen E = ⊤ := by
  classical
  have hAA : ∀ v, spEnd a (spEnd a v) = -v := fun v => by
    rw [← Module.End.mul_apply, haa, LinearMap.neg_apply, Module.End.one_apply]
  have hBB : ∀ v, spEnd b (spEnd b v) = -v := fun v => by
    rw [← Module.End.mul_apply, hbb, LinearMap.neg_apply, Module.End.one_apply]
  have hBA : ∀ v, spEnd b (spEnd a v) = -(spEnd a (spEnd b v)) := fun v => by
    rw [← Module.End.mul_apply, show spEnd b * spEnd a = -(spEnd a * spEnd b) by rw [hc, neg_neg],
      LinearMap.neg_apply, Module.End.mul_apply]
  obtain ⟨c, hca, hcb, hcc⟩ :=
    exists_quat_vec h2K hK hE h4 hani ha hb ha1 hb1 hab hAA hBB hBA
  have hsw : ∀ x y : Fin 2 ⊕ Fin 2 → K, spForm 2 K y x = -spForm 2 K x y := spForm_swap
  have isoA : ∀ u v, spForm 2 K (spEnd a u) (spEnd a v) = spForm 2 K u v := spEnd_isometry a
  have f1 : spForm 2 K (spEnd a (spEnd b c)) (spEnd a c) = 0 := by
    rw [isoA, hsw, hcb, neg_zero]
  have f2 : spForm 2 K (spEnd a (spEnd b c)) (spEnd b c) = 0 := by
    rw [← spEnd_isometry b]
    simp only [hBA, hBB, map_neg, neg_neg, hsw c (spEnd a c), hca, neg_zero]
  have f3 : spForm 2 K (spEnd a c) (spEnd b c) = -spForm 2 K c (spEnd a (spEnd b c)) := by
    rw [← isoA (spEnd a c) (spEnd b c), hAA, map_neg, LinearMap.neg_apply]
  have f1' : spForm 2 K (spEnd a c) (spEnd a (spEnd b c)) = 0 := by rw [hsw, f1, neg_zero]
  have f2' : spForm 2 K (spEnd b c) (spEnd a (spEnd b c)) = 0 := by rw [hsw, f2, neg_zero]
  have f5 : spForm 2 K (spEnd a c) c = 0 := by rw [hsw, hca, neg_zero]
  have f6 : spForm 2 K (spEnd b c) c = 0 := by rw [hsw, hcb, neg_zero]
  obtain ⟨m, hm0, hm1', hmm1⟩ := exists_ne_zero_one_neg_one h2K h3
  have hm1 : m * m ≠ 1 := by
    intro h
    have : (m - 1) * (m + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · exact hm1' (sub_eq_zero.1 h')
    · exact hmm1 (eq_neg_of_add_eq_zero_left h')
  have hm2 : m * m ≠ -1 := fun h => hK ⟨m, h.symm⟩
  have hd : 1 + m * m ≠ 0 := fun h => hm2 (by linear_combination h)
  have hAPi := transCenter_span_ab (E := E) hK ha hb ha1 hb1 haa hbb hc hca hcb hcc hm0 hm1 hm2
  have haE : a ∈ cGen E := mem_cGen_of_commute ha ha1 rfl
  have hPi : ∀ s t : K, TransCenter (cGen E) (s • c + t • spEnd a (spEnd b c)) := by
    intro s t
    have := (hAPi (-s) t).map haE
    have e : spEnd a ((-s) • spEnd a c + t • spEnd b c) = s • c + t • spEnd a (spEnd b c) := by
      rw [map_add, map_smul, map_smul, hAA]
      module
    rwa [e] at this
  set l := (1 - m * m) / (1 + m * m) with hl
  set μ := (2 * m) / (1 + m * m) with hμ
  have hl0 : l ≠ 0 := div_ne_zero (fun h => hm1 (by linear_combination -h)) hd
  have hμ0 : μ ≠ 0 := div_ne_zero (mul_ne_zero h2K hm0) hd
  have hlμ : l ^ 2 + μ ^ 2 = 1 := by
    rw [hl, hμ, div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hd)]
    ring
  obtain ⟨G, hG⟩ := exists_sp_comb hAA hlμ
  have hGE : G ∈ cGen E := by
    refine mem_cGen_of_commute ha ha1 ?_
    apply spLin_injective
    refine Units.ext (LinearMap.ext fun v => ?_)
    change spEnd (G * a) v = spEnd (a * G) v
    rw [spEnd_mul, spEnd_mul, Module.End.mul_apply, Module.End.mul_apply, hG, hG, map_add,
      map_smul, map_smul]
  have hmix : TransCenter (cGen E) (l • c + (0 : K) • spEnd a (spEnd b c) + μ • spEnd a c) := by
    have := (hPi 1 0).map hGE
    have e : spEnd G ((1 : K) • c + (0 : K) • spEnd a (spEnd b c)) =
        l • c + (0 : K) • spEnd a (spEnd b c) + μ • spEnd a c := by
      simp only [hG, one_smul, zero_smul, add_zero]
    rwa [e] at this
  have hsweep1 := transCenter_sweep hcc hPi (z := μ • spEnd a c)
    (by rw [map_smul, hca, smul_zero]) (by rw [map_smul, f1, smul_zero]) (Or.inl hl0) hmix
  apply eq_top_of_transCenter
  intro v
  obtain ⟨s, t, α, β, rfl⟩ := exists_comb_four haa hbb hc hca hcb hcc v
  by_cases hst : s = 0 ∧ t = 0
  · rw [hst.1, hst.2, zero_smul, zero_smul, add_zero, zero_add]
    exact hAPi α β
  by_cases hαβ : α = 0 ∧ β = 0
  · rw [hαβ.1, hαβ.2, zero_smul, zero_smul, add_zero, add_zero]
    exact hPi s t
  have h1 := hsweep1 s t (not_and_or.mp hst)
  have e1 : s • c + t • spEnd a (spEnd b c) + μ • spEnd a c =
      μ • spEnd a c + (0 : K) • spEnd b c + (s • c + t • spEnd a (spEnd b c)) := by module
  rw [e1] at h1
  have h2 := transCenter_sweep (e₁ := spEnd a c) (e₂ := spEnd b c)
    (z := s • c + t • spEnd a (spEnd b c)) (by rw [f3]; exact neg_ne_zero.2 hcc) hAPi
    (by simp only [map_add, map_smul, f5, f1', smul_zero, add_zero])
    (by simp only [map_add, map_smul, f6, f2', smul_zero, add_zero]) (s₀ := μ) (t₀ := 0)
    (Or.inl hμ0) h1 α β (not_and_or.mp hαβ)
  have e2 : α • spEnd a c + β • spEnd b c + (s • c + t • spEnd a (spEnd b c)) =
      s • c + t • spEnd a (spEnd b c) + (α • spEnd a c + β • spEnd b c) := by abel
  rwa [e2] at h2

end Four

end SpSeitz

@[expose] def SeitzFourSp4Q8One : Prop :=
  ∀ (K : Type) [Field K] [Finite K], (2 : K) ≠ 0 → Nat.card K ≠ 3 → IsSquare (-1 : K) →
    ∀ E : Subgroup (StatedProj (StatedSp 2 K)), IsElemAbelian 2 E → Nat.card E = 4 →
    (∀ W : Submodule K (Fin 2 ⊕ Fin 2 → K), (∀ x ∈ W, ∀ y ∈ W, spForm 2 K x y = 0) →
      (∀ g : StatedSp 2 K, proj 2 K g ∈ E → ∀ w ∈ W, spEnd g w ∈ W) → W = ⊥) →
    ∀ a b : StatedSp 2 K, proj 2 K a ∈ E → proj 2 K b ∈ E → proj 2 K a ≠ 1 → proj 2 K b ≠ 1 →
      proj 2 K a ≠ proj 2 K b → spEnd a * spEnd a = -1 → spEnd b * spEnd b = -1 →
      spEnd a * spEnd b = -(spEnd b * spEnd a) →
    (⊤ : Subgroup (StatedProj (StatedSp 2 K))) ≤
      ⨆ x ∈ E, ⨆ (_ : x ≠ 1), (⊤ : Subgroup _) ⊓ centralizer ({x} : Set _)

theorem seitzFourSp4Q8_of_one (h : SeitzFourSp4Q8One) : SeitzFourSp4Q8 := by
  intro K _ _ h2K h3 E hE h4 hA a b ha hb ha1 hb1 hab haa hbb hc
  by_cases hK : IsSquare (-1 : K)
  · exact h K h2K h3 hK E hE h4 hA a b ha hb ha1 hb1 hab haa hbb hc
  have htop := SpSeitz.cGen_eq_top_of_quat h2K h3 hK hE h4 hA ha hb ha1 hb1 hab haa hbb hc
  intro k _
  obtain ⟨g, rfl⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective (r := 2) (K := K) k
  have hg : g ∈ SpSeitz.cGen E := htop ▸ mem_top g
  exact hg

end CFSG.LocalAnalysis.WeakClosure81
