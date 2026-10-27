module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private def ggQ2s08k1_spanB {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (b : Module.Basis (Fin N) (ZMod 3) V) (T : Set (Fin N)) : Submodule (ZMod 3) V :=
  Submodule.span (ZMod 3) (b '' T)

private lemma ggQ2s08k1_coord_self {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (b : Module.Basis (Fin N) (ZMod 3) V) (i : Fin N) : b.coord i (b i) = 1 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]

private lemma ggQ2s08k1_coord_of_ne {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (b : Module.Basis (Fin N) (ZMod 3) V) {i j : Fin N} (h : i ≠ j) : b.coord i (b j) = 0 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self]
  exact Finsupp.single_eq_of_ne h

private lemma ggQ2s08k1_repr_self {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (b : Module.Basis (Fin N) (ZMod 3) V) (i : Fin N) : b.repr (b i) i = 1 := by
  rw [Module.Basis.repr_self, Finsupp.single_eq_same]

private lemma ggQ2s08k1_repr_of_ne {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (b : Module.Basis (Fin N) (ZMod 3) V) {i j : Fin N} (h : i ≠ j) : b.repr (b j) i = 0 := by
  rw [Module.Basis.repr_self]
  exact Finsupp.single_eq_of_ne h

private lemma ggQ2s08k1_coord_mono {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (b : Module.Basis (Fin N) (ZMod 3) V) {w : V ≃ₗ[ZMod 3] V} {σ : Equiv.Perm (Fin N)}
    {ε : Fin N → ZMod 3} (hw : ∀ i, w (b i) = ε i • b (σ i)) (v : V) (i : Fin N) :
    b.coord (σ i) (w v) = ε i * b.coord i v := by
  have hmap : (b.coord (σ i)).comp w.toLinearMap = ε i • b.coord i := by
    apply Module.Basis.ext b
    intro j
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_toLinearMap, hw j,
      map_smul, smul_eq_mul]
    by_cases hji : j = i
    · subst hji
      rw [ggQ2s08k1_coord_self, ggQ2s08k1_coord_self]
      ring
    · have hσ : σ j ≠ σ i := fun h => hji (σ.injective h)
      rw [ggQ2s08k1_coord_of_ne b (Ne.symm hσ), ggQ2s08k1_coord_of_ne b (Ne.symm hji)]
      ring
  exact congrArg (fun f : V →ₗ[ZMod 3] ZMod 3 => f v) hmap

private lemma ggQ2s08k1_repr_mono {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (b : Module.Basis (Fin N) (ZMod 3) V) {w : V ≃ₗ[ZMod 3] V} {σ : Equiv.Perm (Fin N)}
    {ε : Fin N → ZMod 3} (hw : ∀ i, w (b i) = ε i • b (σ i)) (v : V) (i : Fin N) :
    b.repr (w v) (σ i) = ε i * b.repr v i := by
  have h := ggQ2s08k1_coord_mono b hw v i
  simpa only [Module.Basis.coord_apply] using h

private lemma ggQ2s08k1_repr_eq_zero_of_mem_spanB {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {N : ℕ} (b : Module.Basis (Fin N) (ZMod 3) V) {T : Set (Fin N)} {i : Fin N} (hi : i ∉ T)
    {v : V} (hv : v ∈ ggQ2s08k1_spanB b T) : b.repr v i = 0 := by
  have hle : ggQ2s08k1_spanB b T ≤ LinearMap.ker (b.coord i) := by
    rw [ggQ2s08k1_spanB, Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    exact ggQ2s08k1_coord_of_ne b (fun h => hi (h ▸ ht))
  have h := LinearMap.mem_ker.mp (hle hv)
  simpa only [Module.Basis.coord_apply] using h

private lemma ggQ2s08k1_orbit_all {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    {b : Module.Basis (Fin N) (ZMod 3) V} {W : Subgroup (V ≃ₗ[ZMod 3] V)} {xv : V}
    (hWm : ∀ w ∈ W, GGQ2S08Mono b w)
    (hWfix : ∀ v, (∀ w ∈ W, w v = v) ↔ v ∈ Submodule.span (ZMod 3) {xv})
    (hAllNe : ∀ i, b.repr xv i ≠ 0) (i : Fin N) :
    ∀ j, ∃ w ∈ W, ∃ ε : ZMod 3, ε ≠ 0 ∧ w (b i) = ε • b j := by
  classical
  set O : Finset (Fin N) := Finset.univ.filter
    (fun k => ∃ w ∈ W, ∃ ε : ZMod 3, ε ≠ 0 ∧ w (b i) = ε • b k) with hO
  have hO_mem : ∀ k, k ∈ O ↔ ∃ w ∈ W, ∃ ε : ZMod 3, ε ≠ 0 ∧ w (b i) = ε • b k := by
    intro k
    rw [hO, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ k, h⟩⟩
  have hiO : i ∈ O := by
    rw [hO_mem]
    exact ⟨1, W.one_mem, 1, one_ne_zero, by simp⟩
  let y : V := Finset.sum O (fun k => b.repr xv k • b k)
  have hy : y = Finset.sum O (fun k => b.repr xv k • b k) := rfl
  have hyrepr : b.repr y =
      Finset.sum O (fun k => b.repr xv k • (Finsupp.single k 1 : Fin N →₀ ZMod 3)) := by
    rw [hy, map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_smul, Module.Basis.repr_self]
  have hycoord : ∀ l, b.repr y l = if l ∈ O then b.repr xv l else 0 := by
    intro l
    rw [hyrepr, Finsupp.finset_sum_apply]
    have hterm : ∀ k ∈ O, (b.repr xv k • (Finsupp.single k 1 : Fin N →₀ ZMod 3)) l
        = (if l = k then b.repr xv l else 0) := by
      intro k hk
      rw [Finsupp.smul_apply, smul_eq_mul]
      by_cases hlk : l = k
      · rw [if_pos hlk, hlk, Finsupp.single_eq_same, mul_one]
      · rw [if_neg hlk, Finsupp.single_eq_of_ne hlk, mul_zero]
    trans Finset.sum O (fun k => if l = k then b.repr xv l else 0)
    · exact Finset.sum_congr rfl hterm
    · exact Finset.sum_ite_eq O l (fun _ => b.repr xv l)
  have hycoord_mem : ∀ l, l ∈ O → b.repr y l = b.repr xv l := by
    intro l hl
    rw [hycoord l, if_pos hl]
  have hycoord_not : ∀ l, l ∉ O → b.repr y l = 0 := by
    intro l hl
    rw [hycoord l, if_neg hl]
  have hfix : ∀ w ∈ W, w y = y := by
    intro w hwmem
    obtain ⟨σ, ε, hε, hw⟩ := hWm w hwmem
    have hwxv : w xv = xv := ((hWfix xv).2 (Submodule.mem_span_singleton_self xv)) w hwmem
    have hxrel : ∀ l, b.repr xv l = ε (σ.symm l) * b.repr xv (σ.symm l) := by
      intro l
      have h := ggQ2s08k1_repr_mono b hw xv (σ.symm l)
      rw [σ.apply_symm_apply, hwxv] at h
      exact h
    have hOmap : ∀ k ∈ O, σ k ∈ O := by
      intro k hk
      rw [hO_mem] at hk ⊢
      obtain ⟨w₀, hw₀, ε₀, hε₀, hwk⟩ := hk
      refine ⟨w * w₀, W.mul_mem hwmem hw₀, ε₀ * ε k, mul_ne_zero hε₀ (hε k), ?_⟩
      calc (w * w₀) (b i) = w (w₀ (b i)) := rfl
        _ = w (ε₀ • b k) := by rw [hwk]
        _ = ε₀ • w (b k) := by rw [map_smul]
        _ = ε₀ • (ε k • b (σ k)) := by rw [hw k]
        _ = (ε₀ * ε k) • b (σ k) := by rw [smul_smul]
    have hwinv : ∀ k, w⁻¹ (b (σ k)) = (ε k)⁻¹ • b k := by
      intro k
      have h := congrArg (fun z => w⁻¹ z) (hw k)
      rw [show w⁻¹ (w (b k)) = b k from by simp, map_smul] at h
      have h2 := congrArg (fun z => (ε k)⁻¹ • z) h
      rw [smul_smul, inv_mul_cancel₀ (hε k), one_smul] at h2
      exact h2.symm
    have hOmap' : ∀ k, σ k ∈ O → k ∈ O := by
      intro k hk
      rw [hO_mem] at hk ⊢
      obtain ⟨v, hv, δ, hδ, hvk⟩ := hk
      refine ⟨w⁻¹ * v, W.mul_mem (W.inv_mem hwmem) hv, δ * (ε k)⁻¹,
        mul_ne_zero hδ (inv_ne_zero (hε k)), ?_⟩
      calc (w⁻¹ * v) (b i) = w⁻¹ (v (b i)) := rfl
        _ = w⁻¹ (δ • b (σ k)) := by rw [hvk]
        _ = δ • w⁻¹ (b (σ k)) := by rw [map_smul]
        _ = δ • ((ε k)⁻¹ • b k) := by rw [hwinv k]
        _ = (δ * (ε k)⁻¹) • b k := by rw [smul_smul]
    have hOpre : ∀ l, σ.symm l ∈ O ↔ l ∈ O := by
      intro l
      constructor
      · intro h
        have h' := hOmap (σ.symm l) h
        rwa [σ.apply_symm_apply] at h'
      · intro h
        exact hOmap' (σ.symm l) (by rwa [σ.apply_symm_apply])
    apply Module.Basis.ext_elem b
    intro l
    have h := ggQ2s08k1_repr_mono b hw y (σ.symm l)
    rw [σ.apply_symm_apply] at h
    rw [h]
    by_cases hl : l ∈ O
    · rw [hycoord_mem (σ.symm l) ((hOpre l).mpr hl), hycoord_mem l hl, hxrel l]
    · rw [hycoord_not (σ.symm l) (fun hh => hl ((hOpre l).mp hh)), hycoord_not l hl, mul_zero]
  have hy_mem : y ∈ Submodule.span (ZMod 3) {xv} := (hWfix y).1 hfix
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy_mem
  have hc1 : c = 1 := by
    have h := congrArg (fun v => b.repr v i) hc
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hycoord_mem i hiO] at h
    exact mul_right_cancel₀ (hAllNe i) (by rw [one_mul]; exact h)
  intro j
  have hjO : j ∈ O := by
    by_contra hjO
    have h := congrArg (fun v => b.repr v j) hc
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hc1, one_mul, hycoord_not j hjO] at h
    exact hAllNe j h
  exact (hO_mem j).mp hjO

private lemma ggQ2s08k1_orbit_off {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    {b : Module.Basis (Fin N) (ZMod 3) V} {W : Subgroup (V ≃ₗ[ZMod 3] V)} {xv : V}
    (hWm : ∀ w ∈ W, GGQ2S08Mono b w)
    (hWfix : ∀ v, (∀ w ∈ W, w v = v) ↔ v ∈ Submodule.span (ZMod 3) {xv})
    (hWirr : ∀ U : Submodule (ZMod 3) V, Submodule.span (ZMod 3) {xv} ≤ U →
      (∀ w ∈ W, ∀ u ∈ U, w u ∈ U) → U = Submodule.span (ZMod 3) {xv} ∨ U = ⊤)
    {i₀ : Fin N} (hx0 : ∀ i, i ≠ i₀ → b.repr xv i = 0) (hx0ne : b.repr xv i₀ ≠ 0)
    {i : Fin N} (hi : i ≠ i₀) :
    ∀ j, j ≠ i₀ → ∃ w ∈ W, ∃ ε : ZMod 3, ε ≠ 0 ∧ w (b i) = ε • b j := by
  classical
  set O : Finset (Fin N) := Finset.univ.filter
    (fun k => ∃ w ∈ W, ∃ ε : ZMod 3, ε ≠ 0 ∧ w (b i) = ε • b k) with hO
  have hO_mem : ∀ k, k ∈ O ↔ ∃ w ∈ W, ∃ ε : ZMod 3, ε ≠ 0 ∧ w (b i) = ε • b k := by
    intro k
    rw [hO, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ k, h⟩⟩
  have hiO : i ∈ O := by
    rw [hO_mem]
    exact ⟨1, W.one_mem, 1, one_ne_zero, by simp⟩
  have hxv_eq : xv = b.repr xv i₀ • b i₀ := by
    conv_lhs => rw [← b.sum_repr xv]
    apply Finset.sum_eq_single i₀
    · intro k _ hk
      rw [hx0 k hk, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  have hi₀O : i₀ ∉ O := by
    intro hmem
    rw [hO_mem] at hmem
    obtain ⟨w, hw, ε, hε, hwi⟩ := hmem
    obtain ⟨σ, δ, hδ, hwσ⟩ := hWm w hw
    have hwxv : w xv = xv := ((hWfix xv).2 (Submodule.mem_span_singleton_self xv)) w hw
    have hEq : δ i • b (σ i) = ε • b i₀ := by rw [← hwσ i]; exact hwi
    have hσ : σ i = i₀ := by
      by_contra hne
      have h0 : b.repr (δ i • b (σ i)) i₀ = 0 := by
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ggQ2s08k1_repr_of_ne b (Ne.symm hne),
          mul_zero]
      have h1 : b.repr (ε • b i₀) i₀ = 0 := by rw [← hEq]; exact h0
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ggQ2s08k1_repr_self b i₀, mul_one] at h1
      exact hε h1
    have hxrel := ggQ2s08k1_repr_mono b hwσ xv i
    rw [hwxv, hσ, hx0 i hi, mul_zero] at hxrel
    exact hx0ne hxrel
  have hUle : ggQ2s08k1_spanB b (O : Set (Fin N)) ≤
      ggQ2s08k1_spanB b ((O : Set (Fin N)) ∪ {i₀}) :=
    Submodule.span_mono (Set.image_mono Set.subset_union_left)
  have hxle : Submodule.span (ZMod 3) {xv} ≤
      ggQ2s08k1_spanB b ((O : Set (Fin N)) ∪ {i₀}) := by
    rw [Submodule.span_singleton_le_iff_mem, hxv_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨i₀, Set.mem_union_right _ (Set.mem_singleton i₀), rfl⟩)
  set U' : Submodule (ZMod 3) V :=
    ggQ2s08k1_spanB b (O : Set (Fin N)) ⊔ Submodule.span (ZMod 3) {xv} with hU'
  have hU'le : U' ≤ ggQ2s08k1_spanB b ((O : Set (Fin N)) ∪ {i₀}) := sup_le hUle hxle
  have hspanle : Submodule.span (ZMod 3) {xv} ≤ U' := by rw [hU']; exact le_sup_right
  have hinv : ∀ w ∈ W, ∀ u ∈ U', w u ∈ U' := by
    intro w hwmem u hu
    obtain ⟨σ, ε, hε, hw⟩ := hWm w hwmem
    have hwxv : w xv = xv := ((hWfix xv).2 (Submodule.mem_span_singleton_self xv)) w hwmem
    have hσO : ∀ k ∈ O, σ k ∈ O := by
      intro k hk
      rw [hO_mem] at hk ⊢
      obtain ⟨w₀, hw₀, ε₀, hε₀, hwk⟩ := hk
      refine ⟨w * w₀, W.mul_mem hwmem hw₀, ε₀ * ε k, mul_ne_zero hε₀ (hε k), ?_⟩
      calc (w * w₀) (b i) = w (w₀ (b i)) := rfl
        _ = w (ε₀ • b k) := by rw [hwk]
        _ = ε₀ • w (b k) := by rw [map_smul]
        _ = ε₀ • (ε k • b (σ k)) := by rw [hw k]
        _ = (ε₀ * ε k) • b (σ k) := by rw [smul_smul]
    have hmapO : Submodule.map w.toLinearMap (ggQ2s08k1_spanB b (O : Set (Fin N))) ≤
        ggQ2s08k1_spanB b (O : Set (Fin N)) := by
      rw [ggQ2s08k1_spanB, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      rw [LinearEquiv.coe_toLinearMap, hw k]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ k, hσO k hk, rfl⟩)
    have hmapX : Submodule.map w.toLinearMap (Submodule.span (ZMod 3) {xv}) ≤
        Submodule.span (ZMod 3) {xv} := by
      rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_toLinearMap, hwxv]
    rw [hU'] at hu ⊢
    rw [Submodule.mem_sup] at hu ⊢
    obtain ⟨a, ha, c, hc, hacu⟩ := hu
    rw [← hacu, map_add]
    exact ⟨w a, hmapO (Submodule.mem_map_of_mem ha), w c,
      hmapX (Submodule.mem_map_of_mem hc), rfl⟩
  have hne : U' ≠ Submodule.span (ZMod 3) {xv} := by
    intro hEq
    have hbi : b i ∈ Submodule.span (ZMod 3) {xv} := by
      rw [← hEq]
      exact Submodule.mem_sup.mpr ⟨b i, Submodule.subset_span ⟨i, hiO, rfl⟩, 0,
        Submodule.zero_mem _, by simp⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hbi
    have h := congrArg (fun v => b.repr v i) hc
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hx0 i hi, mul_zero] at h
    rw [ggQ2s08k1_repr_self b i] at h
    exact zero_ne_one h
  have hUtop : U' = ⊤ := by
    rcases hWirr U' hspanle hinv with h | h
    · exact absurd h hne
    · exact h
  intro j hj
  have hjO : j ∈ O := by
    by_contra hjO
    have hmem : b j ∈ ggQ2s08k1_spanB b ((O : Set (Fin N)) ∪ {i₀}) :=
      hU'le (by rw [hUtop]; exact Submodule.mem_top)
    have hji : j ∉ (O : Set (Fin N)) ∪ {i₀} := by
      intro h
      rw [Set.mem_union] at h
      rcases h with h | h
      · exact hjO h
      · exact hj (by simpa using h)
    have hzero := ggQ2s08k1_repr_eq_zero_of_mem_spanB b hji hmem
    rw [ggQ2s08k1_repr_self b j] at hzero
    exact one_ne_zero hzero
  exact (hO_mem j).mp hjO

theorem ggQ2s08core_orbit_dichotomy {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (hN : 2 ≤ N)
    (b : Module.Basis (Fin N) (ZMod 3) V) (W : Subgroup (V ≃ₗ[ZMod 3] V))
    (hWm : ∀ w ∈ W, GGQ2S08Mono b w) (xv : V) (hx : xv ≠ 0)
    (hWfix : ∀ v, (∀ w ∈ W, w v = v) ↔ v ∈ Submodule.span (ZMod 3) {xv})
    (hWirr : ∀ U : Submodule (ZMod 3) V, Submodule.span (ZMod 3) {xv} ≤ U →
      (∀ w ∈ W, ∀ u ∈ U, w u ∈ U) → U = Submodule.span (ZMod 3) {xv} ∨ U = ⊤) :
    (∃ i₀ : Fin N, (∀ i, i ≠ i₀ → b.repr xv i = 0) ∧
      ∀ i j, i ≠ i₀ → j ≠ i₀ → ∃ w ∈ W, ∃ ε : ZMod 3, ε ≠ 0 ∧ w (b i) = ε • b j) ∨
    ((∀ i, b.repr xv i ≠ 0) ∧ ∀ i j, ∃ w ∈ W, ∃ ε : ZMod 3, ε ≠ 0 ∧ w (b i) = ε • b j) := by
  classical
  set S : Set (Fin N) := {i | b.repr xv i ≠ 0} with hS
  have hxvU : xv ∈ ggQ2s08k1_spanB b S := by
    rw [← b.sum_repr xv]
    apply Submodule.sum_mem
    intro i hi
    by_cases h : b.repr xv i = 0
    · rw [h, zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨i, by simpa only [hS, Set.mem_setOf_eq] using h, rfl⟩)
  have hUle : Submodule.span (ZMod 3) {xv} ≤ ggQ2s08k1_spanB b S := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact hxvU
  have hUinv : ∀ w ∈ W, ∀ u ∈ ggQ2s08k1_spanB b S, w u ∈ ggQ2s08k1_spanB b S := by
    intro w hwmem u hu
    obtain ⟨σ, ε, hε, hw⟩ := hWm w hwmem
    have hwxv : w xv = xv := ((hWfix xv).2 (Submodule.mem_span_singleton_self xv)) w hwmem
    have hσS : ∀ k ∈ S, σ k ∈ S := by
      intro k hk
      have h := ggQ2s08k1_repr_mono b hw xv k
      rw [hwxv] at h
      simp only [hS, Set.mem_setOf_eq] at hk ⊢
      rw [h]
      exact mul_ne_zero (hε k) hk
    have hmap : Submodule.map w.toLinearMap (ggQ2s08k1_spanB b S) ≤ ggQ2s08k1_spanB b S := by
      rw [ggQ2s08k1_spanB, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      rw [LinearEquiv.coe_toLinearMap, hw k]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ k, hσS k hk, rfl⟩)
    exact hmap (Submodule.mem_map_of_mem hu)
  rcases hWirr (ggQ2s08k1_spanB b S) hUle hUinv with hUspan | hUtop
  · have hSne : S.Nonempty := by
      by_contra h
      have hzero : xv = 0 := by
        rw [← b.sum_repr xv]
        apply Finset.sum_eq_zero
        intro i hi
        have hxi : b.repr xv i = 0 := by
          by_contra hne
          exact h ⟨i, by simpa only [hS, Set.mem_setOf_eq] using hne⟩
        rw [hxi, zero_smul]
      exact hx hzero
    obtain ⟨i₀, hi₀S⟩ := hSne
    have hi₀ne : b.repr xv i₀ ≠ 0 := by
      simpa only [hS, Set.mem_setOf_eq] using hi₀S
    have hx0 : ∀ i, i ≠ i₀ → b.repr xv i = 0 := by
      intro i hi
      by_contra hne
      have hiS : i ∈ S := by simpa only [hS, Set.mem_setOf_eq] using hne
      have hbi : b i ∈ Submodule.span (ZMod 3) {xv} := by
        rw [← hUspan]
        exact Submodule.subset_span ⟨i, hiS, rfl⟩
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hbi
      have hc0 : c = 0 := by
        by_contra hcne
        have h := congrArg (fun v => b.repr v i₀) hc
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ggQ2s08k1_repr_of_ne b (Ne.symm hi)] at h
        exact mul_ne_zero hcne hi₀ne h
      have h1 : b.repr (b i) i = 1 := ggQ2s08k1_repr_self b i
      have h2 := congrArg (fun v => b.repr v i) hc
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hc0, zero_mul] at h2
      rw [h1] at h2
      exact zero_ne_one h2
    exact Or.inl ⟨i₀, hx0, fun i j hi hj =>
      ggQ2s08k1_orbit_off hWm hWfix hWirr hx0 hi₀ne hi j hj⟩
  · have hAllNe : ∀ i, b.repr xv i ≠ 0 := by
      intro i
      by_contra hi0
      have hiS : i ∉ S := by
        simp only [hS, Set.mem_setOf_eq]
        exact fun hne => hne hi0
      have hmem : b i ∈ ggQ2s08k1_spanB b S := by rw [hUtop]; exact Submodule.mem_top
      have hzero := ggQ2s08k1_repr_eq_zero_of_mem_spanB b hiS hmem
      rw [ggQ2s08k1_repr_self b i] at hzero
      exact one_ne_zero hzero
    exact Or.inr ⟨hAllNe, fun i j => ggQ2s08k1_orbit_all hWm hWfix hAllNe i j⟩


end CFSG.StandardType

end
