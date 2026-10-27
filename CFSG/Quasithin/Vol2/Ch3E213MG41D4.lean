module

public import CFSG.Quasithin.Vol2.Ch3E213MG41D3

public section

namespace CFSG.Quasithin.Ch3E213M.G41

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2]

variable {G₀ : Subgroup (antiSp k)} {F₀ : Subfield k}

@[expose] def perpPart (x y m : Fin 4 → k) : Fin 4 → k :=
  m - spBil m y • x - spBil m x • y

theorem perpPart_perp {x y : Fin 4 → k} (hxy : spBil x y = 1) (m : Fin 4 → k) :
    spBil (perpPart x y m) x = 0 ∧ spBil (perpPart x y m) y = 0 :=
  perp_comb hxy m

omit [CharP k 2] in
theorem eq_perpPart (x y m : Fin 4 → k) :
    m = spBil m y • x + spBil m x • y + perpPart x y m := by
  simp only [perpPart]
  abel

theorem isNorm_hub {x y u : Fin 4 → k} (hx : IsNorm G₀ F₀ x) (hy : IsNorm G₀ F₀ y)
    (hxy : spBil x y = 1) (hux : spBil u x = 0) (huy : spBil u y = 0)
    (h : IsNorm G₀ F₀ (x + u)) {α β : k} (hα : α ∈ F₀) (hβ : β ∈ F₀) (h0 : α ≠ 0 ∨ β ≠ 0) :
    IsNorm G₀ F₀ (α • x + β • y + u) :=
  isNorm_plane hx hy hxy hux huy F₀.one_mem F₀.zero_mem (Or.inl one_ne_zero) hα hβ h0
    (by simpa using h)

omit [CharP k 2] in
theorem bil_span_pair_eq_zero {x y v : Fin 4 → k} (h1 : spBil x v = 0) (h2 : spBil y v = 0)
    {w : Fin 4 → k} (hw : w ∈ Submodule.span k (Set.range ![x, y])) : spBil w v = 0 := by
  have hle : Submodule.span k (Set.range ![x, y]) ≤ LinearMap.ker (spBil.flip v) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    fin_cases i
    · exact LinearMap.mem_ker.mpr h1
    · exact LinearMap.mem_ker.mpr h2
  exact LinearMap.mem_ker.mp (hle hw)

section Frame

variable [Finite k] {n : ℕ}

theorem exists_mixing (hk : Nat.card k = 2 ^ n) (hF4 : 4 ≤ Nat.card F₀)
    (hG : ∀ W, DInv G₀ W → W = ⊥ ∨ W = ⊤) {x y : Fin 4 → k} (hx : IsNorm G₀ F₀ x) :
    ∃ m, IsNorm G₀ F₀ m ∧ (spBil m y ≠ 0 ∨ spBil m x ≠ 0) ∧ perpPart x y m ≠ 0 := by
  by_contra hne
  simp only [not_exists, not_and, not_not] at hne
  set W := Submodule.span k (Set.range ![x, y]) with hWdef
  have hxW : x ∈ W := Submodule.subset_span ⟨0, rfl⟩
  have hyW : y ∈ W := Submodule.subset_span ⟨1, rfl⟩
  have hinv : DInv G₀ W := by
    intro d hd w hw
    obtain ⟨v, c, hv, hc, hcL, rfl⟩ := exists_of_mem_transvSet hd
    obtain ⟨μ, hμ, hμv⟩ := exists_isNorm_smul hk hF4 hG hx ⟨hv, c, hc, hcL⟩
    rw [act_trv]
    by_cases hcase : spBil (μ • v) y = 0 ∧ spBil (μ • v) x = 0
    · have h1 : spBil x v = 0 := by
        have := hcase.2
        rw [LinearMap.BilinForm.smul_left] at this
        rw [bil_symm]
        exact (mul_eq_zero.mp this).resolve_left hμ
      have h2 : spBil y v = 0 := by
        have := hcase.1
        rw [LinearMap.BilinForm.smul_left] at this
        rw [bil_symm]
        exact (mul_eq_zero.mp this).resolve_left hμ
      rw [bil_span_pair_eq_zero h1 h2 hw, mul_zero, zero_smul, add_zero]
      exact hw
    · have heq := hne (μ • v) hμv (not_and_or.mp hcase)
      have hvW : v = μ⁻¹ • (spBil (μ • v) y • x + spBil (μ • v) x • y) := by
        have h3 := eq_perpPart x y (μ • v)
        rw [heq, add_zero] at h3
        rw [← h3, smul_smul, inv_mul_cancel₀ hμ, one_smul]
      refine W.add_mem hw (W.smul_mem _ ?_)
      rw [hvW]
      exact W.smul_mem _ (W.add_mem (W.smul_mem _ hxW) (W.smul_mem _ hyW))
  rcases hG W hinv with h | h
  · rw [h, Submodule.mem_bot] at hxW
    exact hx.ne_zero hxW
  · have hle := finrank_range_le_card (R := k) ![x, y]
    change Module.finrank k (Submodule.span k (Set.range ![x, y])) ≤ _ at hle
    rw [← hWdef, h, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at hle
    omega

theorem isNorm_hub_of_mix (hk : Nat.card k = 2 ^ n) (hF4 : 4 ≤ Nat.card F₀) {x y m : Fin 4 → k}
    (hx : IsNorm G₀ F₀ x) (hy : IsNorm G₀ F₀ y) (hxy : spBil x y = 1) (hm : IsNorm G₀ F₀ m)
    (hm0 : spBil m y ≠ 0 ∨ spBil m x ≠ 0) : IsNorm G₀ F₀ (x + perpPart x y m) := by
  obtain ⟨h1, h2⟩ := perpPart_perp hxy m
  have h := isNorm_plane hx hy hxy h1 h2 (bil_mem_of_isNorm hk hF4 hm hy)
    (bil_mem_of_isNorm hk hF4 hm hx) hm0 F₀.one_mem F₀.zero_mem (Or.inl one_ne_zero)
    (by rw [← eq_perpPart]; exact hm)
  simpa using h

theorem isNorm_hub_of_perp (hk : Nat.card k = 2 ^ n) (hF4 : 4 ≤ Nat.card F₀) {x y u u' : Fin 4 → k}
    (hx : IsNorm G₀ F₀ x) (hy : IsNorm G₀ F₀ y) (hxy : spBil x y = 1) (hux : spBil u x = 0)
    (huy : spBil u y = 0) (hu : IsNorm G₀ F₀ (x + u)) (hu'x : spBil u' x = 0)
    (hu'y : spBil u' y = 0) (hu' : IsNorm G₀ F₀ u') (huu' : spBil u u' ≠ 0) :
    IsNorm G₀ F₀ (x + u') := by
  have hF3 : 3 ≤ Nat.card F₀ := le_trans (by norm_num) hF4
  obtain ⟨γ, hγ, hγ0, hγμ⟩ := exists_mem_ne_ne hF3 0 (spBil u' u)
  have hz := isNorm_hub hx hy hxy hux huy hu F₀.zero_mem hγ (Or.inr hγ0)
  have hxu' : spBil x u' = 0 := by rw [bil_symm]; exact hu'x
  have hxu : spBil x u = 0 := by rw [bil_symm]; exact hux
  have e1 : spBil x ((0 : k) • x + γ • y + u) = γ := by
    simp [hxy, hxu]
  have e2 : spBil u' ((0 : k) • x + γ • y + u) = spBil u' u := by
    simp [hu'y]
  have hu'u : spBil u' u ≠ 0 := by rwa [bil_symm] at huu'
  refine isNorm_orth_add hk hF4 hx hu' hz hxu' ?_ ?_ ?_
  · rw [e1]; exact hγ0
  · rw [e2]; exact hu'u
  · rw [e1, e2]; exact hγμ

theorem isNorm_of_hub (hk : Nat.card k = 2 ^ n) (hF4 : 4 ≤ Nat.card F₀) {x y u u' : Fin 4 → k}
    (hx : IsNorm G₀ F₀ x) (hy : IsNorm G₀ F₀ y) (hxy : spBil x y = 1) (hux : spBil u x = 0)
    (huy : spBil u y = 0) (hu : IsNorm G₀ F₀ (x + u)) (hu'x : spBil u' x = 0)
    (hu'y : spBil u' y = 0) (hu' : IsNorm G₀ F₀ (x + u')) (huu' : spBil u u' ≠ 0) :
    IsNorm G₀ F₀ u := by
  have hF3 : 3 ≤ Nat.card F₀ := le_trans (by norm_num) hF4
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  obtain ⟨γ, hγ, hγ0, hγμ⟩ := exists_mem_ne_ne hF3 0 (spBil u u')
  have hz := isNorm_hub hx hy hxy hu'x hu'y hu' F₀.zero_mem hγ (Or.inr hγ0)
  have hxu' : spBil x u' = 0 := by rw [bil_symm]; exact hu'x
  have e1 : spBil (x + u) ((0 : k) • x + γ • y + u') = γ + spBil u u' := by
    simp [hxy, hxu', huy]
  have e2 : spBil x ((0 : k) • x + γ • y + u') = γ := by
    simp [hxy, hxu']
  have e3 : spBil (x + u) x = 0 := by
    simp [bil_self, hux]
  have hsum := isNorm_orth_add hk hF4 hu hx hz e3
    (by rw [e1]; intro h0; exact hγμ (by linear_combination h0 - spBil u u' * h2))
    (by rw [e2]; exact hγ0) (by rw [e1, e2]; intro h0; exact huu' (by linear_combination h0))
  have : x + u + x = u := by
    rw [add_comm x u, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rwa [this] at hsum

end Frame

end CFSG.Quasithin.Ch3E213M.G41
