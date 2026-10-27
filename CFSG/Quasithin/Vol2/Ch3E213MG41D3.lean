module

public import CFSG.Quasithin.Vol2.Ch3E213MG41D1

public section

namespace CFSG.Quasithin.Ch3E213M.G41

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2]

omit [CharP k 2] in
theorem eq_zero_of_orth_span {S : Set (Fin 4 → k)} (hS : Submodule.span k S = ⊤)
    {y : Fin 4 → k} (h : ∀ p ∈ S, spBil y p = 0) : y = 0 := by
  have hle : Submodule.span k S ≤ LinearMap.ker (spBil y) := by
    rw [Submodule.span_le]
    intro v hv
    exact LinearMap.mem_ker.mpr (h v hv)
  rw [hS] at hle
  apply eq_zero_of_bil_eq_zero
  intro z
  rw [bil_symm]
  exact LinearMap.mem_ker.mp (hle (Submodule.mem_top (x := z)))

omit [CharP k 2] in
theorem exists_mem_ne_ne [Finite k] {F₀ : Subfield k} (hF : 3 ≤ Nat.card F₀) (p q : k) :
    ∃ γ ∈ F₀, γ ≠ p ∧ γ ≠ q := by
  by_contra h
  simp only [not_exists, not_and] at h
  have hsub : (F₀ : Set k) ⊆ {p, q} := fun γ hγ => by
    by_cases h1 : γ = p
    · exact Or.inl h1
    · exact Or.inr (by simpa using h γ hγ h1)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({p, q} : Set k).ncard ≤ 2 := by
    have := Set.ncard_insert_le p {q}
    rwa [Set.ncard_singleton] at this
  have h3 : Nat.card F₀ = (F₀ : Set k).ncard := Nat.card_coe_set_eq _
  omega

variable {G₀ : Subgroup (antiSp k)} {F₀ : Subfield k}

section Large

variable [Finite k] {n : ℕ}
  (hk : Nat.card k = 2 ^ n) (hF4 : 4 ≤ Nat.card F₀)

include hk hF4 in
theorem exists_isNorm_smul (hG : ∀ W, DInv G₀ W → W = ⊥ ∨ W = ⊤) {x₁ : Fin 4 → k}
    (hx₁ : IsNorm G₀ F₀ x₁) {y : Fin 4 → k} (hy : y ∈ centres G₀) :
    ∃ μ : k, μ ≠ 0 ∧ IsNorm G₀ F₀ (μ • y) := by
  set P := {y | y ∈ centres G₀ ∧ ∃ μ : k, μ ≠ 0 ∧ IsNorm G₀ F₀ (μ • y)} with hP
  have hstep : ∀ p ∈ P, ∀ v ∈ centres G₀, spBil p v ≠ 0 → v ∈ P := by
    rintro p ⟨-, μ, hμ, hμp⟩ v hv hpv
    have h1 : spBil (μ • p) v ≠ 0 := by
      rw [LinearMap.BilinForm.smul_left]
      exact mul_ne_zero hμ hpv
    exact ⟨hv, _, inv_ne_zero h1, isNorm_of_bil_ne_zero hk hF4 hμp hv h1⟩
  have hinv : DInv G₀ (Submodule.span k P) := by
    intro d hd w hw
    obtain ⟨v, c, hv, hc, hcL, rfl⟩ := exists_of_mem_transvSet hd
    induction hw using Submodule.span_induction with
    | mem p hp =>
      rw [act_trv]
      by_cases hpv : spBil p v = 0
      · rw [hpv, mul_zero, zero_smul, add_zero]
        exact Submodule.subset_span hp
      · exact Submodule.add_mem _ (Submodule.subset_span hp) (Submodule.smul_mem _ _
          (Submodule.subset_span (hstep p hp v ⟨hv, c, hc, hcL⟩ hpv)))
    | zero => rw [act_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [act_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [act_smul]; exact Submodule.smul_mem _ r hx
  have hx₁P : x₁ ∈ P := ⟨hx₁.mem_centres, 1, one_ne_zero, by rwa [one_smul]⟩
  rcases hG _ hinv with h | h
  · have hmem : x₁ ∈ Submodule.span k P := Submodule.subset_span hx₁P
    rw [h, Submodule.mem_bot] at hmem
    exact absurd hmem hx₁.ne_zero
  · by_contra hne
    have hyP : ∀ p ∈ P, spBil y p = 0 := by
      intro p hp
      by_contra hyp
      exact hne (hstep p hp y hy (by rwa [bil_symm])).2
    exact hy.1 (eq_zero_of_orth_span h hyP)

include hk in
theorem exists_init_pair (hirr : IsIrreducibleSp4 G₀) (hD : (transvSet G₀).Nonempty)
    {x₀ : Fin 4 → k} (hx₀ : x₀ ∈ centres G₀) (h4 : 4 ≤ Nat.card (Lam G₀ x₀)) :
    ∃ (F₁ : Subfield k) (x₁ y₁ : Fin 4 → k), 4 ≤ Nat.card F₁ ∧ IsNorm G₀ F₁ x₁ ∧
      IsNorm G₀ F₁ y₁ ∧ spBil x₁ y₁ = 1 := by
  obtain ⟨hx0, c₀, hc₀, hc₀L⟩ := hx₀
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq k 2) c₀
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact hc₀ hr
  set x₁ := r • x₀ with hx₁def
  have hx₁0 : x₁ ≠ 0 := smul_ne_zero hr0 hx0
  have h1 : (1 : k) ∈ Lam G₀ x₁ := by
    rw [mem_Lam_smul, mul_one, sq, ← hr]
    exact hc₀L
  have h4' : 4 ≤ Nat.card (Lam G₀ x₁) := by
    refine le_trans h4 (Nat.card_le_card_of_injective
      (fun d : Lam G₀ x₀ => (⟨(r ^ 2)⁻¹ * d, ?_⟩ : Lam G₀ x₁)) ?_)
    · rw [mem_Lam_smul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hr0), one_mul]
      exact d.2
    · intro d d' h
      have := congrArg Subtype.val h
      simp only at this
      exact Subtype.ext (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 2 hr0)) this)
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ centres G₀, spBil x₁ y ≠ 0 := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hx₁0 (eq_zero_of_orth_span (span_centres_eq_top hirr hD) h)
  obtain ⟨-, b, hb, hbL⟩ := hy
  set y₁ := (spBil x₁ y)⁻¹ • y with hy₁def
  have hxy₁ : spBil x₁ y₁ = 1 := by
    rw [hy₁def, LinearMap.map_smul, smul_eq_mul, inv_mul_cancel₀ hxy]
  have hbL' : spBil x₁ y ^ 2 * b ∈ Lam G₀ y₁ := by
    rw [hy₁def, mem_Lam_smul, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hxy, one_pow, one_mul]
    exact hbL
  obtain ⟨F₁, hx1, hy1⟩ := pair_lemma hk hxy₁ h1 h4' (mul_ne_zero (pow_ne_zero 2 hxy) hb) hbL'
  have hnx : IsNorm G₀ F₁ x₁ := ⟨hx₁0, fun c => Iff.of_eq (congrArg (fun s : Set k => c ∈ s) hx1)⟩
  have hny : IsNorm G₀ F₁ y₁ := ⟨fun h0 => by rw [h0] at hxy₁; simp at hxy₁,
    fun c => Iff.of_eq (congrArg (fun s : Set k => c ∈ s) hy1)⟩
  exact ⟨F₁, x₁, y₁, by rw [← card_lam_of_isNorm hnx]; exact h4', hnx, hny, hxy₁⟩

end Large

end CFSG.Quasithin.Ch3E213M.G41
