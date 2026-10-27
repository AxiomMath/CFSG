module

public import CFSG.Walter.ReeOrder.Ward.Seven

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers

@[expose] noncomputable def deg {G : Type} [Group G] (χ : G → ℂ) : ℤ :=
  if h : ∃ n : ℕ, 0 < n ∧ χ 1 = n then (h.choose : ℤ) else 0

theorem deg_spec {G : Type} [Group G] {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) :
    (deg χ : ℂ) = χ 1 ∧ 0 < deg χ := by
  have h : ∃ n : ℕ, 0 < n ∧ χ 1 = n := exists_deg hχ
  rw [deg, dite_eq_left h]
  refine ⟨?_, by exact_mod_cast h.choose_spec.1⟩
  have := h.choose_spec.2
  push_cast
  exact this.symm

theorem deg_pos {G : Type} [Group G] {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) : 0 < deg χ :=
  (deg_spec hχ).2

theorem deg_eq {G : Type} [Group G] {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) : (deg χ : ℂ) = χ 1 :=
  (deg_spec hχ).1

variable {G : Type} [Group G] [Fintype G]

theorem sum_irr_eq_sum_of_vanish {M : Type*} [AddCommMonoid M] {R : Finset (G → ℂ)}
    (hR : R ⊆ (irreducibles_finite G).toFinset) (f : (G → ℂ) → M)
    (hf : ∀ χ ∈ (irreducibles_finite G).toFinset, χ ∉ R → f χ = 0) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, f χ = ∑ χ ∈ R, f χ :=
  (Finset.sum_subset hR hf).symm

theorem entry_sq_le (d : (G → ℂ) → ℤ)
    (hnorm : ∑ χ ∈ (irreducibles_finite G).toFinset, d χ * d χ = 4)
    (horth : ∑ χ ∈ (irreducibles_finite G).toFinset, d χ * deg χ = 0)
    {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) : d χ * d χ ≤ 1 := by
  have hmem : χ ∈ (irreducibles_finite G).toFinset := by rw [Set.Finite.mem_toFinset]; exact hχ
  by_contra hlt
  push Not at hlt
  have h4 : 4 ≤ d χ * d χ := by
    have h1 : 2 ≤ |d χ| := by
      by_contra h
      push Not at h
      have : |d χ| * |d χ| ≤ 1 := by
        have h0 : 0 ≤ |d χ| := abs_nonneg _
        nlinarith
      rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)] at this
      omega
    have := mul_le_mul h1 h1 (by norm_num) (abs_nonneg _)
    rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)] at this
    linarith
  rw [← Finset.add_sum_erase _ _ hmem] at hnorm
  have hrest : ∑ χ' ∈ (irreducibles_finite G).toFinset.erase χ, d χ' * d χ' = 0 := by
    have hnn : 0 ≤ ∑ χ' ∈ (irreducibles_finite G).toFinset.erase χ, d χ' * d χ' :=
      Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    linarith
  have hzero : ∀ χ' ∈ (irreducibles_finite G).toFinset.erase χ, d χ' = 0 := by
    intro χ' hχ'
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => mul_self_nonneg _)).mp hrest χ' hχ'
    exact zero_eq_mul_self.mp this.symm
  rw [← Finset.add_sum_erase _ _ hmem,
    Finset.sum_eq_zero (fun χ' hχ' => by rw [hzero χ' hχ', zero_mul]), add_zero] at horth
  have hd : d χ ≠ 0 := by
    intro h0
    rw [h0] at hlt
    simp at hlt
  have := deg_pos hχ
  rcases mul_eq_zero.mp horth with h | h
  · exact hd h
  · omega

theorem entry_cases (d : (G → ℂ) → ℤ)
    (hnorm : ∑ χ ∈ (irreducibles_finite G).toFinset, d χ * d χ = 4)
    (horth : ∑ χ ∈ (irreducibles_finite G).toFinset, d χ * deg χ = 0)
    {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) : d χ = 0 ∨ d χ = 1 ∨ d χ = -1 := by
  have h := entry_sq_le d hnorm horth hχ
  have : -1 ≤ d χ ∧ d χ ≤ 1 := by constructor <;> nlinarith
  omega

@[expose] noncomputable def supp (d : (G → ℂ) → ℤ) : Finset (G → ℂ) :=
  (irreducibles_finite G).toFinset.filter fun χ => d χ ≠ 0

theorem mem_supp {d : (G → ℂ) → ℤ} {χ : G → ℂ} :
    χ ∈ supp d ↔ χ ∈ BlocksIrr G ∧ d χ ≠ 0 := by
  rw [supp, Finset.mem_filter, Set.Finite.mem_toFinset]

theorem supp_sub (d : (G → ℂ) → ℤ) : supp d ⊆ (irreducibles_finite G).toFinset :=
  Finset.filter_subset _ _

theorem eq_zero_of_not_mem_supp {d : (G → ℂ) → ℤ} {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G)
    (h : χ ∉ supp d) : d χ = 0 := by
  by_contra hd
  exact h (mem_supp.mpr ⟨hχ, hd⟩)

theorem sq_of_mem_supp (d : (G → ℂ) → ℤ)
    (hnorm : ∑ χ ∈ (irreducibles_finite G).toFinset, d χ * d χ = 4)
    (horth : ∑ χ ∈ (irreducibles_finite G).toFinset, d χ * deg χ = 0)
    {χ : G → ℂ} (hχ : χ ∈ supp d) : d χ * d χ = 1 := by
  obtain ⟨hχ, hd⟩ := mem_supp.mp hχ
  rcases entry_cases d hnorm horth hχ with h | h | h
  · exact absurd h hd
  · rw [h]; norm_num
  · rw [h]; norm_num

theorem card_supp (d : (G → ℂ) → ℤ)
    (hnorm : ∑ χ ∈ (irreducibles_finite G).toFinset, d χ * d χ = 4)
    (horth : ∑ χ ∈ (irreducibles_finite G).toFinset, d χ * deg χ = 0) :
    (supp d).card = 4 := by
  have h := hnorm
  rw [sum_irr_eq_sum_of_vanish (supp_sub d) (fun χ => d χ * d χ) (fun χ hχ hnot => by
    rw [Set.Finite.mem_toFinset] at hχ
    simp only [eq_zero_of_not_mem_supp hχ hnot, mul_zero])] at h
  rw [Finset.sum_congr rfl fun χ hχ => sq_of_mem_supp d hnorm horth hχ] at h
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

namespace WardSetup

variable {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ} {IV : Bool} (S : WardSetup G L q e IV)

theorem deg_orth {Φ : L → ℂ} (d : (G → ℂ) → ℤ)
    (hd : ∀ χ ∈ BlocksIrr G, BlocksInnerProduct (S.σ χ) Φ = d χ) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, d χ * deg χ = 0 := by
  have h := S.orth d hd (x := 1) (by rw [orderOf_one]; exact odd_one)
  have h' : ((∑ χ ∈ (irreducibles_finite G).toFinset, d χ * deg χ : ℤ) : ℂ) = 0 := by
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [Set.Finite.mem_toFinset] at hχ
    rw [deg_eq hχ, conj_one hχ]
  exact_mod_cast h'

theorem d1_orth : ∑ χ ∈ (irreducibles_finite G).toFinset, S.d1 χ * deg χ = 0 :=
  S.deg_orth S.d1 fun _ hχ => S.inner_Φ1 hχ
theorem d2_orth : ∑ χ ∈ (irreducibles_finite G).toFinset, S.d2 χ * deg χ = 0 :=
  S.deg_orth S.d2 fun _ hχ => S.inner_Φ2 hχ
theorem d3_orth : ∑ χ ∈ (irreducibles_finite G).toFinset, S.d3 χ * deg χ = 0 :=
  S.deg_orth S.d3 fun _ hχ => S.inner_Φ3 hχ
theorem dR_orth {θ : L → ℂ} (hθ : θ ∈ S.W.RFam) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.dR χ θ * deg χ = 0 :=
  S.deg_orth (S.dR · θ) fun _ hχ => S.inner_ΦR hχ hθ
theorem dS_orth {θ : L → ℂ} (hθ : θ ∈ S.W.SFam) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.dS χ θ * deg χ = 0 :=
  S.deg_orth (S.dS · θ) fun _ hχ => S.inner_ΦS hχ hθ

theorem d1_norm : ∑ χ ∈ (irreducibles_finite G).toFinset, S.d1 χ * S.d1 χ = 4 :=
  S.gram_principal.1
theorem d2_norm : ∑ χ ∈ (irreducibles_finite G).toFinset, S.d2 χ * S.d2 χ = 4 :=
  S.gram_principal.2.2.2.1
theorem d3_norm : ∑ χ ∈ (irreducibles_finite G).toFinset, S.d3 χ * S.d3 χ = 4 :=
  S.gram_principal.2.2.2.2.2
theorem dS_norm {θ : L → ℂ} (hθ : θ ∈ S.W.SFam) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.dS χ θ * S.dS χ θ = 4 := by
  rw [S.gram_S hθ hθ, ite_eq_left (Or.inl rfl)]
theorem dR_norm {θ : L → ℂ} (hθ : θ ∈ S.W.RFam) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.dR χ θ * S.dR χ θ = 2 := by
  rw [S.gram_R hθ hθ, ite_eq_left rfl]

end WardSetup

end CFSG.Walter.Ward
