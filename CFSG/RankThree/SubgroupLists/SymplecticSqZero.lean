module

public import CFSG.RankThree.SubgroupLists.SymplecticSkewAxes

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem two_le_finrank_unipAxis {x : GL V₄ K} (hx : IsSqZero x) :
    2 ≤ finrank K (unipAxis x) := by
  set f := Matrix.toLin' ((x : Matrix V₄ V₄ K) - 1) with hf
  have hax : unipAxis x = LinearMap.ker f := rfl
  have hle : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, hf, ← LinearMap.comp_apply, ← Matrix.toLin'_mul]
    rw [show ((x : Matrix V₄ V₄ K) - 1) * ((x : Matrix V₄ V₄ K) - 1) = 0 from hx]
    simp
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h4 : finrank K (V₄ → K) = 4 := by simp
  rw [hax]
  omega

theorem eq_one_of_finrank_unipAxis_eq_four {x : GL V₄ K}
    (h4 : finrank K (unipAxis x) = 4) : x = 1 := by
  have htop : unipAxis x = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [h4]
    simp
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ unipAxis x := by rw [htop]; exact Submodule.mem_top
  rw [mem_unipAxis] at hv
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hv, Units.val_one, Matrix.one_mulVec]

theorem exists_eq_spTrans_of_finrank_unipAxis {x : GL V₄ K} (hxS : x ∈ StatedSp 2 K)
    (hx : IsSqZero x) (h3 : finrank K (unipAxis x) = 3) :
    ∃ a : V₄ → K, ∃ c : K, a ≠ 0 ∧ c ≠ 0 ∧ x = spTrans a c := by
  classical
  set f := Matrix.toLin' ((x : Matrix V₄ V₄ K) - 1) with hf
  have hfv : ∀ v, f v = (x : Matrix V₄ V₄ K) *ᵥ v - v := fun v => by
    rw [hf, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hrank : finrank K (LinearMap.range f) = 1 := by
    have h2 := LinearMap.finrank_range_add_finrank_ker f
    have h4 : finrank K (V₄ → K) = 4 := by simp
    have hax : unipAxis x = LinearMap.ker f := rfl
    rw [hax] at h3
    omega
  obtain ⟨a, ha⟩ := finrank_eq_one_iff'.mp hrank
  have ha0 : (a : V₄ → K) ≠ 0 := by
    intro h
    have := ha.1
    exact this (Subtype.ext h)
  have hmul : ∀ v, ∃ c : K, f v = c • (a : V₄ → K) := fun v => by
    obtain ⟨c, hc⟩ := ha.2 ⟨f v, LinearMap.mem_range_self f v⟩
    exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩
  choose φ hφ using hmul
  have haker : f a = 0 := by
    obtain ⟨w, hw⟩ := a.2
    rw [← hw, ← LinearMap.comp_apply, hf, ← Matrix.toLin'_mul,
      show ((x : Matrix V₄ V₄ K) - 1) * ((x : Matrix V₄ V₄ K) - 1) = 0 from hx]
    simp
  have hB : ∀ v w, φ w * spForm 2 K v a + φ v * spForm 2 K a w = 0 := by
    intro v w
    have hpres := spForm_mulVec hxS v w
    have hxv : (x : Matrix V₄ V₄ K) *ᵥ v = v + φ v • (a : V₄ → K) := by
      rw [← hφ v, hfv]; abel
    have hxw : (x : Matrix V₄ V₄ K) *ᵥ w = w + φ w • (a : V₄ → K) := by
      rw [← hφ w, hfv]; abel
    rw [hxv, hxw] at hpres
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      spForm_self, mul_zero, add_zero] at hpres
    linear_combination hpres
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, spForm 2 K w₀ (a : V₄ → K) ≠ 0 := by
    by_contra h
    push Not at h
    exact ha0 (eq_zero_of_forall_spForm h)
  set c := φ w₀ / spForm 2 K w₀ (a : V₄ → K) with hc
  have hφv : ∀ v, φ v = c * spForm 2 K v (a : V₄ → K) := by
    intro v
    have h := hB v w₀
    have hanti : spForm 2 K (a : V₄ → K) w₀ = -spForm 2 K w₀ (a : V₄ → K) :=
      (LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt _ _).symm
    rw [hanti] at h
    rw [hc, div_mul_eq_mul_div, eq_div_iff hw₀]
    linear_combination -h
  have hc0 : c ≠ 0 := by
    intro h0
    apply ha.1
    obtain ⟨w, hw⟩ := a.2
    apply Subtype.ext
    show (a : V₄ → K) = 0
    rw [← hw, hφ w, hφv w, h0, zero_mul, zero_smul]
  refine ⟨a, c, ha0, hc0, ?_⟩
  apply gl_ext_mulVec
  intro v
  rw [spTrans_mulVec, ← hφv v, ← hφ v, hfv]
  abel

theorem finrank_unipAxis_eq_two_of_not_spTrans {x : GL V₄ K} (hxS : x ∈ StatedSp 2 K)
    (hx : IsSqZero x) (hx1 : x ≠ 1)
    (hnotr : ∀ (a : V₄ → K) (c : K), a ≠ 0 → c ≠ 0 → x ≠ spTrans a c) :
    finrank K (unipAxis x) = 2 := by
  have h2 := two_le_finrank_unipAxis hx
  have hle : finrank K (unipAxis x) ≤ 4 := by
    have := Submodule.finrank_le (unipAxis x)
    simpa using this
  rcases (show finrank K (unipAxis x) = 2 ∨ finrank K (unipAxis x) = 3 ∨
      finrank K (unipAxis x) = 4 by omega) with h | h | h
  · exact h
  · obtain ⟨a, c, ha, hc, rfl⟩ := exists_eq_spTrans_of_finrank_unipAxis hxS hx h
    exact absurd rfl (hnotr a c ha hc)
  · exact absurd (eq_one_of_finrank_unipAxis_eq_four h) hx1

end CFSG.RankThree.SubgroupLists
