module

public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameTrans
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainRecOut

public section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open Matrix

variable {G : Type} [Group G] {b₀ : G} {K E : Subgroup G}

theorem e7Good_e0 : e7Good (Pi.single 0 1) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem not_e7Good_e0_add : ∀ c : ZMod 3, c ≠ 0 → ¬ e7Good (Pi.single 0 1 + c • Pi.single 1 1) := by
  decide +kernel

theorem exists_swap [Finite G] (hstd : StdAssumptions b₀ K E Row.E7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hrec : RecOutE7 B b₀)
    (hcard : Nat.card ↥(B.realized (Subgroup.centralizer ({b₀} : Set G))) = 2903040)
    (hfus : Fus42 B b₀) :
    ∃ n ∈ Subgroup.normalizer (B.span : Set G), n * B.b 1 * n⁻¹ = b₀ ∧
      Subgroup.zpowers (n * b₀ * n⁻¹) = Subgroup.zpowers (B.b 1) := by
  have hb0 : B.b 0 = b₀ := hB.2.1
  obtain ⟨g, hg⟩ := (hrec.2.1 _ e7Good_e1.ne_zero).mpr e7Good_e1
  rw [Basis3.line, B.vec_single] at hg
  have hgE : g * b₀ * g⁻¹ ∈ B.span := by
    have h : g * b₀ * g⁻¹ ∈ Subgroup.zpowers (B.b 1) := hg ▸ Subgroup.mem_zpowers _
    exact (Subgroup.zpowers_le.mpr (B.b_mem_span 1)) h
  obtain ⟨x, hxN, hx⟩ := hfus.2 g hgE
  obtain ⟨X, hX⟩ := B.exists_acts hxN
  have hXe0 : B.vec (X *ᵥ Pi.single 0 1) = x * b₀ * x⁻¹ := by
    rw [mulVec_single_one_col, ← hX 0, hb0]
  have hXe0ne : X *ᵥ Pi.single 0 1 ≠ 0 := by
    intro h0
    rw [h0, B.vec_zero] at hXe0
    have : b₀ = 1 := conj_eq_one_iff.mp hXe0.symm
    have hord : orderOf b₀ = 3 := hstd.2.1.1.1
    rw [this, orderOf_one] at hord
    exact absurd hord (by decide)
  have hXe0mem : B.vec (X *ᵥ Pi.single 0 1) ∈ Subgroup.zpowers (B.vec (Pi.single 1 1)) := by
    rw [hXe0, ← hx, B.vec_single, ← hg]
    exact Subgroup.mem_zpowers _
  obtain ⟨c, hc⟩ : ∃ c : ZMod 3, X *ᵥ Pi.single 0 1 = c • Pi.single 1 1 := by
    rcases B.eq_or_eq_neg_of_vec_mem_zpowers hXe0ne hXe0mem with h | h
    · exact ⟨1, by rw [h, one_smul]⟩
    · exact ⟨-1, by rw [h, neg_one_smul]⟩
  obtain ⟨w, hw⟩ := B.exists_vec_eq (show x⁻¹ * b₀ * x⁻¹⁻¹ ∈ B.span from
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) b₀).mp (hb0 ▸ B.b_mem_span 0))
  rw [inv_inv] at hw
  have hXw : X *ᵥ w = Pi.single 0 1 := by
    apply B.vec_injective
    rw [← B.acts_vec hX, hw, B.vec_single, hb0]
    group
  have hgood := good_iff_of_acts hrec hX
  have hwg : e7Good w := (hgood w).mpr (hXw ▸ e7Good_e0)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hXe0ne hc
  have hw0 : w 0 = 0 := by
    refine orth_e0 w hwg ?_ ?_ ?_ ?_
    · rw [hgood, Matrix.mulVec_add, hXw, hc]
      exact not_e7Good_e0_add c hc0
    · rw [hgood, Matrix.mulVec_sub, hXw, hc, sub_eq_add_neg, ← neg_smul]
      exact not_e7Good_e0_add (-c) (neg_ne_zero.mpr hc0)
    · rintro rfl
      have h := hc
      rw [hXw] at h
      have := congrFun h 0
      simp at this
    · intro h0
      have h := congrArg (X *ᵥ ·) h0
      simp only [Matrix.mulVec_add, hXw, hc, Matrix.mulVec_zero] at h
      have := congrFun h 0
      simp at this
  obtain ⟨k, hkC, hkN, hk⟩ := exists_conj_b1 hstd hB hrec hcard hwg hw0
  have hkb0 : k * b₀ * k⁻¹ = b₀ := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hkC]
    group
  refine ⟨x * k, Subgroup.mul_mem _ hxN hkN, ?_, ?_⟩
  · calc x * k * B.b 1 * (x * k)⁻¹ = x * (k * B.b 1 * k⁻¹) * x⁻¹ := by group
      _ = b₀ := by rw [hk, hw]; group
  · calc Subgroup.zpowers (x * k * b₀ * (x * k)⁻¹)
        = Subgroup.zpowers (x * (k * b₀ * k⁻¹) * x⁻¹) := by congr 1; group
      _ = Subgroup.zpowers (B.b 1) := by rw [hkb0, ← hx, hg]

end CFSG.StandardType.FrameRoute.FS81.E7Frame
