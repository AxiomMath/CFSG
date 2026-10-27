module

public import Mathlib.LinearAlgebra.BilinearForm.Properties

public section

namespace CFSG.StandardType.FrameRoute

theorem P13a1_hyperplane_fixer {F : Type} [Field F] (hodd : (2 : F) ≠ 0)
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate) (hsymm : B.IsSymm)
    (g : V ≃ₗ[F] V) (hg : ∀ x y, B (g x) (g y) = B x y)
    (H : Submodule F V) (hH : Module.finrank F H + 1 = Module.finrank F V)
    (hfix : ∀ x ∈ H, g x = x) :
    g = LinearEquiv.refl F V ∨
      ∃ v : V, B v v ≠ 0 ∧ ∀ x, g x = x - (2 * B x v / B v v) • v := by
  classical
  have hHtop : H ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top] at hH
    omega
  obtain ⟨w, hw⟩ : ∃ w, w ∉ H := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hHtop (Submodule.eq_top_iff'.mpr h)
  have hw0 : w ≠ 0 := fun h => hw (h ▸ H.zero_mem)
  have hinf : H ⊓ Submodule.span F {w} = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxH, hxspan⟩ := hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton (R := F) (x := x) (y := w)).mp hxspan
    by_cases hc0 : c = 0
    · rw [← hc, hc0, zero_smul]
      exact Submodule.zero_mem _
    · have hmem : c • w ∈ H := by rw [hc]; exact hxH
      exact absurd ((Submodule.smul_mem_iff H hc0).mp hmem) hw
  have hsupfin :
      Module.finrank F ↥(H ⊔ Submodule.span F {w}) = Module.finrank F V := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq H (Submodule.span F {w})
    rw [hinf, finrank_bot, finrank_span_singleton hw0] at h
    omega
  have hsup : H ⊔ Submodule.span F {w} = ⊤ :=
    Submodule.eq_top_of_finrank_eq hsupfin
  have hdecomp : ∀ x : V, ∃ h ∈ H, ∃ c : F, h + c • w = x := by
    intro x
    have hx : x ∈ H ⊔ Submodule.span F {w} := by rw [hsup]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at hx
    obtain ⟨h, hh, y, hy, hxy⟩ := hx
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨c, hc⟩ := hy
    exact ⟨h, hh, c, by rw [hc]; exact hxy⟩
  let u : V := g w - w
  have hgw : g w = w + u := by simp [u]
  have hgx : ∀ h ∈ H, ∀ c : F, g (h + c • w) = h + c • w + c • u := by
    intro h hh c
    rw [map_add, map_smul, hfix h hh, hgw, smul_add]
    abel
  have huH : ∀ h ∈ H, B u h = 0 := by
    intro h hh
    have h1 : B (g w) h = B w h := by
      calc B (g w) h = B (g w) (g h) := by rw [hfix h hh]
        _ = B w h := hg w h
    have hsub : B u h = B (g w) h - B w h := by simp [u]
    rw [hsub, h1, sub_self]
  by_cases hu0 : u = 0
  · left
    ext x
    obtain ⟨h, hh, c, hc⟩ := hdecomp x
    rw [← hc, hgx h hh c, hu0, smul_zero, add_zero, LinearEquiv.refl_apply]
  · right
    have hrel : 2 * B w u + B u u = 0 := by
      have h0 : B (w + u) (w + u) = B w w := by
        rw [← hgw]
        exact hg w w
      have hexp : B (w + u) (w + u) = B w w + B w u + B u w + B u u := by
        simp only [map_add, LinearMap.add_apply]
        abel
      rw [hexp] at h0
      have hsym : B u w = B w u := hsymm.eq u w
      rw [hsym] at h0
      have h2 : B w w + (B w u + B w u + B u u) = B w w + 0 := by
        rw [add_zero]
        calc B w w + (B w u + B w u + B u u) = B w w + B w u + B w u + B u u := by abel
          _ = B w w := h0
      have h3 : B w u + B w u + B u u = 0 := add_left_cancel h2
      rw [two_mul]
      exact h3
    have hBuu : B u u ≠ 0 := by
      intro huu
      apply hu0
      apply hB.1 u
      intro y
      obtain ⟨h, hh, c, hc⟩ := hdecomp y
      have hwu : B w u = 0 := by
        have h2 : 2 * B w u = -B u u := eq_neg_of_add_eq_zero_left hrel
        rw [huu, neg_zero] at h2
        exact (mul_eq_zero.mp h2).resolve_left hodd
      rw [← hc, map_add, map_smul, huH h hh, zero_add, hsymm.eq u w, hwu, smul_zero]
    refine ⟨u, hBuu, fun x => ?_⟩
    obtain ⟨h, hh, c, hc⟩ := hdecomp x
    rw [← hc, hgx h hh c]
    have hxBu : B (h + c • w) u = c * B w u := by
      calc B (h + c • w) u = B h u + B (c • w) u := by rw [map_add, LinearMap.add_apply]
        _ = c * B w u := by
              rw [hsymm.eq h u, huH h hh, map_smul B c w, LinearMap.smul_apply,
                smul_eq_mul, zero_add]
    have hA : 2 * (c * B w u) / B u u = -c := by
      have h2 : 2 * B w u = -B u u := eq_neg_of_add_eq_zero_left hrel
      have hmain : 2 * (c * B w u) = -(c * B u u) := by
        calc 2 * (c * B w u) = c * (2 * B w u) := by ring
          _ = c * (-B u u) := by rw [h2]
          _ = -(c * B u u) := by ring
      rw [hmain]
      field_simp
    rw [hxBu, hA]
    simp

end CFSG.StandardType.FrameRoute
