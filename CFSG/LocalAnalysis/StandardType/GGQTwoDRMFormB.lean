module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMFormA
import CFSG.LocalAnalysis.StandardType.GGQTwoReflOrth
import CFSG.LocalAnalysis.StandardType.GGDepARefl

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section TransvectionFree

variable {m : ℕ}

theorem transvectionFree_of_hTF {H : Subgroup (DVec m ≃ₗ[ZMod 3] DVec m)}
    (hTF : ∀ g ∈ H, g ≠ 1 →
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g})) :
    QTwoLin.TransvectionFree H := by
  intro g hg ⟨u, ψ, hu, hψ, hψu, hgv⟩
  have hL : g.toLinearMap - LinearMap.id = ψ.smulRight u := by
    refine LinearMap.ext fun v => ?_
    simp [hgv v]
  have hmove : ggLinMove g = Submodule.span (ZMod 3) {u} := by
    rw [ggLinMove, hL, LinearMap.range_smulRight_apply hψ]
  have hne : g ≠ 1 := by
    intro h1
    obtain ⟨v, hv⟩ : ∃ v, ψ v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hψ (LinearMap.ext hcon)
    have h2 : v = v + ψ v • u := by
      have h5 := hgv v
      rwa [h1] at h5
    have h3 : ψ v • u = 0 := by
      have h4 : v + ψ v • u = v + 0 := by rw [← h2, add_zero]
      exact add_left_cancel h4
    rcases smul_eq_zero.mp h3 with h | h
    · exact hv h
    · exact hu h
  refine hTF g hg hne ⟨?_, ?_⟩
  · rw [hmove]
    exact finrank_span_singleton hu
  · rw [hmove, Submodule.span_singleton_le_iff_mem]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    change g u = u
    rw [hgv u, hψu, zero_smul, add_zero]

end TransvectionFree

section Isometry

variable {m : ℕ}

theorem dDot_reflection {c : DVec m} {φ : Module.Dual (ZMod 3) (DVec m)} (hφ : φ c = 2)
    {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1) (hφε : ∀ v, φ v = ε * dDot m c v) (v w : DVec m) :
    dDot m (v - φ v • c) (w - φ w • c) = dDot m v w := by
  have hn : ε * dDot m c c = 2 := by rw [← hφε, hφ]
  have key : ∀ x a b n e : ZMod 3, (e = 1 ∨ e = -1) → e * n = 2 →
      x - e * a * b - e * b * (a - e * a * n) = x := by decide
  rw [hφε v, hφε w]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [dDot_comm v c]
  exact key _ _ _ _ _ hε hn

theorem qtwoD_refl_isometry (hm : 4 ≤ m) {H : Subgroup (DVec m ≃ₗ[ZMod 3] DVec m)}
    (hW : dEven m ≤ H)
    (hTF : ∀ g ∈ H, g ≠ 1 →
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}))
    {t : DVec m ≃ₗ[ZMod 3] DVec m} (ht : t ∈ H) (hr : GGLinRefl t) (v w : DVec m) :
    dDot m (t v) (t w) = dDot m v w := by
  obtain ⟨c, φ, hφ, hT⟩ := (ggDepA_linRefl_iff (p := 3) (by norm_num) t).mp hr
  have htε : t = Module.reflection hφ := by
    ext x
    rw [hT x, Module.reflection_apply]
  have hsymm : (dDot m).IsSymm := ⟨fun x y => dDot_comm x y⟩
  obtain ⟨ε, hε, hφε⟩ := ggQ2_refl_orthogonal (p := 3) rfl (dRMLin m hm) (dRMLin_basis hm)
    (by simpa using hm) (dDot m) hsymm (fun _ => 1) (fun _ => one_ne_zero) (dRMLin_hβh hm) H
    (le_trans (dRMLin_weyl_le hm) hW) (transvectionFree_of_hTF hTF) hφ (htε ▸ ht)
  rw [hT v, hT w]
  exact dDot_reflection hφ hε hφε v w

theorem qtwoD_isometry_of_reflGen (hm : 4 ≤ m) {H : Subgroup (DVec m ≃ₗ[ZMod 3] DVec m)}
    (hW : dEven m ≤ H)
    (hTF : ∀ g ∈ H, g ≠ 1 →
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}))
    (hgen : H = Subgroup.closure {t | t ∈ H ∧ GGLinRefl t})
    {g : DVec m ≃ₗ[ZMod 3] DVec m} (hg : g ∈ H) (v w : DVec m) :
    dDot m (g v) (g w) = dDot m v w := by
  have hg' : g ∈ Subgroup.closure {t | t ∈ H ∧ GGLinRefl t} := by
    rw [← hgen]
    exact hg
  refine Subgroup.closure_induction (p := fun g _ => ∀ v w : DVec m, dDot m (g v) (g w) =
    dDot m v w) ?_ ?_ ?_ ?_ hg' v w
  · rintro x ⟨hxH, hxr⟩ v w
    exact qtwoD_refl_isometry hm hW hTF hxH hxr v w
  · intro v w
    rfl
  · intro x y _ _ hx hy v w
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx, hy]
  · intro x _ hx v w
    have h := hx (x⁻¹ v) (x⁻¹ w)
    have h1 : x (x⁻¹ v) = v := x.apply_symm_apply v
    have h2 : x (x⁻¹ w) = w := x.apply_symm_apply w
    rw [h1, h2] at h
    exact h.symm

end Isometry

end CFSG.StandardType.QTwo

end
