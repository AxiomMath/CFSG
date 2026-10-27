module

public import CFSG.Milestones.ASVolI.B4Natural

public section

namespace CFSG.ASVolI

open CFSG.GroupTheory.GLnTwoSplitting CFSG.Quasithin.JonesParshall Module Submodule

section Inv

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]

theorem burnsideB49x_exists_sep {S : Submodule (ZMod 2) E}
    (hS : finrank (ZMod 2) S < finrank (ZMod 2) E) :
    ∃ f : Dual (ZMod 2) E, (∀ s ∈ S, f s = 0) ∧ ∃ z, f z = 1 := by
  obtain ⟨z, -, hz⟩ := exists_mem_notMem_of_finrank_lt (U := ⊤) (S := S) (by rwa [finrank_top])
  obtain ⟨f, hf, hfz⟩ := exists_dual_eq_one_of_notMem hz
  exact ⟨f, hf, z, hfz⟩

theorem burnsideB49x_exists_sep_two (h3 : 3 ≤ finrank (ZMod 2) E) (u y : E) :
    ∃ f : Dual (ZMod 2) E, f u = 0 ∧ f y = 0 ∧ ∃ z, f z = 1 := by
  obtain ⟨f, hf, z, hz⟩ := burnsideB49x_exists_sep (S := span (ZMod 2) {u, y})
    ((finrank_span_pair_le u y).trans_lt (by omega))
  exact ⟨f, hf u (subset_span (by simp)), hf y (subset_span (by simp)), z, hz⟩

theorem burnsideB49x_exists_sep_three (h4 : 4 ≤ finrank (ZMod 2) E) (u x y : E) :
    ∃ f : Dual (ZMod 2) E, f u = 0 ∧ f x = 0 ∧ f y = 0 ∧ ∃ z, f z = 1 := by
  classical
  have hS : finrank (ZMod 2) (span (ZMod 2) (({u, x, y} : Finset E) : Set E)) <
      finrank (ZMod 2) E :=
    (finrank_span_finset_le_card _).trans_lt (Finset.card_le_three.trans_lt (by omega))
  obtain ⟨f, hf, z, hz⟩ := burnsideB49x_exists_sep hS
  exact ⟨f, hf u (subset_span (by simp)), hf x (subset_span (by simp)),
    hf y (subset_span (by simp)), z, hz⟩

theorem burnsideB49x_inv_one (h3 : 3 ≤ finrank (ZMod 2) E) (α : E → ZMod 2)
    (hα : ∀ x y, α (x + y) = α x + α y) (hinv : ∀ (g : E ≃ₗ[ZMod 2] E) x, α (g x) = α x) :
    ∀ y, α y = 0 := by
  intro y
  obtain ⟨f, hfy, -, z, hz⟩ := burnsideB49x_exists_sep_two h3 y y
  have h := hinv (LinearEquiv.transvection hfy) z
  rw [transvection_apply, hz, one_smul, hα] at h
  exact add_left_cancel (h.trans (add_zero _).symm)

theorem burnsideB49x_inv_two (h3 : 3 ≤ finrank (ZMod 2) E) (B : E → E → ZMod 2)
    (hB : ∀ u y y', B u (y + y') = B u y + B u y')
    (hinv : ∀ (g : E ≃ₗ[ZMod 2] E) u y, B (g u) (g y) = B u y) : ∀ u y, B u y = 0 := by
  intro u y
  obtain ⟨f, hfu, hfy, z, hz⟩ := burnsideB49x_exists_sep_two h3 u y
  have h := hinv (LinearEquiv.transvection hfy) u z
  rw [transvection_apply, transvection_apply, hfu, zero_smul, add_zero, hz, one_smul, hB] at h
  exact add_left_cancel (h.trans (add_zero _).symm)

theorem burnsideB49x_inv_three (h4 : 4 ≤ finrank (ZMod 2) E) (T : E → E → E → ZMod 2)
    (hT : ∀ u x y y', T u x (y + y') = T u x y + T u x y')
    (hinv : ∀ (g : E ≃ₗ[ZMod 2] E) u x y, T (g u) (g x) (g y) = T u x y) :
    ∀ u x y, T u x y = 0 := by
  intro u x y
  obtain ⟨f, hfu, hfx, hfy, z, hz⟩ := burnsideB49x_exists_sep_three h4 u x y
  have h := hinv (LinearEquiv.transvection hfy) u x z
  rw [transvection_apply, transvection_apply, transvection_apply, hfu, hfx, zero_smul, add_zero,
    add_zero, hz, one_smul, hT] at h
  exact add_left_cancel (h.trans (add_zero _).symm)

theorem burnsideB49x_stab_scalar (h3 : 3 ≤ finrank (ZMod 2) E) {u : E} (hu : u ≠ 0)
    (X : E →ₗ[ZMod 2] E) (hX : ∀ g : E ≃ₗ[ZMod 2] E, g u = u → ∀ x, X (g x) = g (X x)) :
    ∃ c : ZMod 2, ∀ x, X x = c • x := by
  have key : ∀ (f : Dual (ZMod 2) E) (d : E), f u = 0 → f d = 0 → ∀ x,
      f x • X d = f (X x) • d := by
    intro f d hfu hfd x
    have hgu : LinearEquiv.transvection hfd u = u := by
      rw [transvection_apply, hfu, zero_smul, add_zero]
    have h := hX _ hgu x
    rw [transvection_apply, transvection_apply, map_add, map_smul] at h
    exact add_left_cancel h
  obtain ⟨f₀, hf₀u, -, z₀, hz₀⟩ := burnsideB49x_exists_sep_two h3 u u
  refine ⟨f₀ (X z₀), fun d => ?_⟩
  obtain ⟨f, hfu, hfd, z, hz⟩ := burnsideB49x_exists_sep_two h3 u d
  have h1 := key f d hfu hfd z
  have h2 := key f u hfu hfu z
  have h3' := key f₀ u hf₀u hf₀u z₀
  rw [hz, one_smul] at h1 h2
  rw [hz₀, one_smul] at h3'
  have hc : f (X z) = f₀ (X z₀) := smul_eq_smul_of_ne_zero hu (h2.symm.trans h3')
  rw [h1, hc]

theorem burnsideB49x_exists_ne_zero (h1 : 1 ≤ finrank (ZMod 2) E) : ∃ u : E, u ≠ 0 :=
  (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2) (M := E)).1 (by omega)

theorem burnsideB49x_equiv_scalar (h3 : 3 ≤ finrank (ZMod 2) E) (γ : E → E)
    (hγ : ∀ x y, γ (x + y) = γ x + γ y)
    (heq : ∀ (g : E ≃ₗ[ZMod 2] E) x, γ (g x) = g (γ x)) :
    ∃ c : ZMod 2, ∀ x, γ x = c • x := by
  obtain ⟨u, hu⟩ := burnsideB49x_exists_ne_zero (E := E) (by omega)
  let X : E →ₗ[ZMod 2] E := (AddMonoidHom.mk' γ hγ).toZModLinearMap 2
  exact burnsideB49x_stab_scalar h3 hu X (fun g _ x => heq g x)

theorem burnsideB49x_equiv_end_zero (h3 : 3 ≤ finrank (ZMod 2) E) (M : E → E →ₗ[ZMod 2] E)
    (hM : ∀ u v, M (u + v) = M u + M v)
    (heq : ∀ (g : E ≃ₗ[ZMod 2] E) u x, M (g u) (g x) = g (M u x)) : ∀ u x, M u x = 0 := by
  have hscal : ∀ u, u ≠ 0 → ∃ c : ZMod 2, ∀ x, M u x = c • x := fun u hu =>
    burnsideB49x_stab_scalar h3 hu (M u) (fun g hg x => by rw [← heq g u x, hg])
  have hsame : ∀ u v, u ≠ 0 → v ≠ 0 → ∀ c c' : ZMod 2, (∀ x, M u x = c • x) →
      (∀ x, M v x = c' • x) → c = c' := by
    intro u v hu hv c c' hc hc'
    obtain ⟨f, d, h, hg⟩ := exists_transvection_apply_eq hu hv
    have hgu : LinearEquiv.transvection h u ≠ 0 := by rw [hg]; exact hv
    have e : c' • LinearEquiv.transvection h u = c • LinearEquiv.transvection h u := by
      rw [← hc', ← hg, heq, hc, map_smul]
    exact (smul_eq_smul_of_ne_zero hgu e).symm
  have hM0 : M 0 = 0 := by
    have h := hM 0 0
    rw [add_zero] at h
    exact (add_left_cancel ((add_zero (M 0)).trans h)).symm
  intro u x
  by_cases hu : u = 0
  · rw [hu, hM0]
    rfl
  · obtain ⟨c, hc⟩ := hscal u hu
    obtain ⟨v, -, hv⟩ := exists_mem_notMem_of_finrank_lt (U := ⊤) (S := span (ZMod 2) {u, u})
      (by rw [finrank_top]; exact (finrank_span_pair_le u u).trans_lt (by omega))
    have hv0 : v ≠ 0 := fun h => hv (h ▸ zero_mem _)
    have huv : u + v ≠ 0 := by
      intro h
      apply hv
      have : v = u := ((two_add_eq_iff.1 h).trans (zero_add v)).symm
      rw [this]
      exact subset_span (by simp)
    obtain ⟨c', hc'⟩ := hscal v hv0
    obtain ⟨c'', hc''⟩ := hscal (u + v) huv
    have e1 := hsame u v hu hv0 c c' hc hc'
    have e2 := hsame u (u + v) hu huv c c'' hc hc''
    have h := congrArg (fun F : E →ₗ[ZMod 2] E => F u) (hM u v)
    simp only [LinearMap.add_apply, hc, hc', hc''] at h
    rw [← e1, ← e2, two_add_self] at h
    have hc0 : c = 0 := by
      rcases zmod_two_eq_zero_or_one c with h0 | h0
      · exact h0
      · rw [h0, one_smul] at h
        exact absurd h hu
    rw [hc x, hc0, zero_smul]

end Inv

section Vanish

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {M : Type*} [AddCommGroup M]

theorem burnsideB49x_vanish_stab {μ : (W ≃ₗ[ZMod 2] W) →* AddMonoid.End M}
    {φ : Dual (ZMod 2) W} {w₀ : W} (hw₀ : φ w₀ = 1) {δ : (W ≃ₗ[ZMod 2] W) → M}
    (hδ : δ ∈ Z1A μ) (hK : ∀ k ∈ burnsideB49_K φ w₀, δ k = 0)
    (hQ : ∀ (u : W) (h : φ u = 0), δ (burnsideB49_tv φ u h) = 0) :
    ∀ s ∈ burnsideB49_stab φ, δ s = 0 := by
  intro s hs
  have hs' := burnsideB49_mem_stab.1 hs
  have hu : φ (s w₀ + w₀) = 0 := by
    rw [map_add, hs', hw₀]
    exact zmod_two_add_self _
  have hkK : burnsideB49_tv φ (s w₀ + w₀) hu * s ∈ burnsideB49_K φ w₀ := by
    refine ⟨fun x => ?_, ?_⟩
    · rw [LinearEquiv.mul_apply, burnsideB49_tv_apply, map_add, map_smul, hu, smul_zero,
        add_zero, hs']
    · rw [LinearEquiv.mul_apply, burnsideB49_tv_apply, hs', hw₀, one_smul]
      calc s w₀ + (s w₀ + w₀) = (s w₀ + s w₀) + w₀ := by abel
        _ = w₀ := by rw [two_add_self, zero_add]
  have hsk : s = burnsideB49_tv φ (s w₀ + w₀) hu * (burnsideB49_tv φ (s w₀ + w₀) hu * s) := by
    rw [← mul_assoc, burnsideB49_tv_mul_self, one_mul]
  rw [hsk, hδ, hQ _ hu, hK _ hkK, map_zero, add_zero]

theorem burnsideB49x_B1A_of_vanish_stab [FiniteDimensional (ZMod 2) W] [Module (ZMod 2) M]
    {μ : (W ≃ₗ[ZMod 2] W) →* AddMonoid.End M} {φ : Dual (ZMod 2) W} (hφ : φ ≠ 0)
    {δ : (W ≃ₗ[ZMod 2] W) → M} (hδ : δ ∈ Z1A μ)
    (hP : ∀ s ∈ burnsideB49_stab φ, δ s = 0) : δ ∈ B1A μ := by
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  haveI : Finite (W ≃ₗ[ZMod 2] W) :=
    Finite.of_injective (fun f : W ≃ₗ[ZMod 2] W => (f : W → W))
      (fun _ _ h => LinearEquiv.ext (congrFun h))
  exact mem_B1A_of_vanish (fun m => two_add_self m) (burnsideB49_stab_index_odd hφ) hδ hP

end Vanish

end CFSG.ASVolI
