module

public import CFSG.Quasithin.Background.F918D0
public import CFSG.Quasithin.Background.QuadraticCocycle

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.JonesParshall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {G : Type*} [Group G] {M E : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  [AddCommGroup E] [Module (ZMod 2) E]

private theorem s16sp_extTwist_apply (ρM : Representation (ZMod 2) G M)
    (ρE : Representation (ZMod 2) G E) (s : E →ₗ[ZMod 2] M) (g : G) (x : E) :
    extTwist ρM ρE s g x = ρM g (s (ρE g⁻¹ x)) - s x := rfl

private theorem s16sp_q_extTwist (ρM : Representation (ZMod 2) G M)
    (ρE : Representation (ZMod 2) G E) (q : M →ₗ[ZMod 2] E) (s : E →ₗ[ZMod 2] M)
    (hqρ : ∀ g m, q (ρM g m) = ρE g (q m)) (hs : ∀ x, q (s x) = x) (g : G) (x : E) :
    q (extTwist ρM ρE s g x) = 0 := by
  rw [s16sp_extTwist_apply, map_sub, hqρ, hs, hs, ← Module.End.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply, sub_self]

private theorem s16sp_extTwist_mul (ρM : Representation (ZMod 2) G M)
    (ρE : Representation (ZMod 2) G E) (q : M →ₗ[ZMod 2] E) (s : E →ₗ[ZMod 2] M)
    (hqρ : ∀ g m, q (ρM g m) = ρE g (q m)) (hs : ∀ x, q (s x) = x)
    (hZ : ∀ g m, q m = 0 → ρM g m = m) (g h : G) (x : E) :
    extTwist ρM ρE s (g * h) x =
      extTwist ρM ρE s g x + extTwist ρM ρE s h (ρE g⁻¹ x) := by
  have h1 := s16sp_q_extTwist ρM ρE q s hqρ hs h (ρE g⁻¹ x)
  have h2 := hZ g _ h1
  rw [s16sp_extTwist_apply] at h2
  simp only [s16sp_extTwist_apply]
  have e1 : ρE (g * h)⁻¹ x = ρE h⁻¹ (ρE g⁻¹ x) := by
    rw [mul_inv_rev, map_mul, Module.End.mul_apply]
  rw [e1, map_mul, Module.End.mul_apply]
  have e2 : ρM g (ρM h (s (ρE h⁻¹ (ρE g⁻¹ x)))) =
      ρM g (ρM h (s (ρE h⁻¹ (ρE g⁻¹ x))) - s (ρE g⁻¹ x)) +
        ρM g (s (ρE g⁻¹ x)) := by
    rw [map_sub]
    abel
  rw [e2, h2]
  abel

private theorem s16sp_rep_inv_apply (ρE : Representation (ZMod 2) G E) (g : G) (y : E) :
    ρE g⁻¹ (ρE g y) = y := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private theorem s16sp_extCocycle_mem_B1 (ρM : Representation (ZMod 2) G M)
    (ρE : Representation (ZMod 2) G E) (q : M →ₗ[ZMod 2] E) (s : E →ₗ[ZMod 2] M)
    (hqρ : ∀ g m, q (ρM g m) = ρE g (q m)) (hs : ∀ x, q (s x) = x)
    (hZ : ∀ g m, q m = 0 → ρM g m = m)
    (hperf : ∀ ψ : M →ₗ[ZMod 2] ZMod 2, (∀ g m, ψ (ρM g m) = ψ m) → ψ = 0)
    (ψ : M →ₗ[ZMod 2] ZMod 2)
    (h : extCocycle ρM ρE s ψ ∈ B1 (Representation.dual ρE)) :
    ∀ m, q m = 0 → ψ m = 0 := by
  obtain ⟨l, hl⟩ := h
  have hl' : ∀ g x, ψ (extTwist ρM ρE s g x) = l (ρE g⁻¹ x) - l x := by
    intro g x
    have := congrArg (fun f => f g x) hl
    simp only [coboundary, LinearMap.coe_mk, AddHom.coe_mk, Representation.dual_apply,
      LinearMap.sub_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, extCocycle] at this
    exact this.symm
  let ψ' : M →ₗ[ZMod 2] ZMod 2 := ψ - ψ.comp (s.comp q) + l.comp q
  have hinv : ∀ g m, ψ' (ρM g m) = ψ' m := by
    intro g m
    have hm0 : q (m - s (q m)) = 0 := by rw [map_sub, hs, sub_self]
    have hfix := hZ g _ hm0
    have h1 := hl' g (ρE g (q m))
    rw [s16sp_extTwist_apply, s16sp_rep_inv_apply, map_sub] at h1
    have hA : ψ (ρM g m) = ψ m - ψ (s (q m)) + ψ (ρM g (s (q m))) := by
      have e : ρM g m = (m - s (q m)) + ρM g (s (q m)) := by
        have : m = (m - s (q m)) + s (q m) := by abel
        conv_lhs => rw [this]
        rw [map_add, hfix]
      rw [e, map_add, map_sub]
    simp only [ψ', LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, hqρ, hA]
    linear_combination (norm := abel_nf) h1
  have h0 := hperf ψ' hinv
  intro m hm
  have := LinearMap.congr_fun h0 m
  simpa [ψ', hm] using this

theorem s16sp_extCocycle_mem (ρM : Representation (ZMod 2) G M) (ρE : Representation (ZMod 2) G E)
    (q : M →ₗ[ZMod 2] E) (s : E →ₗ[ZMod 2] M) (hqρ : ∀ g m, q (ρM g m) = ρE g (q m))
    (hs : ∀ x, q (s x) = x) (hZ : ∀ g m, q m = 0 → ρM g m = m) (ψ : M →ₗ[ZMod 2] ZMod 2) :
    extCocycle ρM ρE s ψ ∈ Z1 (Representation.dual ρE) := by
  intro g h
  ext x
  simp only [extCocycle, LinearMap.comp_apply, LinearMap.add_apply, Representation.dual_apply,
    Module.Dual.transpose_apply]
  rw [s16sp_extTwist_mul ρM ρE q s hqρ hs hZ, map_add]

theorem s16sp_extCocycle_not_mem_B1 (ρM : Representation (ZMod 2) G M)
    (ρE : Representation (ZMod 2) G E) (q : M →ₗ[ZMod 2] E) (s : E →ₗ[ZMod 2] M)
    (hqρ : ∀ g m, q (ρM g m) = ρE g (q m)) (hs : ∀ x, q (s x) = x)
    (hZ : ∀ g m, q m = 0 → ρM g m = m)
    (hperf : ∀ ψ : M →ₗ[ZMod 2] ZMod 2, (∀ g m, ψ (ρM g m) = ψ m) → ψ = 0)
    (ψ : M →ₗ[ZMod 2] ZMod 2) {z : M} (hz : q z = 0) (hψz : ψ z = 1) :
    extCocycle ρM ρE s ψ ∉ B1 (Representation.dual ρE) := by
  intro h
  have hz0 := s16sp_extCocycle_mem_B1 ρM ρE q s hqρ hs hZ hperf ψ h z hz
  rw [hψz] at hz0
  exact one_ne_zero hz0

private theorem s16sp_zmod2_additive (a b c d e : ZMod 2) :
    a + b + c + (d + e + c) = a + d + (b + e) := by
  revert a b c d e
  decide

private theorem s16sp_zmod2_cocycle (a b c : ZMod 2) :
    c + b = (a + b) + (c + a) := by
  revert a b c
  decide

private theorem s16sp_zmod2_swap (a b c d : ZMod 2) (h : c + d = a + b) :
    a + c = b + d := by
  revert a b c d
  decide

private theorem s16sp_q0_zero (q₀ : E → ZMod 2)
    (b₀ : E →ₗ[ZMod 2] E →ₗ[ZMod 2] ZMod 2)
    (hq₀ : ∀ x y, q₀ (x + y) = q₀ x + q₀ y + b₀ x y) : q₀ 0 = 0 := by
  have h := hq₀ 0 0
  simpa using h

theorem s16sp_c0 (ρE : Representation (ZMod 2) G E) (q₀ : E → ZMod 2)
    (b₀ : E →ₗ[ZMod 2] E →ₗ[ZMod 2] ZMod 2) (hq₀ : ∀ x y, q₀ (x + y) = q₀ x + q₀ y + b₀ x y)
    (hb₀ : ∀ g x y, b₀ (ρE g x) (ρE g y) = b₀ x y)
    (hnoinv : ∀ l : Module.Dual (ZMod 2) E, ¬ ∀ g x, q₀ (ρE g x) + l (ρE g x) = q₀ x + l x) :
    ∃ c₀ : G → Module.Dual (ZMod 2) E, (∀ g x, c₀ g x = q₀ (ρE g⁻¹ x) + q₀ x) ∧
      c₀ ∈ Z1 (Representation.dual ρE) ∧ c₀ ∉ B1 (Representation.dual ρE) := by
  have hq0 : q₀ 0 = 0 := s16sp_q0_zero q₀ b₀ hq₀
  let c₀ : G → Module.Dual (ZMod 2) E := fun g =>
    { toFun := fun x => q₀ (ρE g⁻¹ x) + q₀ x
      map_add' := fun x y => by
        have hp : b₀ (ρE g⁻¹ x) (ρE g⁻¹ y) = b₀ x y := hb₀ g⁻¹ x y
        simp only [map_add]
        rw [hq₀, hq₀, hp]
        exact s16sp_zmod2_additive _ _ _ _ _
      map_smul' := fun c x => by
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with hc | hc
        · subst hc
          simp [hq0]
        · subst hc
          simp }
  refine ⟨c₀, ?_, ?_, ?_⟩
  · intro g x
    rfl
  · intro g h
    ext x
    simp only [c₀, LinearMap.add_apply, Representation.dual_apply,
      Module.Dual.transpose_apply, LinearMap.comp_apply, mul_inv_rev, map_mul,
      Module.End.mul_apply]
    exact s16sp_zmod2_cocycle _ _ _
  · intro hc
    rw [B1, LinearMap.mem_range] at hc
    obtain ⟨l, hl⟩ := hc
    apply hnoinv l
    intro g x
    have hg := congrArg (fun f => f g⁻¹ x) hl
    simp only [coboundary, LinearMap.coe_mk, AddHom.coe_mk, Representation.dual_apply,
      Module.Dual.transpose_apply, LinearMap.sub_apply, LinearMap.comp_apply, c₀,
      inv_inv] at hg
    rw [sub_eq_add_neg, ZModModule.neg_eq_self] at hg
    exact s16sp_zmod2_swap _ _ _ _ hg

theorem s16sp_exists_coboundary [Finite G] [Finite E] (ρE : Representation (ZMod 2) G E)
    (hH1 : Module.finrank (ZMod 2) (H1 (Representation.dual ρE)) ≤ 1)
    {c c' : G → Module.Dual (ZMod 2) E} (hc : c ∈ Z1 (Representation.dual ρE))
    (hc' : c' ∈ Z1 (Representation.dual ρE)) (hn : c ∉ B1 (Representation.dual ρE))
    (hn' : c' ∉ B1 (Representation.dual ρE)) :
    ∃ l : Module.Dual (ZMod 2) E, ∀ g, c g = c' g + (Representation.dual ρE g l - l) := by
  have : Module.Finite (ZMod 2) E := Module.Finite.of_finite
  have : Finite (Module.Dual (ZMod 2) E) := Module.finite_of_finite (ZMod 2)
  obtain ⟨l, hl⟩ :=
    exists_coboundary_of_mem_Z1_of_not_mem_B1_of_finrank_H1_le_one
      (Representation.dual ρE) hH1 hc hc' hn hn'
  exact ⟨l, fun g => by simpa [coboundary] using congrFun hl g⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
