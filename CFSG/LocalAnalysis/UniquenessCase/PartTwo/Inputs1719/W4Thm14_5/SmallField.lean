module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDensity
import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDescent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.QuasithinUnique.Setup.SL2Modules

variable {G W : Type} [Group G] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem conj_mem_endRing (ρ : Representation (ZMod 2) G W) (s : W ≃ₗ[ZMod 2] W)
    (hs : ∀ w, s (s w) = w) (hN : ∀ g, ∃ g', ∀ w, s (ρ g (s w)) = ρ g' w) (d : EndRing ρ) :
    ∃ ψ : EndRing ρ, (ψ : W → W) = fun w => s (d (s w)) := by
  have hφ := (mem_endRing_iff ρ ((s : W →ₗ[ZMod 2] W) ∘ₗ
      ((d : W →ₗ[ZMod 2] W).restrictScalars (ZMod 2) ∘ₗ (s : W →ₗ[ZMod 2] W)))).mpr
  obtain ⟨ψ, hψ⟩ := hφ fun g v => by
    obtain ⟨g', hg'⟩ := hN g
    have h1 : ∀ w, s (ρ g w) = ρ g' (s w) := fun w => by rw [← hg', hs]
    have h2 : ∀ w, ρ g (s w) = s (ρ g' w) := fun w => by
      have h := h1 (s w)
      rw [hs] at h
      rw [← h, hs]
    have hd : ∀ w, d (ρ g' w) = ρ g' (d w) := fun w =>
      d.map_smul (⟨ρ g', Algebra.subset_adjoin ⟨g', rfl⟩⟩ : spanAlg ρ) w
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.coe_restrictScalars]
    rw [h1, hd, h2]
  exact ⟨ψ, by rw [hψ]; rfl⟩

theorem card_fix_sq_of_not_commute_endRing (ρ : Representation (ZMod 2) G W)
    [Fact ρ.IsIrreducible] (s : W ≃ₗ[ZMod 2] W) (hs : ∀ w, s (s w) = w)
    (hN : ∀ g, ∃ g', ∀ w, s (ρ g (s w)) = ρ g' w)
    (hD : ∃ d : EndRing ρ, ∃ w, s (d (s w)) ≠ d w) :
    Nat.card {w : W // s w = w} ^ 2 = Nat.card W := by
  classical
  have : Finite (EndRing ρ) := finite_endRing ρ
  have : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  let σf : EndRing ρ → EndRing ρ := fun d => Classical.choose (conj_mem_endRing ρ s hs hN d)
  have hσf : ∀ d w, σf d w = s (d (s w)) := fun d w =>
    congrFun (Classical.choose_spec (conj_mem_endRing ρ s hs hN d)) w
  let σ : EndRing ρ →+* EndRing ρ :=
    { toFun := σf
      map_one' := LinearMap.ext fun w => by rw [hσf]; simp [hs]
      map_mul' := fun a b => LinearMap.ext fun w => by
        simp only [Module.End.mul_apply, hσf, hs]
      map_zero' := LinearMap.ext fun w => by rw [hσf]; simp
      map_add' := fun a b => LinearMap.ext fun w => by
        simp only [LinearMap.add_apply, hσf, map_add] }
  have hσ : ∀ c, σ (σ c) = c := fun c => LinearMap.ext fun w => by
    show σf (σf c) w = c w
    rw [hσf, hσf, hs, hs]
  have hσne : ∃ c, σ c ≠ c := by
    obtain ⟨d, w, hdw⟩ := hD
    exact ⟨d, fun h => hdw (by rw [← hσf]; exact congrArg (fun f : EndRing ρ => f w) h)⟩
  have hsl : ∀ (c : EndRing ρ) (x : W), s.toAddEquiv (c • x) = σ c • s.toAddEquiv x := by
    intro c x
    show s (c x) = σf c (s x)
    rw [hσf, hs]
  exact CFSG.LocalAnalysis.RankThreeUC.card_fix_sq_of_semilinear_involution σ hσ hσne
    s.toAddEquiv hsl hs

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
