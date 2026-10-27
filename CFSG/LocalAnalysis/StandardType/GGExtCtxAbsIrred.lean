module

public import CFSG.LocalAnalysis.StandardType.GGExtCtx
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleFaithful

public section

namespace CFSG.StandardType

theorem GGExtCtx.of_absIrred {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {A : Subgroup (V ≃ₗ[ZMod p] V)}
    {T : Submodule (ZMod p) V} {AT : Subgroup (↥T ≃ₗ[ZMod p] ↥T)}
    (hdisp : ∀ a ∈ A, ∀ v, a v - v ∈ T)
    (hT : T ≤ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)))
    (hfix : ∀ v, (∀ a ∈ A, a v = v) → v = 0)
    (hnt : ∀ g ∈ A, ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hrestr : ∀ q, q ∈ AT ↔ ∃ a ∈ A, ∀ w : ↥T, a (w : V) = ((q w : ↥T) : V))
    (hirr : ZS.AbsIrred p AT) : GGExtCtx A T AT := by
  have hcom : ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) = T := by
    refine le_antisymm ?_ hT
    rw [ggLinCom]
    refine iSup₂_le fun a ha => ?_
    rintro v ⟨w, rfl⟩
    simpa using hdisp a ha w
  have hnotr : ∀ g ∈ A, g ≠ 1 →
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}) := by
    intro g hg _ hcon
    exact hnt g hg ⟨hcon.1, fun w =>
      hcon.2 (LinearMap.mem_range_self (g.toLinearMap - LinearMap.id) w)
        g (Set.mem_singleton g)⟩
  have htriv : ∀ g ∈ A, ∀ v : V,
      g v - v ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) := by
    intro g hg v
    exact le_iSup₂ (f := fun a (_ : a ∈ (A : Set (V ≃ₗ[ZMod p] V))) => ggLinMove a) g hg
      (LinearMap.mem_range_self (g.toLinearMap - LinearMap.id) v)
  have hirr' : ∀ W : Submodule (ZMod p) V,
      W ≤ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) →
      (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) →
      W = ⊥ ∨ W = ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) := by
    rw [hcom]
    intro W hWU hWstab
    let W' : Submodule (ZMod p) ↥T := W.comap T.subtype
    have hW'map : W'.map T.subtype = W := by
      apply le_antisymm
      · rintro _ ⟨u, hu, rfl⟩
        exact hu
      · intro z hz
        exact ⟨⟨z, hWU hz⟩, hz, rfl⟩
    have hinv : ∀ a ∈ AT, ∀ w ∈ W', a w ∈ W' := by
      intro a ha w hw
      obtain ⟨a₀, ha₀, hrest⟩ := (hrestr a).mp ha
      have hmem : a₀ (w : V) ∈ W := hWstab a₀ ha₀ (w : V) hw
      rw [hrest w] at hmem
      exact hmem
    rcases hirr.1 W' hinv with h | h
    · left
      rw [← hW'map, h, Submodule.map_bot]
    · right
      rw [← hW'map, h, Submodule.map_top, Submodule.range_subtype]
  have hend : ∀ f : V →ₗ[ZMod p] V,
      LinearMap.range f ≤ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) →
      (∀ a ∈ A, ∀ u ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)),
        f (a u) = a (f u)) →
      ∃ c : ZMod p, ∀ u ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)), f u = c • u := by
    rw [hcom]
    intro f hfrange hfcomm
    let F : Module.End (ZMod p) ↥T :=
      { toFun := fun u => ⟨f u, hfrange (LinearMap.mem_range_self f u)⟩
        map_add' := by intro u v; ext; simp
        map_smul' := by intro c u; ext; simp }
    have hFcomm : ∀ a ∈ AT,
        F ∘ₗ (a : ↥T →ₗ[ZMod p] ↥T) = (a : ↥T →ₗ[ZMod p] ↥T) ∘ₗ F := by
      intro a ha
      obtain ⟨a₀, ha₀, hrest⟩ := (hrestr a).mp ha
      ext u
      have hL : ((F (a u) : ↥T) : V) = f (a₀ (u : V)) := by
        simpa [F] using congrArg f (hrest u).symm
      have hR : ((a (F u) : ↥T) : V) = a₀ (f (u : V)) := by
        simpa [F] using (hrest (F u)).symm
      change ((F (a u) : ↥T) : V) = ((a (F u) : ↥T) : V)
      rw [hL, hR, hfcomm a₀ ha₀ (u : V) u.2]
    obtain ⟨c, hc⟩ := hirr.2 F hFcomm
    refine ⟨c, fun u hu => ?_⟩
    have h2 := congrArg (fun (g : Module.End (ZMod p) ↥T) => g ⟨u, hu⟩) hc
    have h3 : ((F ⟨u, hu⟩ : ↥T) : V) = c • u := by
      rw [h2]
      simp
    simpa [F] using h3
  exact ⟨hdisp, hfix, fun a ha hgT => ggLin_faithful_on_com A hnotr hirr' hend htriv a ha
    (fun u hu => hgT u (hcom ▸ hu)), hrestr⟩

end CFSG.StandardType

end
