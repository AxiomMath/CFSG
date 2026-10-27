module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RecogDefs

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.QuasithinUnique

theorem e7RootRecog_surjective
    (hRec : E7RootRecog) {X : Type} [Group X] [Finite X]
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) →* X) (hψ : Function.Injective ψ)
    (r : ↥(adjointGroup .E7 (ZMod 2)))
    (hr : (r : ModGL .E7 (ZMod 2)) ∈ CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2))
    (hr3 : orderOf r = 3)
    (hmem : ∀ g : X, g * ψ r * g⁻¹ ∈ ψ.range → g ∈ ψ.range)
    (hchar : ∀ s : ↥(adjointGroup .E7 (ZMod 2)),
      (s : ModGL .E7 (ZMod 2)) ∈ CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) →
      orderOf s = 2 → CharTwo (Subgroup.centralizer ({ψ s} : Set X))) :
    Function.Surjective ψ := by
  unfold E7RootRecog at hRec
  let ψ' : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥(ψ.range) := MonoidHom.ofInjective hψ
  have hψ' : ∀ a : ↥(adjointGroup .E7 (ZMod 2)), ((ψ' a : ↥(ψ.range)) : X) = ψ a :=
    fun a => MonoidHom.ofInjective_apply hψ
  have hC : Subgroup.centralizer ({ψ r} : Set X) ≤ ψ.range := by
    intro g hg
    apply hmem g
    have hg' : ψ r * g = g * ψ r :=
      (Subgroup.mem_centralizer_iff.mp hg) (ψ r) (Set.mem_singleton (ψ r))
    have hconj : g * ψ r * g⁻¹ = ψ r := by
      have h := congrArg (fun t : X => t * g⁻¹) hg'
      simpa using h.symm
    rw [hconj]
    exact MonoidHom.mem_range.mpr ⟨r, rfl⟩
  have htop : ψ.range = ⊤ :=
    hRec X ψ.range ⊥ ψ' r (ψ r) hr hr3
      ⟨1, by simp, by rw [hψ' r]; simp⟩
      bot_le
      (by rw [Subgroup.card_bot]; norm_num)
      (by rw [bot_sup_eq]; exact le_antisymm (le_inf le_rfl hC) inf_le_left)
      (fun g hg => ⟨g, hmem g hg, rfl⟩)
      (fun t ht ht2 => by
        rw [Subgroup.mem_bot.mp ht] at ht2
        exact absurd ht2 (by simp))
      (fun s hs hs2 => by simpa only [hψ' s] using hchar s hs hs2)
  exact MonoidHom.range_eq_top.mp htop

end CFSG.StandardType.FrameRoute.FS81

end
