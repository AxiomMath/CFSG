module

public import CFSG.Quasithin.MS93.M16Close
public import CFSG.Quasithin.MS93.M16Rec
public import CFSG.Quasithin.MS93.M16W

public section

namespace CFSG.Quasithin.MS93.M16

open CFSG.Quasithin Matrix

variable {F : Type} [Field F] {V : Type*} [CommGroup V]

section Core

variable [CharP F 2] [Finite F] [Finite V] {ρ : SL3 F →* MulAut V} {W₀ : Subgroup V}

theorem core_caseN (hV : ∀ v : V, v ^ 2 = 1) (hVne : (⊤ : Subgroup V) ≠ ⊥)
    (hfixV : fixV ρ.range = ⊥)
    (hW₀ : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ w ∈ W₀, ρ g w ∈ W₀)
    (hgen : G6.submoduleClosure ρ.range W₀ = ⊤)
    (hR : Nat.card ↥(G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) (wOff ρ W₀)) ≤
      Nat.card F)
    (hN : G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) (wOff ρ W₀) ≠
      (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) (wOff ρ W₀)).map
        (ρ p01).toMonoidHom) :
    wOff ρ W₀ = ⊤ ∧ commV ρ.range = ⊤ ∧
      ∃ β : ↥(commV ρ.range) ≃* Multiplicative (Fin 3 → F),
        ∀ (g : SL3 F) (v w : ↥(commV ρ.range)), (w : V) = ρ g v →
          Multiplicative.toAdd (β w) =
            ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β v) := by
  have h𝒲 := wOff_inv hW₀
  have hW2 := fun r (hr : r ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ)
    (wOff ρ W₀)) => cyc_mem_wOff hW₀ hR hr
  obtain ⟨β', hβ'⟩ := natEquiv_of_caseN h𝒲 hR hN hW2 hV hfixV
  have hC := commV_eq_closure_R hW₀ hgen
  set β := (MulEquiv.subgroupCongr hC).trans β' with hβdef
  have hβ : ∀ (g : SL3 F) (v w : ↥(commV ρ.range)), (w : V) = ρ g v →
      Multiplicative.toAdd (β w) =
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β v) :=
    fun g v w hvw => hβ' g _ _ hvw
  have hCW := commV_le_wOff β hβ hfixV hW₀ hgen hVne
  have hW : wOff ρ W₀ = ⊤ := eq_top_iff.mpr
    ((top_le_pt_sup_commV hW₀ hgen (x := ![0, 0, 1]) (by simp)).trans
      (sup_le (pt_le_wOff (by simp)) hCW))
  exact ⟨hW, commV_eq_top β hβ hfixV hW hR, β, hβ⟩

end Core

end CFSG.Quasithin.MS93.M16
