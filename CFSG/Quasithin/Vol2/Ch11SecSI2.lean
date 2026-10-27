module

public import CFSG.Quasithin.Vol2.Ch11SecSI
public import CFSG.Quasithin.Vol2.Ch11SecSCartanL
public import CFSG.Quasithin.Vol2.Ch11SecSK0c

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem cartan_inf_L₁_eq_bot (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) (hc : CartanL L V₁ V₂ X) {R : Subgroup G}
    (hRs : Group.IsSolvable ↥R) (hRn : LOf L V₂ ≤ Subgroup.normalizer (R : Set G))
    (hR : ∀ x ∈ X ⊓ LOf L V₁, ∀ l ∈ LOf L V₂, x * l * x⁻¹ * l⁻¹ ∈ R) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := lOf_quot_SL2 hN h1102 h.hyp (Or.inr rfl) h.v₂
  have hXN := cartan_le_normalizer_lOf hN h1102 h.hyp (Or.inr rfl) h.v₂ h.cartan
  have hN₂ : R ⊓ LOf L V₂ ≤ pCoreOf 2 (LOf L V₂) :=
    le_pCoreOf_of_solvable le_rfl hF e inf_le_right
      (fun l hl => Subgroup.inf_normalizer_le_normalizer_inf ⟨hRn hl, Subgroup.le_normalizer hl⟩)
      (isSolvable_of_le inf_le_left hRs)
  have hle : X ⊓ LOf L V₁ ≤ sectionCentralizer (LOf L V₂) (pCoreOf 2 (LOf L V₂)) := by
    intro x hx
    have hxN := hXN hx.1
    refine ⟨hxN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hxN,
      fun l hl => hN₂ ⟨hR x hx l hl, ?_⟩⟩
    exact (LOf L V₂).mul_mem ((Subgroup.mem_normalizer_iff.mp hxN l).mp hl)
      ((LOf L V₂).inv_mem hl)
  have hbot := hc.c
  rw [inf_eq_left.mpr hle] at hbot
  have := hc.card₁
  rw [hbot, Subgroup.card_bot] at this
  exact absurd this (by norm_num)

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
