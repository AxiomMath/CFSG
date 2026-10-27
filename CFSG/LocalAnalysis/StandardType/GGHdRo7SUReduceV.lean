module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULinDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUReduceVIrrB
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUReduceVCard

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem su_reduceV_of_leaves : SUPInvLeaf → SUPCentLeaf → SUStabCardLeaf → (SUNormalizerLeaf → ∀ (p
    : ℕ) [Fact p.Prime] (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V] (b : Module.Basis
    (Fin m) (ZMod p) V) (H A : Subgroup (V ≃ₗ[ZMod p] V)), SULinData p m V b H A → (∃ r ∈ H,
    GGLinRefl r ∧ ¬ ggLinMove r ≤ SUAug p b) → SUClassReady p m H) := by
  intro hP1 hP2 hP3 hN p hpFact m V instV instM b H A hD hV
  have hp3 : p = 3 := hD.hp
  subst hp3
  refine ⟨m, V, instV, instM, H, Or.inr rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Module.finrank_eq_card_basis b]; simp
  · exact hdRo7SUReduceVAux_absIrred b H A hP1 hP2 hN hD hV
  ·
    obtain ⟨S, hS, hHcl, hSconn⟩ := hD.hgen
    have hST : S ⊆ {r : V ≃ₗ[ZMod 3] V | r ∈ Subgroup.closure S ∧ GGLinRefl (p := 3) r} :=
      fun s hs => ⟨by rw [← hHcl]; exact (hS s hs).1, (hS s hs).2⟩
    have hTH : {r : V ≃ₗ[ZMod 3] V | r ∈ Subgroup.closure S ∧ GGLinRefl (p := 3) r} ⊆
        Subgroup.closure S := fun r hr => hr.1
    rw [hHcl]
    exact le_antisymm (Subgroup.closure_mono hST) ((Subgroup.closure_le _).mpr hTH)
  · exact hdRo7SUReduceVAux_card_le b H A hP3 hN hD
  · exact id

end CFSG.StandardType.HdRo7SU
