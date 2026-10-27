module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Walter.J1Props.Hyp
import CFSG.Walter.Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {X : Type} [Group X] [Finite X]

theorem uc22s2122np_card_normalizer_sylow_of_isJ1 (hX : IsJ1 X) (S : Sylow 2 X) :
    Nat.card (Subgroup.normalizer ((S : Subgroup X) : Set X)) = 168 ∧ Nat.card S = 8 := by
  obtain ⟨eJ⟩ := hX
  let e : X ≃* CFSG.Open.walterJ1 := eJ.trans CFSG.Walter.walterJ1EquivNative.symm
  let S' : Sylow 2 CFSG.Open.walterJ1 := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S
  have hmap : (S' : Subgroup CFSG.Open.walterJ1) = Subgroup.map e.toMonoidHom (S : Subgroup X) :=
    Sylow.coe_mapSurjective e.surjective S
  have hcardN : Nat.card (Subgroup.normalizer ((S : Subgroup X) : Set X)) = 168 := by
    have h := CFSG.Walter.J1.JankoHyp.card_normalizer_sylow'' CFSG.Walter.J1Props.jankoHyp S'
    rw [hmap] at h
    rw [← Subgroup.map_equiv_normalizer_eq (H := (S : Subgroup X)) e] at h
    rw [Subgroup.card_map_of_injective e.injective] at h
    exact h
  have hcardS : Nat.card S = 8 := by
    have h := CFSG.Walter.J1.JankoHyp.card_sylow' CFSG.Walter.J1Props.jankoHyp S'
    rw [hmap] at h
    rw [Subgroup.card_map_of_injective e.injective] at h
    exact h
  exact ⟨hcardN, hcardS⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
