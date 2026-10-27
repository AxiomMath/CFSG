module

public import CFSG.LocalAnalysis.WeakClosure81.EightThreeInOne
public import CFSG.LocalAnalysis.WeakClosure81.EightThreeInFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem Hyp83.hyp83K_kGenIn {V H T : Subgroup G} (h : Hyp83 V H T) :
    Hyp83K V H (kGenIn V H) where
  le_K := le_kGenIn_self V H
  K_le_H := kGenIn_le_H h.le_H
  K_le_conjClosure := kGenIn_le_conjClosure V H
  conjSubgroup_le_normalizer := fun _ hx =>
    (conjSubgroup_le_conjClosure V H hx).trans (conjClosure_le_normalizer_kGenIn V H)
  inf_normalizer_le := inf_normalizer_le_normalizer_kGenIn V H
  conjSubgroup_le_centralizer := fun _ hx hxK => h.conjSubgroup_kGenIn_le_centralizer hx hxK
  inf_centralizer_eq_bot := h.inf_centralizer_kGenIn_eq_bot

theorem w3Lem83In_holds : W3Lem83In G := by
  intro V H T hV7 hH hH0 hT
  have h : Hyp83 V H T := Hyp83.of_hyp7 hV7 hH hH0 hT
  exact ⟨fun _ hk => h.kGenIn_transitive hk,
    h.hyp83K_kGenIn.coe_eq_mul_mul h h.coe_inf_normalizer_kGenIn⟩

end CFSG.LocalAnalysis.WeakClosure81

end
