module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamSporJ4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M22
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M23
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M24
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporHS
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporRu
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporHeHall
public import CFSG.Quasithin.H13.GoldschmidtCTKFamSporOrd

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.Blueprint.NativeSporadic

theorem kc3LocalFor_he :
    Kc3LocalFor (Kc3Spor .He) := by
  have hno := Kc3SporLine.noDelta5Norm_of_sylow (Fin 8330) Kc3SporHe.heR_isPGroup
    Kc3SporHe.heR_index Kc3SporHeChk.he_hall
  refine Kc3SporLine.kc3LocalFor_of_noDelta5Norm (Γ := CFSG.Sporadic.He.J) ?_ hno
  intro X _ ⟨e⟩
  exact ⟨e.trans CFSG.Sporadic.He.heEquivJ⟩

theorem not_a5Config_of_kc3LocalFor {s : TauCeti.SporadicName} (h : Kc3LocalFor (Kc3Spor s))
    {S : Type} [Group S] [Finite S] (e : S ≃* Carrier s) : ¬ A5Config S :=
  fun hc => hc.not_kc3LocalData (h S ⟨e⟩)

section Spor


theorem exclA5BlockFor_spor : ExclA5BlockFor fun S _ => SQTKSporFam S := by
  refine ExclA5BlockFor.of_not_config fun S _ _ hS => ?_
  obtain ⟨s, hs, ⟨e⟩⟩ := hS
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_a5Config_m11 e
  · exact not_a5Config_m12 e
  · exact not_a5Config_of_kc3LocalFor kc3LocalFor_m22 e
  · exact not_a5Config_of_kc3LocalFor kc3LocalFor_m23 e
  · exact not_a5Config_of_kc3LocalFor kc3LocalFor_m24 e
  · exact not_a5Config_j1 e
  · exact not_a5Config_j2 e
  · exact not_a5Config_j4 e
  · exact not_a5Config_of_kc3LocalFor kc3LocalFor_hs e
  · exact not_a5Config_of_kc3LocalFor kc3LocalFor_he e
  · exact not_a5Config_of_kc3LocalFor Kc3SporRu.kc3LocalFor_ru e

end Spor

end CFSG.Quasithin.H13.CTK
