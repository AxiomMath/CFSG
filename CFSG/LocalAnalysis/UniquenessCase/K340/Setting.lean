module

public import CFSG.LocalAnalysis.UniquenessCase.K340.QuotientL2
public import CFSG.LocalAnalysis.UniquenessCase.UC22SeedG
import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.Campbell340

variable {G : Type} [Group G] [Finite G]

private theorem charTwo_top_of_fstar {H : Subgroup G}
    (hF : Fstar H = CFSG.Open.pCoreOf 2 H) :
    CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup ↥H) := by
  unfold CFSG.QuasithinUnique.CharTwo
  intro y hy
  rw [CFSG.LocalAnalysis.UniquenessCase.UC22.pCoreOf_top_eq_pCore_two] at hy ⊢
  have hyc : y ∈ Subgroup.centralizer (CFSG.pCore 2 ↥H : Set ↥H) := hy.2
  have hF' : CFSG.Open.genFittingFStar ↥H = CFSG.pCore 2 ↥H :=
    Subgroup.map_injective H.subtype_injective hF
  rw [← hF'] at hyc
  rw [← hF']
  exact CFSG.Adapters.generalized_fitting_self_centralizing ↥H hyc

theorem exists_seedSetting {H L T : Subgroup G} {n : ℕ} (hF : Fstar H = CFSG.Open.pCoreOf 2 H)
    (hL : L = CFSG.Quasithin.opResidual 2 H) (hL2 : IsL2 (Bar2 L) n)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T H) (hH : H = T ⊔ L)
    (hTLQ : T ≤ L ⊔ CFSG.Open.pCoreOf 2 H) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
      (π : ↥H →* Matrix.SpecialLinearGroup (Fin 2) k) (P : Sylow 2 ↥H),
      (P : Subgroup ↥H).map H.subtype = T ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.SeedSetting
        (P : Subgroup ↥H) π := by
  have hLH : L ≤ H := by rw [hL]; exact CFSG.Quasithin.opResidual_le 2 H
  have hpQH : CFSG.Open.pCoreOf 2 H ≤ H := Subgroup.map_subtype_le (CFSG.pCore 2 ↥H)
  have hHL : H = L ⊔ CFSG.Open.pCoreOf 2 H := by
    refine le_antisymm ?_ (sup_le hLH hpQH)
    calc H = T ⊔ L := hH
      _ ≤ L ⊔ CFSG.Open.pCoreOf 2 H := sup_le hTLQ le_sup_left
  obtain ⟨k, hk, hkfin, hkchar, π, hsurj, hker, _, _⟩ := exists_sl2_quotient hL hL2 hHL
  obtain ⟨P, hP⟩ := hT
  refine ⟨k, hk, hkfin, hkchar, π, P, hP, ?_⟩
  refine ⟨hsurj, ?_, ?_, ?_⟩
  · refine ⟨le_top, P.isPGroup', ?_⟩
    show ¬ 2 ∣ (P : Subgroup ↥H).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact P.not_dvd_index
  · exact charTwo_top_of_fstar hF
  · intro Y hY hsup hO
    exact hY (by rw [← hsup, hker, sup_eq_left.mpr hO])

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.Campbell340

end
