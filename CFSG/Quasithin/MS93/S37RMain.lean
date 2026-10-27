module

public import CFSG.Quasithin.MS93.S37RBig
public import CFSG.Quasithin.MS93.S37LMain
public import CFSG.Quasithin.MS93.S37RCov

public section

namespace CFSG.Quasithin.MS93.S37R

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Quasithin.MS93.S37 CFSG.Quasithin.MS93.S37L
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem caseIIQ_holds : S37L.CaseIIQ := by
  intro G _ _ M T L F _ _ C _ _ hT hq ψ hcrit hT1 hII
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  set θ := restr ψ T1_le_T hT1 with hθ
  have hUθ : Ut M T L θ = Ut M T L ψ := tImage_restr ψ T1_le_T hT1 C.Uq_le_T1
  have hQθ : Qt M θ = Qt M ψ := tImage_restr ψ T1_le_T hT1 C.pCore_le_T1
  have hcritθ : ¬ Uq M T L ≤ Qt M θ := by
    rw [hQθ]
    exact hcrit
  have hIIθ : IsLine (fixSp (C.rhoIm (Ut M T L θ))) := by
    rw [hUθ]
    exact hII
  obtain ⟨Ψ, hU, hs, hk, he, hβ⟩ := exists_cover C
  let D : Dat C := ⟨θ, hT, hq, hcritθ, hIIθ, Ψ, hU, hs, hk, he, hβ⟩
  rw [← hQθ, ← hUθ]
  by_cases hA : Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) < Nat.card F
  · exact D.rhoIm_eq_small hA
  · exact D.rhoIm_eq_big hA

end CFSG.Quasithin.MS93.S37R
