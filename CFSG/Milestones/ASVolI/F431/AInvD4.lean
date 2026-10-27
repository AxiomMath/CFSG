module

public import CFSG.Milestones.ASVolI.F431.AInv
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStdIso
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431 CFSG.ASVolI.ChF
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section D4Lie


theorem burnsideF4m_invCent_D4 {f : ℕ} {D : Type} [Group D] [Finite D] {G : Type} [Group G]
    {M1 M2 : Subgroup G} (hD : LieModel D .trialityD4 0 2 f) (X : LieExt D M1 M2)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ X.K) (hcen : Subgroup.center D = ⊥)
    (hodd : ¬ 2 ∣ (Lift.iK X.toLieAmalgamExt hgen).range.index) :
    burnsideF4m_InvCent X.toLieAmalgamExt := by
  obtain ⟨-, hX⟩ := CFSG.LieType.Steinberg.CentralExt.GriessNative.chevalley_of_lieModel hD
    (by decide)
  obtain ⟨K, hF, hFin, σ, hf, hK, hσ, ε, hU, hP⟩ := D4q.Struct.exists_std_iso hX X
  haveI : CharP K 2 := D4q.Struct.charP_two_of_card hK
  have hσ3 := D4q.Struct.sigma_cube σ hK hσ
  have S1 := D4q.Loc.stdTwo_d4 σ hσ3 hf hK hσ
  rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact burnsideF4m_invCent_of_twoClassD _ hgen hcen hodd
      (Lift.twoClassD_of_std X.toLieAmalgamExt ε S1 (Or.inl ⟨rfl, rfl⟩) h1 h2 hU)
  · exact burnsideF4m_invCent_of_twoClassD _ hgen hcen hodd
      (Lift.twoClassD_of_std X.toLieAmalgamExt ε S1 (Or.inr ⟨rfl, rfl⟩) h2 h1 hU)


variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_centInput_D4 (hyp : HypF_4_4 .D4tw 2 f Gp M₁ M₂) (hodd : Odd Gp.index)
    {x : E} (hx1 : x ≠ 1) (hx2 : x * x = 1) :
    ∃ w : E, IsConj x w ∧
      (Subgroup.centralizer ({w} : Set E) ≤ M₁ ∨ Subgroup.centralizer ({w} : Set E) ≤ M₂) := by
  haveI := hyp.finite
  obtain ⟨K, fK, finK, sigma, hscope, marking, h1, h2⟩ := burnsideF4g_chart_D4tw hyp.toHypF_4_4g
  letI := fK
  haveI := finK
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamD4 sigma hscope marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_D4tw hyp.model
  exact burnsideF4m_centInput_of hyp.toHypF_4_4g hTD hodd
    (fun hgen hcen hodd' => burnsideF4m_invCent_D4 hmodel _ hgen hcen hodd') hx1 hx2

end D4Lie

end CFSG.ASVolI
