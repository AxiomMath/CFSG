module

public import CFSG.Milestones.ASVolI.F431.AInv
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4StdTwo
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431 CFSG.ASVolI.ChF
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag

section F4Lie


theorem burnsideF4m_std_iso_F4 {D : Type} [Group D] {f : ℕ} (hD : LieModel D .twistedF4 0 2 f)
    (A : LieAmalgamExt D) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K F4.prime),
      Nat.card K = 2 ^ (2 * a + 1) ∧ 1 ≤ a ∧
      ∃ ε : D ≃* TwoF4.Gm K a, A.TD.map ε.toMonoidHom = TwoF4.Ug K a ∧
        ((A.P1.map ε.toMonoidHom = TwoF4.Pg K a ⟨0, by decide⟩ ∧
            A.P2.map ε.toMonoidHom = TwoF4.Pg K a ⟨1, by decide⟩) ∨
          (A.P1.map ε.toMonoidHom = TwoF4.Pg K a ⟨1, by decide⟩ ∧
            A.P2.map ε.toMonoidHom = TwoF4.Pg K a ⟨0, by decide⟩)) := by
  obtain ⟨a, K, _, _, _, ha, hfa, hK0, ⟨e⟩⟩ := TwoF4.f4_model_data hD
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK0, hfa]
  have := TwoF4.finite_gm K a
  have hS : CFSG.Quasithin.H13.Sec53F.Yam.YamStd (TwoF4.Gm K a) (TwoF4.Ug K a)
      (TwoF4.Pg K a ⟨0, by decide⟩) (TwoF4.Pg K a ⟨1, by decide⟩) :=
    CFSG.Quasithin.H13.Sec53F.ReeF4.f4_yamStd ha hK
  obtain ⟨c, hTD, hP⟩ := hS.pair e A.yam
  have hε : ∀ S : Subgroup D, S.map (e.trans (MulAut.conj c⁻¹)).toMonoidHom =
      (S.map e.toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom := fun S => by
    rw [Subgroup.map_map]
    rfl
  refine ⟨a, K, inferInstance, inferInstance, inferInstance, hK, ha, e.trans (MulAut.conj c⁻¹),
    ?_, ?_⟩
  · rw [hε, hTD, burnsideF4m_map_conj_inv_map]
  · rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [hε, hε, h1, h2, burnsideF4m_map_conj_inv_map, burnsideF4m_map_conj_inv_map]
      exact ⟨rfl, rfl⟩
    · right
      rw [hε, hε, h1, h2, burnsideF4m_map_conj_inv_map, burnsideF4m_map_conj_inv_map]
      exact ⟨rfl, rfl⟩

theorem burnsideF4m_invCent_F4 {f : ℕ} {D : Type} [Group D] [Finite D] {G : Type} [Group G]
    {M1 M2 : Subgroup G} (hD : LieModel D .twistedF4 0 2 f) (X : LieExt D M1 M2)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ X.K) (hcen : Subgroup.center D = ⊥)
    (hodd : ¬ 2 ∣ (Lift.iK X.toLieAmalgamExt hgen).range.index) :
    burnsideF4m_InvCent X.toLieAmalgamExt := by
  obtain ⟨a, K, _, _, _, hK, ha, ε, hU, hP⟩ := burnsideF4m_std_iso_F4 hD X.toLieAmalgamExt
  have S1 := TwoF4.f4_stdTwo ha hK
  rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact burnsideF4m_invCent_of_twoClassD _ hgen hcen hodd
      (Lift.twoClassD_of_std X.toLieAmalgamExt ε S1 (Or.inr ⟨rfl, rfl⟩) h2 h1 hU)
  · exact burnsideF4m_invCent_of_twoClassD _ hgen hcen hodd
      (Lift.twoClassD_of_std X.toLieAmalgamExt ε S1 (Or.inl ⟨rfl, rfl⟩) h1 h2 hU)

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_centInput_F4 (hyp : HypF_4_4 .F4tw 2 f Gp M₁ M₂) (hf : 3 ≤ f)
    (hodd : Odd Gp.index) {x : E} (hx1 : x ≠ 1) (hx2 : x * x = 1) :
    ∃ w : E, IsConj x w ∧
      (Subgroup.centralizer ({w} : Set E) ≤ M₁ ∨ Subgroup.centralizer ({w} : Set E) ≤ M₂) := by
  haveI := hyp.finite
  obtain ⟨a, K, fK, finK, charK, hscope, hfa, marking, h1, h2⟩ :=
    burnsideF4g_chart_F4tw hyp.toHypF_4_4g
  letI := fK
  haveI := finK
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamF4 (by omega) hscope marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_F4tw hf hyp.model
  exact burnsideF4m_centInput_of hyp.toHypF_4_4g hTD hodd
    (fun hgen hcen hodd' => burnsideF4m_invCent_F4 hmodel _ hgen hcen hodd') hx1 hx2

end F4Lie

end CFSG.ASVolI
