module

public import CFSG.Milestones.ASVolI.F431.AInv
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModG2
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431 CFSG.ASVolI.ChF
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section G2Lie


theorem burnsideF4m_invCent_G2 {f : ℕ} (hf : 2 ≤ f) {D : Type} [Group D] [Finite D]
    (hD : LieModel D .G2 0 2 f) (A : LieAmalgamExt D)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) (hcen : Subgroup.center D = ⊥)
    (hodd : ¬ 2 ∣ (Lift.iK A hgen).range.index) : burnsideF4m_InvCent A := by
  obtain ⟨-, K, _, _, _, hKcard, ⟨ε₀⟩⟩ := G2.g2_model_data hD
  have hfinC : Finite ↥(adjointGroup Tag.G2 K) := by
    have : Finite (ModGL Tag.G2 K) := finite_modGL
    infer_instance
  have YS := CFSG.Quasithin.H13.Sec53F.G2.g2_yamStd hKcard hf
  obtain ⟨c, hT, hP⟩ := YS.pair ε₀ A.yam
  let ε : D ≃* ↥(adjointGroup Tag.G2 K) := ε₀.trans (MulAut.conj c⁻¹)
  have hε : ∀ S : Subgroup D, S.map ε.toMonoidHom = (S.map ε₀.toMonoidHom).map
      (MulAut.conj c⁻¹).toMonoidHom := fun S => by
    rw [Subgroup.map_map]
    rfl
  have hU : A.TD.map ε.toMonoidHom = posUnipotentSub Tag.G2 K := by
    rw [hε, hT, burnsideF4m_map_conj_inv_map]
  have hmapε : ∀ (S : Subgroup D) (S' : Subgroup ↥(adjointGroup Tag.G2 K)),
      S.map ε₀.toMonoidHom = S'.map (MulAut.conj c).toMonoidHom → S.map ε.toMonoidHom = S' :=
    fun S S' h => by rw [hε, h, burnsideF4m_map_conj_inv_map]
  have S1 := G2.g2_stdTwo hf hKcard
  have fin2 : ∀ i : Fin Tag.G2.rank, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by decide
  have hne01 : Setup.X6.g2Index 0 ≠ Setup.X6.g2Index 1 := fun h =>
    absurd (Setup.X6.g2Index_injective h) (by decide)
  have hidx : (Setup.X6.g2Index 0 = ⟨0, by decide⟩ ∧ Setup.X6.g2Index 1 = ⟨1, by decide⟩) ∨
      (Setup.X6.g2Index 0 = ⟨1, by decide⟩ ∧ Setup.X6.g2Index 1 = ⟨0, by decide⟩) := by
    rcases fin2 (Setup.X6.g2Index 0) with h0 | h0 <;> rcases fin2 (Setup.X6.g2Index 1) with h1 | h1
    · exact absurd (h0.trans h1.symm) hne01
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1⟩
    · exact absurd (h0.trans h1.symm) hne01
  have finish : ∀ (Q Q' : Subgroup D), ((Q = A.P1 ∧ Q' = A.P2) ∨ (Q = A.P2 ∧ Q' = A.P1)) →
      Q.map ε.toMonoidHom = G2.Pmin K ⟨1, by decide⟩ →
      Q'.map ε.toMonoidHom = G2.Pmin K ⟨0, by decide⟩ → burnsideF4m_InvCent A :=
    fun Q Q' hQ hQP hQP' => burnsideF4m_invCent_of_twoClassD A hgen hcen hodd
      (Lift.twoClassD_of_std A ε S1 hQ hQP hQP' hU)
  rcases hidx with ⟨e0, e1⟩ | ⟨e0, e1⟩ <;> rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact finish A.P2 A.P1 (Or.inr ⟨rfl, rfl⟩)
      (hmapε _ _ (by rw [← e1]; exact h2)) (hmapε _ _ (by rw [← e0]; exact h1))
  · exact finish A.P1 A.P2 (Or.inl ⟨rfl, rfl⟩)
      (hmapε _ _ (by rw [← e1]; exact h1)) (hmapε _ _ (by rw [← e0]; exact h2))
  · exact finish A.P1 A.P2 (Or.inl ⟨rfl, rfl⟩)
      (hmapε _ _ (by rw [← e0]; exact h1)) (hmapε _ _ (by rw [← e1]; exact h2))
  · exact finish A.P2 A.P1 (Or.inr ⟨rfl, rfl⟩)
      (hmapε _ _ (by rw [← e0]; exact h2)) (hmapε _ _ (by rw [← e1]; exact h1))

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_centInput_G2 (hyp : HypF_4_4 .G2 2 f Gp M₁ M₂) (hf : 2 ≤ f)
    (hodd : Odd Gp.index) {x : E} (hx1 : x ≠ 1) (hx2 : x * x = 1) :
    ∃ w : E, IsConj x w ∧
      (Subgroup.centralizer ({w} : Set E) ≤ M₁ ∨ Subgroup.centralizer ({w} : Set E) ≤ M₂) := by
  haveI := hyp.finite
  obtain ⟨K, fK, finK, hcard, marking, h1, h2⟩ := burnsideF4g_chart_G2 hyp.toHypF_4_4g
  letI := fK
  haveI := finK
  haveI : CharP K 2 := burnsideF4f_charP_of_card (by omega) hcard
  have hK3 : 3 ≤ Nat.card K := by
    rw [hcard]
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamG2 hK3 marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_G2 hf hyp.model
  exact burnsideF4m_centInput_of hyp.toHypF_4_4g hTD hodd
    (fun hgen hcen hodd' => burnsideF4m_invCent_G2 hf hmodel _ hgen hcen hodd') hx1 hx2

end G2Lie

end CFSG.ASVolI
