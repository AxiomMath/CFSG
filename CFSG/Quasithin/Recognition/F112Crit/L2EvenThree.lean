module

public import CFSG.Quasithin.Recognition.F112Crit.ListedNoMcL
public import CFSG.Quasithin.Recognition.F112Crit.L2Eight

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.GH74.Uniqueness.Bender

theorem l2Even_three : L2Even 3 := by
  intro G _ _ L₁ L₂ S Z hs hsmall hL2 hb hb4
  obtain ⟨e⟩ := hL2
  have hK : IsBenderQuot (oTwoQuot ↥L₂) (2 ^ 3) 1 :=
    BenderType.isBenderQuot (BenderType.linear 3 (by norm_num) e)
  have hT : IsTorusQuot (oTwoQuot ↥L₂) := isTorusQuot_of_mulEquiv e
  have hcr := hs.toCritAmalgam
  have hcard : Nat.card (oTwoQuot ↥L₁) = 6 ∨ Nat.card (oTwoQuot ↥L₁) = 10 ∨
      Nat.card (oTwoQuot ↥L₁) = 20 := by
    rcases hsmall with h | h
    · exact Or.inl (card_oTwoQuot_of_vS3 h)
    · exact Or.inr (card_oTwoQuot_of_vFD h)
  have hX := hs.isLocalRegGrp (oddGen_inf_borelOf_le hs.hyp hcard)
  have hp : (borelOf L₁ S).relIndex L₁ = 3 ∨ (borelOf L₁ S).relIndex L₁ = 5 := by
    rcases hsmall with h | h
    · exact Or.inl (relIndex_borelOf_eq_three hs.hyp (card_oTwoQuot_of_vS3 h))
    · exact Or.inr (relIndex_borelOf_eq_five hs.hyp (card_oTwoQuot_of_vFD h))
  exact card_nbrs_γ₀_ne_nine hcr (hX.isLocalReg hcr) hp (hs.benderLocal hK)
    (hs.torusLocal hK hT) hb hb4 (by rw [hs.card_nbrs_γ₀ hK]; norm_num)

theorem f112SliceFDBigPlus : CFSG.Quasithin.H13.F112SliceFDBigPlus :=
  f112SliceFDBigPlus_of_l2EvenThree l2Even_three

end CFSG.Quasithin.F112Crit

end
