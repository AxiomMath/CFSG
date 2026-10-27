module

public import CFSG.Quasithin.Background.Harris.Interfaces
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverFinal
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.SmallIsoAlt8

public section

namespace CFSG.Quasithin.Background.Harris.OrdinaryProofs

open CFSG.Quasithin.G11.Harris
open Matrix
open CFSG.Assembly.LowTwoRank

theorem statedClassicalModel_PSL_of_mulEquiv {X Y : Type} [Group X] [Group Y] {n p f : ℕ}
    (e : X ≃* Y) (h : StatedClassicalModel Y .PSL n p f) :
    StatedClassicalModel X .PSL n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm h

theorem famL2_of_famAlt5 (X : Type) [Group X] (h : FamAlt 5 X) :
    FamL2 X := by
  obtain ⟨hs, ⟨e⟩⟩ := h
  have hK2 : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  have hK4 : Nat.card (GaloisField 2 2) = 4 := hK2.trans (by norm_num)
  obtain ⟨e'⟩ :=
    CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five (GaloisField 2 2)
      (Or.inl hK4)
  refine ⟨hs, 2, le_rfl, ?_⟩
  refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  exact ⟨GaloisField 2 2, inferInstance, inferInstance, hK2, ⟨e.trans e'.symm⟩⟩

theorem famLn2_four_of_famAlt8 (X : Type) [Group X] (h : FamAlt 8 X) : FamLn2 4 X := by
  obtain ⟨hs, ⟨e⟩⟩ := h
  exact ⟨hs, statedClassicalModel_PSL_of_mulEquiv e statedClassicalModel_alt8_PSL42⟩

theorem famL2_or_famL3_or_famAlt6_of_famOddL2Small (X : Type)
    [Group X] (h : FamOddL2Small X) : FamL2 X ∨ FamL3 X ∨ FamAlt 6 X := by
  obtain ⟨hs, p, hp, hp2, f, hf, hpf, hm⟩ := h
  rcases hpf with h5 | h7 | h9
  ·
    obtain ⟨-, K, hKf, hKfin, hK, ⟨eX⟩⟩ := hm
    obtain ⟨e5⟩ :=
      CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
        (Or.inr (hK.trans h5))
    exact Or.inl (famL2_of_famAlt5 X ⟨hs, ⟨eX.trans e5⟩⟩)
  ·
    have hf1 : f = 1 := by
      rcases hf with rfl | rfl
      · rfl
      · exfalso
        have hp7 : p ≤ 3 := by nlinarith
        interval_cases p <;> norm_num at h7
    subst hf1
    have hp7 : p = 7 := by simpa using h7
    subst hp7
    obtain ⟨-, K, hKf, hKfin, hK, ⟨eX⟩⟩ := hm
    have : Fintype K := Fintype.ofFinite K
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hK7 : Fintype.card K = Fintype.card (ZMod 7) := by
      rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, pow_one]
    let eK : K ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq hK7
    obtain ⟨e₇⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
    let e₃ : ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
      ((QuotientGroup.quotientMulEquivOfEq
        CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
          QuotientGroup.quotientBot).trans
        (MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
          CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two)
    have hL3 : StatedClassicalModel X .PSL 3 2 1 := by
      refine ⟨⟨Nat.prime_two, le_refl 1, by norm_num, by norm_num, by norm_num⟩, ?_⟩
      refine ⟨ZMod 2, inferInstance, inferInstance,
        Nat.card_eq_fintype_card.trans ((ZMod.card 2).trans (pow_one 2).symm), ⟨?_⟩⟩
      exact eX.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
        ((CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eK (Fin 2)).trans
          (e₇.symm.trans (e₃.symm.trans (projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 2))))))
    exact Or.inr (Or.inl ⟨hs, 1, le_rfl, hL3⟩)
  ·
    have hf2 : f = 2 := by
      rcases hf with rfl | rfl
      · exfalso
        have hp9 : p = 9 := by simpa using h9
        subst hp9
        norm_num at hp
      · rfl
    subst hf2
    have hp3 : p = 3 := by
      have hp3' : p ≤ 3 := by nlinarith
      interval_cases p <;> first | rfl | norm_num at h9
    subst hp3
    obtain ⟨e6⟩ := CFSG.QuasithinUnique.Vol2Native.alternating_six_of_psl_two_nine hm
    exact Or.inr (Or.inr ⟨hs, ⟨e6⟩⟩)

end CFSG.Quasithin.Background.Harris.OrdinaryProofs

end
