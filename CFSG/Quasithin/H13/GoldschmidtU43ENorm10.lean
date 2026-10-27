module

public import CFSG.Quasithin.H13.GoldschmidtU43ENorm9
public import CFSG.Sporadic.Recognition.JankoWongPSLEight
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.Quasithin.H13.GoldschmidtU43ENorm7

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

theorem Nbar_classify :
    (∃ J : Subgroup S.Nbar, J.index = 2) ∨ Nat.card S.Nbar = 168 ∨
      Nonempty (S.Nbar ≃* alternatingGroup (Fin 6)) := by
  by_cases hI : ∀ J : Subgroup S.Nbar, J.index ≠ 2
  · right
    obtain ⟨F, _, _, ⟨e⟩, h | ⟨h360, -, hF9⟩⟩ :=
      CFSG.Sporadic.Recognition.JankoWong.PSLEightStep.exists_mulEquiv_psl_card_cases
        S.hasDihedralSylowTwo_Nbar S.not_hasNormalPComplement_Nbar S.oddCore_Nbar hI
        (u := S.zbar) (by rw [pow_two]; exact S.zbar_sq) S.zbar_ne_one S.card_centralizer_zbar
    · exact Or.inl h.1
    · obtain ⟨e'⟩ :=
        CFSG.Sporadic.Recognition.JankoWong.nonempty_mulEquiv_alternatingGroup_six_of_card_nine hF9
      exact Or.inr ⟨e.trans e'⟩
  · left
    push Not at hI
    exact hI

end JWSetup

end CFSG.Quasithin.H13.U43
