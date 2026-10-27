module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1BC
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CentLin
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CentUni
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CenterE6
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1DSmall
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1E7
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1F4
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1SmallRows
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorLinR
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorLinTor
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorPGU6
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUni

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.StandardType.S2MathAs51642Interfaces

theorem q1On_of_forall_not {S : ℕ → LargeEvenLabel → Prop} (h : ∀ p lab, ¬ S p lab) :
    GGBstarInnerDiagJInputOn S := by
  intro G _ _ p B Bs x L D J _ hmark
  obtain ⟨-, lab, R, _, I, F, θ, -, hS⟩ := largeEvenMarking_exists' hmark
  exact absurd hS.1 (h p lab)

theorem q1RemainderSelector_empty (p : ℕ) (lab : LargeEvenLabel) :
    ¬ (((((((((((¬ E6Three p lab ∧ ¬ TwE6Three p lab ∧ lab.tag ≠ .E8) ∧
          ¬ (CenterPrimeTo p lab ∧ (lab.tag = .E6 ∨ lab.tag = .twE6))) ∧
          ¬ (CenterPrimeTo p lab ∧ (lab.tag = .D ∨ lab.tag = .twD))) ∧ lab.tag ≠ .E7) ∧
          lab.tag ≠ .F4) ∧
          ¬ (CenterPrimeTo p lab ∧ lab.tag = .A)) ∧
          ¬ LinearTorsion p lab) ∧
          ¬ (SmallDerived p lab ∨ lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨
            lab.tag = .twF4)) ∧
          ¬ (UnitaryTorsion p lab ∨ PGU6 p lab)) ∧
          ¬ (CenterPrimeTo p lab ∧ lab.tag = .twA)) ∧
          ¬ (lab.tag = .B ∨ lab.tag = .C)) := by
  rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hE6T, hTwE6T, hE8⟩, hCE6⟩, hCD⟩, hE7⟩, hF4⟩, hCA⟩, hLT⟩, hSm⟩, hUT⟩, hCTwA⟩,
    hBC⟩
  rcases selector_cover p lab with h | h | h | h | h | h | h
  · obtain ⟨tag, rank, n⟩ := lab
    cases tag
    · exact hCA ⟨h, rfl⟩
    · exact hCTwA ⟨h, rfl⟩
    · exact hBC (Or.inl rfl)
    · exact hBC (Or.inr rfl)
    · exact hCD ⟨h, Or.inl rfl⟩
    · exact hCD ⟨h, Or.inr rfl⟩
    · exact hCE6 ⟨h, Or.inl rfl⟩
    · exact hE7 rfl
    · exact hE8 rfl
    · exact hF4 rfl
    · exact hCE6 ⟨h, Or.inr rfl⟩
    · exact hSm (Or.inr (Or.inr (Or.inl rfl)))
    · exact hSm (Or.inr (Or.inl rfl))
    · exact hSm (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact hSm (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    · exact h.1 (Or.inl rfl)
    · exact h.1 (Or.inr (Or.inl rfl))
    · exact h.1 (Or.inr (Or.inr rfl))
  · exact hLT h
  · exact hUT (Or.inl h)
  · exact hUT (Or.inr h)
  · exact hE6T h
  · exact hTwE6T h
  · exact hSm (Or.inl h)

section Holds


theorem ggBstarInnerDiagJInput_holds : GGBstarInnerDiagJInput :=
  ggBstarInnerDiagJInput_of_not_e6Three_twE6Three_centerE6
    (ggBstarInnerDiagJInputOn_of_not_DTwD
      (q1On_of_and_not q1E7InnerDiag_holds
        (ggBstarInnerDiagJInputOn_of_not_F4
          (q1On_of_and_not q1CenterPrimeLinear_holds
            (q1On_of_and_not (q1On_of_selectedTransfer
                (q1SelectedTransfer_of_toral (q1ToralActionTransfer_of_rToral q1RToral_lin)
                    q1TorLin_config))
              (ggBstarInnerDiagJInputOn_of_not_smallExc
                (q1On_of_and_not (q1On_or q1UnitaryTorsion_holds q1PGU6_holds)
                  (q1On_of_and_not q1CenterPrimeToTwA_holds
                    (q1On_of_not_bc (q1On_of_forall_not q1RemainderSelector_empty))))))))))

end Holds

end CFSG.StandardType
