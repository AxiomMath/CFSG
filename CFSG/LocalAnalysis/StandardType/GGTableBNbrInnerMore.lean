module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreU
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreExcB
public import CFSG.LocalAnalysis.StandardType.GGAssemblyElevenDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrNsVacLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrNsSpLabel p lab ∨ GGNbrNsOrthLabel p lab ∨ GGNbrNsLinLabel p lab ∨
    GGNbrNsUnitLabel p lab ∨ GGNbrNsE7Label p lab ∨ GGNbrNsE6Label p lab ∨
    GGNbrNsTwE6Label p lab ∨ GGNbrNsF4Label p lab ∨ GGNbrNsE8Label p lab ∨
    GGNbrNsTriD4Label p lab ∨ GGNbrNsTwF4Label p lab

@[expose] def GGTableBNbrInnerRound12Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBNbrInnerRound11NsLabel p lab ∧ ¬ GGNbrNsVacLabel p lab

theorem ggTableBNbrInnerInputOn_round12_of_round11Ns
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound11NsLabel) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound12Label :=
  h.mono fun _ _ h12 => h12.1

section Round12

theorem ggTableBNbrInnerInputOn_nsVac : GGTableBNbrInnerInputOn GGNbrNsVacLabel :=
  ggTableBNbrInnerInputOn_nsSp.or (ggTableBNbrInnerInputOn_nsOrth.or
    (ggTableBNbrInnerInputOn_nsLin.or (ggTableBNbrInnerInputOn_nsUnit.or
      (ggTableBNbrInnerInputOn_nsE7.or (ggTableBNbrInnerInputOn_nsE6.or
        (ggTableBNbrInnerInputOn_nsTwE6.or (ggTableBNbrInnerInputOn_nsF4.or
          (ggTableBNbrInnerInputOn_nsE8.or (ggTableBNbrInnerInputOn_nsTriD4.or
            ggTableBNbrInnerInputOn_nsTwF4)))))))))

theorem ggTableBNbrInnerInputOn_round11Ns_of_round12
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound12Label) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound11NsLabel :=
  (ggTableBNbrInnerInputOn_nsVac.or h).mono fun p lab h11 => by
    by_cases hv : GGNbrNsVacLabel p lab
    · exact Or.inl hv
    · exact Or.inr ⟨h11, hv⟩

end Round12

section Chain

theorem ggTableBNbrInnerInput_of_round12
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound12Label) : GGTableBNbrInnerInput :=
  ggTableBNbrInnerInput_of_round11
    (ggTableBNbrInnerInputOn_round11_of_round11Ns (ggTableBNbrInnerInputOn_round11Ns_of_round12 h))

end Chain

end CFSG.StandardType

end
