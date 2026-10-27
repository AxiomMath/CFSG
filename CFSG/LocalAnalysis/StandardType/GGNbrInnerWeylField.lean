module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVac

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrWeylFieldRestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrWeylFieldLabel p lab ∧ ¬ GGNbrWeylFieldVacA2Label p lab

theorem ggNbrWeylFieldLabel_cases {p : ℕ} {lab : LargeEvenLabel} (h : GGNbrWeylFieldLabel p lab) :
    GGNbrWeylFieldVacA2Label p lab ∨ GGNbrWeylFieldRestLabel p lab := by
  by_cases hv : GGNbrWeylFieldVacA2Label p lab
  · exact Or.inl hv
  · exact Or.inr ⟨h, hv⟩

end CFSG.StandardType

end
