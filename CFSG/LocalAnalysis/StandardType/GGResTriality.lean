module

public import CFSG.LocalAnalysis.StandardType.GGResLeaves
public import CFSG.LocalAnalysis.StandardType.GGResTrialityNbr
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResTrialityInput_of (hD4 : GGTCJD4TagKnown) (hRig : GGLabelRigidInput)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) : GGResTrialityInput := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ _ hP
  exfalso
  obtain ⟨hcfg, -, hinn, -, hnb, -, -⟩ := hH
  rcases hP with h | h
  · obtain ⟨labJ, labX, hΛJ, hΛX, hJ, hX, hr⟩ := h
    rcases hr with ⟨htag, hp, heq⟩ | ⟨htag, hp, heq⟩
    · subst heq
      exact (ggNbr_D4Tag_L hD4 hRig hcfg hinn.1 hp hnb hΛX hX hΛJ hJ).2 htag
    · subst heq
      exact (ggNbr_D4Tag_L hD4 hRig hcfg hinn.1 hp hnb hΛX hX hΛJ hJ).1 htag
  · obtain ⟨labJ, labX, hΛJ, hΛX, hJ, hX, hr⟩ := h
    have hI3 : GGNbrSubcomponentInput := ggNbrSubcomponentInput_of_lBalance hLB hSP
    rcases hr with ⟨htag, hp, heq⟩ | ⟨htag, hp, heq⟩
    · subst heq
      exact (ggNbr_D4Tag_K hD4 hRig hI3 hcfg hinn hp hnb hΛX hX hΛJ hJ).2 htag
    · subst heq
      exact (ggNbr_D4Tag_K hD4 hRig hI3 hcfg hinn hp hnb hΛX hX hΛJ hJ).1 htag

end CFSG.StandardType

end
