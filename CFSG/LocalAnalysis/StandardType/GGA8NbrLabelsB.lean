module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.MarkingClassical

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

theorem statedClassicalModel_of_hasLabel_C33 {X : Type} [Group X]
    (hX : GGHasLabel ⟨.C, 3, 3⟩ X) : StatedClassicalModel X .PSp 3 2 3 := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := hX
  refine ⟨⟨Nat.prime_two, by norm_num, by omega, ?_⟩, K, hF, hfin, hK, ⟨e⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  omega

theorem statedClassicalModel_of_hasLabel_twD43 {X : Type} [Group X]
    (hX : GGHasLabel ⟨.twD, 4, 3⟩ X) : StatedClassicalModel X .POmegaMinus 4 2 3 := by
  obtain ⟨K, hF, hfin, hK, b, c, hbc, ⟨e⟩⟩ := hX
  refine ⟨by simp only [StatedLieAdmissible]; norm_num, K, hF, hfin, hK, b, c, hbc,
    ⟨e.trans (omegaMinusProjEquiv 4 b c)⟩⟩

end CFSG.StandardType

end
