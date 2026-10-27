module

public import CFSG.Sporadic.Co2Schreier.Outer
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingOuterBound

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Sporadic.Co2Cert
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem AT_Co2_model_Schreier
    (K : Type*) [Group K] (e : K ≃* CFSG.Blueprint.NativeSporadic.Co2) :
    Finite (Outer K) ∧ IsPGroup 2 (Outer K) ∧ Group.IsSolvable (Outer K) := by
  obtain ⟨hfin, hp, hsolv⟩ := AT_Co2_permutation_Schreier
  obtain ⟨⟨E, -⟩, hiff⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism (e.trans co2PermEquiv)
  exact ⟨Finite.of_equiv _ E.symm.toEquiv, hp.of_equiv E.symm, hiff.2 hsolv⟩

theorem AT_Co2_Schreier :
    Group.IsSolvable (Outer CFSG.Blueprint.NativeSporadic.Co2) :=
  (@CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism CFSG.Blueprint.NativeSporadic.Co2 co2P
    Units.instGroup _ co2PermEquiv).2.2 AT_Co2_permutation_Schreier.2.2

end CFSG.Sporadic.Co2Schreier
