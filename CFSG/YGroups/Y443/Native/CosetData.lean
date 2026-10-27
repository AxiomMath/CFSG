module

public import CFSG.YGroups.Y443.Native.Hom
public import CFSG.YGroups.Y443.CentralProjection

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster.Generated CFSG.Open

@[expose] noncomputable def xbar :
    Gmat := fM y443X

@[expose] noncomputable def ybar :
    Gmat := fM y443Y

@[expose] noncomputable def Hbar :
    Subgroup Gmat := y443H.map fM

@[expose] noncomputable def Kbar :
    Subgroup Gmat := y443K.map fM

noncomputable abbrev GammaMat :=
    y443GammaMat fM

abbrev TMat :=
    y443TMat fM

theorem central_projection_coset_data :
    xbar = fM y443X ∧ ybar = fM y443Y ∧ Hbar = y443H.map fM ∧ Kbar = y443K.map fM :=
  ⟨rfl, rfl, rfl, rfl⟩

end CFSG.YGroups.Y443
