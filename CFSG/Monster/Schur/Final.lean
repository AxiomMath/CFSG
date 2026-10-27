module

public import CFSG.Monster.Schur.GmatStructureLemmaA
public import CFSG.Monster.Schur.EvisCentralizer
public import CFSG.Monster.AxisCount.HSCount
public import CFSG.Monster.AxisCount.BabySetup
public import CFSG.Monster.Schur.GmatStructureSetting

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Schur

open CFSG.Monster CFSG.Monster.Generated

theorem natCard_Gmat_eq :
    Nat.card Gmat = 97239461142009186000 * (11707448673375 * (2 ^ 24 * 42305421312000)) := by
  rw [CFSG.Monster.AxisCount.HS.natCard_Gmat, CFSG.Monster.AxisCount.Baby.natCard_Cgen,
    CFSG.Monster.AxisCount.natCard_Jstar]

theorem noPerfectDoubleCover_iff_not_exists (G : Type*) [Group G] :
    NoPerfectDoubleCover G ↔ ¬ ∃ (E : Type) (_ : Group E) (π : E →* G),
      Function.Surjective π ∧ Group.IsPerfect E ∧ Nat.card π.ker = 2 := by
  constructor
  · rintro h ⟨E, _, π, hπ, hE, hk⟩
    exact h E π hπ hE hk
  · intro h E _ π hπ hE hk
    exact h ⟨E, inferInstance, π, hπ, hE, hk⟩

theorem noPerfectDoubleCover_Gmat
    (hM24 : M24NoPerfectDoubleCover) :
    NoPerfectDoubleCover ↥Gmat :=
  noPerfectDoubleCover_of_setting
    (schurSetting_Gmat hM24 Evis_inf_centralizer_Nvis natCard_Gmat_eq) lemmaAConclusion_Gmat

theorem noPerfectDoubleCover_Gmat_of_native
    (h : NoPerfectDoubleCover CFSG.Blueprint.NativeSporadic.M24) : NoPerfectDoubleCover ↥Gmat :=
  noPerfectDoubleCover_Gmat (M24NoPerfectDoubleCover.of_native h)

end CFSG.Monster.Schur
