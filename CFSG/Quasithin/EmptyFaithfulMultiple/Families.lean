module

public import CFSG.Quasithin.Vol2.Ch1Xi
public import CFSG.Quasithin.Background.D2Params

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G]

@[expose] def IsSmallXi (T X : Subgroup G) : Prop :=
  X = oTwoUpper X ∧ T ≤ Subgroup.normalizer (X : Set G) ∧ InH T (X ⊔ T) ∧
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (pCoreOf 2 X).relIndex X = p

@[expose] def IsSmallXiStar (T X : Subgroup G) : Prop :=
  IsSmallXi T X ∧ ∃ M : Subgroup G, IsUniqueM (X ⊔ T) M

@[expose] def IsSmallXiF (T X : Subgroup G) : Prop := IsSmallXi T X ∧ IsXf X

@[expose] def IsYFamily (T Y : Subgroup G) : Prop :=
  (IsXi T Y ∨ IsSmallXi T Y) ∧ ⁅Y, thompsonJ T⁆ = Y

@[expose] noncomputable def qhatInt [Finite G] (H V : Subgroup G) (hV : IsElemAbelian 2 V) :
    WithTop ℚ :=
  @qhatOf ↥V (commGroupOfElemAbelian hV) inferInstance (autOn H V)

end CFSG.Quasithin.EmptyFaithfulMultiple
