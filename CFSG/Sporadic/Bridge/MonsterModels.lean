module

public import CFSG.Blueprint.MonsterModels
public import CFSG.Sporadic.Bridge.Y443Relabel
public import CFSG.Sporadic.Bridge.Y322Central

public section

namespace CFSG.Blueprint.NativeSporadic.MonsterModel

@[expose] def Iso (m m' : MonsterModel) : Prop :=
  Nonempty (m.Carrier ≃* m'.Carrier)

theorem Iso.refl (m : MonsterModel) : Iso m m :=
  ⟨MulEquiv.refl _⟩

theorem Iso.symm {m m' : MonsterModel} (h : Iso m m') : Iso m' m :=
  h.map MulEquiv.symm

theorem Iso.trans {m m' m'' : MonsterModel} (h : Iso m m') (h' : Iso m' m'') : Iso m m'' :=
  h.elim fun e => h'.elim fun e' => ⟨e.trans e'⟩

theorem Iso.nonempty_mulEquiv {G : Type*} [Group G] {m m' : MonsterModel} (h : Iso m m')
    (hG : Nonempty (G ≃* m.Carrier)) : Nonempty (G ≃* m'.Carrier) :=
  hG.elim fun e => h.elim fun e' => ⟨e.trans e'⟩

noncomputable def y443DerivedEquivOpen :
    y443Derived.Carrier ≃* CFSG.Open.MonsterY443Derived :=
  CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv

theorem iso_y443Derived_tauCeti :
    Iso .y443Derived .tauCeti :=
  CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv

end CFSG.Blueprint.NativeSporadic.MonsterModel
