module

public import CFSG.Quasithin.Vol2.GoldschmidtCh7NormalGroup
public import CFSG.Quasithin.Vol2.Ch10SecQ1M2x
public import CFSG.Quasithin.Vol2.Ch10SecQ1M12

public section

namespace CFSG.Quasithin.H13

open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.Vol2.Ch10.SecA

theorem normalDichotomy_autPerm : NormalDichotomy ↥AutPerm :=
  NormalDichotomy.of_isSimpleGroup AutPerm_isSimpleGroup

theorem normalDichotomy_stab_m23
    (x : Fin 24) :
    NormalDichotomy ↥(AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x) :=
  NormalDichotomy.of_isSimpleGroup (C10P01.stab_props_m23 x).1

theorem normalDichotomy_stab_m22
    {x y : Fin 24} (hxy : x ≠ y) :
    NormalDichotomy ↥(AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 24)) y) :=
  NormalDichotomy.of_isSimpleGroup (C10P01.stab_props_m22 hxy).1

theorem normalDichotomy_m24Fix
    {eY : G6.PermMod 24} (heY : eY ∈ golayC) (hw : hammingNorm (Multiplicative.toAdd eY) = 12) :
    NormalDichotomy ↥(m24Fix eY) := by
  obtain ⟨p, hp, hpe⟩ := C10P01.exists_permAct_eq heY hw
  have hmap : (m24Fix C10P01.dodecadE).map (MulAut.conj p).toMonoidHom = m24Fix eY := by
    rw [← hpe, C10P01.m24Fix_permAct hp]
  let e1 : ↥(m24Fix C10P01.dodecadE) ≃* ↥(m24Fix eY) :=
    ((m24Fix C10P01.dodecadE).equivMapOfInjective _ (MulAut.conj p).injective).trans
      (MulEquiv.subgroupCongr hmap)
  obtain ⟨⟨e2⟩, -⟩ := C10P01.m24Fix_dodecadE_props
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M12 :=
    CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  exact NormalDichotomy.of_isSimpleGroup (e1.symm.trans e2).isSimpleGroup

end CFSG.Quasithin.H13
