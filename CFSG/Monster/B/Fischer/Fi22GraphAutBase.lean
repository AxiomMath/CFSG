
module

public import CFSG.Monster.B.Fischer.Fi22GraphBoundBase
public import CFSG.Sporadic.Fi22.Simple

@[expose] public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates

@[expose] def fi22Sec
    (i : Fin 3510) : fi22P :=
  ⟨Classical.choose (fi22P_exists_smul 0 i), (Classical.choose_spec (fi22P_exists_smul 0 i)).1⟩

theorem fi22Sec_apply
    (i : Fin 3510) : ((fi22Sec i : fi22P) : Equiv.Perm (Fin 3510)) 0 = i :=
  (Classical.choose_spec (fi22P_exists_smul 0 i)).2

theorem isSimpleGroup_fi22P :
    IsSimpleGroup fi22P :=
  @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi22.isSimpleGroup_Fi22 fi22PermEquiv.symm

end CFSG.Monster.B.Fischer
