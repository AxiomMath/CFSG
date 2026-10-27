module

public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.BabyMonster.E35B
public import CFSG.Open.LocalVocabulary

public section

namespace Certificates

open CFSG CFSG.SectionRank CFSG.Open CFSG.SectionRank.Native in
theorem certificate8010 : ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.B, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 :=
  CFSG.KC.BM.E35Group.elemAbelian_three_four_B

end Certificates
