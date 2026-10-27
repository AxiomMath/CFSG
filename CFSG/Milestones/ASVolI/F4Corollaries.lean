module

public import CFSG.Milestones.ASVolI.F48
public import CFSG.Milestones.ASVolI.F4N.Cor
public import CFSG.Milestones.ASVolI.F438

public section

namespace CFSG.ASVolI

section Certificates64


theorem f_4_24_of (h8 : F_4_8) : F_4_24 := burnside_as_F_4_24_of as_F_4_5 as_F_4_6 h8

theorem f_4_26_of (h8 : F_4_8) : F_4_26 := burnside_as_F_4_26_of as_F_4_6 h8

end Certificates64

section CertificatesF48

set_option linter.unusedSectionVars false


theorem as_F_4_24 : F_4_24 := f_4_24_of as_F_4_8

theorem as_F_4_26 : F_4_26 := f_4_26_of as_F_4_8

end CertificatesF48

section Certificates44

set_option linter.unusedSectionVars false


theorem as_F_4_44_partial : F_4_44_partial :=
  burnsideF4ja_F_4_44_of as_F_4_24 as_F_4_38 as_F_4_43

theorem as_F_4_44 : F_4_44 := as_F_4_44_partial

end Certificates44

end CFSG.ASVolI
