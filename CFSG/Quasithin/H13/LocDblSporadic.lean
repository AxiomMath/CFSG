module

public import CFSG.Quasithin.H13.LocDblFamilies
public import CFSG.Quasithin.H13.LocDblJ2
public import CFSG.Quasithin.H13.LocDblHS
public import CFSG.Quasithin.H13.LocDblHe
public import CFSG.Quasithin.H13.LocDblRu

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem sporadicSylowNoDouble
    : SporadicSylowNoDouble :=
  ⟨sylowNoDouble_J2, sylowNoDouble_HS, sylowNoDouble_He, sylowNoDouble_Ru⟩

theorem local_double_embedding_exclusion
    : LocalDoubleEmbeddingExclusion :=
  local_double_embedding_exclusion_of_sporadic sporadicSylowNoDouble

end CFSG.Quasithin.H13.LocDbl
