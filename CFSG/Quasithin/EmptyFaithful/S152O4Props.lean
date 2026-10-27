module

public import CFSG.Quasithin.EmptyFaithful.S152O4Facts
public import CFSG.Quasithin.EmptyFaithful.S152Y11
public import CFSG.Quasithin.EmptyFaithful.S152N2L14D

public section

namespace CFSG.Quasithin

theorem om4IsoStatement : Om4IsoStatement :=
  fun _ _ _ _ hX => S152O4.om4_iso hX

theorem om4FactsStatement : Om4FactsStatement :=
  fun _ _ _ _ hX => S152O4.om4_facts hX

theorem om4Z152 : Om4Z152 :=
  fun _ _ _ _ _ _ hX hTb hB₀T hB₀2 hodd => S152O4.om4_Z152 hX hTb hB₀T hB₀2 hodd

namespace S152N2

theorem omega4PlusIsS3xS3 : Omega4PlusIsS3xS3 :=
  fun _ _ _ _ hX => S152O4.om4_iso hX

end S152N2

end CFSG.Quasithin
