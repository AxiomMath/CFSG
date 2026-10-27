module

public import CFSG.Quasithin.Background.F6CatRecogSetting
public import CFSG.LocalAnalysis.SectionRank.SectionAssembly

public section

namespace CFSG.Quasithin

namespace F6

theorem nativeSQTSection
    : NativeSQTSection :=
  fun _ _ _ hX H N _ _ hnonab =>
    (CFSG.SectionRank.sqt_catalog_of_simple_section_of_sqtk hX H N hnonab).1

end F6

end CFSG.Quasithin
