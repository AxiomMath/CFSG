module

public import CFSG.Quasithin.Background.F6CatSetting
public import CFSG.Milestones.CL_LIT_SQTK_simple_list

public section

namespace CFSG.Quasithin

namespace F6

theorem nativeTheoremCSection
    : NativeTheoremCSection :=
  fun X _ _ hX H N _ _ hnonab => CFSG.Milestones.cl_lit_sqtk_simple_list_section X hX H N hnonab

end F6

end CFSG.Quasithin
