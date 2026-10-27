module

public import CFSG.Quasithin.EmptyFaithful.S152FinMain
public import CFSG.Quasithin.EmptyFaithful.S152FinKLA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

theorem input152Kernel : Input152Kernel := by
  intro G _ _ T Mc M _ H _ _ hC hq
  exact S152Fin.kernel_le_pCoreOf hC.elemAbelian hC hq

theorem input152Transvection : Input152Transvection := by
  intro G _ _ T Mc M _ H _ _ hC hq X hXH hXab hX
  exact S152Fin.relIndex_pCoreOf_le_two hC hq hXH hXab hX

end CFSG.Quasithin
