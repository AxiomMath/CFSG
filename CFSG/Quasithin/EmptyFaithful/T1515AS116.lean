module

public import CFSG.Quasithin.EmptyFaithful.T1515Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma116

public section

namespace CFSG.Quasithin

theorem as116Statement : AS116Statement := by
  intro G _ _ hev B H S T M z hB hB1 hBH hHB hS hT hST hzT hzc hz1 hz2 hM hCM
  exact CFSG.QuasithinUnique.lemma116 hev hB hB1 hBH hHB hS hT hST hzT hzc hz1 hz2 hM hCM

end CFSG.Quasithin
