module

public import CFSG.Quasithin.EmptyFaithful.S143KN
public import CFSG.Quasithin.EmptyFaithful.S143HA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

theorem lemma_14_3_19_four : Lemma14319Four := by
  intro G _ _ T M g A t c c18 _
  obtain ⟨r, hrW, hrV, hr2, rfl⟩ := c.exists_Ac_eq c18.b
  obtain ⟨x, z, a, r1, hS⟩ := c.exists_setup hrW hrV hr2 c18.a
  obtain ⟨y, cm, hM⟩ := hS.exists_KModel c18.b.t_mem c18.b.t_nmem
  exact hS.isA6Block c18.b.t_mem c18.b.t_nmem hM

end S143

end CFSG.Quasithin
