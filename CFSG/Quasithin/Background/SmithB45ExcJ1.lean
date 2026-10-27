module

public import CFSG.Quasithin.Background.SmithB45ExcEngine
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J1

public section

namespace CFSG.Quasithin.B45Exc

open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
  CFSG.Open CFSG.Blueprint CFSG.Walter CFSG.Walter.J1Props

theorem sporadicExclusion2F_J1 : SporadicExclusion2F .J1 := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel
  have e' : CQ L ≃* walterJ1 := e.trans walterJ1EquivNative.symm
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  exact exclusion2F_of_autInner hW hq.1 hirr hE hEne hEel e' walterJ1_autInner (r := 3) (ρ := 9)
    (by norm_num) walterJ1_elemAbelian_le
    (rank_of_dihedral hW hirr e' (ρ := 9) (p := 19) (by norm_num)
      (by norm_num [orderOf_two_zmod_19]) walterJ1_dihedral)

end CFSG.Quasithin.B45Exc
