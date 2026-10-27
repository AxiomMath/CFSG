module

public import CFSG.Quasithin.Vol2.Ch4Sec4Prime443Defs
public import CFSG.Quasithin.Vol2.Ch4Sec4Prime443Trans
public import CFSG.Quasithin.Vol2.Ch4Sec4L448
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E12Map

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13

theorem lemma443End'_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hS : Vol2Native.SchreierFactCat) (hm2 : Mult2Fact) (hA134 : A134Fact) (h4411 : Fact4411)
    (hInsp : Insp443') (hJ4 : Gap443J4) : Lemma443End' := by
  intro G _ _ T M L B Tp VB s' hU h448
  have s : Setting443 G T M L B Tp VB := setting443_of_prime s'
  obtain ⟨K, hKGB, hGBK, hKq, hKM, hVK, hLK, hC⟩ :=
    exists_component ⟨hA134, hm2⟩ hS h4411 s hU h448 h37 h38 h39 s.VB_eq_commutator_LB
  rcases concl_or_J4' s h37 h38 h39 hVK
      (hInsp G T M L B Tp VB K s hU h448 hKGB hGBK hKq hKM hVK hLK hC) with h | ⟨hJ, hL⟩
  · exact s'.not_concl h
  · exact hJ4 G T M L B Tp VB K s hU h448 hKGB hGBK hKq hKM hVK hLK hC hJ hL

end CFSG.Quasithin.H13.Ch4.E443

end
