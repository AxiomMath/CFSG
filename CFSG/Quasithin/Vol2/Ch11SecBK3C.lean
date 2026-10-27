module

public import CFSG.Quasithin.Vol2.Ch11SecBFactsG2S
public import CFSG.LieType.Simplicity.Exceptional
public import CFSG.Quasithin.Background.SmithB42G2Id

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit

theorem factG2Simple_holds : FactG2Simple := by
  intro K _ _ n hn hK
  have := B42G2Id.charP_two_of_card hK
  obtain ⟨c, hc0, hc1⟩ :=
    B42G2Id.exists_ne_zero_ne_one_of_three_le (K := K) (hK ▸ B42G2Id.three_le_two_pow hn)
  have hc : ⁅quasithinG2 K, quasithinG2 K⁆ = cayleyGroup K := by
    rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
      cayley_commutator_eq hc0 hc1]
  have := (CFSG.LieType.Simplicity.fam_g2_simplicity _ 2 n
    (B42G2Id.chevalleyExceptionalModel_cayleyGroup hK hn)).2
  exact (MulEquiv.subgroupCongr hc).isSimpleGroup

end CFSG.Quasithin.Vol2.Ch11.SecB
