module

public import CFSG.Quasithin.Background.SmithB42G2Id
public import CFSG.Quasithin.EmptyFaithful.LRed3Four

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.Explicit

theorem factG2Cayley_holds : FactG2Cayley := by
  intro K _ _ n hn hK
  have := B42G2Id.charP_two_of_card hK
  obtain ⟨c, hc0, hc1⟩ :=
    B42G2Id.exists_ne_zero_ne_one_of_three_le (K := K) (hK ▸ B42G2Id.three_le_two_pow hn)
  have hZ : Subgroup.center ↥(cayleyGroup K) = ⊥ := A318Excl.center_cayleyGroup_eq_bot hc0 hc1
  let e₀ : ↥(quasithinG2 K) ≃* ↥(cayleyGroup K) :=
    MulEquiv.subgroupCongr G11.P3G2.quasithinG2_eq_cayleyGroup
  let e₁ : ↥(quasithinG2 K) ⧸ Subgroup.center ↥(quasithinG2 K) ≃*
      ↥(cayleyGroup K) ⧸ Subgroup.center ↥(cayleyGroup K) :=
    QuotientGroup.congr _ _ e₀ (Subgroup.map_center_eq e₀)
  let e₂ : ↥(cayleyGroup K) ⧸ Subgroup.center ↥(cayleyGroup K) ≃* ↥(cayleyGroup K) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact IsG2.of_mulEquiv (e₁.trans e₂).symm (B42G2Id.chevalleyExceptionalModel_cayleyGroup hK hn)

end CFSG.Quasithin
