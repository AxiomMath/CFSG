module

public import CFSG.Quasithin.Background.GoldschmidtG22SylowIsoGroup
public import CFSG.Quasithin.Background.GoldschmidtG22M12Ident
public import CFSG.Quasithin.Recognition.CertR2aBridges

public section

namespace CFSG.Quasithin

namespace F6

theorem g22SylowIsoM12Fact_holds :
    G22SylowIsoM12Fact := by
  intro W _ _ hW P
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, _, _, hk, ⟨ε⟩⟩ := isG22_equiv_g2Group W hW
  have h2 := two_eq_zero_of_card_two hk
  have hk2 := eq_zero_or_eq_one_of_card_two hk
  have : Finite (G2Group k) := finite_g2Group
  obtain ⟨P', ⟨e₁⟩⟩ : ∃ P' : Sylow 2 (G2Group k), Nonempty (↥P ≃* ↥P') :=
    ⟨P.mapSurjective (f := ε.toMonoidHom) ε.surjective,
      ⟨((P : Subgroup W).equivMapOfInjective ε.toMonoidHom ε.injective).trans
        (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective _ _).symm)⟩⟩
  let S' : Sylow 2 (G2Group k) :=
    (G22SylowIso.Ssub_sylow h2 hk2).1.toSylow (G22SylowIso.Ssub_sylow h2 hk2).2
  obtain ⟨e₃⟩ := G22SylowIso.S_mulEquiv_T h2 hk2
  let Q : Sylow 2 ↥CFSG.Blueprint.NativeSporadic.M12 :=
    M12Amal.m12_syl.1.toSylow M12Amal.m12_syl.2
  exact ⟨Q, ⟨e₁.trans ((Sylow.equiv P' S').trans e₃)⟩⟩

end F6

end CFSG.Quasithin
