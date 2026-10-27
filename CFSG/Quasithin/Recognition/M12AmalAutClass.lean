module

public import CFSG.Quasithin.Recognition.M12AmalAutInst
public import CFSG.Quasithin.Recognition.CertTwoLocalPair

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.M12AmalAut

theorem autM12Model_twoLocalPairProp : TwoLocalPairProp AutG :=
  autExtra.twoLocalPairProp

@[expose] def AutM12PermModel : Prop :=
  Nonempty (AutG ≃* MulAut ↥CFSG.Open.quasithinM12)

theorem autM12_f6YBridge (hmodel : AutM12PermModel) (D : Type) [Group D] [Finite D]
    (H₁ H₂ : Subgroup D) (h : F6.IsYAmalgam F6.IsAutM12 H₁ H₂) :
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H₁ H₂)
      (fun Y _ => Nonempty (Y ≃* MulAut quasithinM12)) :=
  f6_bridge_of_pair (IsY := F6.IsAutM12)
    (P := fun Y _ => Nonempty (Y ≃* MulAut quasithinM12))
    (fun W _ _ hW => hW)
    (fun W _ _ hW => by
      obtain ⟨e⟩ := hW
      obtain ⟨m⟩ := hmodel
      exact TwoLocalPairProp.of_mulEquiv (e.trans m.symm).symm autM12Model_twoLocalPairProp)
    D H₁ H₂ h

end CFSG.Quasithin
