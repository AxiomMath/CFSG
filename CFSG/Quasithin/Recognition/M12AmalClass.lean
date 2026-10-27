module

public import CFSG.Quasithin.Recognition.M12AmalInst
public import CFSG.Quasithin.Recognition.CertTwoLocalPair

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.M12Amal

theorem m12_twoLocalPairProp : TwoLocalPairProp M12G :=
  m12Extra.twoLocalPairProp

theorem nativeM12_eq_quasithinM12 :
    CFSG.Blueprint.NativeSporadic.M12 = CFSG.Open.quasithinM12 := rfl

theorem nonempty_mulEquiv_quasithinM12_of_isM12 {W : Type} [Group W] (h : F6.IsM12 W) :
    Nonempty (W ≃* ↥CFSG.Open.quasithinM12) := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans (MulEquiv.subgroupCongr nativeM12_eq_quasithinM12.symm).symm⟩

theorem m12_f6YBridge (D : Type) [Group D] [Finite D] (H₁ H₂ : Subgroup D)
    (h : F6.IsYAmalgam F6.IsM12 H₁ H₂) :
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H₁ H₂)
      (fun Y _ => Nonempty (Y ≃* quasithinM12)) :=
  f6_bridge_of_pair (IsY := F6.IsM12) (P := fun Y _ => Nonempty (Y ≃* quasithinM12))
    (fun W _ _ hW => nonempty_mulEquiv_quasithinM12_of_isM12 hW)
    (fun W _ _ hW => by
      obtain ⟨e⟩ := nonempty_mulEquiv_quasithinM12_of_isM12 hW
      exact TwoLocalPairProp.of_mulEquiv e.symm m12_twoLocalPairProp)
    D H₁ H₂ h

end CFSG.Quasithin
