
module


public import Certificates.Certificate3166

public section

namespace CFSG.Sporadic.HN

open CFSG.Sporadic.F5 CFSG.Sporadic.Recognition.HNMultiplier CFSG.Sporadic.Bridge.TableSurj

theorem hn_certificate :
    mA Native.hnData ^ 2 = 1 ∧ mB Native.hnData ^ 3 = 1 ∧
    (∃ g : J Native.hnData, orderOf (a Native.hnData * (g⁻¹ * b Native.hnData * g)) = 19) ∧
    (∀ M : Matrix (Fin (Native.hnData.d)) (Fin (Native.hnData.d)) (ZMod 5),
      M * mA Native.hnData = mA Native.hnData * M → M * mB Native.hnData = mB Native.hnData * M →
      ∃ c : ZMod 5, M = c • 1) ∧
    Nat.card (J Native.hnData) = 273030912000000 ∧
    ((∀ r ∈ hnRels, FreeGroup.lift (fun i : Fin 7 =>
        img hnTabSpec (CFSG.Perm.pairG (gs Native.hnData)) i.val) (FreeGroup.mk r) = 1) ∧
      (∀ i, FreeGroup.lift (fun j : Fin 7 => img hnTabSpec (CFSG.Perm.pairG (gs Native.hnData)) j.val)
        (FreeGroup.mk (hnCommWord i)) = img hnTabSpec (CFSG.Perm.pairG (gs Native.hnData)) i.val) ∧
      Subgroup.closure (Set.range fun i : Fin 7 =>
        img hnTabSpec (CFSG.Perm.pairG (gs Native.hnData)) i.val) = ⊤) :=
  Certificates.certificate3166

end CFSG.Sporadic.HN
