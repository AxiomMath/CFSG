module

public import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVPComp
public import CFSG.LocalAnalysis.StandardType.GGPumpupBalance

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggPComponent_of_le {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Y Y' J : Subgroup G} (hJ : LargeEvenPComponent p Y J) (hJY' : J ≤ Y') (hY'Y : Y' ≤ Y) :
    LargeEvenPComponent p Y' J := by
  obtain ⟨_, hJpc⟩ := (ggLargeEvenPComponent_iff p Y J).1 hJ
  exact (ggLargeEvenPComponent_iff p Y' J).2
    ⟨hJY', ggPComponent_subgroupOf_of_le p hJY' hY'Y hJpc⟩

theorem ggJ_pComponent_centralizer {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G}
    {x : G} {L D J : Subgroup G} (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hpJ : p ∣ Nat.card J) {z : G} (hD : D = Subgroup.closure {x, z}) {X : Subgroup G}
    (hX : LargeEvenPComponent p (Subgroup.centralizer ({z} : Set G)) X) (hJX : J ≤ X) :
    LargeEvenPComponent p (X ⊓ Subgroup.centralizer ({x} : Set G)) J := by
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hJ0 := lBalanceIsPComponent_pLayer_of_stdSub hI hDJ hpJ hD
  have hJM : CFSG.Open.lBalanceIsPComponent p
      (Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) J :=
    GGPumpup.lBalanceIsPComponent_inf_of_pLayer hJ0
  have hJMle : J ≤ Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G) :=
    CFSG.ComponentClassification.LBalance.subnormal_le hJM.1
  have hXz : X ≤ Subgroup.centralizer ({z} : Set G) :=
    ((largeEvenPComponent_iff_lBalance p (Subgroup.centralizer ({z} : Set G)) X).1 hX).1
  have hJcx : J ≤ Subgroup.centralizer ({x} : Set G) := fun j hj => (hJMle hj).2
  have hJME : LargeEvenPComponent p (Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G)) J :=
    (largeEvenPComponent_iff_lBalance p _ J).2 ⟨hJMle, hJM⟩
  have hJY' : J ≤ X ⊓ Subgroup.centralizer ({x} : Set G) := le_inf hJX hJcx
  have hY'Y : X ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
    inf_le_inf_right _ hXz
  exact ggPComponent_of_le hJME hJY' hY'Y

end CFSG.StandardType
