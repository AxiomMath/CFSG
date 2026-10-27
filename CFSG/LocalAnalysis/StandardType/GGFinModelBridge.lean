module

public import CFSG.LocalAnalysis.StandardType.GGFinModelPkg
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E7Rep
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverCentral
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

section Bridge

@[expose] noncomputable def ggKbEquivOfCenterEqBot {G : Type} [Group G]
    (h : Subgroup.center G = ⊥) : G ⧸ Subgroup.center G ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

@[expose] noncomputable def ggKbEquivF4 (n f : ℕ) :
    GGKb .F4 n f ≃* adjointGroup .F4 (GaloisField 2 f) :=
  ggKbEquivOfCenterEqBot
    (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (K := GaloisField 2 f))

@[expose] noncomputable def ggKbEquivE8 (n f : ℕ) :
    GGKb .E8 n f ≃* adjointGroup .E8 (GaloisField 2 f) :=
  ggKbEquivOfCenterEqBot
    (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (K := GaloisField 2 f))

theorem ggCenter_E7_eq_bot (n f : ℕ) : Subgroup.center ((ggU .E7 n f).K) = ⊥ := by
  have hZadj : Subgroup.center (↥(adjointGroup .E7 (GaloisField 2 f))) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (K := GaloisField 2 f)
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hz' : e7Equiv (K := GaloisField 2 f) z ∈
      Subgroup.center (↥(adjointGroup .E7 (GaloisField 2 f))) := by
    rw [← Subgroup.map_center_eq (e7Equiv (K := GaloisField 2 f))]
    exact ⟨z, hz, rfl⟩
  rw [hZadj, Subgroup.mem_bot] at hz'
  exact (e7Equiv (K := GaloisField 2 f)).injective (hz'.trans (map_one _).symm)

@[expose] noncomputable def ggKbEquivE7 (n f : ℕ) :
    GGKb .E7 n f ≃* adjointGroup .E7 (GaloisField 2 f) :=
  (ggKbEquivOfCenterEqBot (ggCenter_E7_eq_bot n f)).trans (e7Equiv (K := GaloisField 2 f))

end Bridge

end CFSG.StandardType.GGFinModel
