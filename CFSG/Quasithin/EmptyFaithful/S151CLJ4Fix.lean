module

public import CFSG.Quasithin.EmptyFaithful.S151S9C
public import CFSG.Quasithin.EmptyFaithful.A38c8J4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank

theorem autFixSimple_of_isSporadic_j4
    {Q : Type} [Group Q] [Finite Q]
    (h : IsSporadic .J4 Q) {P : Subgroup Q} (hP2 : IsPGroup 2 ↥P) (hPi : ¬ 2 ∣ P.index) :
    AutFixSimple Q P :=
  autFixSimple_of_inner hP2 hPi (A38c8.center_eq_bot_of_isSporadic_j4 h)
    (fun β hβ hP => j4AutInner_of_outOdd CFSG.QuasithinUnique.Setup.X1.j4OuterOdd Q h β hβ hP)

variable {G : Type} [Group G] [Finite G]

theorem autFixOn_of_isSporadic_j4
    {L B : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hB : IsSylowTwoOf B L)
    (hJ4 : IsSporadic .J4 (↥L ⧸ CFSG.pCore 2 ↥L)) : AutFixOn L B := by
  have hperf : Group.IsPerfect ↥L := ⟨hq.1⟩
  have hBL : B ≤ L := hB.1
  let π₂ : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' _
  have hπ₂ : Function.Surjective π₂ := QuotientGroup.mk'_surjective _
  have hk₂ : π₂.ker = CFSG.pCore 2 ↥L := QuotientGroup.ker_mk' _
  have hP₂ := sylow_map hB π₂ hπ₂
  have hker₂ : π₂.ker ≤ Subgroup.center ↥L := by
    rw [hk₂]
    exact pCore_le_center_of_quasisimple hq
  have hKg₂ : π₂.ker = (pCoreOf 2 L).subgroupOf L := by
    rw [hk₂, pCoreOf_subgroupOf]
  have hN₂ : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
  exact S151S6.autFixOn_of_central_quotient hperf hBL π₂ hπ₂ hker₂ hKg₂ hN₂
    (autFixSimple_of_isSporadic_j4 hJ4 hP₂.1 hP₂.2)

end CFSG.Quasithin
