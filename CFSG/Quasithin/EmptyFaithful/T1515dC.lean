module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Background.InternalSecISec

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.InternalSec
open scoped Pointwise commutatorElement IsMulCommutative

variable {G : Type} [Group G]

section Comm

variable {L W : Subgroup G} [IsMulCommutative ↥W]

theorem commV_autOn_eq1527d (hLW : L ≤ Subgroup.normalizer (W : Set G)) :
    commV (autOn L W) = (⁅W, L⁆).subgroupOf W :=
  CFSG.Quasithin.AutOn.commV_autOn_eq hLW

end Comm

section Quot

variable {L U : Subgroup G}

theorem ker_autOnHom_eq_pCore1527d (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hO2 : pCoreOf 2 (autOn L U) = ⊥) (hker : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (U : Set G))) :
    (autOnHom hLU).ker = CFSG.pCore 2 ↥L := by
  refine le_antisymm ?_ (pCore_le_ker_autOnHom hLU hO2)
  have hpg : IsPGroup 2 ↥(autOnHom hLU).ker := fun x => by
    obtain ⟨k, hk⟩ := hker ⟨((x : ↥L) : G), (x : ↥L).2, (mem_ker_autOnHom hLU _).1 x.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  exact le_sSup ⟨MonoidHom.normal_ker _, hpg⟩

theorem autOn_equiv_quotient1527d (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hO2 : pCoreOf 2 (autOn L U) = ⊥) (hker : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (U : Set G))) :
    Nonempty (↥(autOn L U) ≃* ↥L ⧸ CFSG.pCore 2 ↥L) :=
  ⟨(QuotientGroup.quotientKerEquivOfSurjective _ (autOnHom_surjective hLU)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (ker_autOnHom_eq_pCore1527d hLU hO2 hker))⟩

end Quot

theorem isPSL_congr1527d {n p f : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsPSL n p f X) : IsPSL n p f Y := by
  obtain ⟨hadm, F, hF1, hF2, hc, ⟨e'⟩⟩ := h
  exact ⟨hadm, F, hF1, hF2, hc, ⟨e.symm.trans e'⟩⟩

end CFSG.Quasithin
