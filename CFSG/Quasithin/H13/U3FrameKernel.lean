module

public import CFSG.Quasithin.H13.U3Basic
public import CFSG.Quasithin.SteinbergCBU3Frame
public import CFSG.Quasithin.SteinbergBMSimpleCoreQuotientKernel
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LieType.BorelTits.Basic
import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative

variable {G : Type*} [Group G]

theorem inSubgroup_pCore_eq_pCoreOf (p : ℕ) (L : Subgroup G) :
    CFSG.inSubgroup (CFSG.pCore p) L = CFSG.Open.pCoreOf p L := by
  rw [CFSG.inSubgroup, CFSG.Open.pCoreOf]

theorem pCoreOf_le_pCoreOf_sup [Finite G] {L T : Subgroup G}
    (hTL : T ≤ normalizer (L : Set G)) :
    CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) ?_
    (LieType.BorelTits.pCoreOf_isPGroup 2 L)
  exact (sup_le le_normalizer hTL).trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)

theorem isSimpleGroup_of_lieModel_PSU {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .PSU 3 3 1) : IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

theorem u3_internal_frame_kernel {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {z : G}
    [IsElementaryAbelian 2 V] (hLV : L ≤ normalizer (V : Set G))
    (hU3 : CFSG.Blueprint.LieModel (L ⧸ CFSG.pCore 2 L) .PSU 3 3 1)
    (hF : QTU3InternalFrame T L V z) :
    L ⊓ centralizer (V : Set G) = CFSG.Open.pCoreOf 2 L ∧
      Nonempty ((u3ConjLin V L hLV).range ≃* L ⧸ CFSG.pCore 2 L) ∧
      CFSG.Blueprint.LieModel (u3ConjLin V L hLV).range .PSU 3 3 1 := by
  obtain ⟨hTL, -, -, -, -, hVC, -, -, -, ⟨l₀, hl₀, v₀, hv₀, hlv⟩, -, -, -⟩ := hF
  have hsimple : IsSimpleGroup (L ⧸ CFSG.pCore 2 L) := isSimpleGroup_of_lieModel_PSU hU3
  have hO : CFSG.inSubgroup (CFSG.pCore 2) L ≤ L ⊓ centralizer (V : Set G) := by
    rw [inSubgroup_pCore_eq_pCoreOf]
    refine le_inf (LieType.BorelTits.pCoreOf_le 2 L) ?_
    have h1 : CFSG.Open.pCoreOf 2 (L ⊔ T) ≤ centralizer (V : Set G) := by
      rw [← le_centralizer_iff]
      exact hVC
    exact (pCoreOf_le_pCoreOf_sup hTL).trans h1
  have hlt : L ⊓ centralizer (V : Set G) < L := by
    refine lt_of_le_of_ne inf_le_left fun h => hlv ?_
    have h1 : l₀ ∈ centralizer (V : Set G) := (h.symm ▸ hl₀ : l₀ ∈ L ⊓ _).2
    rw [← mem_centralizer_iff.1 h1 v₀ hv₀, mul_inv_cancel_right]
  have hCL := SteinbergBM.simple_core_quotient_centralizer_eq_pCore hLV hO hlt
  have hker : (u3ConjLin V L hLV).ker = CFSG.pCore 2 L := by
    ext l
    rw [MonoidHom.mem_ker, u3ConjLin_eq_one_iff]
    constructor
    · intro hl
      have h1 : (l : G) ∈ CFSG.inSubgroup (CFSG.pCore 2) L := hCL ▸ ⟨l.2, hl⟩
      obtain ⟨l', hl', hll'⟩ := h1
      rwa [← Subtype.ext hll']
    · intro hl
      exact (hO ⟨l, hl, rfl⟩).2
  have e : (u3ConjLin V L hLV).range ≃* L ⧸ CFSG.pCore 2 L :=
    (QuotientGroup.quotientKerEquivRange _).symm.trans (QuotientGroup.quotientMulEquivOfEq hker)
  exact ⟨hCL.trans (inSubgroup_pCore_eq_pCoreOf 2 L), ⟨e⟩,
    LieType.CurtisTits.lieModel_of_mulEquiv e.symm hU3⟩

end CFSG.Quasithin.H13.U3
