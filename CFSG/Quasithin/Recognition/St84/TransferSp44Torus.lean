module

public import CFSG.Quasithin.Recognition.St84.TransferVertex

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

structure Sp44VertexData (E : Subgroup H) : Prop where
  quot : IsL2Quot 2 (oTwoQuot ↥(oTwoPrime E))
  elem : IsElemAbelian 2 (pCoreOf 2 E)
  card : Nat.card (pCoreOf 2 E) = 2 ^ 6
  center : Nat.card ↥(centerOf (oTwoPrime E)) = 2 ^ 2
  nat : NatSec (oTwoPrime E) (centerOf (oTwoPrime E)) (pCoreOf 2 E)
  indec : ⁅pCoreOf 2 E, oTwoPrime E⁆ = pCoreOf 2 E

section Generic

variable {G : Type*} [Group G]

private theorem centerOf_oTwoPrime_eq_inf_centralizer {E : Subgroup G} (hchar : CharTwo E) :
    centerOf (oTwoPrime E) =
      pCoreOf 2 E ⊓ Subgroup.centralizer (oTwoPrime E : Set G) := by
  have hQL : pCoreOf 2 E ≤ oTwoPrime E :=
    le_oTwoPrime_of_isPGroup
      (pCore_isPGroup (G := ↥E) (p := 2) |>.map E.subtype)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 E)
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxL, hxC⟩
    have hxE : x ∈ E := oTwoPrime_le E hxL
    have hxQ : x ∈ pCoreOf 2 E := hchar (Subgroup.mem_inf.mpr ⟨hxE, ?_⟩)
    · exact Subgroup.mem_inf.mpr ⟨hxQ, hxC⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact Subgroup.mem_centralizer_iff.mp hxC q (hQL hq)
  · rintro x ⟨hxQ, hxC⟩
    exact Subgroup.mem_inf.mpr ⟨hQL hxQ, hxC⟩

end Generic

theorem transferVertexData_of_sp44VertexData {E : Subgroup H} (h : Sp44VertexData E)
    (hchar : CharTwo E) :
    TransferVertexData E := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := centerOf_oTwoPrime_eq_inf_centralizer hchar
  have hZle : centerOf (oTwoPrime E) ≤ pCoreOf 2 E := by
    rw [hZ]
    exact inf_le_left
  refine ⟨h.quot, h.elem.1, ?_, ?_, h.indec⟩
  · rw [← hZ]
    have hmul := Subgroup.relIndex_mul_card (H := centerOf (oTwoPrime E)) (K := pCoreOf 2 E)
    rw [inf_of_le_left hZle, h.card, h.center] at hmul
    norm_num at hmul ⊢
    omega
  · simpa [hZ] using h.nat

end CFSG.Quasithin.F112R.St84
