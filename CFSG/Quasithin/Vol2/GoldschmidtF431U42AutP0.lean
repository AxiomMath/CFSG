module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutIface
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP0Good

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 L0S)
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QP45)
open scoped Pointwise

@[expose] def fhatA : Ah := ⟨fhat, fhat_mem⟩

theorem fhatA_coe : (fhatA : P45) = fhat := rfl

theorem mem_P1h_iff (g : Ah) : g ∈ P1h ↔ (g : P45) 0 = 0 := MulAction.mem_stabilizer_iff

theorem mem_P2h_iff (g : Ah) : g ∈ P2h ↔ (g : P45) '' L0S = L0S := by
  rw [P2h, MulAction.mem_stabilizer_iff, ← Set.image_smul]
  rfl

theorem fhatA_mem_Bh : fhatA ∈ Bh := by
  refine ⟨(mem_P1h_iff _).2 ?_, (mem_P2h_iff _).2 ?_⟩
  · rw [fhatA_coe]
    exact fhat_zero
  · rw [fhatA_coe]
    exact fhat_line

theorem mem_Yh_iff (g : Ah) : g ∈ Yh ↔ (g : P45) ∈ QP45.originalSubgroup := by
  rw [Yh, Subgroup.mem_subgroupOf]

theorem fhatA_not_mem_Yh : fhatA ∉ Yh := fun h => by
  have := (mem_Yh_iff fhatA).1 h
  rw [fhatA_coe] at this
  exact fhat_not_mem_QP45 this

theorem fhatA_sq : fhatA ^ 2 = 1 := Subtype.ext (by
  rw [pow_two, Subgroup.coe_mul, fhatA_coe]
  exact fhat_sq)

theorem isGoodInv_fhatA : IsGoodInv fhatA :=
  ⟨fhatA_mem_Bh, fhatA_not_mem_Yh, fhatA_sq, card_centralizer_fhat⟩

theorem u42AutModelGood : U42AutModelGood :=
  ⟨fhatA, isGoodInv_fhatA⟩

end CFSG.Quasithin.H13.F431.U42Aut
