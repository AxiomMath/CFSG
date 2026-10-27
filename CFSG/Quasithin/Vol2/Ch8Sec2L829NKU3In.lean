module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKDefs
import CFSG.Quasithin.Vol2.Ch8Sec2L829NKU3InA
import CFSG.Quasithin.EmptyFaithful.T1521SU3Base
import CFSG.GH74.Bender
import CFSG.Timmesfeld.Bridge.Asc72Bender

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Quasithin

theorem nk_u3_uin (n : ℕ) (hn : 4 ≤ n) (hn4 : n % 4 = 0) (X : Type) [Group X]
    (hX : IsPSU 3 2 n X) : UIn X := by
  have hB : fusionIsBenderGroup X := CFSG.Quasithin.U31521.bender_of_isPSU (by omega) hX
  obtain ⟨-, K, _, hKf, hKc, ⟨e⟩⟩ := hX
  haveI : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have hchar : CharP K 2 := U3In.charP_two_of_natCard_eq hKc
  have h16 : 16 ≤ 2 ^ n := by
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hconj : ∀ a b : X, orderOf a = 2 → orderOf b = 2 → IsConj a b := fun a b ha hb =>
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isConj_of_orderOf_eq_two
      (CFSG.GH74.isBenderGroup_of_fusionIsBenderGroup hB) ha hb
  obtain ⟨z, g, hz, hzg⟩ := U3In.u3_exists_order_witness h16 hKc
  unfold UIn
  refine ⟨hconj, e.symm z, e.symm g, ?_, ?_⟩
  · rw [e.symm.orderOf_eq]
    exact hz
  · have h : e.symm z * ((e.symm g)⁻¹ * e.symm z * e.symm g) = e.symm (z * (g⁻¹ * z * g)) := by
      simp only [map_mul, map_inv]
    rw [h, e.symm.orderOf_eq]
    exact hzg

end CFSG.Quasithin.H13.L829NK
