module

public import CFSG.Quasithin.Vol2.Ch7Lem756Two
public import CFSG.Quasithin.Background.HFL3Hyp

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H

theorem hL3NineHyp_holds : HL3NineHyp := by
  intro V _ _ L M hLM n hn hL A hA hrk
  obtain ⟨K, _, _, _, hK, hreal⟩ := hL
  have hK' : Nat.card K = (2 ^ n) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨e, he⟩ := L3Nine.exists_model hK' hreal
  have hMN : M.map (congrHom e) ≤ L3Nine.norm hK' := by
    have h1 : (Subgroup.normalizer (L : Set (MulAut V))).map (congrHom e) =
        Subgroup.normalizer ((L.map (congrHom e) : Subgroup (MulAut (L3Nine.HMod n K))) :
          Set (MulAut (L3Nine.HMod n K))) :=
      Subgroup.map_equiv_normalizer_eq L (MulAut.congr e)
    rw [L3Nine.norm, ← he, ← h1]
    exact Subgroup.map_mono hLM.2
  have hA' : A.map (congrHom e) ∈ aSet (2 * n + 1) (L3Nine.norm hK') :=
    aSet_mono hMN ((map_mem_aSet_iff e).2 hA)
  have hcard : 2 ^ (3 * n) < Nat.card ↥(A.map (congrHom e)) := by
    have : Finite (MulAut V) := MulEquiv.finite_left
    rw [card_map_congrHom, card_eq_two_pow_of_isPGroup (isPGroup_of_isElemAbelian2 hA.2.2.1)]
    exact Nat.pow_lt_pow_right (by norm_num) hrk
  calc rkIdx (gammaCheck (3 * n) A)
      = rkIdx ((gammaCheck (3 * n) A).map e.toMonoidHom) := (rkIdx_map_mulEquiv e _).symm
    _ ≤ rkIdx (gammaCheck (3 * n) (A.map (congrHom e))) :=
      L3Nine.rkIdx_anti (L3Nine.gammaCheck_map_le e _ A)
    _ ≤ n := L3Nine.rkIdx_gammaCheck_le hn hK' hA' hcard

end CFSG.Quasithin.H13
