module

public import CFSG.Quasithin.H13.A6S1372L76Y
public import CFSG.Quasithin.H13.A6S13821m

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem oTwoUpper_l0 : oTwoUpper (l0 L) = l0 L := by
  rw [l0, oTwoRes_eq_oTwoUpper, oTwoUpper_oTwoUpper, ← oTwoRes_eq_oTwoUpper]

theorem l0_le_of_hat (h139 : Stmt13_3_9) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (hhat : IsHatA6 L) {H K : Subgroup G} (hH : H ∈ S.Hz)
    (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hP : IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K)) : l0 L ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hl0H : l0 L ≤ H := S.l0_le_L1.trans hL1H
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hP' : IsPSL 3 2 1 (L32A.cStar K) := IsPSL.of_mulEquiv (L32A.C.cStarEquiv K).symm hP
  have hX := S.oTwoUpper_l0
  have hTl0 : T ≤ Subgroup.normalizer (l0 L : Set G) := S.frame.T_le.trans S.normalizer_le_l0
  have h3 : (pCoreOf 2 (l0 L)).relIndex (l0 L) = 3 := by
    obtain ⟨c, hc, hc3, hcO, hdec⟩ := l0_decomp hhat
    exact A6L32.relIndex_eq_three_of_decomp hc hc3 hcO hdec
  have hcomm : ∀ x ∈ oTwoUpper (l0 L), ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K :=
    A6L32.comm_of_not_le (X := l0 L) hK hKn hTsyl hP' (by rw [hX]; exact h3)
      (by rw [hX]; exact hl0H) (by rw [hX]; exact hTl0) (by rw [hX]; exact hnot)
  have hcomm' : ∀ x ∈ l0 L, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K :=
    fun x hx => hcomm x (by rw [hX]; exact hx)
  have h0 : l0 L ≤ centralizerMod (pCoreOf 2 K) S.L1 K := fun w hw =>
    ⟨S.l0_le_L1 hw, (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K) (hKn (hl0H hw)),
      fun u hu => hcomm' w hw u hu⟩
  have hKM : K ≤ Subgroup.normalizer (l0 L : Set G) := S.le_normalizer_l0_of hH hK h0
  exact (S.lem13812_one h139 h37 h38 hH hK).1 (hKM.trans (S.normalizer_l0_le_M hhat))

end Setting4

end CFSG.Quasithin.H13.A6
