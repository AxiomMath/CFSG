module

public import CFSG.RankThree.GF2n.Stroth80.Sec11CM
import CFSG.RankThree.GF2n.Stroth80.Sec119Beisiegel
import CFSG.RankThree.GF2n.Stroth80.Sec119Filtration
import CFSG.RankThree.GF2n.Stroth80.Sec119XbarOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec3Action

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.false_of_omega_naturalRep (hc : Ctx M Q Z B) {m x : ℕ}
    (hO : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .POmegaPlus m 2 x ∨
      CFSG.Blueprint.LieModel (XbarMod M Q Z B) .POmegaMinus m 2 x ∨
      (m = 3 ∧ CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x))
    (hx : 2 ^ x = Nat.card Z) {K : Type} [Field K] [Finite K] (hK : Nat.card K = Nat.card Z)
    {X : Subgroup (GL (Fin (2 * m)) K)}
    (hR : NaturalRep (ι := Fin (2 * m)) K X (XbarPre M Q Z B) (Z ⊔ ⁅Q, XbarPre M Q Z B⁆) Z Q) :
    False := by
  have hm : 3 ≤ m := by
    rcases hO with h | h | ⟨rfl, -⟩
    · have h4 : 4 ≤ m := h.admissible.2.2
      omega
    · have h4 : 4 ≤ m := h.admissible.2.2
      omega
    · exact le_rfl
  obtain ⟨n₀, γ, M₀, -, hD⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφk, hφQ⟩ := exists_actionHom_H0 hc.hyp hD
  have hq : (2 : ℤ) ^ x = (Nat.card (GaloisField 2 n₀) : ℤ) := by
    rw [hD.card, ← hx, Nat.cast_pow, Nat.cast_ofNat]
  have hcard := card_ge_of_omega_lieModel hO
  rw [hq] at hcard
  exact hc.false_of_card_xbarMod_ge hD φ hφπ hφk hφQ hm
    (hc.finrank_cmComm_eq_of_naturalRep hD φ hφπ hK hR) hcard

end CFSG.RankThree.GF2n.Stroth80
