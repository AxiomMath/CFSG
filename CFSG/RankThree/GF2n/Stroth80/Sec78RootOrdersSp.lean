module

public import CFSG.RankThree.GF2n.Stroth80.Sec8Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec83Card
public import CFSG.RankThree.GF2n.Stroth80.Sec39

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7ctr_card_LB_sp (hPts : Sec5NatPointsSpStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec8Hyp hc n t) {r : G} (hr : Sec7A hc t r) :
    ∃ m : ℕ, 2 ≤ m ∧ Nat.card (Vt M (LB M Q B) B Z t) = Nat.card Z * Nat.card Z ^ (2 * m) ∧
      Nat.card (LB M Q B) = Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ (2 * m - 1) := by
  obtain ⟨K, hKf, hKfin, hKZ, m, hm, φ, u, u', hrange, hker, hsec, huu', hLu, -⟩ :=
    hPts G M Q Z B hc n t hs.toSec5 hs.spNat r hr.mem hr.plane
  have hu0 : u ≠ 0 := fun h => huu' (by simp [h])
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.toSec5.mem
  have hnat : NaturalRep (ι := Fin m ⊕ Fin m) K (StatedSp m K) (Rt M (LB M Q B) t)
      (Vt M (LB M Q B) B Z t) Z (hc.CN t) :=
    ⟨φ, hrange, hker, hsec⟩
  have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
  have hcardι : Fintype.card (Fin m ⊕ Fin m) = 2 * m := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hsplit := card_inf_mul_card_map hLR φ hker
  rw [hLu, CFSG.ClassicalGroups.Symplectic.card_LspGL hu0] at hsplit
  refine ⟨m, hm, ?_, ?_⟩
  · rw [hcard, hcardι]
  · rw [← hsplit, hKZ]

end CFSG.RankThree.GF2n.Stroth80
