module

public import CFSG.RankThree.GF2n.Stroth80.Sec83Arith
public import CFSG.RankThree.GF2n.Stroth80.Sec83Elem
public import CFSG.RankThree.GF2n.Stroth80.Sec83Lower
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix


theorem stroth83_of_inputs (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (h53 : Stroth53Statement) (h54 : Stroth54Statement) (hPts : Sec5NatPointsSpStatement)
    (hA : Sec8AExistsStatement) (hInv : Sec8InvStatement) (h82 : Stroth82Statement)
    (hC : Sec83UpperStatement) (hG : Sec83SevenStatement) : Stroth83Statement := by
  have hT : Sec83TypeStatement := sec83Type_of_nat
  have hE : Sec83FixedStatement := sec83Fixed_of_53 h53 hInv
  have hF : Sec83A2Statement := sec83A2_of_53 h53 hInv
  have hD : Sec83LowerStatement := sec83Lower_of_53 h53 hInv
  intro G _ _ M Q Z B hc n t hs hsp
  have h8 : Sec8Hyp hc n t := ⟨hs, hsp⟩
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t h8
  obtain ⟨K, iK, iF, hK, m, hm, φ, u, u', hrange, hker, hact, huu', hL, hL'⟩ :=
    hPts G M Q Z B hc n t hs h8.spNat r hr.mem hr.plane
  have hpts : Sec8Pts hc t r m K φ u u' := ⟨hm, hK, hrange, hker, hact, huu', hL, hL'⟩
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  obtain ⟨a, hn, hV1, hW1⟩ := sec83_count_A h53 hInv hs hr hpts
  have hN := sec83_count_B h34 h51 hs hr hpts (e := a * 2 ^ m) (by omega)
  have ha : 1 ≤ a := by
    by_contra h0
    have h00 : a = 0 := by omega
    refine h54 G M Q Z B hc n t hs h8.spNat ?_
    rw [hN, h00]
    simp
  obtain ⟨s, hsR, hsc, g, hg, hzL, hzN⟩ := h82 G M Q Z B hc n t h8
  have hzR : g * s * g⁻¹ ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem hzL
  have hCz : Nat.card ↥(Ut Q Z (g * s * g⁻¹)) ≤ Nat.card Z ^ (2 * m + 1) := by
    rw [card_Ut_conj hc hg s]
    exact hC G M Q Z B hc n t m hs hm hpts.spMNat s hsR hsc
  have hDz := hD G M Q Z B hc n t h8 r hr (g * s * g⁻¹) hzL
  have hcases : ((Nat.card ↥(CommSec (Vt M (LB M Q B) B Z t) Z (g * s * g⁻¹)) = Nat.card Z ^ 2 ∨
        Nat.card ↥(CommSec (Vt M (LB M Q B) B Z t) Z (g * s * g⁻¹)) = Nat.card Z ^ 3) ∧
      Nat.card ↥(CommSec (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) (g * s * g⁻¹)) ^ 2 =
        Nat.card ↥(Sec8V1 M Q Z B t r) * Nat.card ↥(Sec8W1 M Q Z B t r)) ∨
      (Nat.card ↥(CommSec (Vt M (LB M Q B) B Z t) Z (g * s * g⁻¹)) = Nat.card Z ^ 3 ∧
        Nat.card ↥(Sec8V1 M Q Z B t r) ^ 3 * Nat.card ↥(Sec8W1 M Q Z B t r) ≤
          Nat.card ↥(CommSec (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) (g * s * g⁻¹)) ^ 4) := by
    by_cases hna : SpNonA2 (φ ⟨g * s * g⁻¹, hzR⟩)
    · exact Or.inl ⟨(hT G M Q Z B hc n t r m K φ u u' hs hr hpts _ hzR hzL hzN).1 hna,
        hE G M Q Z B hc n t r m K φ u u' hs hr hpts _ hzR hzL hzN hna⟩
    · exact Or.inr ⟨(hT G M Q Z B hc n t r m K φ u u' hs hr hpts _ hzR hzL hzN).2 hna,
        hF G M Q Z B hc n t r m K φ u u' hs hr hpts _ hzR hzL hzN hna⟩
  have hbound := sec83_bound_of_parts (x := a * 2 ^ m) hq2 hV1 hW1 hCz hDz hcases
  rcases sec83_arith hm ha hn hbound with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact absurd rfl (hG G M Q Z B hc 7 t hs hpts.spMNat)
  · exact Or.inl ⟨rfl, hpts.spMNat, by rw [hN]; norm_num⟩
  · exact Or.inr ⟨rfl, hpts.spMNat, by rw [hN]; norm_num⟩

end CFSG.RankThree.GF2n.Stroth80
