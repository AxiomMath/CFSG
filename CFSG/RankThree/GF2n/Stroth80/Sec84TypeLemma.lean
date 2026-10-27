module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Stroth80.Sec83Upper

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

theorem sec83_bound_nonA2 {q m x cQ cV cW cV1 cW1 : ℕ} (hq : 2 ≤ q)
    (hV1 : cV1 = q ^ (2 * m + 2)) (hW1 : cW1 = cV1 * q ^ x) (hC : cQ ≤ q ^ (2 * m + 1))
    (hD : cV ^ 2 * cW ≤ cQ * q * cV1) (hv : cV = q ^ 2 ∨ cV = q ^ 3)
    (hE : cW ^ 2 = cV1 * cW1) : x + 4 ≤ 4 * m := by
  have hq1 : 1 < q := hq
  have hqpos : 0 < q := by omega
  have hV1pos : 0 < cV1 := by rw [hV1]; positivity
  have hD' : cV ^ 2 * cW ≤ q ^ (2 * m + 2) * cV1 := by
    calc cV ^ 2 * cW ≤ cQ * q * cV1 := hD
      _ ≤ q ^ (2 * m + 1) * q * cV1 := by gcongr
      _ = q ^ (2 * m + 2) * cV1 := by ring
  have hv2 : q ^ 2 ≤ cV := by
    rcases hv with h | h
    · exact h.ge
    · rw [h]; exact Nat.pow_le_pow_right hqpos (by norm_num)
  have h1 : q ^ 4 * cW ≤ q ^ (2 * m + 2) * cV1 := by
    calc q ^ 4 * cW = (q ^ 2) ^ 2 * cW := by ring
      _ ≤ cV ^ 2 * cW := by gcongr
      _ ≤ q ^ (2 * m + 2) * cV1 := hD'
  have h2 : (q ^ 4 * cW) ^ 2 ≤ (q ^ (2 * m + 2) * cV1) ^ 2 := Nat.pow_le_pow_left h1 2
  have h3 : q ^ (8 + x) * cV1 ^ 2 ≤ q ^ (4 * m + 4) * cV1 ^ 2 := by
    calc q ^ (8 + x) * cV1 ^ 2 = q ^ 8 * (cV1 * cW1) := by rw [hW1]; ring
      _ = q ^ 8 * cW ^ 2 := by rw [hE]
      _ = (q ^ 4 * cW) ^ 2 := by ring
      _ ≤ (q ^ (2 * m + 2) * cV1) ^ 2 := h2
      _ = q ^ (4 * m + 4) * cV1 ^ 2 := by ring
  have h4 : q ^ (8 + x) ≤ q ^ (4 * m + 4) := Nat.le_of_mul_le_mul_right h3 (by positivity)
  have h5 := (Nat.pow_le_pow_iff_right hq1).mp h4
  omega

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec84_not_nonA2 (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (h53 : Stroth53Statement) (hPts : Sec5NatPointsSpStatement) (hA : Sec8AExistsStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {r : G} (hr : Sec7A hc t r)
    {K : Type} [Field K] [Finite K] {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 4 ⊕ Fin 4) K}
    {u u' : Fin 4 ⊕ Fin 4 → K} (hpts : Sec8Pts hc t r 4 K φ u u')
    (hN : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ 17)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {s : G} (hsZ : s ∈ Z0)
    {g : G} (hg : g ∈ M) (hzL : g * s * g⁻¹ ∈ LB M Q B) (hzN : g * s * g⁻¹ ∉ hc.CN t) :
    ¬ SpNonA2 (φ ⟨g * s * g⁻¹, le_Rt (M := M) (LB M Q B) hs.toSec5.mem hzL⟩) := by
  intro hna
  have hs5 := hs.toSec5
  have hInv := sec8InvStatement_holds
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hm4 : (4 : ℕ) = 4 := rfl
  obtain ⟨a, hn, hV1, hW1⟩ := sec83_count_A h53 hInv hs5 hr hpts
  have hNB := sec83_count_B h34 h51 hs5 hr hpts (e := a * 2 ^ 4) (by omega)
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hpow : Nat.card Z ^ (a * 2 ^ 4 + 1) = Nat.card Z ^ 17 := by
    have h1 : Nat.card Q * Nat.card Z ^ (a * 2 ^ 4 + 1) = Nat.card Q * Nat.card Z ^ 17 := by
      rw [← hNB, hN]
    exact Nat.eq_of_mul_eq_mul_left hQpos h1
  have ha16 : a * 2 ^ 4 + 1 = 17 := Nat.pow_right_injective hq2 hpow
  have hzR : g * s * g⁻¹ ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs5.mem hzL
  have hsR : s ∈ Rt M (LB M Q B) t := hZ0.le hsZ
  have hCz : Nat.card ↥(Ut Q Z (g * s * g⁻¹)) ≤ Nat.card Z ^ (2 * 4 + 1) := by
    rw [card_Ut_conj hc hg s]
    exact sec83Upper_of_53 h34 h53 hA hPts G M Q Z B hc n t 4 hs5 hpts.two_le hpts.spMNat s hsR
      (fun ρ hρ => hZ0.comm_mem hsZ hρ)
  have hDz := sec83Lower_of_53 h53 hInv G M Q Z B hc n t hs r hr (g * s * g⁻¹) hzL
  have hT := (sec83Type_of_nat G M Q Z B hc n t r 4 K φ u u' hs5 hr hpts _ hzR hzL hzN).1 hna
  have hE := sec83Fixed_of_53 h53 hInv G M Q Z B hc n t r 4 K φ u u' hs5 hr hpts _ hzR hzL hzN
    hna
  have hbound := sec83_bound_nonA2 (x := a * 2 ^ 4) hq2 hV1 hW1 hCz hDz hT hE
  omega

end CFSG.RankThree.GF2n.Stroth80
