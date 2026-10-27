module

public import CFSG.RankThree.GF2n.Stroth80.Sec711Setup
public import CFSG.RankThree.GF2n.Stroth80.Sec83Card
public import CFSG.RankThree.GF2n.Stroth80.Sec7Transport

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem n12N_arith {q n m N Qc V W : ℕ} (hq : 4 ≤ q) (hQc : Qc = q ^ (2 * n + 1))
    (hN : N * q ^ (4 * m) = Qc ^ 2) (hlarge : Qc * q < N)
    (hV : V = q * q ^ (2 * m)) (hchi : Qc * q = W * V) (hWV : W = V) : False := by
  subst hQc
  subst hV
  subst hWV
  have hp : q ^ (2 * n + 2) = q ^ (4 * m + 2) := by
    calc q ^ (2 * n + 2) = q ^ (2 * n + 1) * q := by ring
      _ = q * q ^ (2 * m) * (q * q ^ (2 * m)) := hchi
      _ = q ^ (4 * m + 2) := by ring
  have h2 : 2 * n + 2 = 4 * m + 2 := Nat.pow_right_injective (by omega) hp
  have h3 : q ^ (2 * n + 1) * q * q ^ (4 * m) < N * q ^ (4 * m) :=
    mul_lt_mul_of_pos_right hlarge (pow_pos (by omega) _)
  have e1 : q ^ (2 * n + 1) * q * q ^ (4 * m) = q ^ (2 * n + 2 + 4 * m) := by ring
  have e2 : (q ^ (2 * n + 1)) ^ 2 = q ^ (4 * n + 2) := by ring
  rw [hN, e1, e2] at h3
  have h4 : 2 * n + 2 + 4 * m < 4 * n + 2 := by
    by_contra hcon
    exact absurd h3 (not_lt.2 (Nat.pow_le_pow_right (by omega) (by omega)))
  omega

theorem n12N_card_V {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} (hc : Ctx M Q Z B)
    (t : G) (m : ℕ) (hm : 2 ≤ m) (hmO : OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) :
    Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card ↥Z * Nat.card ↥Z ^ (2 * m) := by
  rcases hmO with ⟨K, _, _, hK, hrep⟩ | ⟨K, _, _, hK, b, c, _, hrep⟩
  · have hcard := card_of_naturalRep hrep sec39_Z_le_Vt hK
    have hι : Fintype.card (Fin m ⊕ Fin m) = 2 * m := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι] at hcard
    exact hcard
  · have hcard := card_of_naturalRep hrep sec39_Z_le_Vt hK
    have hι : Fintype.card (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) = 2 * m := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι] at hcard
    exact hcard

theorem n12WneV_of (hNO : Sec7NOrderStatement) (h52c : Stroth52cStatement) :
    N12WneVStatement := by
  intro G _ _ M Q Z B hc n t hs hWV
  obtain ⟨m, hm, hmO⟩ := hs.orth
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  haveI : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hVQ hv)))
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hchi := card_mul_card_of_isChiIso
    (h52c G M Q Z B hc n t hs.toSec5 hs.omegaNat (Rt M (LB M Q B) t)
      (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl)
    hWQ sec39_Z_le_Vt
  have hWVn : Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) =
      Nat.card ↥(Vt M (LB M Q B) B Z t) :=
    congrArg (fun H : Subgroup G => Nat.card ↥H) hWV
  have hQc : Nat.card ↥Q = Nat.card ↥Z ^ (2 * n + 1) := hs.toSec5.width
  have hN : Nat.card ↥(hc.CN t) * Nat.card ↥Z ^ (4 * m) = Nat.card ↥Q ^ 2 :=
    hNO G M Q Z B hc n t hs m hm hmO
  have hV := n12N_card_V hc t m hm hmO
  exact n12N_arith hc.hyp.q4 hQc hN hs.large hV hchi hWVn

end CFSG.RankThree.GF2n.Stroth80
