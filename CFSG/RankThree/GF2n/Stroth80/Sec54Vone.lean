module

public import CFSG.RankThree.GF2n.Stroth80.Sec54Order
public import CFSG.RankThree.GF2n.Stroth80.Sec53cVone

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec54_vone_eq_Wt_of_53a (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (h53a : Stroth53aStatement) (hc : Ctx M Q Z B) {n m : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hm : 2 ≤ m) (hV : SpMNat hc t m)
    (hN : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z)
    {r : G} (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    Sec8V1 M Q Z B t r = Sec8W1 M Q Z B t r := by
  classical
  have hsp : SpNat hc t := by
    obtain ⟨K, hK, hKf, hKc, hrep⟩ := hV
    exact ⟨K, hK, hKf, hKc, m, hm, hrep⟩
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hVdef
  set V1 : Subgroup G := Sec8V1 M Q Z B t r with hV1def
  set W : Subgroup G := Wt Q V with hWdef
  set W1 : Subgroup G := Sec8W1 M Q Z B t r with hW1def
  have hn : n = 2 * m + 1 := sec54_n_eq h34 h51 hc hs hm hV hN
  have hVW : V1 ≤ W1 := by
    have := stroth53VW_holds h34 hRoot h51 G M Q Z B hc n t hs hsp r hr hplane
    simpa [hV1def, hW1def] using this
  obtain ⟨hV₁card, hWcard, -⟩ :=
    h53a G M Q Z B hc n t hs hsp r hr hplane (conjSubgroup r B) V W V1 W1
      rfl hVdef.symm hWdef.symm hV1def.symm hW1def.symm
  have hVcard : Nat.card ↥V = Nat.card Z ^ (2 * m + 1) := SpMNat.card_V hV
  have hQcard : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs.width
  have hWmul : Nat.card ↥W * Nat.card ↥V = Nat.card Q * Nat.card Z := hc.card_Wt_mul_card_Vt t
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have h3 : Nat.card ↥W1 * Nat.card Z * Nat.card ↥V = Nat.card Q * Nat.card Z := by
    rw [← hWcard]
    exact hWmul
  rw [hVcard, hQcard, hn] at h3
  have hL : Nat.card ↥W1 * Nat.card Z * Nat.card Z ^ (2 * m + 1) =
      Nat.card ↥W1 * Nat.card Z ^ (2 * m + 2) := by
    rw [mul_assoc, ← pow_succ']
  have hR : Nat.card Z ^ (2 * (2 * m + 1) + 1) * Nat.card Z =
      Nat.card Z ^ (2 * m + 2) * Nat.card Z ^ (2 * m + 2) := by
    rw [← pow_succ]
    congr 1
    ring
  rw [hL, hR] at h3
  have hW1card : Nat.card ↥W1 = Nat.card Z ^ (2 * m + 2) := by
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hZpos _) h3
  have hV1card : Nat.card ↥V1 = Nat.card Z ^ (2 * m + 2) := by
    rw [hV₁card, hVcard, ← pow_succ]
  have hcard : Nat.card ↥W1 ≤ Nat.card ↥V1 := by
    rw [hW1card, hV1card]
  have hEq : V1 = W1 := Subgroup.eq_of_le_of_card_ge hVW hcard
  simpa [hV1def, hW1def] using hEq

end CFSG.RankThree.GF2n.Stroth80
