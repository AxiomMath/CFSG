module

public import CFSG.RankThree.GF2n.Stroth80.Sec53Hbound

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec54_n_eq (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hm : 2 ≤ m)
    (hV : SpMNat hc t m)
    (hN : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z) :
    n = 2 * m + 1 := by
  classical
  have hRoot : Stroth310RootStatement := stroth310Root_of_34 h34
  have hVkeep : SpMNat hc t m := hV
  have hsp : SpNat hc t := by
    obtain ⟨K, iF, iFin, hK, hrep⟩ := hVkeep
    exact ⟨K, iF, iFin, hK, m, hm, hrep⟩
  obtain ⟨r, hr, hplane, -⟩ := hc.exists_hypPlane_sp h34 hRoot hs hsp
  obtain ⟨-, hcardI, -, hopp⟩ :=
    h51 G M Q Z B hc n t hs (Or.inl hsp) r hr hplane
      (conjSubgroup r B) (LB M Q B) (LB M Q (conjSubgroup r B)) (hc.CN t)
      (Rt M (LB M Q B) t) rfl rfl rfl rfl rfl
  have hIN : LB M Q B ⊓ LB M Q (conjSubgroup r B) ≤ hc.CN t :=
    hopp.1.trans hopp.2.1
  have hIeqN : LB M Q B ⊓ LB M Q (conjSubgroup r B) = hc.CN t := by
    refine Subgroup.eq_of_le_of_card_ge hIN ?_
    rw [hcardI, hN]
  have hNI : hc.CN t ≤ LB M Q B := by
    rw [← hIeqN]
    exact hopp.1.trans inf_le_left
  have hAeqN : LB M Q B ⊓ hc.CN t = hc.CN t :=
    le_antisymm inf_le_right (le_inf hNI le_rfl)
  have hcard := Ctx.card_LB_inf_CN_sp h34 hc hs hm hV
  rw [hAeqN] at hcard
  have hN' : Nat.card ↥(hc.CN t) =
      Nat.card Z ^ (2 * n + 1) * Nat.card Z := by
    rw [hN, hs.width]
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hpow : Nat.card Z ^ (n - 2 * m) = Nat.card Z ^ 1 := by
    have h := hcard.symm.trans hN'
    have h' : Nat.card Z ^ (2 * n + 1) * Nat.card Z ^ (n - 2 * m) =
        Nat.card Z ^ (2 * n + 1) * Nat.card Z ^ 1 := by
      simpa [pow_one] using h
    exact Nat.eq_of_mul_eq_mul_left
      (pow_pos (Nat.card_pos (α := ↥Z)) (2 * n + 1)) h'
  have hexp : n - 2 * m = 1 := Nat.pow_right_injective hq2 hpow
  omega

end CFSG.RankThree.GF2n.Stroth80
