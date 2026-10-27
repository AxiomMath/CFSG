module

public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Sporadic.J1.Setup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

theorem a38d_three_dvd_mul_sq_sub_one (p : ℕ) : 3 ∣ p * (p ^ 2 - 1) := by
  by_cases h : 3 ∣ p
  · exact Dvd.dvd.mul_right h _
  · refine Dvd.dvd.mul_left ?_ p
    have h1 : p % 3 = 1 ∨ p % 3 = 2 := by omega
    have h2 : p ^ 2 % 3 = 1 := by rcases h1 with h1 | h1 <;> simp [Nat.pow_mod, h1]
    omega

theorem a38d_three_dvd_card_psl_two_two {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X) :
    3 ∣ Nat.card X :=
  CFSG.Open.StatedAPI.three_dvd_card_of_statedClassicalModel_psl_two_two h

theorem a38d_three_dvd_card_psl_odd {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsPSL 2 p 1 X) : 3 ∣ Nat.card X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK' : Nat.card K = p := by simpa using hK
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hfm := CFSG.GorensteinWalter.psl2_card_formula K ⟨p, 1, hp, hodd, le_rfl, by simpa using hK⟩
  rw [Nat.card_congr (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).toEquiv,
    hfm, hK']
  have h2 : 2 ∣ p * (p ^ 2 - 1) :=
    dvd_mul_of_dvd_right (even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd.pow odd_one)) _
  have h3 : 3 ∣ 2 * (p * (p ^ 2 - 1) / 2) := by
    rw [Nat.mul_div_cancel' h2]
    exact a38d_three_dvd_mul_sq_sub_one p
  exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 3 2) h3

theorem a38d_three_dvd_card_j1 {X : Type} [Group X] (h : IsSporadic .J1 X) : 3 ∣ Nat.card X := by
  obtain ⟨e⟩ := h
  have hc : Nat.card X = Nat.card CFSG.Sporadic.J1.J :=
    Nat.card_congr (e.toEquiv.trans CFSG.Sporadic.J1.nativeEquiv.toEquiv)
  have hd := orderOf_dvd_natCard CFSG.Sporadic.J1.b
  rwa [CFSG.Sporadic.J1.orderOf_b, ← hc] at hd

theorem a38_three_dvd {X : Type} [Group X] (h : A38Types X) (hsz : ¬ ∃ n, IsSz n X) :
    3 ∣ Nat.card X := by
  rcases h with ⟨n, hn⟩ | hs | hJ | ⟨p, hp, hp3, hpsl⟩
  · exact a38d_three_dvd_card_psl_two_two hn
  · exact absurd hs hsz
  · exact a38d_three_dvd_card_j1 hJ
  · exact a38d_three_dvd_card_psl_odd hp (by omega) hpsl

end CFSG.Quasithin
