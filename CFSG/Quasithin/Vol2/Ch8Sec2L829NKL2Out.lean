module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKL2OutE2
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKDefs

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique GorensteinWalter Subgroup
open CFSG.Quasithin.H13.L829NK.L2Out
open CFSG.ComponentClassification.AutL2Facts

theorem fix_of_centralizer {X : Type} [Group X] (S : Subgroup X) (y : MulAut X)
    (hfix : ∀ b ∈ centralizer ((S ⊓ centralizer (S : Set X) : Subgroup X) : Set X), y b = b) :
    ∀ s ∈ S, y s = s := by
  intro s hs
  apply hfix
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hz' : z ∈ (S ⊓ centralizer (S : Set X) : Subgroup X) := hz
  rw [Subgroup.mem_inf] at hz'
  exact (Subgroup.mem_centralizer_iff.mp hz'.2 s hs).symm

theorem nk_l2_out :
    ∀ (p e : ℕ), p.Prime → 3 < p → (e = 1 ∨ e = 2) → (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) →
      p ^ e ≠ 7 → p ^ e ≠ 25 → ∀ (X : Type) [Group X], IsPSL 2 p e X →
        ∀ S : Subgroup X, IsSylowTwoOf S ⊤ →
          UOut X (Subgroup.centralizer ((S ⊓ Subgroup.centralizer (S : Set X) : Subgroup X) : Set X)) := by
  intro p e hp h3 he h8 h7 h25 X _ hX S hS
  unfold UOut
  intro y hy hfix
  have hL : CFSG.Blueprint.LieModel X .PSL 2 p e := Or.inl ⟨by decide, hX⟩
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨φ⟩⟩ := lieModel_psl2_data hL
  have hi : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  let Q : Sylow 2 X := hS.2.1.toSylow hi
  have hQS : (Q : Subgroup X) = S := rfl
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite X := Finite.of_equiv _ φ.symm.toEquiv
  have hp2 : p ≠ 2 := by omega
  rcases he with rfl | rfl
  ·
    have hodd : IsOddPrimePower (Nat.card F) := isOddPrimePower_of hp hp2 le_rfl hF
    have h16 : Nat.card F ^ 2 % 16 = 1 := by
      rw [hF, pow_one]
      exact sq_mod_sixteen_of_mod_eight (by simpa using h8)
    have h8X : 8 ∣ Nat.card X := by
      rw [Nat.card_congr φ.toEquiv]
      exact eight_dvd_card_PSL2 hodd h16
    have hQ8 : 8 ≤ Nat.card Q := eight_le_card_sylow Q h8X
    exact core hodd φ Q hQ8 y hy (fix_of_centralizer S y hfix)
      (right_one_of_odd hp hF odd_one φ y hy)
  ·
    have hodd : IsOddPrimePower (Nat.card F) := isOddPrimePower_of hp hp2 (by norm_num) hF
    have h16 : Nat.card F ^ 2 % 16 = 1 := by
      rw [hF]
      exact sq_mod_sixteen_of_mod_eight
        (Or.inl (sq_mod_eight_of_odd (Nat.odd_iff.mp (hp.odd_of_ne_two hp2))))
    have h8X : 8 ∣ Nat.card X := by
      rw [Nat.card_congr φ.toEquiv]
      exact eight_dvd_card_PSL2 hodd h16
    have hQ8 : 8 ≤ Nat.card Q := eight_le_card_sylow Q h8X
    have hp7 : 7 ≤ p := by
      rcases (show p = 4 ∨ p = 5 ∨ p = 6 ∨ 7 ≤ p by omega) with h | h | h | h
      · exact absurd hp (by rw [h]; norm_num)
      · exact absurd (show p ^ 2 = 25 by rw [h]; norm_num) h25
      · exact absurd hp (by rw [h]; norm_num)
      · exact h
    haveI : CharP F p := charP_of_card_sq hp hF
    have hfixQ := fix_of_centralizer S y hfix
    exact core hodd φ Q hQ8 y hy hfixQ (right_one_e2 hp hp7 hF φ Q hQ8 y hy hfix)

end CFSG.Quasithin.H13.L829NK
