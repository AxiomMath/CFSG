module

public import CFSG.Quasithin.Background.E2TwoProofOddB

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace E2P

theorem pow_mod_eight_cases {p f : ℕ} (hp : Odd p) :
    p ^ f % 8 = 1 ∨ p ^ f % 8 = 3 ∨ p ^ f % 8 = 5 ∨ p ^ f % 8 = 7 := by
  have h := Nat.odd_iff.mp (hp.pow (n := f))
  omega

theorem e22OddL2Fam :
    E22OddL2Fam := by
  intro X _ _ K T M hX p f hp hp2 hf h5 h9 h
  have : Fact p.Prime := ⟨hp⟩
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  rcases pow_mod_eight_cases (f := f) hpo with h8 | h8 | h8 | h8
  rotate_left
  ·
    exfalso
    by_cases h11 : 11 ≤ p ^ f
    · exact hX.false_of_psl2_three_mod_eight hpo h h11 (Or.inl h8)
    ·
      have hq3 : p ^ f = 3 := by
        have : 3 ≤ p ^ f :=
          le_trans hp3 (Nat.le_self_pow (by rcases hf with rfl | rfl <;> norm_num) p)
        omega
      obtain ⟨hf0, -, -, -, -, -, ⟨e⟩⟩ := exists_psl2_galois_equiv h
      have hcK : Nat.card ↥K = 2 ^ 2 * 3 ^ 1 := by
        rw [Nat.card_congr e.toEquiv]
        have h1 := Glauberman.Dickson.MaxUp.card_psl2_galoisField hp2 hf0.ne'
        rw [h1, pow_mul', ← pow_mul, mul_comm, pow_mul, hq3]
        norm_num
      have hsolv := Vol2Native.A312L.isSolvable_of_card_two_three hcK
      have := hX.simple
      obtain ⟨a, b, hab⟩ := hX.nonab
      exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) a b)
  ·
    exfalso
    by_cases h11 : 11 ≤ p ^ f
    · exact hX.false_of_psl2_three_mod_eight hpo h h11 (Or.inr h8)
    · have : 3 ≤ p ^ f :=
        le_trans hp3 (Nat.le_self_pow (by rcases hf with rfl | rfl <;> norm_num) p)
      omega
  all_goals
    have h8' : p ^ f % 8 = 1 ∨ p ^ f % 8 = 7 := by omega
    obtain ⟨hC, hA⟩ := hX.oddL2_of_one_mod_eight hpo h h8' h9
    refine ⟨?_, h8', hC, hA⟩
    by_contra hle
    have hp3' : p = 3 := by omega
    subst hp3'
    rcases hf with rfl | rfl
    · norm_num at h8'
    · exact h9 rfl

end E2P

end CFSG.Quasithin
