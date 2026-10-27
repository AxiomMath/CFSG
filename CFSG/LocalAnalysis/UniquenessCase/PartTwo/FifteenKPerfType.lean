module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKPerfOrdLn
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKPerfOrdSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKPerfOrdOmP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKPerfOrdOmM
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOuterSix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s15k_ptype_fact {n N : ℕ} (hn : 5 ≤ n) (h : n.factorial / 2 = N) :
    (N = 60 → n = 5) ∧ (N = 360 → n = 6) ∧ (N = 2520 → n = 7) ∧ N ≠ 168 ∧ N ≠ 25920 := by
  rcases Nat.lt_or_ge n 9 with h8 | h9
  · interval_cases n <;> simp [Nat.factorial] at h <;> omega
  · have h1 : Nat.factorial 9 ≤ n.factorial := Nat.factorial_le h9
    have h2 : Nat.factorial 9 = 362880 := by decide
    omega

private theorem s15k_ptype_cases {V : Type} [CommGroup V] {X : Type} [Group X]
    {K : Subgroup (MulAut V)} {Z : Subgroup V} (h : s15KNatPerf X K Z) :
    (∃ n : ℕ, 3 ≤ n ∧ BinaryNaturalSL K Z ⊥ n 1 ∧
      ((n = 3 ∧ Nat.card X = 168) ∨ (n = 4 ∧ Nat.card X = 20160) ∨
        (5 ≤ n ∧ 2 ^ 7 ∣ Nat.card X))) ∨
    2 ^ 7 ∣ Nat.card X ∨
    (Nat.card X = 20160 ∨ 2 ^ 7 ∣ Nat.card X) ∨
    ((NatOmegaMinus K Z ⊥ 6 1 ∧ Nat.card X = 25920) ∨ 2 ^ 7 ∣ Nat.card X) ∨
    (∃ n : ℕ, 5 ≤ n ∧ AlternatingNatural K Z ⊥ n ∧ Nat.card X = n.factorial / 2) := by
  rcases h with ⟨n, hn, hX, hZ⟩ | ⟨n, hn, hX, hZ⟩ | ⟨n, hn, hX, hZ⟩ | ⟨n, hn, hX, hZ⟩ |
    ⟨n, hn, hX, hZ⟩
  · obtain ⟨h3, h4, h5⟩ := s15k_pord_ln hn hX
    refine Or.inl ⟨n, hn, hZ, ?_⟩
    rcases Nat.lt_or_ge n 5 with h5' | h5'
    · rcases (by omega : n = 3 ∨ n = 4) with rfl | rfl
      · exact Or.inl ⟨rfl, h3 rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, h4 rfl⟩)
    · exact Or.inr (Or.inr ⟨h5', h5 h5'⟩)
  · exact Or.inr (Or.inl (s15k_pord_sp hn hX))
  · obtain ⟨m, hm⟩ := hX.1
    obtain ⟨h6, h8⟩ := s15k_pord_omega_plus hn hX
    rcases (by omega : n = 6 ∨ 8 ≤ n) with h | h
    · exact Or.inr (Or.inr (Or.inl (Or.inl (h6 h))))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (h8 h))))
  · obtain ⟨m, hm⟩ := hX.1
    rcases (by omega : n = 6 ∨ 8 ≤ n) with rfl | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨hZ, (s15k_six_om6 hX).1⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (s15k_pord_omega_minus h hX)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, hn, hZ, s15k_six_alt_card hX (by omega)⟩)))

theorem rPerfType153_holds : RPerfType153 := by
  intro V _ X _ K Z h
  have hc := s15k_ptype_cases h
  refine ⟨fun hX => ?_, fun hX => ?_, fun hX => ?_, fun hX => ?_, fun hX => ?_⟩
  · have hN : Nat.card X = 168 := (s15k_pord_ln (n := 3) le_rfl hX).1 rfl
    rcases hc with ⟨n, hn, hZ, ⟨rfl, -⟩ | ⟨rfl, h4⟩ | ⟨h5, h7⟩⟩ | h7 | h | h | ⟨n, hn, hZ, hf⟩
    · exact hZ
    · omega
    · omega
    · omega
    · omega
    · rcases h with ⟨-, h⟩ | h <;> omega
    · exact absurd rfl (s15k_ptype_fact hn (hf.symm.trans hN)).2.2.2.1
  · have hN : Nat.card X = 60 := by
      rw [s15k_six_alt_card hX (by norm_num)]
      norm_num [Nat.factorial]
    rcases hc with ⟨n, hn, hZ, ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨h5, h7⟩⟩ | h7 | h | h | ⟨n, hn, hZ, hf⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · rcases h with ⟨-, h⟩ | h <;> omega
    · obtain rfl : n = 5 := (s15k_ptype_fact hn (hf.symm.trans hN)).1 rfl
      exact hZ
  · have hN : Nat.card X = 360 := by
      rw [s15k_six_alt_card hX (by norm_num)]
      norm_num [Nat.factorial]
    rcases hc with ⟨n, hn, hZ, ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨h5, h7⟩⟩ | h7 | h | h | ⟨n, hn, hZ, hf⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · rcases h with ⟨-, h⟩ | h <;> omega
    · obtain rfl : n = 6 := (s15k_ptype_fact hn (hf.symm.trans hN)).2.1 rfl
      exact hZ
  · have hN : Nat.card X = 2520 := by
      rw [s15k_six_alt_card hX (by norm_num)]
      norm_num [Nat.factorial]
    rcases hc with ⟨n, hn, hZ, ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨h5, h7⟩⟩ | h7 | h | h | ⟨n, hn, hZ, hf⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · rcases h with ⟨-, h⟩ | h <;> omega
    · obtain rfl : n = 7 := (s15k_ptype_fact hn (hf.symm.trans hN)).2.2.1 rfl
      exact hZ
  · have hN : Nat.card X = 25920 := (s15k_six_om6 hX).1
    rcases hc with ⟨n, hn, hZ, ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨h5, h7⟩⟩ | h7 | h | h | ⟨n, hn, hZ, hf⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · rcases h with ⟨hZ, -⟩ | h
      · exact hZ
      · omega
    · exact absurd rfl (s15k_ptype_fact hn (hf.symm.trans hN)).2.2.2.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
