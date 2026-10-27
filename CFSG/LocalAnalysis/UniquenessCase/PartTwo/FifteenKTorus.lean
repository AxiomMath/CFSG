module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOuterSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s15k_tor_sylow {H : Type} [Group H] [Finite H] {p e : ℕ} [Fact p.Prime]
    (hH : (Nat.card H).factorization p = e) :
    (∀ B : Subgroup H, IsPGroup p B → Nat.card B ≤ p ^ e) ∧
    ∀ A B : Subgroup H, IsPGroup p A → Nat.card A = p ^ e → IsPGroup p B →
      ∃ h : H, B.map (MulAut.conj h).toMonoidHom ≤ A := by
  refine ⟨fun B hB => ?_, fun A B _ hAc hB => ?_⟩
  · obtain ⟨Q, hQ⟩ := hB.exists_le_sylow
    calc Nat.card B ≤ Nat.card (Q : Subgroup H) := Subgroup.card_le_of_le hQ
      _ = p ^ e := by rw [Sylow.card_eq_multiplicity Q, hH]
  · let P : Sylow p H := Sylow.ofCard A (by rw [hH]; exact hAc)
    obtain ⟨Q, hQ⟩ := hB.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q P
    have hmapped := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hQ
    have hQmap := congrArg (fun R : Sylow p H => (R : Subgroup H)) hg
    change (Q : Subgroup H).map (MulAut.conj g).toMonoidHom = A at hQmap
    exact ⟨g, hQmap ▸ hmapped⟩

private theorem s15k_tor_factorization {N k e : ℕ} (hN : N ≠ 0) (h1 : 3 ^ e ∣ N)
    (h2 : ¬ 3 ^ (e + 1) ∣ N) : (N * 2 ^ k).factorization 3 = e := by
  have hv1 : e ≤ N.factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hN).mp h1
  have hv2 : N.factorization 3 < e + 1 := by
    by_contra hcon
    exact h2 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hN).mpr (not_lt.mp hcon))
  rw [Nat.factorization_mul hN (by positivity), Finsupp.add_apply, Nat.factorization_pow]
  simp [Nat.prime_two.factorization]
  omega

theorem rTorus3_153_holds : RTorus3_153 := by
  intro S H _ _ _ _ f hf hn hc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : Odd 3 := by decide
  refine ⟨fun hS => ?_, fun hΩ => ?_⟩
  · have hex : s15ExcList S := by
      rcases hS with h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inl h)
    obtain ⟨k, hk⟩ := s15k_six_index_pow f hf hn hc hex
    have hcard : Nat.card H = Nat.card S * 2 ^ k := by
      rw [← s15k_out_card_eq f hf, hk]
    have hN : Nat.card S = 360 ∨ Nat.card S = 2520 ∨ Nat.card S = 20160 := by
      rcases hS with h | h | h
      · refine Or.inl ?_
        rw [s15k_six_alt_card h (by norm_num)]
        norm_num [Nat.factorial]
      · refine Or.inr (Or.inl ?_)
        rw [s15k_six_alt_card h (by norm_num)]
        norm_num [Nat.factorial]
      · exact Or.inr (Or.inr (s15k_six_l4 h).1)
    have hfac : (Nat.card H).factorization 3 = 2 := by
      rw [hcard]
      rcases hN with hN | hN | hN <;> rw [hN] <;>
        exact s15k_tor_factorization (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨h1, h2⟩ := s15k_tor_sylow hfac
    refine ⟨fun B hB => ?_, fun A B hA hAc hB _ => ?_⟩
    · simpa using h1 B hB.isPGroup
    · exact h2 A B hA.isPGroup (by rw [hAc]; norm_num) hB.isPGroup
  · obtain ⟨k, hk⟩ := s15k_six_index_pow f hf hn hc
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hΩ)))))
    refine ⟨fun B hB => ?_, fun A B hA hAc hB _ => ?_⟩
    · obtain ⟨B', hB', -, hcB⟩ :=
        s15k_out_elem_comap f hf hB (s15k_out_elem_le_range f hn hk hodd hB)
      rw [← hcB]
      exact s15k_om6_card_le hΩ B' hB'
    · obtain ⟨A', hA', hAmap, hAcard⟩ :=
        s15k_out_elem_comap f hf hA (s15k_out_elem_le_range f hn hk hodd hA)
      obtain ⟨B', hB', hBmap, -⟩ :=
        s15k_out_elem_comap f hf hB (s15k_out_elem_le_range f hn hk hodd hB)
      obtain ⟨x, hx⟩ := s15k_om6_conj_into hΩ A' B' hA' (hAcard.trans hAc) hB'
      refine ⟨f x, ?_⟩
      rw [← hAmap, ← hBmap]
      have hmap : (B'.map f).map (MulAut.conj (f x)).toMonoidHom =
          (B'.map (MulAut.conj x).toMonoidHom).map f := by
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
        ext y
        simp [MulAut.conj_apply]
      rw [hmap]
      exact Subgroup.map_mono hx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
