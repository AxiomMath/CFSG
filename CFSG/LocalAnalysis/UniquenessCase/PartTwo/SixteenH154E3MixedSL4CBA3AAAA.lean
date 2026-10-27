module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8SA3BAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16h_three_dvd_card_of_isSLn_two {X : Type} [Group X] [Finite X]
    (h : IsSLn X 2 2) : 3 ∣ Nat.card X := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hKcard]
  norm_num

theorem s16h_e9_of_commuting_isSLn_two {Q : Type} [Group Q] [Finite Q] {A B : Subgroup Q}
    (hA : IsSLn ↥A 2 2) (hB : IsSLn ↥B 2 2)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∃ E : Subgroup Q, E ≤ A ⊔ B ∧ IsElemAbelian 3 E ∧ 9 ≤ Nat.card ↥E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3A : 3 ∣ Nat.card ↥A := s16h_three_dvd_card_of_isSLn_two hA
  have h3B : 3 ∣ Nat.card ↥B := s16h_three_dvd_card_of_isSLn_two hB
  obtain ⟨a, ha_ord⟩ := exists_prime_orderOf_dvd_card' 3 h3A
  obtain ⟨b, hb_ord⟩ := exists_prime_orderOf_dvd_card' 3 h3B
  have ha1 : a ≠ 1 := (orderOf_eq_prime_iff.mp ha_ord).2
  have ha_pow : (a : Q) ^ 3 = 1 := by
    simpa using congrArg Subtype.val (orderOf_eq_prime_iff.mp ha_ord).1
  have hb_pow : (b : Q) ^ 3 = 1 := by
    simpa using congrArg Subtype.val (orderOf_eq_prime_iff.mp hb_ord).1
  let k : Set Q := {(a : Q), (b : Q)}
  let E : Subgroup Q := Subgroup.closure k
  have ha_mem : (a : Q) ∈ A := a.2
  have hb_mem : (b : Q) ∈ B := b.2
  have ha_mem_E : (a : Q) ∈ E := Subgroup.subset_closure (by simp [k])
  have hb_mem_E : (b : Q) ∈ E := Subgroup.subset_closure (by simp [k])
  have hpair : k.Pairwise Commute := by
    intro y hy z hz _
    simp only [k, Set.mem_insert_iff, Set.mem_singleton_iff] at hy hz
    rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
    · exact Commute.refl _
    · exact hcomm _ ha_mem _ hb_mem
    · exact (hcomm _ ha_mem _ hb_mem).symm
    · exact Commute.refl _
  have hexp : ∀ y ∈ k, y ^ 3 = 1 := by
    intro y hy
    simp only [k, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact ha_pow
    · exact hb_pow
  have hEab : IsElemAbelian 3 E := s16h_sl8_closure_elemAbelian hpair hexp
  have hEsup : E ≤ A ⊔ B := by
    change Subgroup.closure k ≤ A ⊔ B
    rw [Subgroup.closure_le]
    intro y hy
    simp only [k, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Subgroup.mem_sup_left ha_mem
    · exact Subgroup.mem_sup_right hb_mem
  have hcenter : Subgroup.center ↥A = ⊥ :=
    s16h_sl8_center_eq_bot_of_isSLn_two (by norm_num) hA
  have hinf : B ⊓ A = ⊥ :=
    s16h_sl8_inf_eq_bot_of_commute (A := B) (B := A)
      (fun c hc d hd => (hcomm d hd c hc).symm) hcenter
  have ha_notin_B : (a : Q) ∉ B := by
    intro haB
    have hmem : (a : Q) ∈ B ⊓ A := ⟨haB, ha_mem⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact ha1 (Subtype.ext hmem)
  have hEcard : 9 ≤ Nat.card ↥E := by
    have hEp : IsPGroup 3 ↥E := by
      refine IsPGroup.of_exponent_dvd_pow (n := 1) ?_
      rw [pow_one]
      exact Monoid.exponent_dvd_of_forall_pow_eq_one fun y =>
        Subtype.ext (by simpa using hEab.2 (y : Q) y.2)
    obtain ⟨n, hn⟩ := hEp.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      have hEbot : E = ⊥ := Subgroup.eq_bot_of_card_eq E hn
      have hmem : (a : Q) ∈ (⊥ : Subgroup Q) := hEbot ▸ ha_mem_E
      rw [Subgroup.mem_bot] at hmem
      exact ha1 (Subtype.ext hmem)
    have hn1 : n ≠ 1 := by
      rintro rfl
      rw [pow_one] at hn
      have hzple : Subgroup.zpowers (b : Q) ≤ E := Subgroup.zpowers_le.mpr hb_mem_E
      have hcard_zp : Nat.card ↥(Subgroup.zpowers (b : Q)) = 3 := by
        rw [Nat.card_zpowers, orderOf_coe]
        exact hb_ord
      have hEq : Subgroup.zpowers (b : Q) = E :=
        Subgroup.eq_of_le_of_card_ge hzple (by simp [hcard_zp, hn])
      have ha_zp : (a : Q) ∈ Subgroup.zpowers (b : Q) := by
        rw [hEq]
        exact ha_mem_E
      exact ha_notin_B (Subgroup.zpowers_le.mpr hb_mem ha_zp)
    have hn2 : 2 ≤ n := by omega
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      _ = Nat.card ↥E := hn.symm
  exact ⟨E, hEsup, hEab, hEcard⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
