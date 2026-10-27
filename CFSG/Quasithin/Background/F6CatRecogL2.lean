module

public import CFSG.Quasithin.Background.F6CatRecogSetting
public import CFSG.Milestones.LR_dihedral_simple_recognition

public section

namespace CFSG.Quasithin

namespace F6

open CFSG.Assembly.LowTwoRank

variable {D : Type} [Group D] [Finite D]

theorem psl_two_of_card_inf_eq_four
    (hS : F618RecogSettingSQT D) (S : Sylow 2 D)
    (h4 : Nat.card ↥((S : Subgroup D) ⊓ twoResidual ⊤) = 4) :
    ∃ (p : ℕ) (K : Type) (_ : Field K) (_ : Finite K), p.Prime ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
      5 ≤ p ∧ Nat.card K = p ∧ StatedLieAdmissible .PSL 2 p 1 ∧
      Subgroup.center ↥(twoResidual (⊤ : Subgroup D)) = ⊥ ∧
      Nonempty (TwoResidualQuot D ≃* StatedProj (StatedSL 2 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, ⟨eQ⟩⟩ := exists_sylow_quotient_of_setting hS.toF618RecogSetting S
  have : IsSimpleGroup (TwoResidualQuot D) := hS.quasisimple.2.1
  have hnonab : ∃ a b : TwoResidualQuot D, a * b ≠ b * a := hS.quasisimple.2.2
  have hQ4 : Nat.card (Q : Subgroup (TwoResidualQuot D)) = 4 := by
    rw [← Nat.card_congr eQ.toEquiv, h4]
  have : IsKleinFour (Q : Subgroup (TwoResidualQuot D)) :=
    isKleinFour_of_card_four hQ4 (not_isCyclic_sylow_two hnonab Q).1
  have eQ' : Nonempty ((Q : Subgroup (TwoResidualQuot D)) ≃* DihedralGroup (2 ^ (2 - 1))) := by
    rw [show (2 : ℕ) ^ (2 - 1) = 2 by norm_num]
    exact IsKleinFour.nonempty_mulEquiv
  rcases CFSG.Milestones.lr_dihedral_simple_recognition (TwoResidualQuot D) hnonab Q 2 le_rfl
      eQ' with ⟨p, f, hp, hp2, -, hadm, K, _, _, hK, ⟨eK⟩⟩ | he7
  · have : Fact p.Prime := ⟨hp⟩
    have : Group.IsPerfect ↥(twoResidual (⊤ : Subgroup D)) := hS.quasisimple.1
    have hcard := card_twoResidualQuot hp hp2 hK eK
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5 := by
      by_contra hne
      have h17 : p ^ f % 8 = 1 ∨ p ^ f % 8 = 7 := by
        obtain ⟨m, hm⟩ := hodd
        omega
      have h := eight_dvd_card_psl_two h17
      rw [← hcard] at h
      have h' := Sylow.pow_dvd_card_of_pow_dvd_card (P := Q) (n := 3) (by simpa using h)
      rw [hQ4] at h'
      norm_num at h'
    have hf2 := le_two_of_isStronglyQuasithin hS.sqt hp hp2 hK eK
    have hf1 : f = 1 := by
      have hf : 1 ≤ f := hadm.2.1
      interval_cases f
      · rfl
      · have := odd_sq_mod_eight (hp.odd_of_ne_two hp2)
        omega
    subst hf1
    rw [pow_one] at hK h8
    have hp3 : p ≠ 3 := by
      intro h3
      subst h3
      exact hadm.2.2.2.2 rfl
    have h5 : 5 ≤ p := by
      have := hp.two_le
      have : p ≠ 4 := by rintro rfl; norm_num at hp
      omega
    have hZ := (center_of_quotient_psl_two hS.center hp2 (by rw [hK, pow_one]) eK).1
      (by rw [pow_one]; omega)
    exact ⟨p, K, inferInstance, inferInstance, hp, h8, h5, hK, hadm, hZ, ⟨eK⟩⟩
  · exfalso
    obtain ⟨e7⟩ := he7
    have h := Sylow.pow_dvd_card_of_pow_dvd_card (P := Q) (n := 3)
      (by rw [Nat.card_congr e7.toEquiv, card_alternating_seven]; norm_num)
    rw [hQ4] at h
    norm_num at h

theorem f618RecogE4_of_sqt
    (D : Type) [Group D] [Finite D] (hS : F618RecogSettingSQT D)
    (hT : ∃ S : Sylow 2 D, Nonempty (↥S ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    ∃ p : ℕ, p.Prime ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsL2 p 1 D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, ⟨eS⟩⟩ := hT
  have hS4 : Nat.card (S : Subgroup D) = 4 := (Nat.card_congr eS.toEquiv).trans (by simp)
  have : IsSimpleGroup (TwoResidualQuot D) := hS.quasisimple.2.1
  have hP : Nat.card ↥((S : Subgroup D) ⊓ twoResidual ⊤) = 4 := by
    obtain ⟨Q, ⟨eQ⟩⟩ := exists_sylow_quotient_of_setting hS.toF618RecogSetting S
    have h4 := (not_isCyclic_sylow_two hS.quasisimple.2.2 Q).2
    rw [← Nat.card_congr eQ.toEquiv] at h4
    exact Nat.dvd_antisymm (hS4 ▸ Subgroup.card_dvd_of_le inf_le_left) h4
  obtain ⟨p, K, _, _, hp, hp8, -, hK, hadm, hZ, ⟨eK⟩⟩ := psl_two_of_card_inf_eq_four hS S hP
  have := twoResidual_top_normal (D := D)
  obtain ⟨n, hn⟩ := exists_index_twoResidual_eq (D := D)
  have h := card_sylow_eq_mul_index (twoResidual ⊤) hn S
  rw [hS4, hP] at h
  have hn0 : 2 ^ n = 1 := by omega
  have hL : twoResidual (⊤ : Subgroup D) = ⊤ := by rw [← Subgroup.index_eq_one, hn, hn0]
  exact ⟨p, hp, hp8, hadm, K, inferInstance, inferInstance, by rw [pow_one]; exact hK,
    ⟨(mulEquivTwoResidualQuot hL hZ).trans eK⟩⟩

theorem f618RecogD8_of_sqt
    (D : Type) [Group D] [Finite D] (hS : F618RecogSettingSQT D)
    (hT : ∃ S : Sylow 2 D, Nonempty (↥S ≃* DihedralGroup 4)) :
    (∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ e ≤ 2 ∧ (p ^ e % 16 = 7 ∨ p ^ e % 16 = 9) ∧ IsL2 p e D) ∨
      IsHatAlt 6 D ∨ (∃ q : ℕ, q.Prime ∧ (q % 8 = 3 ∨ q % 8 = 5) ∧ IsPGL2 q D) ∨
      Nonempty (D ≃* ↥(alternatingGroup (Fin 7))) ∨ IsHatAlt 7 D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, ⟨eS⟩⟩ := hT
  have hS8 : Nat.card (S : Subgroup D) = 8 :=
    (Nat.card_congr eS.toEquiv).trans (by rw [DihedralGroup.nat_card])
  have : IsSimpleGroup (TwoResidualQuot D) := hS.quasisimple.2.1
  have hnonab : ∃ a b : TwoResidualQuot D, a * b ≠ b * a := hS.quasisimple.2.2
  have : Group.IsPerfect ↥(twoResidual (⊤ : Subgroup D)) := hS.quasisimple.1
  have := twoResidual_top_normal (D := D)
  obtain ⟨Q, ⟨eQ⟩⟩ := exists_sylow_quotient_of_setting hS.toF618RecogSetting S
  have h4 := (not_isCyclic_sylow_two hnonab Q).2
  rw [← Nat.card_congr eQ.toEquiv] at h4
  have hdvd : Nat.card ↥((S : Subgroup D) ⊓ twoResidual ⊤) ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hS8]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨n, hn⟩ := exists_index_twoResidual_eq (D := D)
  have hidx := card_sylow_eq_mul_index (twoResidual ⊤) hn S
  rw [hS8] at hidx
  have hcases : Nat.card ↥((S : Subgroup D) ⊓ twoResidual ⊤) = 4 ∨
      Nat.card ↥((S : Subgroup D) ⊓ twoResidual ⊤) = 8 := by
    obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hie] at h4 ⊢
    interval_cases i
    · norm_num at h4
    · norm_num at h4
    · left; norm_num
    · right; norm_num
  rcases hcases with hP | hP
  ·
    obtain ⟨p, K, _, _, hp, hp8, hp5, hK, -, hZ, ⟨eK⟩⟩ := psl_two_of_card_inf_eq_four hS S hP
    have : Fact p.Prime := ⟨hp⟩
    rw [hP] at hidx
    have hindex : (twoResidual (⊤ : Subgroup D)).index = 2 := by rw [hn]; omega
    obtain ⟨ε⟩ := nonempty_mulEquiv_pgl2_of_setting hS.toF618RecogSetting hZ hindex hp5 hK eK
    exact Or.inr (Or.inr (Or.inl ⟨p, hp, hp8, K, inferInstance, inferInstance, hK, ⟨ε⟩⟩))
  ·
    rw [hP] at hidx
    have hn0 : 2 ^ n = 1 := by omega
    have hL : twoResidual (⊤ : Subgroup D) = ⊤ := by rw [← Subgroup.index_eq_one, hn, hn0]
    have hQ8 : Nat.card (Q : Subgroup (TwoResidualQuot D)) = 8 := by
      rw [← Nat.card_congr eQ.toEquiv, hP]
    have hSL : (S : Subgroup D) ⊓ twoResidual ⊤ = S :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hP, hS8])
    have eQ' : Nonempty ((Q : Subgroup (TwoResidualQuot D)) ≃* DihedralGroup (2 ^ (3 - 1))) := by
      rw [show (2 : ℕ) ^ (3 - 1) = 4 by norm_num]
      exact ⟨eQ.symm.trans ((MulEquiv.subgroupCongr hSL).trans eS)⟩
    rcases CFSG.Milestones.lr_dihedral_simple_recognition (TwoResidualQuot D) hnonab Q 3
        (by norm_num) eQ' with ⟨p, f, hp, hp2, hf, hadm, K, _, _, hK, ⟨eK⟩⟩ | he7
    · have : Fact p.Prime := ⟨hp⟩
      have hcard := card_twoResidualQuot hp hp2 hK eK
      have hQd : 8 ∣ p ^ f * (((p ^ f) ^ 2 - 1) / 2) := by
        rw [← hcard, ← hQ8]
        exact Subgroup.card_subgroup_dvd_card _
      have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
      have h16 : p ^ f % 16 = 7 ∨ p ^ f % 16 = 9 := by
        by_contra hne
        have hc : (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∨ (p ^ f % 16 = 1 ∨ p ^ f % 16 = 15) := by
          obtain ⟨m, hm⟩ := hodd
          omega
        rcases hc with hc | hc
        · exact not_eight_dvd_card_psl_two hc hQd
        · have h := sixteen_dvd_card_psl_two hc
          rw [← hcard] at h
          have h' := Sylow.pow_dvd_card_of_pow_dvd_card (P := Q) (n := 4) (by simpa using h)
          rw [hQ8] at h'
          norm_num at h'
      have hf2 := le_two_of_isStronglyQuasithin hS.sqt hp hp2 hK eK
      obtain ⟨hZ1, hZ9⟩ := center_of_quotient_psl_two hS.center hp2 hK eK
      by_cases h9 : p ^ f = 9
      · rcases card_center_eq_one_or_three hS.toF618RecogSetting (hZ9 h9) with hZ | hZ
        · exact Or.inl ⟨p, f, hp, hf, hf2, h16, hadm, K, inferInstance, inferInstance, hK,
            ⟨(mulEquivTwoResidualQuot hL hZ).trans eK⟩⟩
        · obtain ⟨e6⟩ := nonempty_mulEquiv_alternating_six (by rw [hK, h9]) eK
          exact Or.inr (Or.inl (isHatAlt_of_setting hS.toF618RecogSetting hL hZ e6))
      · exact Or.inl ⟨p, f, hp, hf, hf2, h16, hadm, K, inferInstance, inferInstance, hK,
          ⟨(mulEquivTwoResidualQuot hL (hZ1 h9)).trans eK⟩⟩
    · obtain ⟨e7⟩ := he7
      rcases card_center_eq_one_or_three hS.toF618RecogSetting
          (card_center_le_three_of_alternating_seven hS.center e7) with hZ | hZ
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(mulEquivTwoResidualQuot hL hZ).trans e7⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (isHatAlt_of_setting hS.toF618RecogSetting hL hZ e7))))

end F6

end CFSG.Quasithin
