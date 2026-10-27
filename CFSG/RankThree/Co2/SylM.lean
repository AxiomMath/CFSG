module

public import CFSG.RankThree.Co2.CrMatConj
public import CFSG.RankThree.Co2.XSylowCert

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Co2Inv

section SylGrp

variable {ws : Array (List ℕ)} {n : ℕ} {cls : List ℕ}

theorem le_centralizer_of_sylGrp (hws : ∀ k < ws.size, ∀ l ∈ ws[k]!, l < 42)
    (h : SylGrp ws n cls) {j : ℕ} (hj : j ∈ cls) (hj10 : j < 10) :
    subW ws ≤ Subgroup.centralizer ({rep j} : Set Cr) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply crMat_injective
  rw [map_mul, map_mul, crMat_rep hj10]
  exact h.comm j hj _ ((mem_subW_iff_crMat hws).1 hy)

theorem isPGroup_of_sylGrp (hws : ∀ k < ws.size, ∀ l ∈ ws[k]!, l < 42)
    (h : SylGrp ws n cls) : IsPGroup 2 (subW ws) := fun y => ⟨5, by
  apply Subtype.ext
  apply crMat_injective
  rw [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one]
  exact h.pow _ ((mem_subW_iff_crMat hws).1 y.2)⟩

theorem card_subW_eq_card_matGrp (hws : ∀ k < ws.size, ∀ l ∈ ws[k]!, l < 42) :
    Nat.card (subW ws) = Nat.card (matGrp ws) := by
  rw [← card_map_subW, map_subW_eq hws]

theorem card_subW_of_sylGrp (hws : ∀ k < ws.size, ∀ l ∈ ws[k]!, l < 42)
    (h : SylGrp ws n cls) {j : ℕ} (hj : j ∈ cls) (hj10 : j < 10)
    (hn : n = 2 ^ (Nat.card (Subgroup.centralizer ({rep j} : Set Cr))).factorization 2) :
    Nat.card (subW ws) = n := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_of_sylGrp hws h)
  have hdvd := Subgroup.card_dvd_of_le (le_centralizer_of_sylGrp hws h hj hj10)
  rw [hk] at hdvd
  have hle : k ≤ (Nat.card (Subgroup.centralizer ({rep j} : Set Cr))).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
  have hge : n ≤ Nat.card (subW ws) := by
    rw [card_subW_eq_card_matGrp hws]
    exact h.card
  rw [hk] at hge ⊢
  rw [hn] at hge ⊢
  exact le_antisymm (Nat.pow_le_pow_right (by norm_num) hle) hge

end SylGrp

theorem sylLetters1 : ∀ k < pWords1.size, ∀ l ∈ pWords1[k]!, l < 42 := by decide +kernel
theorem sylLetters3 : ∀ k < pWords3.size, ∀ l ∈ pWords3[k]!, l < 42 := by decide +kernel
theorem sylLetters4 : ∀ k < pWords4.size, ∀ l ∈ pWords4[k]!, l < 42 := by decide +kernel
theorem sylLetters5 : ∀ k < pWords5.size, ∀ l ∈ pWords5[k]!, l < 42 := by decide +kernel
theorem sylLetters6 : ∀ k < pWords6.size, ∀ l ∈ pWords6[k]!, l < 42 := by decide +kernel
theorem sylLetters8 : ∀ k < pWords8.size, ∀ l ∈ pWords8[k]!, l < 42 := by decide +kernel

theorem sylLe1 :
    subW pWords1 ≤ Subgroup.centralizer ({rep 1} : Set Cr) :=
  le_centralizer_of_sylGrp sylLetters1 sylFacts_cert.1.1 (by simp) (by norm_num)

theorem sylLe3 {j : ℕ} (hj : j ∈ [2, 3]) :
    subW pWords3 ≤ Subgroup.centralizer ({rep j} : Set Cr) :=
  le_centralizer_of_sylGrp sylLetters3 sylFacts_cert.2.1.1 hj (by simp at hj; omega)

theorem sylLe4 :
    subW pWords4 ≤ Subgroup.centralizer ({rep 4} : Set Cr) :=
  le_centralizer_of_sylGrp sylLetters4 sylFacts_cert.2.2.1.1 (by simp) (by norm_num)

theorem sylLe8 {j : ℕ} (hj : j ∈ [7, 8]) :
    subW pWords8 ≤ Subgroup.centralizer ({rep j} : Set Cr) :=
  le_centralizer_of_sylGrp sylLetters8 sylFacts_cert.2.2.2.2.2.1 hj (by simp at hj; omega)

theorem two_part_C {i : ℕ}
    (hi : i < 10) {m k o : ℕ} (hm : m * classSizes[i]! = 743178240) (hmo : m = 2 ^ k * o)
    (ho : ¬ 2 ∣ o) : 2 ^ k = 2 ^ (Nat.card (Subgroup.centralizer ({rep i} : Set Cr))).factorization 2 := by
  have hpos : 0 < classSizes[i]! := by
    rcases Nat.eq_zero_or_pos classSizes[i]! with h0 | h0
    · rw [h0, mul_zero] at hm
      omega
    · exact h0
  have hC : Nat.card (Subgroup.centralizer ({rep i} : Set Cr)) = m :=
    Nat.eq_of_mul_eq_mul_right hpos ((card_centralizer_rep hi).trans hm.symm)
  have ho0 : o ≠ 0 := fun h0 => ho (h0 ▸ dvd_zero 2)
  rw [hC, hmo, Nat.factorization_mul (by positivity) ho0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd ho, add_zero]

theorem sylCard1 :
    Nat.card (subW pWords1) = 2 ^ 17 :=
  card_subW_of_sylGrp sylLetters1 sylFacts_cert.1.1 (j := 1) (by simp) (by norm_num)
    (two_part_C (by norm_num) (m := 2752512) (by decide) (by norm_num : 2752512 = 2 ^ 17 * 21)
      (by decide))

theorem sylCard3 :
    Nat.card (subW pWords3) = 2 ^ 16 :=
  card_subW_of_sylGrp sylLetters3 sylFacts_cert.2.1.1 (j := 3) (by simp) (by norm_num)
    (two_part_C (by norm_num) (m := 589824) (by decide) (by norm_num : 589824 = 2 ^ 16 * 9)
      (by decide))

theorem sylCard4 :
    Nat.card (subW pWords4) = 2 ^ 15 :=
  card_subW_of_sylGrp sylLetters4 sylFacts_cert.2.2.1.1 (j := 4) (by simp) (by norm_num)
    (two_part_C (by norm_num) (m := 32768) (by decide) (by norm_num : 32768 = 2 ^ 15 * 1)
      (by decide))

theorem sylCard8 :
    Nat.card (subW pWords8) = 2 ^ 14 :=
  card_subW_of_sylGrp sylLetters8 sylFacts_cert.2.2.2.2.2.1 (j := 8) (by simp) (by norm_num)
    (two_part_C (by norm_num) (m := 737280) (by decide) (by norm_num : 737280 = 2 ^ 14 * 45)
      (by decide))

end CFSG.RankThree.Co2

end
