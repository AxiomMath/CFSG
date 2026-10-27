module

public import CFSG.RankThree.PartOne.S12K.OrdRigid
import all CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.RankThree.PartOne.HNB

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.S12K

@[expose] def RowTable (t : StatedLieTag) (n : ℕ) : Prop :=
  (t = .PSL ∧ (n = 3 ∨ n = 4)) ∨ (t = .G2 ∧ n = 0) ∨ (t = .trialityD4 ∧ n = 0) ∨
    (t = .twistedF4 ∧ n = 0) ∨ (t = .PSU ∧ (n = 4 ∨ n = 5)) ∨ (t = .PSp ∧ (n = 2 ∨ n = 3))

@[expose] def RowSpecial (t : StatedLieTag) (n : ℕ) : Prop :=
  (t = .PSU ∧ (n = 4 ∨ n = 5)) ∨ (t = .PSp ∧ n = 3)

theorem false_of_index {m N N' : ℕ} {Z Z' : ℕ → Prop} (h : Profile m N Z) (h' : Profile m N' Z')
    {k : ℕ} (hk2 : 2 ≤ k) (hk6 : k ≠ 6) (hZ : Z k) (hZ' : ¬ Z' k) : False :=
  hZ' (((h.transfer h').2 k hk2 hk6).mp hZ)

theorem ordTwistedA_inj {n f g : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (h : ordTwistedA n (2 ^ f) = ordTwistedA n (2 ^ g)) : f = g := by
  have hX := profile_ordTwistedA hn hf
  have hY := profile_ordTwistedA hn hg
  rw [← h] at hY
  have hN := (hX.transfer hY).1
  have hc : 0 < n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
  exact Nat.eq_of_mul_eq_mul_right hc hN

theorem ordBC_inj {n f g : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (h : ordBC n (2 ^ f) = ordBC n (2 ^ g)) : f = g := by
  have hX := profile_ordBC (n := n) hf
  have hY := profile_ordBC (n := n) hg
  rw [← h] at hY
  have hN := (hX.transfer hY).1
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hn hn) hN

theorem ordTwistedA_three_ne_four {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordTwistedA 3 (2 ^ f) ≠ ordTwistedA 4 (2 ^ g) := by
  intro hm
  have hX := profile_ordTwistedA (n := 3) (by norm_num) hf
  have hY := profile_ordTwistedA (n := 4) (by norm_num) hg
  rw [← hm] at hY
  have hN := (hX.transfer hY).1
  norm_num at hN
  obtain ⟨s, rfl, rfl⟩ : ∃ s, f = 5 * s ∧ g = 3 * s := ⟨f / 5, by omega, by omega⟩
  have hs : 0 < s := by omega
  refine false_of_index hY hX (k := 12 * s) (by omega) (by omega)
    ⟨4, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, Or.inl ⟨by decide, ⟨1, by ring⟩⟩⟩ ?_
  rintro ⟨i, hi, hcase⟩
  obtain ⟨hi2, hi4⟩ := Finset.mem_Icc.mp hi
  interval_cases i
  · rcases hcase with ⟨-, hd⟩ | ⟨ho, -⟩
    · rw [show 5 * s * 2 = 10 * s by ring] at hd
      exact absurd (Nat.dvd_of_mul_dvd_mul_right hs hd) (by norm_num)
    · exact absurd ho (by decide)
  · rcases hcase with ⟨he, -⟩ | ⟨-, hd, -⟩
    · exact absurd he (by decide)
    · rw [show 2 * (5 * s * 3) = 30 * s by ring] at hd
      exact absurd (Nat.dvd_of_mul_dvd_mul_right hs hd) (by norm_num)
  · rcases hcase with ⟨-, hd⟩ | ⟨ho, -⟩
    · rw [show 5 * s * 4 = 20 * s by ring] at hd
      exact absurd (Nat.dvd_of_mul_dvd_mul_right hs hd) (by norm_num)
    · exact absurd ho (by decide)

theorem not_zBC_three {f s a c : ℕ} (hs : 0 < s) (hf : f = a * s)
    (hc : ∀ i ∈ Finset.Icc 1 3, ¬ c ∣ a * (2 * i)) : ¬ zBC 3 f (c * s) := by
  rintro ⟨i, hi, hd⟩
  apply hc i hi
  rw [hf, show a * s * (2 * i) = a * (2 * i) * s by ring] at hd
  exact Nat.dvd_of_mul_dvd_mul_right hs hd

theorem ordBC_three_ne_ordA_two {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordBC 3 (2 ^ f) ≠ ordA 2 (2 ^ g) := by
  intro hm
  have hX := profile_ordBC (n := 3) hf
  have hY := profile_ordA (n := 2) (by norm_num) hg
  rw [← hm] at hY
  have hN := (hX.transfer hY).1
  norm_num at hN
  obtain rfl : g = 3 * f := by omega
  exact false_of_index hY hX (k := 9 * f) (by omega) (by omega)
    ⟨3, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, ⟨1, by ring⟩⟩
    (not_zBC_three (a := 1) (by omega) (by ring) (by decide))

theorem ordBC_three_ne_ordA_three {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordBC 3 (2 ^ f) ≠ ordA 3 (2 ^ g) := by
  intro hm
  have hX := profile_ordBC (n := 3) hf
  have hY := profile_ordA (n := 3) (by norm_num) hg
  rw [← hm] at hY
  have hN := (hX.transfer hY).1
  norm_num at hN
  obtain ⟨s, rfl, rfl⟩ : ∃ s, f = 2 * s ∧ g = 3 * s := ⟨f / 2, by omega, by omega⟩
  have hs : 0 < s := by omega
  exact false_of_index hY hX (k := 9 * s) (by omega) (by omega)
    ⟨3, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, ⟨1, by ring⟩⟩
    (not_zBC_three (a := 2) hs rfl (by decide))

theorem ordBC_three_ne_ordG2 {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordBC 3 (2 ^ f) ≠ ordG2 (2 ^ g) := by
  intro hm
  have hX := profile_ordBC (n := 3) hf
  have hY := profile_ordG2 hg
  rw [← hm] at hY
  have hN := (hX.transfer hY).1
  norm_num at hN
  obtain ⟨s, rfl, rfl⟩ : ∃ s, f = 2 * s ∧ g = 3 * s := ⟨f / 2, by omega, by omega⟩
  have hs : 0 < s := by omega
  exact false_of_index hY hX (k := 18 * s) (by omega) (by omega)
    ⟨6, by simp, ⟨1, by ring⟩⟩ (not_zBC_three (a := 2) hs rfl (by decide))

theorem ordBC_three_ne_ordTrialityD4 {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordBC 3 (2 ^ f) ≠ ordTrialityD4 (2 ^ g) := by
  intro hm
  have hX := profile_ordBC (n := 3) hf
  have hY := profile_ordTrialityD4 hg
  rw [← hm] at hY
  have hN := (hX.transfer hY).1
  norm_num at hN
  obtain ⟨s, rfl, rfl⟩ : ∃ s, f = 4 * s ∧ g = 3 * s := ⟨f / 4, by omega, by omega⟩
  have hs : 0 < s := by omega
  exact false_of_index hY hX (k := 36 * s) (by omega) (by omega)
    (Or.inl ⟨⟨1, by ring⟩, fun hd => by have := Nat.le_of_dvd (by omega) hd; omega⟩)
    (not_zBC_three (a := 4) hs rfl (by decide))

theorem ordBC_three_ne_ordTwistedF4 {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordBC 3 (2 ^ f) ≠ ordTwistedF4 (2 ^ g) := by
  intro hm
  have hX := profile_ordBC (n := 3) hf
  have hY := profile_ordTwistedF4 hg
  rw [← hm] at hY
  have hN := (hX.transfer hY).1
  norm_num at hN
  obtain ⟨s, rfl, rfl⟩ : ∃ s, f = 4 * s ∧ g = 3 * s := ⟨f / 4, by omega, by omega⟩
  have hs : 0 < s := by omega
  exact false_of_index hY hX (k := 36 * s) (by omega) (by omega)
    (Or.inl ⟨⟨1, by ring⟩, fun hd => by have := Nat.le_of_dvd (by omega) hd; omega⟩)
    (not_zBC_three (a := 4) hs rfl (by decide))

theorem rigid_U4 {t : StatedLieTag} {n f g : ℕ} (hT : RowTable t n)
    (hadm : StatedLieAdmissible t n 2 f) (hg : 1 ≤ g)
    (h : charTwoOrder t n f = ordTwistedA 3 (2 ^ g)) : t = .PSU ∧ n = 4 ∧ f = g := by
  obtain ⟨-, hf, hrest⟩ := hadm
  rcases hT with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ |
    ⟨rfl, rfl | rfl⟩
  · exact absurd (h : ordA 2 (2 ^ f) = _) (ordA_ne_ordTwistedA (by norm_num) hf (by norm_num) hg)
  · exact absurd (h : ordA 3 (2 ^ f) = _) (ordA_ne_ordTwistedA (by norm_num) hf (by norm_num) hg)
  · have hf2 : 2 ≤ f := by
      by_contra hlt
      obtain rfl : f = 1 := by omega
      exact absurd hrest.2 (by norm_num)
    exact absurd (h : ordG2 (2 ^ f) = _) (ordG2_ne_ordTwistedA hf2 (by norm_num) hg)
  · exact absurd (h : ordTrialityD4 (2 ^ f) = _)
      (ordTrialityD4_ne_ordTwistedA hf (by norm_num) hg)
  · exact absurd (h : ordTwistedF4 (2 ^ f) = _) (ordTwistedF4_ne_ordTwistedA hf (by norm_num) hg)
  · exact ⟨rfl, rfl, ordTwistedA_inj (n := 3) (by norm_num) hf hg h⟩
  · exact absurd (h : ordTwistedA 4 (2 ^ f) = _).symm (ordTwistedA_three_ne_four hg hf)
  · exact absurd (h : ordBC 2 (2 ^ f) = _).symm (ordTwistedA_ne_ordBC_two (by norm_num) hg hf)
  · exact absurd (h : ordBC 3 (2 ^ f) = _) (ordBC_ne_ordTwistedA (by norm_num) hf (by norm_num) hg)

theorem rigid_U5 {t : StatedLieTag} {n f g : ℕ} (hT : RowTable t n)
    (hadm : StatedLieAdmissible t n 2 f) (hg : 1 ≤ g)
    (h : charTwoOrder t n f = ordTwistedA 4 (2 ^ g)) : t = .PSU ∧ n = 5 ∧ f = g := by
  obtain ⟨-, hf, hrest⟩ := hadm
  rcases hT with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ |
    ⟨rfl, rfl | rfl⟩
  · exact absurd (h : ordA 2 (2 ^ f) = _) (ordA_ne_ordTwistedA (by norm_num) hf (by norm_num) hg)
  · exact absurd (h : ordA 3 (2 ^ f) = _) (ordA_ne_ordTwistedA (by norm_num) hf (by norm_num) hg)
  · have hf2 : 2 ≤ f := by
      by_contra hlt
      obtain rfl : f = 1 := by omega
      exact absurd hrest.2 (by norm_num)
    exact absurd (h : ordG2 (2 ^ f) = _) (ordG2_ne_ordTwistedA hf2 (by norm_num) hg)
  · exact absurd (h : ordTrialityD4 (2 ^ f) = _)
      (ordTrialityD4_ne_ordTwistedA hf (by norm_num) hg)
  · exact absurd (h : ordTwistedF4 (2 ^ f) = _) (ordTwistedF4_ne_ordTwistedA hf (by norm_num) hg)
  · exact absurd (h : ordTwistedA 3 (2 ^ f) = _) (ordTwistedA_three_ne_four hf hg)
  · exact ⟨rfl, rfl, ordTwistedA_inj (n := 4) (by norm_num) hf hg h⟩
  · exact absurd (h : ordBC 2 (2 ^ f) = _).symm (ordTwistedA_ne_ordBC_two (by norm_num) hg hf)
  · exact absurd (h : ordBC 3 (2 ^ f) = _) (ordBC_ne_ordTwistedA (by norm_num) hf (by norm_num) hg)

theorem rigid_Sp6 {t : StatedLieTag} {n f g : ℕ} (hT : RowTable t n)
    (hadm : StatedLieAdmissible t n 2 f) (hg : 1 ≤ g)
    (h : charTwoOrder t n f = ordBC 3 (2 ^ g)) : t = .PSp ∧ n = 3 ∧ f = g := by
  obtain ⟨-, hf, -⟩ := hadm
  rcases hT with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ |
    ⟨rfl, rfl | rfl⟩
  · exact absurd (h : ordA 2 (2 ^ f) = _).symm (ordBC_three_ne_ordA_two hg hf)
  · exact absurd (h : ordA 3 (2 ^ f) = _).symm (ordBC_three_ne_ordA_three hg hf)
  · exact absurd (h : ordG2 (2 ^ f) = _).symm (ordBC_three_ne_ordG2 hg hf)
  · exact absurd (h : ordTrialityD4 (2 ^ f) = _).symm (ordBC_three_ne_ordTrialityD4 hg hf)
  · exact absurd (h : ordTwistedF4 (2 ^ f) = _).symm (ordBC_three_ne_ordTwistedF4 hg hf)
  · exact absurd (h : ordTwistedA 3 (2 ^ f) = _).symm
      (ordBC_ne_ordTwistedA (by norm_num) hg (by norm_num) hf)
  · exact absurd (h : ordTwistedA 4 (2 ^ f) = _).symm
      (ordBC_ne_ordTwistedA (by norm_num) hg (by norm_num) hf)
  · exact absurd (h : ordBC 2 (2 ^ f) = _).symm (ordBC_ne_ordBC_two (by norm_num) hg hf)
  · exact ⟨rfl, rfl, ordBC_inj (n := 3) (by norm_num) hf hg h⟩

theorem rigid_special {t t' : StatedLieTag} {n n' f f' : ℕ} (hs : RowSpecial t n)
    (hT' : RowTable t' n') (hadm : StatedLieAdmissible t n 2 f)
    (hadm' : StatedLieAdmissible t' n' 2 f')
    (h : charTwoOrder t' n' f' = charTwoOrder t n f) : t' = t ∧ n' = n ∧ f' = f := by
  have hf : 1 ≤ f := hadm.2.1
  rcases hs with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
  · exact rigid_U4 hT' hadm' hf h
  · exact rigid_U5 hT' hadm' hf h
  · exact rigid_Sp6 hT' hadm' hf h

end CFSG.RankThree.PartOne.HNB
