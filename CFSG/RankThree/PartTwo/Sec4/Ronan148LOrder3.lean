module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.I1420 Finset

section Three

private theorem three_dvd_or_sq_sub_one (q : ℕ) : 3 ∣ q ∨ 3 ∣ q ^ 2 - 1 := by
  have hmod : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases hmod with h | h | h
  · exact Or.inl (Nat.dvd_of_mod_eq_zero h)
  · have h2 : q ^ 2 % 3 = 1 := by simp [Nat.pow_mod, h]
    exact Or.inr (by omega)
  · have h2 : q ^ 2 % 3 = 1 := by simp [Nat.pow_mod, h]
    exact Or.inr (by omega)

private theorem three_dvd_pow_mul {q e R : ℕ} (he : e ≠ 0) (hR : q ^ 2 - 1 ∣ R) :
    3 ∣ q ^ e * R := by
  rcases three_dvd_or_sq_sub_one q with h | h
  · exact Dvd.dvd.mul_right (dvd_pow h he) R
  · exact Dvd.dvd.mul_left (h.trans hR) _

private theorem three_dvd_div_of_coprime {N g : ℕ} (hgN : g ∣ N) (h3N : 3 ∣ N)
    (hc : Nat.Coprime 3 g) : 3 ∣ N / g :=
  Nat.dvd_div_of_mul_dvd (Nat.Coprime.mul_dvd_of_dvd_of_dvd hc.symm hgN h3N)

private theorem three_dvd_div_of_sq {N g : ℕ} (hgg : g * g ∣ N) (h3g : 3 ∣ g) :
    3 ∣ N / g := by
  apply Nat.dvd_div_of_mul_dvd
  exact (mul_dvd_mul_left g h3g).trans hgg

private theorem three_dvd_div_gcd_of_coprime {q e R g : ℕ} (he : e ≠ 0)
    (hR : q ^ 2 - 1 ∣ R) (hgR : g ∣ R) (hc : Nat.Coprime 3 g) : 3 ∣ q ^ e * R / g :=
  three_dvd_div_of_coprime (Dvd.dvd.mul_left hgR _) (three_dvd_pow_mul he hR) hc

private theorem three_dvd_div_gcd {q e R g : ℕ} (he : e ≠ 0) (hR : q ^ 2 - 1 ∣ R)
    (hgR : g ∣ R) (hgg : 3 ∣ g → g * g ∣ R) : 3 ∣ q ^ e * R / g := by
  by_cases h3 : 3 ∣ g
  · exact three_dvd_div_of_sq (Dvd.dvd.mul_left (hgg h3) _) h3
  · exact three_dvd_div_of_coprime (Dvd.dvd.mul_left hgR _) (three_dvd_pow_mul he hR)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)

private theorem three_dvd_orderA (n q : ℕ) (hn : 1 ≤ n) : 3 ∣ orderA n q := by
  have hmem : 2 ∈ Icc 2 (n + 1) := Finset.mem_Icc.2 ⟨le_refl 2, by omega⟩
  have hfac2 : q ^ 2 - 1 ∣ ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) :=
    Finset.dvd_prod_of_mem (fun i => q ^ i - 1) hmem
  have hgq : Nat.gcd (n + 1) (q - 1) ∣ q - 1 := Nat.gcd_dvd_right _ _
  have he : n * (n + 1) / 2 ≠ 0 := by
    have : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
    omega
  unfold orderA
  refine three_dvd_div_gcd he hfac2 (hgq.trans ((sub_one_dvd_sq_sub_one q).trans hfac2)) ?_
  intro h3
  have h3n : 3 ∣ n + 1 := h3.trans (Nat.gcd_dvd_left _ _)
  have hsub : ({2, 3} : Finset ℕ) ⊆ Icc 2 (n + 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  have hprod : (q ^ 2 - 1) * (q ^ 3 - 1) ∣ ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) := by
    have h := Finset.prod_dvd_prod_of_subset ({2, 3} : Finset ℕ) (Icc 2 (n + 1))
      (fun i => q ^ i - 1) hsub
    rw [Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3)] at h
    exact h
  exact (mul_dvd_mul hgq hgq).trans
    ((mul_dvd_mul (sub_one_dvd_sq_sub_one q) (Nat.sub_one_dvd_pow_sub_one q 3)).trans hprod)

private theorem three_dvd_orderTwistedA (n q : ℕ) (hn : 1 ≤ n) (hq : 2 ≤ q) :
    3 ∣ orderTwistedA n q := by
  have hq1 : 1 ≤ q := by omega
  have hmem : 2 ∈ Icc 2 (n + 1) := Finset.mem_Icc.2 ⟨le_refl 2, by omega⟩
  have hfac2 :
      q ^ 2 - 1 ∣ ∏ i ∈ Icc 2 (n + 1), (if Even i then q ^ i - 1 else q ^ i + 1) := by
    have h2 : q ^ 2 - 1 ∣ (fun i => if Even i then q ^ i - 1 else q ^ i + 1) 2 := by
      show q ^ 2 - 1 ∣ (if Even 2 then q ^ 2 - 1 else q ^ 2 + 1)
      simp
    exact h2.trans
      (Finset.dvd_prod_of_mem (fun i => if Even i then q ^ i - 1 else q ^ i + 1) hmem)
  have hqq : q + 1 ∣ q ^ 2 - 1 := add_one_dvd_sq_sub_one q hq1
  have h13 : q + 1 ∣ q ^ 3 + 1 := by
    have h := Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)
    rwa [one_pow] at h
  have he : n * (n + 1) / 2 ≠ 0 := by
    have : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
    omega
  unfold orderTwistedA
  refine three_dvd_div_gcd he hfac2
    ((Nat.gcd_dvd_right (n + 1) (q + 1)).trans (hqq.trans hfac2)) ?_
  intro h3
  have h3n : 3 ∣ n + 1 := h3.trans (Nat.gcd_dvd_left _ _)
  have hsub : ({2, 3} : Finset ℕ) ⊆ Icc 2 (n + 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  have hprod : (q ^ 2 - 1) * (q ^ 3 + 1) ∣
      ∏ i ∈ Icc 2 (n + 1), (if Even i then q ^ i - 1 else q ^ i + 1) := by
    have h := Finset.prod_dvd_prod_of_subset ({2, 3} : Finset ℕ) (Icc 2 (n + 1))
      (fun i => if Even i then q ^ i - 1 else q ^ i + 1) hsub
    rw [Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3), if_pos (even_two : Even (2 : ℕ)),
      if_neg (show ¬Even (3 : ℕ) by decide)] at h
    exact h
  have hgg0 : Nat.gcd (n + 1) (q + 1) * Nat.gcd (n + 1) (q + 1) ∣ (q + 1) * (q + 1) :=
    mul_dvd_mul (Nat.gcd_dvd_right (n + 1) (q + 1)) (Nat.gcd_dvd_right (n + 1) (q + 1))
  exact hgg0.trans ((mul_dvd_mul hqq h13).trans hprod)

private theorem three_dvd_orderBC (n q : ℕ) (hn : 1 ≤ n) : 3 ∣ orderBC n q := by
  have hmem : 1 ∈ Icc 1 n := Finset.mem_Icc.2 ⟨le_refl 1, hn⟩
  have hfac : q ^ 2 - 1 ∣ (fun i => q ^ (2 * i) - 1) 1 := by simp
  have hP2 : q ^ 2 - 1 ∣ ∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1) :=
    hfac.trans (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) hmem)
  have hgR : Nat.gcd 2 (q - 1) ∣ ∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1) :=
    (Nat.gcd_dvd_right 2 (q - 1)).trans ((sub_one_dvd_sq_sub_one q).trans hP2)
  have hc : Nat.Coprime 3 (Nat.gcd 2 (q - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 2 (q - 1)) (by norm_num)
  have he : n * n ≠ 0 := mul_ne_zero (by omega) (by omega)
  unfold orderBC
  exact three_dvd_div_gcd_of_coprime he hP2 hgR hc

private theorem three_dvd_orderD (n q : ℕ) (hn : 4 ≤ n) : 3 ∣ orderD n q := by
  have hmem : 1 ∈ Icc 1 (n - 1) := Finset.mem_Icc.2 ⟨le_refl 1, by omega⟩
  have hfac : q ^ 2 - 1 ∣ (fun i => q ^ (2 * i) - 1) 1 := by simp
  have hP2 : q ^ 2 - 1 ∣ ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
    hfac.trans (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) hmem)
  have hR : q ^ 2 - 1 ∣ (q ^ n - 1) * (∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) :=
    Dvd.dvd.mul_left hP2 _
  have hgR : Nat.gcd 4 (q ^ n - 1) ∣
      (q ^ n - 1) * (∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) :=
    Dvd.dvd.mul_right (Nat.gcd_dvd_right 4 (q ^ n - 1)) _
  have hc : Nat.Coprime 3 (Nat.gcd 4 (q ^ n - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 4 (q ^ n - 1)) (by norm_num)
  have he : n * (n - 1) ≠ 0 := by
    have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    omega
  have hE : orderD n q = q ^ (n * (n - 1)) *
      ((q ^ n - 1) * (∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1))) / Nat.gcd 4 (q ^ n - 1) := by
    unfold orderD
    rw [mul_assoc]
  rw [hE]
  exact three_dvd_div_gcd_of_coprime he hR hgR hc

private theorem three_dvd_orderTwistedD (n q : ℕ) (hn : 4 ≤ n) : 3 ∣ orderTwistedD n q := by
  have hmem : 1 ∈ Icc 1 (n - 1) := Finset.mem_Icc.2 ⟨le_refl 1, by omega⟩
  have hfac : q ^ 2 - 1 ∣ (fun i => q ^ (2 * i) - 1) 1 := by simp
  have hP2 : q ^ 2 - 1 ∣ ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
    hfac.trans (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) hmem)
  have hR : q ^ 2 - 1 ∣ (q ^ n + 1) * (∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) :=
    Dvd.dvd.mul_left hP2 _
  have hgR : Nat.gcd 4 (q ^ n + 1) ∣
      (q ^ n + 1) * (∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) :=
    Dvd.dvd.mul_right (Nat.gcd_dvd_right 4 (q ^ n + 1)) _
  have hc : Nat.Coprime 3 (Nat.gcd 4 (q ^ n + 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 4 (q ^ n + 1)) (by norm_num)
  have he : n * (n - 1) ≠ 0 := by
    have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    omega
  have hE : orderTwistedD n q = q ^ (n * (n - 1)) *
      ((q ^ n + 1) * (∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1))) / Nat.gcd 4 (q ^ n + 1) := by
    unfold orderTwistedD
    rw [mul_assoc]
  rw [hE]
  exact three_dvd_div_gcd_of_coprime he hR hgR hc

private theorem three_dvd_orderE6 (q : ℕ) : 3 ∣ orderE6 q := by
  have hE : orderE6 q = q ^ 36 * ((q ^ 2 - 1) * (q ^ 5 - 1) *
      ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1))) / Nat.gcd 3 (q - 1) := by
    unfold orderE6
    congr 1
    ring
  have hR : q ^ 2 - 1 ∣ (q ^ 2 - 1) * (q ^ 5 - 1) *
      ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1)) :=
    Dvd.dvd.mul_right (dvd_mul_right _ _) _
  have hgR : Nat.gcd 3 (q - 1) ∣ (q ^ 2 - 1) * (q ^ 5 - 1) *
      ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1)) :=
    ((Nat.gcd_dvd_right 3 (q - 1)).trans (sub_one_dvd_sq_sub_one q)).trans hR
  have hgg : Nat.gcd 3 (q - 1) * Nat.gcd 3 (q - 1) ∣ (q ^ 2 - 1) * (q ^ 5 - 1) *
      ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1)) :=
    (mul_dvd_mul (Nat.gcd_dvd_right 3 (q - 1)) (Nat.gcd_dvd_right 3 (q - 1))).trans
      ((mul_dvd_mul (sub_one_dvd_sq_sub_one q) (Nat.sub_one_dvd_pow_sub_one q 5)).trans
        (dvd_mul_right _ _))
  rw [hE]
  exact three_dvd_div_gcd (by norm_num : (36 : ℕ) ≠ 0) hR hgR (fun _ => hgg)

private theorem three_dvd_orderE7 (q : ℕ) : 3 ∣ orderE7 q := by
  have hE : orderE7 q = q ^ 63 * ((q ^ 2 - 1) * ((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) *
      (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1))) / Nat.gcd 2 (q - 1) := by
    unfold orderE7
    congr 1
    ring
  have hR : q ^ 2 - 1 ∣ (q ^ 2 - 1) * ((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) *
      (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1)) :=
    dvd_mul_right _ _
  have hgR : Nat.gcd 2 (q - 1) ∣ (q ^ 2 - 1) * ((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) *
      (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1)) :=
    ((Nat.gcd_dvd_right 2 (q - 1)).trans (sub_one_dvd_sq_sub_one q)).trans hR
  have hc : Nat.Coprime 3 (Nat.gcd 2 (q - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 2 (q - 1)) (by norm_num)
  rw [hE]
  exact three_dvd_div_gcd_of_coprime (by norm_num : (63 : ℕ) ≠ 0) hR hgR hc

private theorem three_dvd_orderE8 (q : ℕ) : 3 ∣ orderE8 q := by
  have hE : orderE8 q = q ^ 120 * ((q ^ 2 - 1) * ((q ^ 30 - 1) * (q ^ 24 - 1) *
      (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1))) := by
    unfold orderE8
    ring
  rw [hE]
  exact three_dvd_pow_mul (by norm_num : (120 : ℕ) ≠ 0) (dvd_mul_right (q ^ 2 - 1) _)

private theorem three_dvd_orderF4 (q : ℕ) : 3 ∣ orderF4 q := by
  have hE : orderF4 q =
      q ^ 24 * ((q ^ 2 - 1) * ((q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1))) := by
    unfold orderF4
    ring
  rw [hE]
  exact three_dvd_pow_mul (by norm_num : (24 : ℕ) ≠ 0) (dvd_mul_right (q ^ 2 - 1) _)

private theorem three_dvd_orderG2 (q : ℕ) : 3 ∣ orderG2 q := by
  have hE : orderG2 q = q ^ 6 * ((q ^ 2 - 1) * (q ^ 6 - 1)) := by
    unfold orderG2
    ring
  rw [hE]
  exact three_dvd_pow_mul (by norm_num : (6 : ℕ) ≠ 0) (dvd_mul_right (q ^ 2 - 1) _)

private theorem three_dvd_orderTrialityD4 (q : ℕ) : 3 ∣ orderTrialityD4 q := by
  have hE : orderTrialityD4 q =
      q ^ 12 * ((q ^ 2 - 1) * ((q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1))) := by
    unfold orderTrialityD4
    ring
  rw [hE]
  exact three_dvd_pow_mul (by norm_num : (12 : ℕ) ≠ 0) (dvd_mul_right (q ^ 2 - 1) _)

private theorem three_dvd_orderTwistedE6 (q : ℕ) (hq : 2 ≤ q) : 3 ∣ orderTwistedE6 q := by
  have hq1 : 1 ≤ q := by omega
  have hE : orderTwistedE6 q = q ^ 36 * ((q ^ 2 - 1) * (q ^ 5 + 1) *
      ((q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1))) / Nat.gcd 3 (q + 1) := by
    unfold orderTwistedE6
    congr 1
    ring
  have hR : q ^ 2 - 1 ∣ (q ^ 2 - 1) * (q ^ 5 + 1) *
      ((q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1)) :=
    Dvd.dvd.mul_right (dvd_mul_right _ _) _
  have hqq : q + 1 ∣ q ^ 2 - 1 := add_one_dvd_sq_sub_one q hq1
  have h15 : q + 1 ∣ q ^ 5 + 1 := by
    have h := Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 5)
    rwa [one_pow] at h
  have hgR : Nat.gcd 3 (q + 1) ∣ (q ^ 2 - 1) * (q ^ 5 + 1) *
      ((q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1)) :=
    ((Nat.gcd_dvd_right 3 (q + 1)).trans hqq).trans hR
  have hgg : Nat.gcd 3 (q + 1) * Nat.gcd 3 (q + 1) ∣ (q ^ 2 - 1) * (q ^ 5 + 1) *
      ((q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1)) :=
    (mul_dvd_mul (Nat.gcd_dvd_right 3 (q + 1)) (Nat.gcd_dvd_right 3 (q + 1))).trans
      ((mul_dvd_mul hqq h15).trans (dvd_mul_right _ _))
  rw [hE]
  exact three_dvd_div_gcd (by norm_num : (36 : ℕ) ≠ 0) hR hgR (fun _ => hgg)

private theorem two_pow_odd_mod_three (m : ℕ) : 2 ^ (2 * m + 1) % 3 = 2 := by
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

private theorem three_dvd_orderTwistedF4 (m : ℕ) : 3 ∣ orderTwistedF4 (2 ^ (2 * m + 1)) := by
  have hmod := two_pow_odd_mod_three m
  have h3 : 3 ∣ 2 ^ (2 * m + 1) + 1 := by omega
  have h13 : 2 ^ (2 * m + 1) + 1 ∣ (2 ^ (2 * m + 1)) ^ 3 + 1 := by
    have h := Odd.nat_add_dvd_pow_add_pow (2 ^ (2 * m + 1)) 1 (by decide : Odd 3)
    rwa [one_pow] at h
  have h3' : 3 ∣ (2 ^ (2 * m + 1)) ^ 3 + 1 := h3.trans h13
  unfold orderTwistedF4
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h3' _) _

private theorem three_dvd_orderRee (m : ℕ) : 3 ∣ orderRee (3 ^ (2 * m + 1)) := by
  have h3 : 3 ∣ 3 ^ (2 * m + 1) := dvd_pow_self 3 (by omega)
  unfold orderRee
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow h3 (by norm_num : (3 : ℕ) ≠ 0)) _) _

private theorem three_dvd_orderTits : 3 ∣ orderTits := by
  unfold orderTits
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
    (Dvd.dvd.mul_left (dvd_pow_self 3 (by norm_num : (3 : ℕ) ≠ 0)) _) _) _

end Three

theorem three_dvd_lieOrderFormula {d : TauCeti.LieTypeIndex} (hd : d.Valid)
    (hsz : ∀ m, d ≠ .suzuki m) : 3 ∣ lieOrderFormula d := by
  have hs : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff d).1 hd).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases d with
  | A n q => exact three_dvd_orderA n q.card (by omega)
  | twistedA n q =>
    exact three_dvd_orderTwistedA n q.card (by omega) q.isPrimePow_card.two_le
  | B n q => exact three_dvd_orderBC n q.card (by omega)
  | C n q => exact three_dvd_orderBC n q.card (by omega)
  | D n q => exact three_dvd_orderD n q.card (by omega)
  | twistedD n q => exact three_dvd_orderTwistedD n q.card (by omega)
  | E6 q => exact three_dvd_orderE6 q.card
  | E7 q => exact three_dvd_orderE7 q.card
  | E8 q => exact three_dvd_orderE8 q.card
  | F4 q => exact three_dvd_orderF4 q.card
  | G2 q => exact three_dvd_orderG2 q.card
  | twistedE6 q => exact three_dvd_orderTwistedE6 q.card q.isPrimePow_card.two_le
  | trialityD4 q => exact three_dvd_orderTrialityD4 q.card
  | suzuki m => exact absurd rfl (hsz m)
  | reeG2 m => exact three_dvd_orderRee m
  | reeF4 m => exact three_dvd_orderTwistedF4 m
  | tits => exact three_dvd_orderTits

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
