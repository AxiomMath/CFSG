module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

theorem s1614_weights {W : Type} [CommGroup W] (hW : ∀ x : W, x * x = 1) {z g : MulAut W}
    (hz3 : z * z * z = 1) (hg3 : g * g * g = 1) (hgz : g * z = z * g)
    (hzfix : ∀ x : W, z x = x → x = 1) :
    iSupIndep (fun j : Fin 3 => fixV (Subgroup.zpowers (g * z ^ (j : ℕ)))) ∧
      ⨆ j : Fin 3, fixV (Subgroup.zpowers (g * z ^ (j : ℕ))) = ⊤ := by
  have hz3' : z ^ 3 = 1 := by simpa [pow_succ] using hz3
  have hg3' : g ^ 3 = 1 := by simpa [pow_succ] using hg3
  have hz3_apply : ∀ x : W, z (z (z x)) = x := by
    intro x
    have h := congrArg (fun f : MulAut W => f x) hz3
    simpa [MulAut.mul_apply] using h
  have hz4_apply : ∀ x : W, z (z (z (z x))) = z x := fun x => hz3_apply (z x)
  have hgz1 : ∀ x : W, g (z x) = z (g x) := by
    intro x
    have h := congrArg (fun f : MulAut W => f x) hgz
    simpa [MulAut.mul_apply] using h
  have hgz_c : Commute g z := (commute_iff_eq g z).mpr hgz
  have hgz_pow : ∀ n : ℕ, g * z ^ n = z ^ n * g := fun n => hgz_c.pow_right n
  have hgz_apply : ∀ (n : ℕ) (x : W), g ((z ^ n) x) = (z ^ n) (g x) := by
    intro n x
    have h := congrArg (fun f : MulAut W => f x) (hgz_pow n)
    simpa [MulAut.mul_apply] using h
  have hz_add : ∀ (m n : ℕ) (x : W), (z ^ m) ((z ^ n) x) = (z ^ (m + n)) x := by
    intro m n x
    rw [← MulAut.mul_apply, ← pow_add]
  have hz2 : ∀ x : W, z (z x) = x * z x := by
    intro x
    have hzzz : z (z (z x)) = x := hz3_apply x
    have ht : z (x * z x * z (z x)) = x * z x * z (z x) := by
      rw [map_mul, map_mul, hzzz]
      ac_rfl
    have h1 := hzfix _ ht
    have hinv : ∀ u : W, u⁻¹ = u := fun u => inv_eq_of_mul_eq_one_right (hW u)
    calc z (z x) = (x * z x)⁻¹ := eq_inv_of_mul_eq_one_right h1
      _ = x * z x := hinv _
  have hN : ∀ x : W, x * z x * z (z x) = 1 := by
    intro x
    calc x * z x * z (z x) = x * z x * (x * z x) := by rw [hz2 x]
      _ = (x * x) * (z x * z x) := by ac_rfl
      _ = 1 := by rw [hW x, hW (z x), one_mul]
  have hN' : ∀ x : W, x * z (z x) * z x = 1 := by
    intro x
    calc x * z (z x) * z x = x * (x * z x) * z x := by rw [hz2 x]
      _ = (x * x) * (z x * z x) := by ac_rfl
      _ = 1 := by rw [hW x, hW (z x), one_mul]
  have ha3 : ∀ n : ℕ, (g * z ^ n) * (g * z ^ n) * (g * z ^ n) = 1 := by
    intro n
    have hcomm : Commute g (z ^ n) := hgz_c.pow_right n
    have hzn3 : (z ^ n) ^ 3 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hz3', one_pow]
    have hpow : (g * z ^ n) ^ 3 = 1 := by rw [hcomm.mul_pow 3, hg3', hzn3, one_mul]
    simpa [pow_succ] using hpow
  have ha3_apply : ∀ (n : ℕ) (x : W),
      (g * z ^ n) ((g * z ^ n) ((g * z ^ n) x)) = x := by
    intro n x
    have h := congrArg (fun f : MulAut W => f x) (ha3 n)
    simpa [MulAut.mul_apply] using h
  let E : ℕ → W →* W := fun n =>
    MonoidHom.mk' (fun w => w * (g * z ^ n) w * (g * z ^ n) ((g * z ^ n) w)) (by
      intro u v
      simp only [map_mul]
      ac_rfl)
  have hE_apply : ∀ n w, E n w = w * (g * z ^ n) w * (g * z ^ n) ((g * z ^ n) w) :=
    fun n w => rfl
  have hE_formula : ∀ n w, E n w = w * (z ^ n) (g w) * (z ^ n) ((z ^ n) (g (g w))) := by
    intro n w
    have hzz : (z ^ n) ((z ^ n) (g w)) = (z ^ (2 * n)) (g w) := by
      rw [hz_add n n (g w), two_mul]
    have hzz' : (z ^ (2 * n)) (g (g w)) = (z ^ n) ((z ^ n) (g (g w))) := by
      rw [two_mul, hz_add n n (g (g w))]
    rw [hE_apply n w]
    simp only [MulAut.mul_apply]
    rw [hgz_apply n w, hzz, hgz_apply (2 * n) (g w), hzz']
  have hz2_apply : ∀ x : W, (z ^ 2) x = z (z x) := by
    intro x
    rw [pow_two, MulAut.mul_apply]
  have hz22 : ∀ x : W, (z ^ 2) ((z ^ 2) x) = z x := by
    intro x
    simp only [pow_two, MulAut.mul_apply]
    exact hz4_apply x
  have hE0 : ∀ w, E 0 w = w * g w * g (g w) := by
    intro w
    rw [hE_formula 0 w]
    simp
  have hE1 : ∀ w, E 1 w = w * z (g w) * z (z (g (g w))) := by
    intro w
    rw [hE_formula 1 w, pow_one]
  have hE2 : ∀ w, E 2 w = w * z (z (g w)) * z (g (g w)) := by
    intro w
    rw [hE_formula 2 w, hz22, hz2_apply]
  have hE_mem : ∀ n w, E n w ∈ fixV (Subgroup.zpowers (g * z ^ n)) := by
    intro n w
    rw [mem_fixV_zpowers_iff_apply, hE_apply n w]
    simp only [map_mul]
    rw [ha3_apply n w]
    ac_rfl
  have hE_diag : ∀ n w, (g * z ^ n) w = w → E n w = w := by
    intro n w hw
    rw [hE_apply n w]
    simp only [hw]
    rw [hW w, one_mul]
  have hE_kill : ∀ i j : Fin 3, i ≠ j → ∀ w : W,
      (g * z ^ (j : ℕ)) w = w → E (i : ℕ) w = 1 := by
    intro i j hij w hw
    fin_cases j
    · simp only [Fin.val_zero, pow_zero, mul_one] at hw
      have hgw : g w = w := hw
      fin_cases i <;> simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at hij ⊢
      · exact absurd rfl hij
      · rw [hE1 w, hgw, hgw]; exact hN w
      · rw [hE2 w, hgw, hgw]; exact hN' w
    · simp only [Fin.val_one, pow_one] at hw
      have hz1 : z (g w) = w := by
        rw [MulAut.mul_apply, hgz1 w] at hw
        exact hw
      have hgw : g w = z (z w) := by
        have h2 := congrArg (fun x => z (z x)) hz1
        rw [hz3_apply (g w)] at h2
        exact h2
      have hggw : g (g w) = z w := by rw [hgw, hgz1 (z w), hgz1 w, hz1]
      fin_cases i <;> simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at hij ⊢
      · rw [hE0 w, hggw, hgw]; exact hN' w
      · exact absurd rfl hij
      · have h1 : z (z (g w)) = z w := by rw [hgw, hz4_apply w]
        rw [hE2 w, h1, hggw]; exact hN w
    · simp only [Fin.val_two] at hw
      have hz2' : z (z (g w)) = w := by
        simp only [pow_two, MulAut.mul_apply, hgz1 (z w), hgz1 w] at hw
        exact hw
      have hgw : g w = z w := by
        have h3 := congrArg (fun x => z x) hz2'
        rw [hz3_apply (g w)] at h3
        exact h3
      have hggw : g (g w) = z (z w) := by rw [hgw, hgz1 w, hgw]
      fin_cases i <;> simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at hij ⊢
      · rw [hE0 w, hggw, hgw]; exact hN w
      · have h1 : z (g w) = z (z w) := by rw [hgw]
        have h2 : z (z (g (g w))) = z w := by rw [hggw, hz4_apply w]
        rw [hE1 w, h1, h2]; exact hN' w
      · exact absurd rfl hij
  have hsum : ∀ w : W, E 0 w * E 1 w * E 2 w = w := by
    intro w
    calc E 0 w * E 1 w * E 2 w
        = (w * w * w) * (g w * z (g w) * z (z (g w))) *
            (g (g w) * z (z (g (g w))) * z (g (g w))) := by
          rw [hE0 w, hE1 w, hE2 w]; ac_rfl
      _ = w * (g w * z (g w) * z (z (g w))) *
            (g (g w) * z (z (g (g w))) * z (g (g w))) := by rw [hW w, one_mul]
      _ = w := by rw [hN (g w), hN' (g (g w)), mul_one, mul_one]
  refine ⟨?_, ?_⟩
  · rw [iSupIndep_def]
    intro i
    rw [disjoint_iff, eq_bot_iff]
    rintro w ⟨hw1, hw2⟩
    have hw1' : (g * z ^ (i : ℕ)) w = w := (mem_fixV_zpowers_iff_apply).mp hw1
    have hle : (⨆ j : Fin 3, ⨆ (_ : j ≠ i),
        fixV (Subgroup.zpowers (g * z ^ (j : ℕ)))) ≤ (E (i : ℕ)).ker := by
      refine iSup₂_le ?_
      intro j hj x hx
      rw [MonoidHom.mem_ker]
      exact hE_kill i j (Ne.symm hj) x (mem_fixV_zpowers_iff_apply.mp hx)
    have hkill : E (i : ℕ) w = 1 := MonoidHom.mem_ker.mp (hle hw2)
    have hdiag : E (i : ℕ) w = w := hE_diag (i : ℕ) w hw1'
    rw [Subgroup.mem_bot, ← hdiag, hkill]
  · rw [Subgroup.eq_top_iff']
    intro w
    rw [← hsum w]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mem_iSup_of_mem (0 : Fin 3) (hE_mem 0 w))
        (Subgroup.mem_iSup_of_mem (1 : Fin 3) (hE_mem 1 w)))
      (Subgroup.mem_iSup_of_mem (2 : Fin 3) (hE_mem 2 w))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
