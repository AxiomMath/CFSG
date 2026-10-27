module

public import CFSG.LocalAnalysis.StandardType.FS81.LocalGen
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Defs

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem

theorem Basis3.exists_orderOf_eq_two_acts {G : Type} [Group G] [Finite G] {k : ℕ}
    (B : Basis3 G k) (hodd : Odd (Nat.card ↥(Subgroup.centralizer (B.span : Set G))))
    {A : Matrix (Fin k) (Fin k) (ZMod 3)} (hA : A ∈ B.realized ⊤) (hA2 : A * A = 1)
    (hA1 : A ≠ 1) :
    ∃ t : G, orderOf t = 2 ∧ B.Acts t A := by
  rcases hA with ⟨g, -, hgA⟩
  have hA2' : A ^ 2 = 1 := by rw [pow_two]; exact hA2
  have hg2 : B.Acts (g ^ 2) 1 := by
    have h := B.acts_mul hgA hgA
    rw [← pow_two, hA2] at h
    exact h
  have hmem : g ^ 2 ∈ Subgroup.centralizer (B.span : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨e, rfl⟩ := B.exists_vec_eq hy
    have h := B.acts_vec hg2 e
    rw [Matrix.one_mulVec] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  obtain ⟨a, r, hr, hord⟩ :=
    Nat.exists_eq_two_pow_mul_odd (orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite g))
  obtain ⟨m, rfl⟩ := hr
  have hpowacts : ∀ n : ℕ, B.Acts (g ^ n) (A ^ n) := by
    intro n
    induction n with
    | zero => simpa using B.acts_one
    | succ n ih => simpa [pow_succ] using B.acts_mul ih hgA
  have hAr : A ^ (2 * m + 1) = A := by
    rw [pow_succ, pow_mul, hA2', one_pow, one_mul]
  have htA : B.Acts (g ^ (2 * m + 1)) A := by
    have h := hpowacts (2 * m + 1)
    rwa [hAr] at h
  have ht2mem : (g ^ (2 * m + 1)) ^ 2 ∈
      Subgroup.centralizer (B.span : Set G) := by
    have hpow : (g ^ (2 * m + 1)) ^ 2 = (g ^ 2) ^ (2 * m + 1) := by
      calc (g ^ (2 * m + 1)) ^ 2 = g ^ ((2 * m + 1) * 2) := by rw [pow_mul]
        _ = g ^ (2 * (2 * m + 1)) := by rw [mul_comm (2 * m + 1) 2]
        _ = (g ^ 2) ^ (2 * m + 1) := by rw [pow_mul]
    rw [hpow]
    exact Subgroup.pow_mem _ hmem _
  have htpow : (g ^ (2 * m + 1)) ^ 2 ^ a = 1 := by
    calc (g ^ (2 * m + 1)) ^ 2 ^ a = g ^ ((2 * m + 1) * 2 ^ a) := by rw [pow_mul]
      _ = g ^ (2 ^ a * (2 * m + 1)) := by rw [mul_comm (2 * m + 1) (2 ^ a)]
      _ = g ^ orderOf g := by rw [← hord]
      _ = 1 := pow_orderOf_eq_one g
  have ht2dvd : orderOf ((g ^ (2 * m + 1)) ^ 2) ∣ 2 ^ a :=
    (orderOf_pow_dvd 2).trans (orderOf_dvd_of_pow_eq_one htpow)
  have ht2one : (g ^ (2 * m + 1)) ^ 2 = 1 := by
    have hcop : Nat.Coprime
        (Nat.card ↥(Subgroup.centralizer (B.span : Set G))) (2 ^ a) :=
      hodd.coprime_two_right.pow_right a
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (Subgroup.orderOf_dvd_natCard _ ht2mem) ht2dvd)
  have ht1 : g ^ (2 * m + 1) ≠ 1 := by
    intro h
    apply hA1
    have h' : B.Acts (g ^ (2 * m + 1)) 1 := by rw [h]; exact B.acts_one
    exact B.acts_unique htA h'
  exact ⟨g ^ (2 * m + 1), orderOf_eq_prime ht2one ht1, htA⟩

private theorem pow_val_neg_one {G : Type} [Group G] {a : G} (ha : a ^ 3 = 1) :
    a ^ ((-1 : ZMod 3)).val = a⁻¹ := by
  rw [show ((-1 : ZMod 3)).val = 2 from rfl, eq_inv_iff_mul_eq_one, ← pow_succ]
  exact ha

theorem exists_nineInvol_of_recOutTwD5 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (E : Set G)))) :
    ∃ t : G, orderOf t = 2 ∧ t * B.b 0 * t⁻¹ = (B.b 0)⁻¹ ∧ t * B.b 1 * t⁻¹ = (B.b 1)⁻¹ ∧
      ∀ j : Fin (5 + 1), 2 ≤ j.val → t * B.b j = B.b j * t := by
  let s : Fin (5 + 1) → ZMod 3 := ![-1, -1, 1, 1, 1, 1]
  have hsign : IsSign s := by
    unfold IsSign
    intro i
    fin_cases i <;> simp [s]
  have hprod : ∏ i : Fin (5 + 1), s i = 1 := by decide +kernel
  have hAeven : spMat (1 : Equiv.Perm (Fin (5 + 1))) s ∈ evenAll0 5 :=
    ⟨1, s, hsign, ⟨rfl, hprod⟩, rfl⟩
  have hArec : spMat (1 : Equiv.Perm (Fin (5 + 1))) s ∈
      B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) := by
    rw [hrec.2.1]
    exact hAeven
  have hA : spMat (1 : Equiv.Perm (Fin (5 + 1))) s ∈ B.realized ⊤ :=
    realized_mono B le_top hArec
  have hA2 : spMat (1 : Equiv.Perm (Fin (5 + 1))) s *
      spMat (1 : Equiv.Perm (Fin (5 + 1))) s = 1 :=
    spMat_mul_self 1 s (by simp) (by
      intro j
      fin_cases j <;> decide +kernel)
  have hA1 : spMat (1 : Equiv.Perm (Fin (5 + 1))) s ≠ 1 := by
    intro h
    have h00 : s 0 = (1 : ZMod 3) := by
      simpa [spMat_apply] using congrFun (congrFun h 0) 0
    have hs0 : s 0 = -1 := by simp [s]
    rw [hs0] at h00
    exact (by decide : (-1 : ZMod 3) ≠ 1) h00
  have hoddB : Odd (Nat.card ↥(Subgroup.centralizer (B.span : Set G))) := by
    simpa [hB.1] using hodd
  obtain ⟨t, htord, htA⟩ :=
    Basis3.exists_orderOf_eq_two_acts B hoddB hA hA2 hA1
  have hcols : ∀ j : Fin (5 + 1), t * B.b j * t⁻¹ = B.b j ^ (s j).val := by
    intro j
    exact B.acts_spMat_iff.mp htA j
  refine ⟨t, htord, ?_, ?_, ?_⟩
  · have h := hcols 0
    rw [show s 0 = -1 by simp [s]] at h
    rw [h]
    exact pow_val_neg_one (by rw [← B.ord 0]; exact pow_orderOf_eq_one _)
  · have h := hcols 1
    rw [show s 1 = -1 by simp [s]] at h
    rw [h]
    exact pow_val_neg_one (by rw [← B.ord 1]; exact pow_orderOf_eq_one _)
  · intro j hj
    have hsj : s j = 1 := by
      fin_cases j <;> simp [s] at hj ⊢
    have h := hcols j
    rw [hsj, show ((1 : ZMod 3)).val = 1 by decide, pow_one] at h
    exact mul_inv_eq_iff_eq_mul.mp h

end CFSG.StandardType.FrameRoute.FS81

end
