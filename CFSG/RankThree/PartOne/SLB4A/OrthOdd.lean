module

public import CFSG.RankThree.PartOne.SLB4A.Reflection
public import CFSG.RankThree.PartOne.SLB4A.Sign

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits Matrix

section Orth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem eig_pow {g : GL ι K} {f : ι → K} {l : K} (h : (g : Matrix ι ι K) *ᵥ f = l • f) (n : ℕ) :
    ((g ^ n : GL ι K) : Matrix ι ι K) *ᵥ f = l ^ n • f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul,
      pow_succ, mul_comm]

theorem eig_mul {g g' : GL ι K} {f : ι → K} {l l' : K} (h : (g : Matrix ι ι K) *ᵥ f = l • f)
    (h' : (g' : Matrix ι ι K) *ᵥ f = l' • f) :
    ((g * g' : GL ι K) : Matrix ι ι K) *ᵥ f = (l * l') • f := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, h', Matrix.mulVec_smul, h, smul_smul, mul_comm]

theorem scalar_mulVec_eq (c : K) (f : ι → K) : Matrix.scalar ι c *ᵥ f = c • f := by
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

variable (Φ : QuadForm K (ι → K))

theorem neg_one_pow_ex (x : C2) : (-1 : K) ^ ex x = eps K x := rfl

theorem exists_two_pow_five_orth_odd (h2 : (2 : K) ≠ 0) (f : Fin 7 → ι → K)
    (hnz : ∀ j, Φ.Q (f j) ≠ 0) (horth : ∀ i j, i ≠ j → Φ.polar.β (f i) (f j) = 0)
    (hp : ∀ j : Fin 7, j.1 < 4 → Φ.Q (f j) = 1) (hm : ∀ j : Fin 7, 4 ≤ j.1 → Φ.Q (f j) = -1) :
    ∃ U : Subgroup (StatedProj (StatedOmega Φ.Q)), IsElementaryAbelian 2 U ∧
      Nat.card U = 2 ^ 5 := by
  have hneg : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  let s : Fin 7 → GL ι K := fun j => RGL Φ (hnz j)
  have hsc : ∀ i j, s i * s j = s j * s i := fun i j => by
    by_cases hij : i = j
    · rw [hij]
    · exact RGL_comm Φ (hnz i) (hnz j) (horth i j hij)
  have hss : ∀ j, s j * s j = 1 := fun j => RGL_mul_self Φ (hnz j)
  let a : Fin 5 → Fin 7 := ![0, 1, 2, 4, 5]
  let b : Fin 5 → Fin 7 := ![1, 2, 3, 5, 6]
  let g : Fin 5 → GL ι K := fun k => s (a k) * s (b k)
  have hQeq : ∀ k, Φ.Q (f (b k)) = Φ.Q (f (a k)) := by
    intro k
    fin_cases k
    · exact (hp 1 (by decide)).trans (hp 0 (by decide)).symm
    · exact (hp 2 (by decide)).trans (hp 1 (by decide)).symm
    · exact (hp 3 (by decide)).trans (hp 2 (by decide)).symm
    · exact (hm 5 (by decide)).trans (hm 4 (by decide)).symm
    · exact (hm 6 (by decide)).trans (hm 5 (by decide)).symm
  have hmem : ∀ k, g k ∈ StatedOmega Φ.Q := fun k =>
    RGL_mul_RGL_mem_statedOmega Φ h2 (hnz _) (hnz _) (hQeq k)
  have hgc : ∀ i j, g i * g j = g j * g i := fun i j =>
    (Commute.mul_left (Commute.mul_right (hsc _ _ : Commute _ _) (hsc _ _ : Commute _ _))
      (Commute.mul_right (hsc _ _ : Commute _ _) (hsc _ _ : Commute _ _))).eq
  have hgs : ∀ k, g k * g k = 1 := fun k => by
    have hc := hsc (b k) (a k)
    calc g k * g k = s (a k) * (s (b k) * s (a k)) * s (b k) := by simp only [g, mul_assoc]
      _ = s (a k) * (s (a k) * s (b k)) * s (b k) := by rw [hc]
      _ = (s (a k) * s (a k)) * (s (b k) * s (b k)) := by simp only [mul_assoc]
      _ = 1 := by rw [hss, hss, one_mul]
  refine exists_two_pow_five_statedProj_inv _ g hmem ?_ ?_ ?_
  · intro i j
    rw [hgc i j, inv_mul_cancel]
    exact one_mem _
  · intro k
    rw [hgs k]
    exact one_mem _
  · intro v hv
    obtain ⟨c, hc⟩ := mem_statedScalars_iff.1 hv
    have heig : ∀ j k, ((s j : GL ι K) : Matrix ι ι K) *ᵥ f k =
        (if j = k then (-1 : K) else 1) • f k := by
      intro j k
      show Rmat Φ (f j) *ᵥ f k = _
      rw [Rmat_mulVec]
      by_cases hjk : j = k
      · subst hjk
        simpa using Φ.reflect_smul_self (hnz j) 1
      · simp only [hjk, reduceIte, one_smul]
        exact Φ.reflect_apply_of_polar_eq_zero (horth j k hjk)
    have hgeig : ∀ k j, ((g k : GL ι K) : Matrix ι ι K) *ᵥ f j =
        ((if a k = j then (-1 : K) else 1) * (if b k = j then (-1 : K) else 1)) • f j :=
      fun k j => eig_mul (heig _ _) (heig _ _)
    have hfne : ∀ j, f j ≠ 0 := fun j h => hnz j (by rw [h]; exact Φ.Q_zero)
    have hE : ∀ j, (c : K) = ((if a 0 = j then (-1 : K) else 1) * (if b 0 = j then (-1 : K) else 1)) ^
          ex (v 0) *
        ((if a 1 = j then (-1 : K) else 1) * (if b 1 = j then (-1 : K) else 1)) ^ ex (v 1) *
        ((if a 2 = j then (-1 : K) else 1) * (if b 2 = j then (-1 : K) else 1)) ^ ex (v 2) *
        ((if a 3 = j then (-1 : K) else 1) * (if b 3 = j then (-1 : K) else 1)) ^ ex (v 3) *
        ((if a 4 = j then (-1 : K) else 1) * (if b 4 = j then (-1 : K) else 1)) ^ ex (v 4) := by
      intro j
      have h := eig_mul (eig_mul (eig_mul (eig_mul (eig_pow (hgeig 0 j) (ex (v 0)))
        (eig_pow (hgeig 1 j) (ex (v 1)))) (eig_pow (hgeig 2 j) (ex (v 2))))
        (eig_pow (hgeig 3 j) (ex (v 3)))) (eig_pow (hgeig 4 j) (ex (v 4)))
      rw [hc, scalar_mulVec_eq] at h
      exact smul_left_injective K (hfne j) h
    have e0 := hE 0
    have e1 := hE 1
    have e2 := hE 2
    have e3 := hE 3
    have e4 := hE 4
    have e5 := hE 5
    have e6 := hE 6
    simp [a, b, neg_one_pow_ex] at e0 e1 e2 e3 e4 e5 e6
    have hc0 : (c : K) ≠ 0 := c.ne_zero
    have hc1 : (c : K) = 1 := by
      have : (c : K) * c = c * 1 := by
        calc (c : K) * c = eps K (v 3) * eps K (v 4) := by rw [← e4, ← e6]
          _ = c := e5.symm
          _ = c * 1 := (mul_one _).symm
      exact mul_left_cancel₀ hc0 this
    have E0 : eps K (v 0) = 1 := by rw [← e0, hc1]
    have E2 : eps K (v 2) = 1 := by rw [← e3, hc1]
    have E3 : eps K (v 3) = 1 := by rw [← e4, hc1]
    have E4 : eps K (v 4) = 1 := by rw [← e6, hc1]
    have E1 : eps K (v 1) = 1 := by
      rw [hc1, E0, one_mul] at e1
      exact e1.symm
    funext k
    fin_cases k
    · exact eps_inj hneg (E0.trans (eps_one K).symm)
    · exact eps_inj hneg (E1.trans (eps_one K).symm)
    · exact eps_inj hneg (E2.trans (eps_one K).symm)
    · exact eps_inj hneg (E3.trans (eps_one K).symm)
    · exact eps_inj hneg (E4.trans (eps_one K).symm)

end Orth

end CFSG.RankThree.PartOne.SLB4A
