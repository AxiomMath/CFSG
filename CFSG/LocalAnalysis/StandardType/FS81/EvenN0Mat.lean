module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainBasic
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreOrthRows
public import CFSG.LocalAnalysis.StandardType.FS81.WtTwo
public import CFSG.LocalAnalysis.ZStar
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

section GLk

variable {k : ℕ}

theorem gl_inv_mulVec_mulVec (A : GL (Fin k) (ZMod 3)) (z : Fin k → ZMod 3) :
    ((A⁻¹ : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ
      ((A : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem gl_mulVec_inv_mulVec (A : GL (Fin k) (ZMod 3)) (z : Fin k → ZMod 3) :
    (A : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ
      (((A⁻¹ : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem gl_mul_mulVec (A B : GL (Fin k) (ZMod 3)) (z : Fin k → ZMod 3) :
    ((A * B : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ z =
      (A : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ ((B : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ z) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem gl_conj_mulVec (A B : GL (Fin k) (ZMod 3)) (z : Fin k → ZMod 3) :
    ((A * B * A⁻¹ : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ z =
      (A : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ ((B : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ
        (((A⁻¹ : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ z)) := by
  rw [gl_mul_mulVec, gl_mul_mulVec]

theorem gl_mulVec_ne_zero (A : GL (Fin k) (ZMod 3)) {z : Fin k → ZMod 3} (hz : z ≠ 0) :
    (A : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ z ≠ 0 := by
  intro h
  apply hz
  rw [← gl_inv_mulVec_mulVec A z, h, Matrix.mulVec_zero]

end GLk

theorem zmod3_eq_zero_of_eq_neg {a : ZMod 3} (h : a = -a) : a = 0 := by
  revert a
  decide

@[expose] def tau0Sign (n : ℕ) : Fin (n + 1) → ZMod 3 := fun i => if i = 0 then -1 else 1

@[expose] def tau0Mat (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3) :=
  Matrix.diagonal (tau0Sign n)

theorem tau0Mat_eq_spMat_one (n : ℕ) : tau0Mat n = spMat 1 (tau0Sign n) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [tau0Mat, spMat_apply]
  · simp [tau0Mat, spMat_apply, h]

theorem tau0Sign_isSign (n : ℕ) : IsSign (tau0Sign n) := by
  intro i
  by_cases hi : i = 0
  · subst hi
    exact Or.inr rfl
  · exact Or.inl (by rw [tau0Sign, if_neg hi])

theorem tau0Mat_mem_evenN0 (n : ℕ) : tau0Mat n ∈ evenN0 n := by
  rw [tau0Mat_eq_spMat_one]
  exact ⟨1, tau0Sign n, tau0Sign_isSign n, ⟨rfl, Finset.prod_eq_one fun i _ => by
    show (if i.succ = 0 then (-1 : ZMod 3) else 1) = 1
    rw [if_neg (Fin.succ_ne_zero i)]⟩, rfl⟩

theorem mul_self_of_isSign {k : ℕ} {s : Fin k → ZMod 3} (hs : IsSign s) (j : Fin k) :
    s j * s j = 1 := by
  rcases hs j with h | h <;> rw [h] <;> decide

theorem tau0Mat_mul_self (n : ℕ) : tau0Mat n * tau0Mat n = 1 := by
  rw [tau0Mat_eq_spMat_one, spMat_mul, mul_one]
  simp only [Equiv.Perm.one_apply]
  rw [show (fun j => tau0Sign n j * tau0Sign n j) = fun _ => 1 from
    funext fun j => mul_self_of_isSign (tau0Sign_isSign n) j, spMat_one]

theorem tau0Mat_mulVec_e0 (n : ℕ) : tau0Mat n *ᵥ Pi.single 0 1 = -(Pi.single 0 1) := by
  rw [tau0Mat_eq_spMat_one, spMat_mulVec_single]
  simp only [Equiv.Perm.one_apply]
  have h0 : tau0Sign n 0 = -1 := rfl
  rw [h0, neg_one_mul]
  funext i
  by_cases hi : i = 0
  · subst hi
    simp
  · simp [Pi.single_eq_of_ne hi]

theorem eq_one_or_neg_one_zmod_three {c : ZMod 3} (hc : c ≠ 0) : c = 1 ∨ c = -1 := by
  revert hc
  revert c
  decide

theorem evenN0_comm_tau0Mat {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (hM : M ∈ evenN0 n) : M * tau0Mat n = tau0Mat n * M := by
  obtain ⟨σ, s, -, ⟨hσ0, -⟩, rfl⟩ := hM
  rw [tau0Mat_eq_spMat_one, spMat_mul, spMat_mul, mul_one, one_mul]
  congr 1
  funext j
  simp only [Equiv.Perm.one_apply]
  have hs : tau0Sign n (σ j) = tau0Sign n j := by
    unfold tau0Sign
    by_cases hj : j = 0
    · subst hj
      rw [hσ0]
    · rw [if_neg hj, if_neg (fun h => hj (σ.injective (h.trans hσ0.symm)))]
  rw [hs, mul_comm]

theorem evenN0_col_apply_eq_zero {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (hM : M ∈ evenN0 n) {i : Fin (n + 1)} (hi : i ≠ 0) : M i 0 = 0 := by
  obtain ⟨σ, s, -, ⟨hσ0, -⟩, rfl⟩ := hM
  rw [spMat_apply, hσ0, if_neg hi]

theorem pi_single_zero_ne_zero (n : ℕ) : (Pi.single 0 1 : Fin (n + 1) → ZMod 3) ≠ 0 := by
  intro h
  have e := congrFun h 0
  simp at e

theorem tau0Mat_mulVec (n : ℕ) (z : Fin (n + 1) → ZMod 3) :
    tau0Mat n *ᵥ z = fun i => tau0Sign n i * z i := by
  rw [tau0Mat_eq_spMat_one, spMat_mulVec]
  simp only [Equiv.Perm.one_symm, Equiv.Perm.one_apply]

theorem tau0Mat_mulVec_sub (n : ℕ) (z : Fin (n + 1) → ZMod 3) :
    tau0Mat n *ᵥ z - z = z 0 • Pi.single 0 1 := by
  rw [tau0Mat_mulVec]
  funext i
  show tau0Sign n i * z i - z i = z 0 • (Pi.single 0 1 : Fin (n + 1) → ZMod 3) i
  rw [smul_eq_mul]
  by_cases hi : i = 0
  · subst hi
    rw [Pi.single_eq_same, mul_one, show tau0Sign n 0 = -1 from rfl]
    generalize z 0 = a
    revert a
    decide
  · rw [Pi.single_eq_of_ne hi, mul_zero, show tau0Sign n i = 1 from if_neg hi, one_mul, sub_self]

theorem tau0Mat_mulVec_of_apply_zero {n : ℕ} {z : Fin (n + 1) → ZMod 3} (hz : z 0 = 0) :
    tau0Mat n *ᵥ z = z := by
  rw [← sub_eq_zero, tau0Mat_mulVec_sub, hz, zero_smul]

theorem tau0Mat_ne_one (n : ℕ) : tau0Mat n ≠ 1 := by
  intro h
  have e := congrFun (congrFun h 0) 0
  simp [tau0Mat, tau0Sign] at e
  exact absurd e (by decide)

theorem axis_apply_eq_zero_of_axis_zero_ne {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))}
    {s : Fin (n + 1) → ZMod 3} (hσ0 : σ 0 = 0) {u : Fin (n + 1) → ZMod 3}
    (hu0 : u 0 ≠ 0) (hu : spMat σ s *ᵥ u = -u)
    (hl : ∀ z, ∃ c : ZMod 3, spMat σ s *ᵥ z - z = c • u) :
    ∀ j : Fin (n + 1), j ≠ 0 → u j = 0 := by
  intro j hj
  obtain ⟨c, hc⟩ := hl (Pi.single j 1)
  have hσj : σ j ≠ 0 := fun h => hj (σ.injective (h.trans hσ0.symm))
  have e0 := congrFun hc 0
  rw [spMat_mulVec_single, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm hσj),
    Pi.single_eq_of_ne (Ne.symm hj), sub_zero, Pi.smul_apply, smul_eq_mul] at e0
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp e0.symm with h | h
    · exact h
    · exact absurd h hu0
  rw [hc0, zero_smul, sub_eq_zero, spMat_mulVec_single, mul_one] at hc
  have hσjj : σ j = j := by
    by_contra hne
    have e := congrFun hc j
    rw [Pi.single_eq_of_ne (Ne.symm hne), Pi.single_eq_same] at e
    exact absurd e (by decide)
  have hsj : s j = 1 := by
    have e := congrFun hc j
    rwa [hσjj, Pi.single_eq_same, Pi.single_eq_same] at e
  have hsymm : σ.symm j = j := by rw [Equiv.symm_apply_eq, hσjj]
  have e := congrFun hu j
  rw [spMat_mulVec] at e
  simp only [hsymm, hsj, one_mul, Pi.neg_apply] at e
  exact zmod3_eq_zero_of_eq_neg e

theorem false_of_fixed_of_reflection {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))}
    {s : Fin (n + 1) → ZMod 3} (hs : IsSign s) {j : Fin (n + 1)} (hj0 : j ≠ 0)
    (hσj : σ j = j) (hp : ∏ i : Fin n, s i.succ = 1) {u : Fin (n + 1) → ZMod 3}
    (hl : ∀ z, ∃ c : ZMod 3, spMat σ s *ᵥ z - z = c • u)
    {c : ZMod 3} (hc : (Pi.single j (s j) : Fin (n + 1) → ZMod 3) - Pi.single j 1 = c • u)
    (hj : (Pi.single j (s j) : Fin (n + 1) → ZMod 3) ≠ Pi.single j 1) : False := by
  have hcne : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, sub_eq_zero] at hc
    exact hj hc
  have hsj : s j = -1 := by
    rcases hs j with h | h
    · rw [h] at hj
      exact absurd rfl hj
    · exact h
  have hul : ∀ l, l ≠ j → u l = 0 := by
    intro l hl'
    have e := congrFun hc l
    rw [Pi.sub_apply, Pi.single_eq_of_ne hl', Pi.single_eq_of_ne hl', sub_zero, Pi.smul_apply,
      smul_eq_mul] at e
    rcases mul_eq_zero.mp e.symm with h | h
    · exact absurd h hcne
    · exact h
  have hsl : ∀ l, l ≠ j → s l = 1 := by
    intro l hl'
    obtain ⟨c', hc'⟩ := hl (Pi.single l 1)
    have e := congrFun hc' l
    rw [spMat_mulVec_single, mul_one, Pi.sub_apply, Pi.smul_apply, hul l hl', smul_zero,
      sub_eq_zero, Pi.single_eq_same] at e
    by_cases hσl : σ l = l
    · rwa [hσl, Pi.single_eq_same] at e
    · rw [Pi.single_eq_of_ne (Ne.symm hσl)] at e
      exact absurd e (by decide)
  obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj0
  rw [Finset.prod_eq_single j' (fun i _ hi => hsl _ (fun h => hi (Fin.succ_injective _ h)))
    (fun h => absurd (Finset.mem_univ _) h), hsj] at hp
  exact absurd hp (by decide)

theorem wt_axis_of_apply_zero {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))}
    {s : Fin (n + 1) → ZMod 3} (hs : IsSign s) (hσ0 : σ 0 = 0)
    (hp : ∏ i : Fin n, s i.succ = 1) {u : Fin (n + 1) → ZMod 3} (hu0 : u 0 = 0)
    (hune : u ≠ 0) (hu : spMat σ s *ᵥ u = -u)
    (hl : ∀ z, ∃ c : ZMod 3, spMat σ s *ᵥ z - z = c • u) : wt u = 2 := by
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), spMat σ s *ᵥ Pi.single j 1 ≠ Pi.single j 1 := by
    by_contra hall
    push Not at hall
    have h1 : spMat σ s = 1 := by
      ext i j
      have e := congrFun (hall j) i
      rw [Matrix.mulVec_single_one, Matrix.col_apply] at e
      rw [e, Matrix.one_apply, Pi.single_apply]
    rw [h1, Matrix.one_mulVec] at hu
    exact hune (funext fun i => zmod3_eq_zero_of_eq_neg (congrFun hu i))
  obtain ⟨c, hc⟩ := hl (Pi.single j 1)
  rw [spMat_mulVec_single, mul_one] at hc hj
  have hcne : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, sub_eq_zero] at hc
    exact hj hc
  have hj0 : j ≠ 0 := by
    rintro rfl
    have e := congrFun hc 0
    rw [hσ0, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_same, Pi.smul_apply, hu0,
      smul_zero, sub_eq_zero] at e
    rw [hσ0, e] at hj
    exact hj rfl
  by_cases hσj : σ j = j
  · rw [hσj] at hc hj
    exact absurd (false_of_fixed_of_reflection hs hj0 hσj hp hl hc hj) (not_false)
  · have hw : wt (c • u) = 2 := by
      rw [← hc]
      exact wt_single_sub_single hσj (by rcases hs j with h | h <;> rw [h] <;> decide) one_ne_zero
    rwa [wt_smul hcne] at hw

structure EvenN0MatHyp (n : ℕ) (Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))) : Prop where
  norm : ∀ A ∈ Xg, (∀ i : Fin (n + 1), i ≠ 0 →
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) i 0 = 0) →
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ evenN0 n
  sub : ∀ M ∈ evenN0 n, ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = M
  odd : ∀ N : Subgroup ↥Xg, N.Normal → Odd (Nat.card N) → N = ⊥
  moves : ∃ A ∈ Xg, ∃ i : Fin (n + 1), i ≠ 0 ∧
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) i 0 ≠ 0

@[expose] def IsOrbitE0 (n : ℕ) (Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3)))
    (v : Fin (n + 1) → ZMod 3) : Prop :=
  ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = v

namespace EvenN0MatHyp

variable {n : ℕ} {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}

theorem mem_H_of_mulVec_e0 (h : EvenN0MatHyp n Xg) {A : GL (Fin (n + 1)) (ZMod 3)}
    (hA : A ∈ Xg) {c : ZMod 3}
    (hc : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      c • Pi.single 0 1) :
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ evenN0 n := by
  refine h.norm A hA fun i hi => ?_
  have e := congrFun hc i
  rwa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, Pi.single_eq_of_ne hi,
    smul_zero] at e

theorem exists_T (h : EvenN0MatHyp n Xg) :
    ∃ T ∈ Xg, (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = tau0Mat n :=
  h.sub _ (tau0Mat_mem_evenN0 n)

theorem mem_H_of_comm (h : EvenN0MatHyp n Xg) {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = tau0Mat n)
    {ρ : GL (Fin (n + 1)) (ZMod 3)} (hρ : ρ ∈ Xg) (hc : ρ * T = T * ρ) :
    (ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ evenN0 n := by
  refine h.norm ρ hρ fun i hi => ?_
  have e : tau0Mat n *ᵥ ((ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
      Pi.single 0 1) = -((ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
      Pi.single 0 1) := by
    rw [← hT, ← gl_mul_mulVec, ← hc, gl_mul_mulVec, hT, tau0Mat_mulVec_e0, Matrix.mulVec_neg]
  have e' := congrFun e i
  rw [tau0Mat, Matrix.mulVec_diagonal, tau0Sign, if_neg hi, one_mul, Pi.neg_apply] at e'
  have hcol : (ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) i 0 =
      ((ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) i := by
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  rw [hcol]
  refine zmod3_eq_zero_of_eq_neg ?_
  rw [← e']

theorem comm_of_mem_H {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = tau0Mat n)
    {A : GL (Fin (n + 1)) (ZMod 3)}
    (hA : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ evenN0 n) :
    A * T = T * A := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hT]
  exact evenN0_comm_tau0Mat hA

theorem conj_eq_of_mulVec_e0 (h : EvenN0MatHyp n Xg) {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = tau0Mat n)
    {A B : GL (Fin (n + 1)) (ZMod 3)} (hA : A ∈ Xg) (hB : B ∈ Xg) {c : ZMod 3}
    (hAB : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      c • ((B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1)) :
    A * T * A⁻¹ = B * T * B⁻¹ := by
  have hC : B⁻¹ * A ∈ Xg := Xg.mul_mem (Xg.inv_mem hB) hA
  have hCe : ((B⁻¹ * A : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = c • Pi.single 0 1 := by
    rw [gl_mul_mulVec, hAB, Matrix.mulVec_smul, gl_inv_mulVec_mulVec]
  have hcomm := comm_of_mem_H hT (h.mem_H_of_mulVec_e0 hC hCe)
  calc A * T * A⁻¹ = B * ((B⁻¹ * A) * T) * (B⁻¹ * A)⁻¹ * B⁻¹ := by group
    _ = B * (T * (B⁻¹ * A)) * (B⁻¹ * A)⁻¹ * B⁻¹ := by rw [hcomm]
    _ = B * T * B⁻¹ := by group

end EvenN0MatHyp

theorem conj_tau0_neg_mulVec_e0 {n : ℕ} {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = tau0Mat n)
    (A : GL (Fin (n + 1)) (ZMod 3)) :
    ((A * T * A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
      ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) =
      -((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) := by
  rw [gl_conj_mulVec, gl_inv_mulVec_mulVec, hT, tau0Mat_mulVec_e0, Matrix.mulVec_neg]

theorem conj_tau0_mulVec_sub {n : ℕ} {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = tau0Mat n)
    (A : GL (Fin (n + 1)) (ZMod 3)) (z : Fin (n + 1) → ZMod 3) :
    ((A * T * A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z - z =
      ((((A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z) 0) •
        ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) := by
  rw [gl_conj_mulVec, hT]
  calc (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        (tau0Mat n *ᵥ (((A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z)) - z =
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        (tau0Mat n *ᵥ (((A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z) -
        ((A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z) := by
        rw [Matrix.mulVec_sub, gl_mulVec_inv_mulVec]
    _ = _ := by rw [tau0Mat_mulVec_sub, Matrix.mulVec_smul]

namespace EvenN0MatHyp

variable {n : ℕ} {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}

theorem eq_smul_single_zero_of_commute_tau0 {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = tau0Mat n)
    {S : GL (Fin (n + 1)) (ZMod 3)} (hST : S * T = T * S) :
    ∃ μ : ZMod 3, (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      μ • Pi.single 0 1 := by
  have hSneg : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
      ((S : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) =
      -((S : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) := by
    calc (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
          ((S : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1)
        = ((T * S : GL (Fin (n + 1)) (ZMod 3)) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 := by
          rw [gl_mul_mulVec]
      _ = ((S * T : GL (Fin (n + 1)) (ZMod 3)) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 := by rw [← hST]
      _ = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
            ((T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) := by
          rw [gl_mul_mulVec]
      _ = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ (-(Pi.single 0 1)) := by
          rw [hT, tau0Mat_mulVec_e0]
      _ = -((S : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) := by
          rw [Matrix.mulVec_neg]
  refine ⟨((S : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0, ?_⟩
  funext i
  by_cases hi : i = 0
  · subst hi
    rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · have e := congrFun hSneg i
    rw [hT, tau0Mat] at e
    rw [Matrix.mulVec_diagonal, tau0Sign, if_neg hi, one_mul, Pi.neg_apply] at e
    rw [zmod3_eq_zero_of_eq_neg e, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero]

theorem eq_zero_or_eq_smul_of_commute_tau0 {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = tau0Mat n)
    {A : GL (Fin (n + 1)) (ZMod 3)}
    (hc : (A * T * A⁻¹) * T = T * (A * T * A⁻¹)) :
    ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 0 ∨
      ∃ c : ZMod 3, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
        c • Pi.single 0 1 := by
  set S : GL (Fin (n + 1)) (ZMod 3) := A⁻¹ * T * A with hS
  have hST : S * T = T * S := by
    have := congrArg (fun x => A⁻¹ * x * A) hc
    have h1 : A⁻¹ * ((A * T * A⁻¹) * T) * A = T * (A⁻¹ * T * A) := by group
    have h2 : A⁻¹ * (T * (A * T * A⁻¹)) * A = (A⁻¹ * T * A) * T := by group
    rw [h1, h2] at this
    exact this.symm
  obtain ⟨μ, hμ⟩ := eq_smul_single_zero_of_commute_tau0 hT hST
  have hμne : μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hμ
    exact gl_mulVec_ne_zero S (pi_single_zero_ne_zero n) hμ
  have hTAe : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
      ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) =
      μ • ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) := by
    have hS_eq : (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
        ((A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
          ((T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
            ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1)) := by
      rw [hS, gl_mul_mulVec, gl_mul_mulVec]
    rw [hμ] at hS_eq
    have := congrArg (fun x => (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ x) hS_eq
    rw [Matrix.mulVec_smul, gl_mulVec_inv_mulVec A
      (T *ᵥ ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1))] at this
    exact this.symm
  rcases eq_one_or_neg_one_zmod_three hμne with hμ1 | hμneg
  · left
    have e := congrFun hTAe 0
    rw [hT, tau0Mat] at e
    rw [hμ1, one_smul, Matrix.mulVec_diagonal, tau0Sign, if_pos rfl] at e
    generalize ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = a at e
    revert a; decide
  · right
    refine ⟨((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0, ?_⟩
    funext i
    by_cases hi : i = 0
    · subst hi
      rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · have e := congrFun hTAe i
      rw [hT, tau0Mat] at e
      rw [hμneg, neg_smul, one_smul, Matrix.mulVec_diagonal, tau0Sign, if_neg hi, one_mul,
        Pi.neg_apply] at e
      have h0 := zmod3_eq_zero_of_eq_neg e
      rw [h0, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero]

end EvenN0MatHyp

namespace EvenN0MatHyp

variable {n : ℕ} {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}

theorem eq_tau0_of_commute_of_no_U2 (h : EvenN0MatHyp n Xg) {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = tau0Mat n) (hTX : T ∈ Xg)
    (hno : ∀ v, IsOrbitE0 n Xg v → v 0 = 0 → wt v ≠ 2)
    {g : GL (Fin (n + 1)) (ZMod 3)} (hg : g ∈ Xg)
    (hc : (g * T * g⁻¹) * T = T * (g * T * g⁻¹)) :
    g * T * g⁻¹ = T := by
  have hrX : g * T * g⁻¹ ∈ Xg := Xg.mul_mem (Xg.mul_mem hg hTX) (Xg.inv_mem hg)
  obtain ⟨σ, s, hs, ⟨hσ0, hp⟩, hr⟩ := h.mem_H_of_comm hT hrX hc
  have hneg := conj_tau0_neg_mulVec_e0 hT g
  have hl : ∀ z, ∃ c : ZMod 3, spMat σ s *ᵥ z - z =
      c • ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) :=
    fun z => ⟨_, by rw [← hr]; exact conj_tau0_mulVec_sub hT g z⟩
  rw [hr] at hneg
  by_cases hu0 : ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 0
  · exact absurd (wt_axis_of_apply_zero hs hσ0 hp hu0
      (gl_mulVec_ne_zero g (pi_single_zero_ne_zero n)) hneg hl) (hno _ ⟨g, hg, rfl⟩ hu0)
  · have hz := axis_apply_eq_zero_of_axis_zero_ne hσ0 hu0 hneg hl
    have hge : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
        (((g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0) •
          Pi.single 0 1 := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul]
      by_cases hi : i = 0
      · subst hi
        rw [Pi.single_eq_same, mul_one]
      · rw [hz i hi, Pi.single_eq_of_ne hi, mul_zero]
    have hgc := comm_of_mem_H hT (h.mem_H_of_mulVec_e0 hg hge)
    rw [hgc, mul_assoc, mul_inv_cancel, mul_one]

theorem exists_U2 (h : EvenN0MatHyp n Xg) : ∃ v, IsOrbitE0 n Xg v ∧ v 0 = 0 ∧ wt v = 2 := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨T, hTX, hT⟩ := h.exists_T
  have : Fintype ↥Xg := Fintype.ofFinite _
  set τ : ↥Xg := ⟨T, hTX⟩ with hτ
  have hτ1 : τ ≠ 1 := by
    intro e
    have hT1 : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = 1 := by
      have hval := congrArg Subtype.val e
      have hval2 := congrArg Units.val hval
      simpa only [hτ, OneMemClass.coe_one, Units.val_one] using hval2
    rw [hT] at hT1
    exact tau0Mat_ne_one n hT1
  have hτ2 : τ * τ = 1 := by
    apply Subtype.ext
    apply Units.ext
    show (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) * T = 1
    rw [hT, tau0Mat_mul_self]
  have hiso : ∀ g : ↥Xg, (g * τ * g⁻¹) * τ = τ * (g * τ * g⁻¹) → g * τ * g⁻¹ = τ := by
    intro g hc
    have hc' : ((g : GL (Fin (n + 1)) (ZMod 3)) * T * (g : GL (Fin (n + 1)) (ZMod 3))⁻¹) * T =
        T * ((g : GL (Fin (n + 1)) (ZMod 3)) * T * (g : GL (Fin (n + 1)) (ZMod 3))⁻¹) := by
      have := congrArg Subtype.val hc
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
    exact Subtype.ext (h.eq_tau0_of_commute_of_no_U2 hT hTX hno g.2 hc')
  obtain ⟨N, hNn, hNodd, hNτ⟩ := CFSG.ZStar.glauberman_zStar ↥Xg τ hτ1 hτ2 hiso
  have hN0 := h.odd N hNn hNodd
  obtain ⟨A, hA, i, hi, hAi⟩ := h.moves
  apply hAi
  have h1 := hNτ ⟨A, hA⟩
  rw [hN0, Subgroup.mem_bot, mul_inv_eq_one] at h1
  have h1' : A * T * A⁻¹ = T := by
    have := congrArg Subtype.val h1
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hτ] using this
  have hcomm : A * T = T * A := by
    calc A * T = A * T * A⁻¹ * A := by group
      _ = T * A := by rw [h1']
  exact evenN0_col_apply_eq_zero (h.mem_H_of_comm hT hA hcomm) hi

theorem wt_two_of_O6 (h : EvenN0MatHyp n Xg) {v : Fin (n + 1) → ZMod 3}
    (hv : IsOrbitE0 n Xg v) (hv0 : v 0 = 0) : wt v = 2 := by
  obtain ⟨T, hTX, hT⟩ := h.exists_T
  obtain ⟨A, hA, rfl⟩ := hv
  have hTA : ((T * A : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      (1 : ZMod 3) • ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) := by
    rw [gl_mul_mulVec, hT, tau0Mat_mulVec_of_apply_zero hv0, one_smul]
  have hu := h.conj_eq_of_mulVec_e0 hT (Xg.mul_mem hTX hA) hA hTA
  have hc : (A * T * A⁻¹) * T = T * (A * T * A⁻¹) := by
    calc (A * T * A⁻¹) * T = (T * A) * T * (T * A)⁻¹ * T := by rw [hu]
      _ = T * (A * T * A⁻¹) * (T⁻¹ * T) := by group
      _ = T * (A * T * A⁻¹) := by rw [inv_mul_cancel, mul_one]
  have hrX : A * T * A⁻¹ ∈ Xg := Xg.mul_mem (Xg.mul_mem hA hTX) (Xg.inv_mem hA)
  obtain ⟨σ, s, hs, ⟨hσ0, hp⟩, hr⟩ := h.mem_H_of_comm hT hrX hc
  have hneg := conj_tau0_neg_mulVec_e0 hT A
  rw [hr] at hneg
  exact wt_axis_of_apply_zero hs hσ0 hp hv0 (gl_mulVec_ne_zero _ (pi_single_zero_ne_zero n)) hneg
    fun z => ⟨_, by rw [← hr]; exact conj_tau0_mulVec_sub hT A z⟩

end EvenN0MatHyp

end CFSG.StandardType.FrameRoute.FS81

end
