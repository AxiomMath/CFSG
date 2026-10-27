module

public import CFSG.RankThree.PartOne.TCX.Ree.Perm
public import CFSG.RankThree.PartOne.KLR.SectorTori

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Calculus


theorem nseqW_add_two (w₀ : WeylGroup ReeTag.F4.tag) (k : ℕ) :
    nseqW w₀ (k + 2) = (w₀ * ReeTag.F4.weylPerm w₀) * nseqW w₀ k := by
  rw [nseqW_succ, nseqW_succ, map_mul, ReeTag.weylPerm_weylPerm, mul_assoc]

theorem nseqW_odd (w₀ : WeylGroup ReeTag.F4.tag) (m : ℕ) :
    nseqW w₀ (2 * m + 1) = (w₀ * ReeTag.F4.weylPerm w₀) ^ m * w₀ := by
  induction m with
  | zero =>
    rw [show 2 * 0 + 1 = 0 + 1 by norm_num, nseqW_succ]
    simp [nseqW]
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, nseqW_add_two, ih, pow_succ']
    simp only [mul_assoc]

theorem mul_mul_pow_eq {G : Type*} [Group G] (a b : G) (m : ℕ) :
    a * (b * a) ^ m = (a * b) ^ m * a := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc a * (b * a) ^ (m + 1) = a * ((b * a) * (b * a) ^ m) := by rw [pow_succ']
      _ = (a * b) * (a * (b * a) ^ m) := by simp only [mul_assoc]
      _ = (a * b) * ((a * b) ^ m * a) := by rw [ih]
      _ = (a * b) ^ (m + 1) * a := by rw [pow_succ']; simp only [mul_assoc]

theorem nseqW_mul_weylPerm (w₀ : WeylGroup ReeTag.F4.tag) (m : ℕ) :
    nseqW w₀ (2 * m + 1) * ReeTag.F4.weylPerm (nseqW w₀ (2 * m + 1)) =
      (w₀ * ReeTag.F4.weylPerm w₀) ^ (2 * m + 1) := by
  rw [nseqW_odd, map_mul, map_pow, map_mul, ReeTag.weylPerm_weylPerm]
  set v := w₀ * ReeTag.F4.weylPerm w₀ with hv
  have key : w₀ * (ReeTag.F4.weylPerm w₀ * w₀) ^ m = v ^ m * w₀ := mul_mul_pow_eq w₀ _ m
  calc v ^ m * w₀ * ((ReeTag.F4.weylPerm w₀ * w₀) ^ m * ReeTag.F4.weylPerm w₀)
      = v ^ m * (w₀ * (ReeTag.F4.weylPerm w₀ * w₀) ^ m) * ReeTag.F4.weylPerm w₀ := by
        simp only [mul_assoc]
    _ = v ^ m * (v ^ m * w₀) * ReeTag.F4.weylPerm w₀ := by rw [key]
    _ = v ^ m * v ^ m * (w₀ * ReeTag.F4.weylPerm w₀) := by simp only [mul_assoc]
    _ = v ^ (2 * m + 1) := by
      rw [← pow_add, ← pow_succ, show m + m + 1 = 2 * m + 1 by ring]

end Calculus

section Neg

variable {τ : Tag}

@[expose] def NegAct (u : WeylGroup τ) : Prop :=
  (∀ v : Fin τ.rank → ℤ, u • v = -v) ∨ (∀ v : Fin τ.rank → ℤ, u • u • v = -v)

theorem smul_pow_of_neg {W : WeylGroup τ} (h : ∀ v : Fin τ.rank → ℤ, W • v = -v) (k : ℕ)
    (v : Fin τ.rank → ℤ) : W ^ k • v = ((-1 : ℤ) ^ k) • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_smul, ih, smul_comm, h, pow_succ, mul_comm, mul_smul, neg_one_smul ℤ]
    simp

theorem negAct_pow_odd {V : WeylGroup τ} (hV : NegAct V) {p : ℕ} (hp : Odd p) :
    NegAct (V ^ p) := by
  have hodd : ∀ W : WeylGroup τ, (∀ v : Fin τ.rank → ℤ, W • v = -v) →
      ∀ v : Fin τ.rank → ℤ, W ^ p • v = -v := fun W hW v => by
    rw [smul_pow_of_neg hW, hp.neg_one_pow, neg_one_smul ℤ]
  rcases hV with h | h
  · exact Or.inl (hodd V h)
  · right
    intro v
    have h2 : ∀ v : Fin τ.rank → ℤ, (V * V) • v = -v := fun v => by
      rw [mul_smul]
      exact h v
    have h3 := hodd (V * V) h2 v
    have e : V ^ p * V ^ p = (V * V) ^ p := by
      rw [← pow_add, ← two_mul, pow_mul, sq]
    rw [← mul_smul, e]
    exact h3

end Neg

section Sectors


theorem negI_mulVec (v : Fin 4 → ℤ) :
    (toMat 4 [[-1, 0, 0, 0], [0, -1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]]).mulVec v = -v := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, toMat, lget]

theorem wordProd_mul_weylPerm (l : List (Fin ReeTag.F4.tag.rank)) :
    (coxeterSystem ReeTag.F4.tag).wordProd l *
        ReeTag.F4.weylPerm ((coxeterSystem ReeTag.F4.tag).wordProd l) =
      (coxeterSystem ReeTag.F4.tag).wordProd (l ++ l.map ReeTag.F4.perm) := by
  rw [ReeTag.weylPerm_wordProd, CoxeterSystem.wordProd_append]

theorem negAct_of_word_left (l : List (Fin ReeTag.F4.tag.rank))
    (hW : wordMat ReeTag.F4.tag (l ++ l.map ReeTag.F4.perm) =
      toMat 4 [[-1, 0, 0, 0], [0, -1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]]) :
    NegAct ((coxeterSystem ReeTag.F4.tag).wordProd l *
      ReeTag.F4.weylPerm ((coxeterSystem ReeTag.F4.tag).wordProd l)) := by
  left
  intro v
  rw [wordProd_mul_weylPerm, wordProd_smul_eq_wordMat_mulVec, hW]
  exact negI_mulVec v

theorem negAct_of_word_right (l : List (Fin ReeTag.F4.tag.rank))
    (hW : wordMat ReeTag.F4.tag ((l ++ l.map ReeTag.F4.perm) ++ (l ++ l.map ReeTag.F4.perm)) =
      toMat 4 [[-1, 0, 0, 0], [0, -1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]]) :
    NegAct ((coxeterSystem ReeTag.F4.tag).wordProd l *
      ReeTag.F4.weylPerm ((coxeterSystem ReeTag.F4.tag).wordProd l)) := by
  right
  intro v
  rw [← mul_smul, wordProd_mul_weylPerm, ← CoxeterSystem.wordProd_append,
    wordProd_smul_eq_wordMat_mulVec, hW]
  exact negI_mulVec v

theorem negAct_wPhi2 : NegAct (wPhi2 * ReeTag.F4.weylPerm wPhi2) :=
  negAct_of_word_left [0, 1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 0]
    (wordMat_eq_toMat .F4 _ (by decide +kernel))

theorem negAct_wPhi4m : NegAct (wPhi4m * ReeTag.F4.weylPerm wPhi4m) :=
  negAct_of_word_right [0, 1, 0, 2, 1, 0] (wordMat_eq_toMat .F4 _ (by decide +kernel))

theorem negAct_wPhi4p : NegAct (wPhi4p * ReeTag.F4.weylPerm wPhi4p) :=
  negAct_of_word_right [0, 1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 0, 2, 1, 3, 2, 1, 0]
    (wordMat_eq_toMat .F4 _ (by decide +kernel))

end Sectors

section Stab

variable {τ : Tag} {L : Type} [Field L]

theorem rootChar_neg_apply (a : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar a (-v) = (rootChar a v)⁻¹ := by
  have h := rootChar_sub a 0 v
  rwa [zero_sub, rootChar_zero, one_mul] at h

theorem eq_one_of_stab_negAct {a : Fin τ.rank → Lˣ} {u : WeylGroup τ}
    (hu : u ∈ rootCharStabilizer a) (hneg : NegAct u) {m : ℕ} (hm : Odd m)
    (ham : ∀ j, a j ^ m = 1) : a = 1 := by
  funext j
  have hu' : ∀ v : Fin τ.rank → ℤ, rootChar a (u • v) = rootChar a v := hu
  have hsq : a j * a j = 1 := by
    have h1 : rootChar a (Pi.single j 1) = a j := by
      have := rootChar_nsmul_single a j 1
      rwa [one_smul, pow_one] at this
    have h2 : rootChar a (-(Pi.single j 1 : Fin τ.rank → ℤ)) = a j := by
      rcases hneg with h | h
      · rw [← h (Pi.single j 1), hu', h1]
      · rw [← h (Pi.single j 1), hu', hu', h1]
    rw [rootChar_neg_apply, h1] at h2
    calc a j * a j = a j * (a j)⁻¹ := by rw [h2]
      _ = 1 := mul_inv_cancel (a j)
  obtain ⟨k, rfl⟩ := hm
  have hpow : a j ^ (2 * k) = 1 := by
    rw [pow_mul, sq, hsq, one_pow]
  have := ham j
  rw [pow_succ, hpow, one_mul] at this
  exact this

end Stab

end CFSG.RankThree.PartOne.TCX.Ree
