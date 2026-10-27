module

public import CFSG.Sporadic.Fi24I301Cover.Elements
public import CFSG.Sporadic.Fi24I301.Elements

public section

namespace CFSG.Sporadic.Fi24I301Cover

open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Fi24I301
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
open CFSG.Sporadic.Fi24 (J)

theorem ofFn_prod_five {M : Type*} [Monoid M] (f : Fin 5 → M) :
    (List.ofFn f).prod = f 0 * f 1 * f 2 * f 3 * f 4 := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

private def triRow : Fin 10 → Fin 5 := ![0, 0, 0, 0, 1, 1, 1, 2, 2, 3]

private def triCol : Fin 10 → Fin 5 := ![1, 2, 3, 4, 2, 3, 4, 3, 4, 4]

private theorem tri_spec : ∀ i j : Fin 5, i < j → triRow (triIdx i j) = i ∧
    triCol (triIdx i j) = j := by
  decide

private theorem altMat_tri (C : Matrix (Fin 5) (Fin 5) (ZMod 3)) (hd : ∀ i, C i i = 0)
    (ha : ∀ i j, C j i = -C i j) : altMat (fun t => C (triRow t) (triCol t)) = C := by
  ext i j
  unfold altMat
  split_ifs with h1 h2
  · obtain ⟨h3, h4⟩ := tri_spec i j h1
    dsimp only
    rw [h3, h4]
  · obtain ⟨h3, h4⟩ := tri_spec j i h2
    dsimp only
    rw [h3, h4]
    exact (ha j i).symm
  · have hij : i = j := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
    subst hij
    exact (hd i).symm

private theorem altMat_zero : altMat 0 = 0 := by
  ext i j
  unfold altMat
  split_ifs
  · rfl
  · exact neg_zero
  · rfl


theorem nMat_noAlt (C : Matrix (Fin 5) (Fin 5) (ZMod 3)) (hd : ∀ i, C i i = 0)
    (ha : ∀ i j, C j i = -C i j) (hk : ∀ k, nMat k * C * (nMat k).transpose = C) : C = 0 := by
  have hC := altMat_tri C hd ha
  rw [← hC] at hk ⊢
  rw [noAltForm _ hk, altMat_zero]

section Action


private theorem nMats_lt : ∀ k < 2, ∀ i < 5, ∀ j < 5, ((nMats[k]!)[i]!)[j]! < 3 := by
  decide

theorem prodElt_eq_ofFn (v : List ℕ) :
    prodElt v = (List.ofFn fun j : Fin 5 => xJ j ^ v[(j : ℕ)]!).prod := by
  rw [ofFn_prod_five, prodElt, show List.range 5 = [0, 1, 2, 3, 4] from rfl]
  simp only [List.foldl_cons, List.foldl_nil, one_mul]
  rfl

theorem nJ_conj_ofFn (k : Fin 2) (i : Fin 5) :
    nJ k * xJ i * (nJ k)⁻¹ = (List.ofFn fun j : Fin 5 => xJ j ^ (nMat k i j).val).prod := by
  rw [nJ_conj k.isLt i.isLt, prodElt_eq_ofFn]
  congr 1
  refine List.ofFn_inj.2 (funext fun j => ?_)
  congr 1
  unfold nMat
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (nMats_lt k k.isLt i i.isLt j j.isLt)]

theorem xJ_indep_ofFn (e : Fin 5 → ℕ) (he : ∀ i, e i < 3)
    (h : (List.ofFn fun i : Fin 5 => xJ i ^ e i).prod = 1) : ∀ i, e i = 0 := by
  rw [ofFn_prod_five] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := xJ_indep (e 0) (e 1) (e 2) (e 3) (e 4) (he 0) (he 1) (he 2)
    (he 3) (he 4) h
  intro i
  fin_cases i
  exacts [h0, h1, h2, h3, h4]

theorem range_xJ : Set.range (fun i : Fin 5 => xJ i) = {xJ 0, xJ 1, xJ 2, xJ 3, xJ 4} := by
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · rintro (rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]

end Action

end CFSG.Sporadic.Fi24I301Cover
