module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpWeylOrbit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Curtis
import CFSG.LieType.Universal.SymplecticExtras.RankOne
public import Mathlib.LinearAlgebra.Matrix.Permutation

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Universal.Symplectic
open CFSG.LieType.Universal.Symplectic.SpExtras CFSG.StandardType CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open Matrix TauCeti.GLSymplecticFin

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
private theorem E_difference_eq_left {n : ℕ} {k : Fin n} (hk : k.val + 1 < n) :
    E K (RootSubgroupIndex.difference k ⟨k.val + 1, hk⟩ (SpExtras.ne_succ' hk)) =
      single (Sum.inl k) (Sum.inl ⟨k.val + 1, hk⟩) (1 : K) +
      single (Sum.inr ⟨k.val + 1, hk⟩) (Sum.inr k) (1 : K) := by
  rw [E, sub_eq_add_neg, single_neg, CharTwo.neg_eq]

omit [Finite K] in
private theorem E_difference_eq_right {n : ℕ} {k : Fin n} (hk : k.val + 1 < n) :
    E K (RootSubgroupIndex.difference ⟨k.val + 1, hk⟩ k (SpExtras.ne_succ' hk).symm) =
      single (Sum.inl ⟨k.val + 1, hk⟩) (Sum.inl k) (1 : K) +
      single (Sum.inr k) (Sum.inr ⟨k.val + 1, hk⟩) (1 : K) := by
  rw [E, sub_eq_add_neg, single_neg, CharTwo.neg_eq]

omit [Finite K] in
private theorem single_add_self {ι : Type} [DecidableEq ι] (x : ι) :
    ((Pi.single x (1 : K) : ι → K)) + (Pi.single x (1 : K) : ι → K) = 0 := by
  funext a
  simp [Pi.add_apply, CharTwo.add_self_eq_zero]

omit [Finite K] in
private theorem mat_weylRep_short_col (n : ℕ) (k : Fin n) (hk : k.val + 1 < n) :
    ∀ x : Fin n ⊕ Fin n,
      (((1 + E K (RootSubgroupIndex.difference k ⟨k.val + 1, hk⟩ (SpExtras.ne_succ' hk))) *
        (1 + E K (RootSubgroupIndex.difference ⟨k.val + 1, hk⟩ k
          (SpExtras.ne_succ' hk).symm)) *
        (1 + E K (RootSubgroupIndex.difference k ⟨k.val + 1, hk⟩ (SpExtras.ne_succ' hk)))) *ᵥ
        Pi.single x (1 : K)) =
      Pi.single (spMonoPerm (Equiv.swap k ⟨k.val + 1, hk⟩) 1 x) (1 : K) := by
  intro x
  rw [E_difference_eq_left hk, E_difference_eq_right hk]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rcases x with i | i <;>
    (by_cases hik : i = k <;> by_cases hik' : i = ⟨k.val + 1, hk⟩ <;>
      simp [-Matrix.mulVec_mulVec, -Matrix.mulVec_single, hik, hik',
        Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq, spMonoPerm, spFlip,
        Equiv.sumCongr_apply, Equiv.swap_apply_def, CharTwo.add_self_eq_zero,
        SpExtras.ne_succ' hk, (SpExtras.ne_succ' hk).symm, single_add_self,
        add_comm, add_left_comm, ← add_assoc])

omit [Finite K] in
private theorem mat_weylRep_short_prod (n : ℕ) (k : Fin n) (hk : k.val + 1 < n) :
    (1 + E K (RootSubgroupIndex.difference k ⟨k.val + 1, hk⟩ (SpExtras.ne_succ' hk))) *
    (1 + E K (RootSubgroupIndex.difference ⟨k.val + 1, hk⟩ k (SpExtras.ne_succ' hk).symm)) *
    (1 + E K (RootSubgroupIndex.difference k ⟨k.val + 1, hk⟩ (SpExtras.ne_succ' hk))) =
    Equiv.Perm.permMatrix K (spMonoPerm (Equiv.swap k ⟨k.val + 1, hk⟩) 1).symm := by
  let M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    (1 + E K (RootSubgroupIndex.difference k ⟨k.val + 1, hk⟩ (SpExtras.ne_succ' hk))) *
    (1 + E K (RootSubgroupIndex.difference ⟨k.val + 1, hk⟩ k (SpExtras.ne_succ' hk).symm)) *
    (1 + E K (RootSubgroupIndex.difference k ⟨k.val + 1, hk⟩ (SpExtras.ne_succ' hk)))
  change M = Equiv.Perm.permMatrix K (spMonoPerm (Equiv.swap k ⟨k.val + 1, hk⟩) 1).symm
  have hcol : ∀ b : Fin n ⊕ Fin n,
      M.col b = Pi.single (spMonoPerm (Equiv.swap k ⟨k.val + 1, hk⟩) 1 b) (1 : K) := by
    intro b
    rw [← Matrix.mulVec_single_one]
    exact mat_weylRep_short_col (K := K) n k hk b
  apply Matrix.ext
  intro a b
  rw [show M a b = (M.col b) a from rfl, congrFun (hcol b) a]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Pi.single_apply, Equiv.symm_apply_eq]

omit [Finite K] [CharP K 2] in
private theorem mat_elt_one {n : ℕ} (r : RootSubgroupIndex n) :
    mat n K (elt r (1 : K)) = 1 + E K r := by
  rw [mat_elt, one_smul]

omit [Finite K] in
private theorem mat_elt_neg_one {n : ℕ} (r : RootSubgroupIndex n) :
    mat n K (elt r (-1 : K)) = 1 + E K r := by
  rw [mat_elt, neg_smul, one_smul]
  rw [show -(E K r) = E K r from by
    ext a b
    exact CharTwo.neg_eq _]

omit [Finite K] in
private theorem mat_weylRep_short_scalar (n : ℕ) (k : Fin n) (hk : k.val + 1 < n) :
    mat n K (weylRep n K k) =
      (1 + E K (RootSubgroupIndex.difference k ⟨k.val + 1, hk⟩ (SpExtras.ne_succ' hk))) *
      (1 + E K (RootSubgroupIndex.difference ⟨k.val + 1, hk⟩ k
        (SpExtras.ne_succ' hk).symm)) *
      (1 + E K (RootSubgroupIndex.difference k ⟨k.val + 1, hk⟩ (SpExtras.ne_succ' hk))) := by
  rw [weylRep_eq_short hk, map_mul, map_mul, mat_elt_one, mat_elt_neg_one]

omit [Finite K] in
private theorem mat_weylRep_short (n : ℕ) (k : Fin n) (hk : k.val + 1 < n) :
    mat n K (weylRep n K k) =
      Equiv.Perm.permMatrix K (spMonoPerm (Equiv.swap k ⟨k.val + 1, hk⟩) 1).symm :=
  (mat_weylRep_short_scalar n k hk).trans (mat_weylRep_short_prod (K := K) n k hk)

omit [Finite K] in
private theorem mat_weylRep_long_mat (n : ℕ) (k : Fin n) (hk : ¬ k.val + 1 < n) :
    mat n K (weylRep n K k) =
      (1 + single (Sum.inl k) (Sum.inr k) (1 : K)) *
      (1 + single (Sum.inr k) (Sum.inl k) (1 : K)) *
      (1 + single (Sum.inl k) (Sum.inr k) (1 : K)) := by
  rw [weylRep_eq_long hk, map_mul, map_mul, mat_elt_positiveLong, mat_elt_negativeLong]
  simp only [Matrix.transvection]
  rw [show (-1 : K) = 1 from CharTwo.neg_eq 1]

omit [Finite K] in
private theorem mat_weylRep_long_col (n : ℕ) (k : Fin n) (_hk : ¬ k.val + 1 < n) :
    ∀ x : Fin n ⊕ Fin n,
      (((1 + single (Sum.inl k) (Sum.inr k) (1 : K)) *
        (1 + single (Sum.inr k) (Sum.inl k) (1 : K)) *
        (1 + single (Sum.inl k) (Sum.inr k) (1 : K))) *ᵥ Pi.single x (1 : K)) =
      Pi.single (spMonoPerm 1 (spSgn k) x) (1 : K) := by
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rcases x with i | i <;>
    (by_cases hik : i = k <;>
      simp [-Matrix.mulVec_mulVec, -Matrix.mulVec_single, hik, Matrix.add_mulVec,
        Matrix.one_mulVec, Matrix.single_mulVec_eq, spMonoPerm, spFlip, spSgn, single_add_self,
        add_comm, add_left_comm, ← add_assoc])

omit [Finite K] in
private theorem mat_weylRep_long_prod (n : ℕ) (k : Fin n) (hk : ¬ k.val + 1 < n) :
    (1 + single (Sum.inl k) (Sum.inr k) (1 : K)) *
    (1 + single (Sum.inr k) (Sum.inl k) (1 : K)) *
    (1 + single (Sum.inl k) (Sum.inr k) (1 : K)) =
    Equiv.Perm.permMatrix K (spMonoPerm 1 (spSgn k)).symm := by
  let M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    (1 + single (Sum.inl k) (Sum.inr k) (1 : K)) *
    (1 + single (Sum.inr k) (Sum.inl k) (1 : K)) *
    (1 + single (Sum.inl k) (Sum.inr k) (1 : K))
  change M = Equiv.Perm.permMatrix K (spMonoPerm 1 (spSgn k)).symm
  have hcol : ∀ b : Fin n ⊕ Fin n,
      M.col b = Pi.single (spMonoPerm 1 (spSgn k) b) (1 : K) := by
    intro b
    rw [← Matrix.mulVec_single_one]
    exact mat_weylRep_long_col (K := K) n k hk b
  apply Matrix.ext
  intro a b
  rw [show M a b = (M.col b) a from rfl, congrFun (hcol b) a]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Pi.single_apply, Equiv.symm_apply_eq]

omit [Finite K] in
private theorem mat_weylRep_long (n : ℕ) (k : Fin n) (hk : ¬ k.val + 1 < n) :
    mat n K (weylRep n K k) =
      Equiv.Perm.permMatrix K (spMonoPerm 1 (spSgn k)).symm :=
  (mat_weylRep_long_mat n k hk).trans (mat_weylRep_long_prod (K := K) n k hk)

private abbrev spCoxeterCs (n : ℕ) : CoxeterSystem (coxeterMatrix (isFiniteType_cartanC n))
    (coxeterMatrix (isFiniteType_cartanC n)).Group :=
  (coxeterMatrix (isFiniteType_cartanC n)).toCoxeterSystem

private theorem spCurtisDatum_nW_one (n : ℕ) :
    (spCurtisDatum n K).nW (1 : (coxeterMatrix (isFiniteType_cartanC n)).Group) = 1 :=
  (spCurtisDatum n K).nW_one

private theorem spCurtisDatum_nW_simple_mul (n : ℕ)
    (w : (coxeterMatrix (isFiniteType_cartanC n)).Group) (s : Fin n)
    (h : (spCoxeterCs n).length ((spCoxeterCs n).simple s * w) = (spCoxeterCs n).length w + 1) :
    (spCurtisDatum n K).nW ((spCoxeterCs n).simple s * w) =
      (spCurtisDatum n K).n s * (spCurtisDatum n K).nW w :=
  (spCurtisDatum n K).nW_simple_mul w s h

private theorem mat_nW_one (n : ℕ) {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ}
    (hw : SpRealizes n 1 π s) (hs : SpIsSign s) :
    mat n K ((spCurtisDatum n K).nW (1 : (coxeterMatrix (isFiniteType_cartanC n)).Group)) =
      Equiv.Perm.permMatrix K (spMonoPerm π s).symm := by
  obtain ⟨rfl, rfl⟩ := spRealizes_unique hw spRealizes_one hs
  rw [spCurtisDatum_nW_one n, map_one,
    show (spMonoPerm (1 : Equiv.Perm (Fin n)) (1 : Fin n → ℤ)).symm =
      (1 : Equiv.Perm (Fin n ⊕ Fin n)) by rw [spMonoPerm_one]; rfl,
    Matrix.permMatrix_one]

omit [Finite K] [CharP K 2] in
private theorem permMatrix_symm_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ₁ τ₂ : Equiv.Perm ι) :
    Equiv.Perm.permMatrix K τ₁.symm * Equiv.Perm.permMatrix K τ₂.symm =
      Equiv.Perm.permMatrix K (τ₁ * τ₂).symm := by
  rw [← Matrix.permMatrix_mul (σ := τ₂.symm) (τ := τ₁.symm)]
  congr 1

private theorem mat_nW_step_short {n : ℕ} {w' : (coxeterMatrix (isFiniteType_cartanC n)).Group}
    {π' : Equiv.Perm (Fin n)} {s' : Fin n → ℤ} (hs' : SpIsSign s')
    (ih' : mat n K ((spCurtisDatum n K).nW w') =
      Equiv.Perm.permMatrix K (spMonoPerm π' s').symm)
    {k : Fin n} (hlt : k.val + 1 < n)
    (hcond : (spCoxeterCs n).length ((spCoxeterCs n).simple k * w') = (spCoxeterCs n).length w' + 1)
    {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ}
    (hπ : π = Equiv.swap k ⟨k.val + 1, hlt⟩ * π')
    (hs_eq : s = fun c => s' c * (1 : Fin n → ℤ) (π' c)) :
    mat n K ((spCurtisDatum n K).nW ((spCoxeterCs n).simple k * w')) =
      Equiv.Perm.permMatrix K (spMonoPerm π s).symm := by
  rw [spCurtisDatum_nW_simple_mul n w' k hcond, map_mul, spCurtisDatum_n,
    mat_weylRep_short n k hlt, ih', permMatrix_symm_mul,
    ← spMonoPerm_mul (spIsSign_one) hs', ← hπ, ← hs_eq]

private theorem mat_nW_step_long {n : ℕ} {w' : (coxeterMatrix (isFiniteType_cartanC n)).Group}
    {π' : Equiv.Perm (Fin n)} {s' : Fin n → ℤ} (hs' : SpIsSign s')
    (ih' : mat n K ((spCurtisDatum n K).nW w') =
      Equiv.Perm.permMatrix K (spMonoPerm π' s').symm)
    {k : Fin n} (hlt : ¬ k.val + 1 < n)
    (hcond : (spCoxeterCs n).length ((spCoxeterCs n).simple k * w') = (spCoxeterCs n).length w' + 1)
    {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ} (hπ : π = 1 * π')
    (hs_eq : s = fun c => s' c * spSgn k (π' c)) :
    mat n K ((spCurtisDatum n K).nW ((spCoxeterCs n).simple k * w')) =
      Equiv.Perm.permMatrix K (spMonoPerm π s).symm := by
  rw [spCurtisDatum_nW_simple_mul n w' k hcond, map_mul, spCurtisDatum_n,
    mat_weylRep_long n k hlt, ih', permMatrix_symm_mul,
    ← spMonoPerm_mul (spIsSign_spSgn k) hs', ← hπ, ← hs_eq]

theorem mat_nW_spCurtisDatum {n : ℕ} {w : (coxeterMatrix (isFiniteType_cartanC n)).Group}
    {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ} (hw : SpRealizes n w π s) (hs : SpIsSign s) :
    mat n K ((spCurtisDatum n K).nW w) = Equiv.Perm.permMatrix K (spMonoPerm π s).symm := by
  let cs := spCoxeterCs n
  have key : ∀ m, ∀ (w : (coxeterMatrix (isFiniteType_cartanC n)).Group),
      cs.length w ≤ m → ∀ π s, SpRealizes n w π s → SpIsSign s →
      mat n K ((spCurtisDatum n K).nW w) = Equiv.Perm.permMatrix K (spMonoPerm π s).symm := by
    intro m
    induction m with
    | zero =>
      intro w hwle π s hw hs
      have hw1 : w = 1 := cs.length_eq_zero_iff.mp (Nat.le_zero.mp hwle)
      subst hw1
      exact mat_nW_one n hw hs
    | succ m ih =>
      intro w hwle π s hw hs
      by_cases hw1 : w = 1
      · subst hw1
        exact mat_nW_one n hw hs
      · obtain ⟨k, hk⟩ := cs.exists_leftDescent_of_ne_one hw1
        set w' : (coxeterMatrix (isFiniteType_cartanC n)).Group := cs.simple k * w with hw'def
        have hww' : cs.simple k * w' = w := cs.simple_mul_simple_cancel_left (w := w) k
        have hlen' : cs.length w' < cs.length w := hk
        have hlenle : cs.length w' ≤ m := by omega
        obtain ⟨π', s', hs', hw'⟩ := exists_spRealizes (m := n) w'
        have ih' := ih w' hlenle π' s' hw' hs'
        have hcond : cs.length (cs.simple k * w') = cs.length w' + 1 := by
          have hA : cs.length (cs.simple k * w') = cs.length w := by rw [hww']
          have hB : cs.length w' < cs.length (cs.simple k * w') := by rw [hA]; exact hlen'
          rcases cs.length_simple_mul w' k with h | h <;> omega
        rw [show w = cs.simple k * w' from hww'.symm]
        by_cases hlt : k.val + 1 < n
        · have hm := (spRealizes_simple_of_lt hlt).mul hw'
          rw [hww'] at hm
          obtain ⟨hπ, hs_eq⟩ := spRealizes_unique hw hm hs
          exact mat_nW_step_short (K := K) hs' ih' hlt hcond hπ hs_eq
        · have hm := (spRealizes_simple_of_not_lt hlt).mul hw'
          rw [hww'] at hm
          obtain ⟨hπ, hs_eq⟩ := spRealizes_unique hw hm hs
          exact mat_nW_step_long (K := K) hs' ih' hlt hcond hπ hs_eq
  exact key (cs.length w) w le_rfl π s hw hs

theorem exists_nW_eq_of_mat_eq {n : ℕ} {g : StatedSp n K} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hs : SpIsSign s)
    (hg : mat n K g = Equiv.Perm.permMatrix K (spMonoPerm π s).symm) :
    ∃ x : (coxeterMatrix (isFiniteType_cartanC n)).Group,
      SpRealizes n x π s ∧ (spCurtisDatum n K).nW x = g := by
  obtain ⟨x, hx⟩ := exists_spRealizes_of_spIsSign π hs
  exact ⟨x, hx, mat_injective ((mat_nW_spCurtisDatum hx hs).trans hg.symm)⟩

end CFSG.LocalAnalysis.WeakClosure81
