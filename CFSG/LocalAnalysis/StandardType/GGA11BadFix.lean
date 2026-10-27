module

public import CFSG.LocalAnalysis.StandardType.GGA11NbrDefs

public section

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.A8Coord Matrix

namespace CFSG.StandardType.A11

private def a11bf_mon (π : Equiv.Perm (Fin 4)) (k : Fin 4 → ZMod 3) :
    Certificates.A8Nbr476.M4 :=
  Matrix.of fun i j => if π i = j then (2 : ZMod 7) ^ (k i).val else 0

private lemma a11bf_pow_add (x y : ZMod 3) :
    (2 : ZMod 7) ^ (x + y).val = (2 : ZMod 7) ^ x.val * (2 : ZMod 7) ^ y.val := by
  revert x y; decide

private lemma a11bf_mon_one : a11bf_mon 1 0 = (1 : Certificates.A8Nbr476.M4) := by decide

private lemma a11bf_mon_mul (π k π' k') :
    a11bf_mon π k * a11bf_mon π' k' =
      a11bf_mon (π.trans π') (fun i => k i + k' (π i)) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [a11bf_mon, Matrix.of_apply]
  rw [Finset.sum_eq_single (π i)]
  · rw [if_pos rfl]
    by_cases h : π' (π i) = j
    · rw [if_pos h, if_pos (show (Equiv.trans π π') i = j from h), a11bf_pow_add]
    · rw [if_neg h,
        if_neg (show ¬ (Equiv.trans π π') i = j from fun hc => h hc), mul_zero]
  · intro b _ hb
    rw [if_neg (Ne.symm hb), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

private def a11bf_monSub : Submonoid Certificates.A8Nbr476.M4 where
  carrier := {X | ∃ π k, X = a11bf_mon π k}
  one_mem' := ⟨1, 0, a11bf_mon_one⟩
  mul_mem' := by
    rintro X Y ⟨π, k, rfl⟩ ⟨π', k', rfl⟩
    exact ⟨π.trans π', fun i => k i + k' (π i), a11bf_mon_mul π k π' k'⟩

private lemma a11bf_closure_le_mon :
    Submonoid.closure G314gens ≤ a11bf_monSub := by
  rw [Submonoid.closure_le]
  intro g hg
  simp only [G314gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact ⟨Equiv.swap 0 1, 0, by decide⟩
  · exact ⟨Equiv.swap 1 2, 0, by decide⟩
  · exact ⟨Equiv.swap 2 3, 0, by decide⟩
  · exact ⟨1, fun i => if i = 0 then 1 else 0, by decide⟩

private abbrev a11bf_rankOneB (X : Certificates.A8Nbr476.M4) : Prop :=
  X ≠ 1 ∧ ∀ i j k l : Fin 4,
    (X - 1) i k * (X - 1) j l = (X - 1) i l * (X - 1) j k

private lemma a11bf_minors_field {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (h : A.rank ≤ 1) :
    ∀ i j k l : Fin 4, A i k * A j l = A i l * A j k := by
  have hspan : Module.finrank K (Submodule.span K (Set.range A.row)) ≤ 1 := by
    rw [Matrix.rank_eq_finrank_span_row A] at h; exact h
  haveI : Module.Free K (Submodule.span K (Set.range A.row)) :=
    Module.Free.of_divisionRing K _
  haveI : Module.Finite K (Submodule.span K (Set.range A.row)) := inferInstance
  obtain ⟨v, hv⟩ :=
    (finrank_le_one_iff (K := K) (V := Submodule.span K (Set.range A.row))).mp hspan
  intro i j k l
  obtain ⟨ci, hci⟩ := hv ⟨A.row i, Submodule.subset_span ⟨i, rfl⟩⟩
  obtain ⟨cj, hcj⟩ := hv ⟨A.row j, Submodule.subset_span ⟨j, rfl⟩⟩
  have hi : ∀ m, A i m = ci * (v : Fin 4 → K) m := by
    intro m
    have := congrArg (fun w : Fin 4 → K => w m) (congrArg Subtype.val hci)
    simpa [Pi.smul_apply, smul_eq_mul] using this.symm
  have hj : ∀ m, A j m = cj * (v : Fin 4 → K) m := by
    intro m
    have := congrArg (fun w : Fin 4 → K => w m) (congrArg Subtype.val hcj)
    simpa [Pi.smul_apply, smul_eq_mul] using this.symm
  rw [hi k, hj l, hi l, hj k]
  ring

private lemma a11bf_ne_one_field {K : Type*} [Field K]
    (X : Matrix (Fin 4) (Fin 4) K) (h : (X - 1).rank = 1) : X ≠ 1 := by
  intro hX
  rw [hX, sub_self, Matrix.rank_zero] at h
  exact zero_ne_one h

private lemma a11bf_rankOneB_of_rank (X : Certificates.A8Nbr476.M4)
    (h : (X - 1).rank = 1) : a11bf_rankOneB X := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact ⟨a11bf_ne_one_field X h, a11bf_minors_field (X - 1) (le_of_eq h)⟩

private lemma a11bf_mon_fix_0 :
    ∀ (π : Equiv.Perm (Fin 4)) (k : Fin 4 → ZMod 3),
      a11bf_rankOneB (a11bf_mon π k) →
      vecMul ![1, 1, 1, (0 : ZMod 7)] (a11bf_mon π k) = ![1, 1, 1, 0] →
      (π = Equiv.swap 0 1 ∧ k = 0) ∨ (π = Equiv.swap 0 2 ∧ k = 0) ∨
      (π = Equiv.swap 1 2 ∧ k = 0) ∨
      (π = 1 ∧ k = fun i => if i = 3 then 1 else 0) ∨
      (π = 1 ∧ k = fun i => if i = 3 then 2 else 0) := by
  decide +kernel

private lemma a11bf_mon_fix_3 :
    ∀ (π : Equiv.Perm (Fin 4)) (k : Fin 4 → ZMod 3),
      a11bf_rankOneB (a11bf_mon π k) →
      vecMul ![1, 1, 1, (3 : ZMod 7)] (a11bf_mon π k) = ![1, 1, 1, 3] →
      (π = Equiv.swap 0 1 ∧ k = 0) ∨ (π = Equiv.swap 0 2 ∧ k = 0) ∨
      (π = Equiv.swap 1 2 ∧ k = 0) := by
  decide +kernel

private lemma a11bf_mon_fix_5 :
    ∀ (π : Equiv.Perm (Fin 4)) (k : Fin 4 → ZMod 3),
      a11bf_rankOneB (a11bf_mon π k) →
      vecMul ![1, 1, 1, (5 : ZMod 7)] (a11bf_mon π k) = ![1, 1, 1, 5] →
      (π = Equiv.swap 0 1 ∧ k = 0) ∨ (π = Equiv.swap 0 2 ∧ k = 0) ∨
      (π = Equiv.swap 1 2 ∧ k = 0) := by
  decide +kernel

private lemma a11bf_mon_fix_6 :
    ∀ (π : Equiv.Perm (Fin 4)) (k : Fin 4 → ZMod 3),
      a11bf_rankOneB (a11bf_mon π k) →
      vecMul ![1, 1, 1, (6 : ZMod 7)] (a11bf_mon π k) = ![1, 1, 1, 6] →
      (π = Equiv.swap 0 1 ∧ k = 0) ∨ (π = Equiv.swap 0 2 ∧ k = 0) ∨
      (π = Equiv.swap 1 2 ∧ k = 0) := by
  decide +kernel

theorem a11BadFixInput_holds : A11BadFixInput := by
  intro c hc r hr hrank hfix
  obtain ⟨π, k, rfl⟩ := a11bf_closure_le_mon hr
  have hrk : a11bf_rankOneB (a11bf_mon π k) := a11bf_rankOneB_of_rank _ hrank
  rcases hc with rfl | rfl | rfl | rfl
  · rcases a11bf_mon_fix_0 π k hrk hfix with
      ⟨hπ, hk⟩ | ⟨hπ, hk⟩ | ⟨hπ, hk⟩ | ⟨hπ, hk⟩ | ⟨hπ, hk⟩
    · left; rw [hπ, hk]; decide
    · right; left; rw [hπ, hk]; decide
    · right; right; left; rw [hπ, hk]; decide
    · right; right; right; exact ⟨rfl, Or.inl (by rw [hπ, hk]; decide)⟩
    · right; right; right; exact ⟨rfl, Or.inr (by rw [hπ, hk]; decide)⟩
  · rcases a11bf_mon_fix_3 π k hrk hfix with ⟨hπ, hk⟩ | ⟨hπ, hk⟩ | ⟨hπ, hk⟩
    · left; rw [hπ, hk]; decide
    · right; left; rw [hπ, hk]; decide
    · right; right; left; rw [hπ, hk]; decide
  · rcases a11bf_mon_fix_5 π k hrk hfix with ⟨hπ, hk⟩ | ⟨hπ, hk⟩ | ⟨hπ, hk⟩
    · left; rw [hπ, hk]; decide
    · right; left; rw [hπ, hk]; decide
    · right; right; left; rw [hπ, hk]; decide
  · rcases a11bf_mon_fix_6 π k hrk hfix with ⟨hπ, hk⟩ | ⟨hπ, hk⟩ | ⟨hπ, hk⟩
    · left; rw [hπ, hk]; decide
    · right; left; rw [hπ, hk]; decide
    · right; right; left; rw [hπ, hk]; decide

end CFSG.StandardType.A11

end
