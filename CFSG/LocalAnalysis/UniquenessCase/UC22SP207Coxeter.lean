module

public import CFSG.GH74.BNPair.Defs
public import Mathlib.GroupTheory.Coxeter.Length
import CFSG.Monster.B.Geometry.PolarCoxeter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.GH74.BNPair (wordLength)

theorem uc22sp207_wordLength_range_simple {ι : Type*} {M : CoxeterMatrix ι} {W : Type*}
    [Group W] (cs : CoxeterSystem M W) (w : W) :
    wordLength (Set.range cs.simple) w = cs.length w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  refine le_antisymm ?_ (le_csInf ?_ ?_)
  · refine Nat.sInf_le ⟨ω.map cs.simple, fun s hs => ?_, by simp [hω.eq], rfl⟩
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hs
    exact ⟨i, rfl⟩
  · exact ⟨_, ω.map cs.simple, fun s hs => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hs
      exact ⟨i, rfl⟩, rfl, rfl⟩
  · rintro k ⟨l, hl, rfl, hprod⟩
    have hlift : ∀ l : List W, (∀ s ∈ l, s ∈ Set.range cs.simple) →
        ∃ ω' : List ι, ω'.map cs.simple = l := by
      intro l hl
      induction l with
      | nil => exact ⟨[], rfl⟩
      | cons s l ih =>
        obtain ⟨i, hi⟩ := hl s (List.mem_cons_self ..)
        obtain ⟨ω', hω'⟩ := ih fun t ht => hl t (List.mem_cons_of_mem _ ht)
        exact ⟨i :: ω', by simp [hi, hω']⟩
    obtain ⟨ω', rfl⟩ := hlift l hl
    have h := cs.length_wordProd_le ω'
    rw [CoxeterSystem.wordProd] at h
    rw [hprod] at h
    simpa using h

theorem uc22sp207_wordLength_map {W W' : Type*} [Group W] [Group W'] (e : W ≃* W') (J : Set W)
    (w : W) : wordLength (e '' J) (e w) = wordLength J w := by
  unfold wordLength
  congr 1
  ext k
  constructor
  · rintro ⟨l, hl, rfl, hprod⟩
    refine ⟨l.map e.symm, fun s hs => ?_, by simp, ?_⟩
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
      obtain ⟨j, hj, rfl⟩ := hl t ht
      simpa using hj
    · rw [← map_list_prod, hprod, MulEquiv.symm_apply_apply]
  · rintro ⟨l, hl, rfl, hprod⟩
    refine ⟨l.map e, fun s hs => ?_, by simp, by rw [← map_list_prod, hprod]⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    exact ⟨t, hl t ht, rfl⟩

theorem uc22sp207_exists_central_longest_of_subsingleton {ι : Type*} [Subsingleton ι]
    {M : CoxeterMatrix ι} {W : Type*} [Group W] (cs : CoxeterSystem M W) :
    ∃ z : W, (∀ w, cs.length w ≤ cs.length z) ∧ ∀ w, z * w = w * z := by
  have hcomm : ∀ (i : ι) (ω : List ι),
      cs.simple i * cs.wordProd ω = cs.wordProd ω * cs.simple i := by
    intro i ω
    induction ω with
    | nil => simp
    | cons j ω ih =>
      rw [cs.wordProd_cons, Subsingleton.elim j i, mul_assoc, ih, ← mul_assoc]
  have hlen : ∀ w : W, cs.length w ≤ 1 := by
    intro w
    obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
    rw [hω.eq]
    match ω, hω with
    | [], _ => simp
    | [_], _ => simp
    | i :: j :: ω, hω =>
      exfalso
      have h := cs.length_wordProd_le ω
      rw [Subsingleton.elim j i] at hω
      have heq : cs.wordProd (i :: i :: ω) = cs.wordProd ω := by
        rw [cs.wordProd_cons, cs.wordProd_cons, ← mul_assoc, cs.simple_mul_simple_self, one_mul]
      have := hω.eq
      rw [heq] at this
      simp only [List.length_cons] at this
      omega
  by_cases hι : Nonempty ι
  · obtain ⟨i⟩ := hι
    refine ⟨cs.simple i, fun w => (hlen w).trans (cs.length_simple i).ge, fun w => ?_⟩
    obtain ⟨ω, rfl⟩ := cs.wordProd_surjective w
    exact hcomm i ω
  · refine ⟨1, fun w => ?_, fun w => by simp⟩
    obtain ⟨ω, rfl⟩ := cs.wordProd_surjective w
    cases ω with
    | nil => simp
    | cons i _ => exact absurd ⟨i⟩ hι

theorem uc22sp207_exists_central_longest_B3 {ι : Type*} {M : CoxeterMatrix ι} {W : Type*}
    [Group W] [Finite W] (cs : CoxeterSystem M W) {p l π : ι} (hpl : p ≠ l) (hlπ : l ≠ π)
    (hpπ : p ≠ π) (hι : ∀ i, i = p ∨ i = l ∨ i = π) (hMpl : M p l = 3) (hMlπ : M l π = 4)
    (hMpπ : M p π = 2) :
    ∃ z : W, (∀ w, cs.length w ≤ cs.length z) ∧ ∀ w, z * w = w * z :=
  ⟨CFSG.Monster.B.Geometry.longest cs Set.univ, fun w =>
    (CFSG.Monster.B.Geometry.isLongest_univ (cs := cs)).2 w (by rw [cs.parabolic_univ]; trivial),
    CFSG.Monster.B.Geometry.longest_comm_C3 hpl hlπ hpπ hι hMpl hMlπ hMpπ⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
