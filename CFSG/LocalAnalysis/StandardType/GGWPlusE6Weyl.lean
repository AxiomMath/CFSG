module

public import CFSG.LieType.Chevalley.WeylRoots
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.StandardType

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

open scoped commutatorElement

private abbrev e6s (i : Fin 6) : WeylGroup .E6 := simple .E6 i

private abbrev e6M : CoxeterMatrix (Fin 6) :=
  TauCeti.coxeterMatrixOfCartanMatrix (Tag.cartanE 6) (by decide) (by decide)

private def weylE6Even : Subgroup (WeylGroup .E6) :=
  Subgroup.closure (Set.range fun p : Fin 6 × Fin 6 => e6s p.1 * e6s p.2)

private lemma weylE6Even_gen (a b : Fin 6) :
    e6s a * e6s b ∈ weylE6Even :=
  Subgroup.mem_closure_of_mem (Set.mem_range_self (a, b))

private lemma commutator_eq_of_inverts {G : Type*} [Group G] {s t k : G}
    (hs : s * s = 1) (ht : t * t = 1) (hk : k * k = 1)
    (hst : (s * t) ^ 3 = 1) (hsk : s * k = k * s) (htk : t * k = k * t) :
    ⁅s * k, s * t⁆ = s * t := by
  have hinv : (s * k) * (s * t) * (s * k)⁻¹ = (s * t)⁻¹ := by
    have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
    have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have hk' : k⁻¹ = k := inv_eq_of_mul_eq_one_right hk
    rw [mul_inv_rev, hs', hk', mul_inv_rev, ht', hs']
    simp only [← mul_assoc]
    rw [hsk, mul_assoc k s s, hs, mul_one, ← htk, mul_assoc t k k, hk, mul_one]
  rw [commutatorElement_def, hinv]
  have h3 : (s * t) * (s * t) * (s * t) = 1 := by
    have h := hst
    rw [pow_three] at h
    simpa only [mul_assoc] using h
  calc
    (s * t)⁻¹ * (s * t)⁻¹ = (s * t)⁻¹ * (s * t)⁻¹ * ((s * t) * (s * t) * (s * t)) := by
      rw [h3, mul_one]
    _ = s * t := by group

private lemma e6M_eq_three (i j : Fin 6) (h : Tag.cartanE 6 i j * Tag.cartanE 6 j i = 1) :
    e6M i j = 3 := by
  rw [TauCeti.coxeterMatrixOfCartanMatrix_apply, h, TauCeti.coxeterOrder_one]

private lemma e6M_eq_two (i j : Fin 6) (h : Tag.cartanE 6 i j * Tag.cartanE 6 j i = 0) :
    e6M i j = 2 := by
  rw [TauCeti.coxeterMatrixOfCartanMatrix_apply, h, TauCeti.coxeterOrder_zero]

private lemma e6M_pow_three (i j : Fin 6) (hM : e6M i j = 3) :
    (e6s i * e6s j) ^ 3 = 1 := by
  show (e6M.toCoxeterSystem.simple i * e6M.toCoxeterSystem.simple j) ^ 3 = 1
  have h := e6M.toCoxeterSystem.simple_mul_simple_pow i j
  rwa [hM] at h

private lemma e6M_commute (i j : Fin 6) (hM : e6M i j = 2) :
    e6s i * e6s j = e6s j * e6s i := by
  have hsi : (e6s i)⁻¹ = e6s i := (coxeterSystem .E6).inv_simple i
  have hsj : (e6s j)⁻¹ = e6s j := (coxeterSystem .E6).inv_simple j
  have h2' : (e6s i * e6s j) * (e6s i * e6s j) = 1 := by
    show (e6M.toCoxeterSystem.simple i * e6M.toCoxeterSystem.simple j) *
        (e6M.toCoxeterSystem.simple i * e6M.toCoxeterSystem.simple j) = 1
    have h := e6M.toCoxeterSystem.simple_mul_simple_pow i j
    have h2 : (e6M.toCoxeterSystem.simple i * e6M.toCoxeterSystem.simple j) ^ 2 = 1 := by
      rwa [hM] at h
    simpa [pow_two] using h2
  have h1 : e6s i * e6s j = (e6s i * e6s j)⁻¹ :=
    (mul_eq_one_iff_inv_eq.mp h2').symm
  rw [h1, mul_inv_rev, hsi, hsj]

private lemma edge_mem_commutator {i j k : Fin 6}
    (h3 : e6M i j = 3) (hik : e6M i k = 2) (hjk : e6M j k = 2) :
    e6s i * e6s j ∈ ⁅weylE6Even, weylE6Even⁆ := by
  have hpow : (e6s i * e6s j) ^ 3 = 1 := e6M_pow_three i j h3
  have hik' : e6s i * e6s k = e6s k * e6s i := e6M_commute i k hik
  have hjk' : e6s j * e6s k = e6s k * e6s j := e6M_commute j k hjk
  have hcomm : ⁅e6s i * e6s k, e6s i * e6s j⁆ = e6s i * e6s j :=
    commutator_eq_of_inverts ((coxeterSystem .E6).simple_mul_simple_self i)
      ((coxeterSystem .E6).simple_mul_simple_self j) ((coxeterSystem .E6).simple_mul_simple_self k)
      hpow hik' hjk'
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (weylE6Even_gen i k) (weylE6Even_gen i j)

private lemma e6path1 : e6s 0 * e6s 1 =
    (e6s 0 * e6s 2) * (e6s 2 * e6s 3) * (e6s 3 * e6s 1) := by
  show (coxeterSystem .E6).simple (0 : Fin 6) * (coxeterSystem .E6).simple (1 : Fin 6) =
    ((coxeterSystem .E6).simple (0 : Fin 6) * (coxeterSystem .E6).simple (2 : Fin 6)) *
      ((coxeterSystem .E6).simple (2 : Fin 6) * (coxeterSystem .E6).simple (3 : Fin 6)) *
      ((coxeterSystem .E6).simple (3 : Fin 6) * (coxeterSystem .E6).simple (1 : Fin 6))
  simp only [mul_assoc]
  rw [(coxeterSystem .E6).simple_mul_simple_cancel_left (2 : Fin 6),
    (coxeterSystem .E6).simple_mul_simple_cancel_left (3 : Fin 6)]

private lemma e6path3 : e6s 0 * e6s 3 =
    (e6s 0 * e6s 2) * (e6s 2 * e6s 3) := by
  show (coxeterSystem .E6).simple (0 : Fin 6) * (coxeterSystem .E6).simple (3 : Fin 6) =
    ((coxeterSystem .E6).simple (0 : Fin 6) * (coxeterSystem .E6).simple (2 : Fin 6)) *
      ((coxeterSystem .E6).simple (2 : Fin 6) * (coxeterSystem .E6).simple (3 : Fin 6))
  simp only [mul_assoc]
  rw [(coxeterSystem .E6).simple_mul_simple_cancel_left (2 : Fin 6)]

private lemma e6path4 : e6s 0 * e6s 4 =
    (e6s 0 * e6s 2) * (e6s 2 * e6s 3) * (e6s 3 * e6s 4) := by
  show (coxeterSystem .E6).simple (0 : Fin 6) * (coxeterSystem .E6).simple (4 : Fin 6) =
    ((coxeterSystem .E6).simple (0 : Fin 6) * (coxeterSystem .E6).simple (2 : Fin 6)) *
      ((coxeterSystem .E6).simple (2 : Fin 6) * (coxeterSystem .E6).simple (3 : Fin 6)) *
      ((coxeterSystem .E6).simple (3 : Fin 6) * (coxeterSystem .E6).simple (4 : Fin 6))
  simp only [mul_assoc]
  rw [(coxeterSystem .E6).simple_mul_simple_cancel_left (2 : Fin 6),
    (coxeterSystem .E6).simple_mul_simple_cancel_left (3 : Fin 6)]

private lemma e6path5 : e6s 0 * e6s 5 =
    (e6s 0 * e6s 2) * (e6s 2 * e6s 3) * (e6s 3 * e6s 4) * (e6s 4 * e6s 5) := by
  show (coxeterSystem .E6).simple (0 : Fin 6) * (coxeterSystem .E6).simple (5 : Fin 6) =
    ((coxeterSystem .E6).simple (0 : Fin 6) * (coxeterSystem .E6).simple (2 : Fin 6)) *
      ((coxeterSystem .E6).simple (2 : Fin 6) * (coxeterSystem .E6).simple (3 : Fin 6)) *
      ((coxeterSystem .E6).simple (3 : Fin 6) * (coxeterSystem .E6).simple (4 : Fin 6)) *
      ((coxeterSystem .E6).simple (4 : Fin 6) * (coxeterSystem .E6).simple (5 : Fin 6))
  simp only [mul_assoc]
  rw [(coxeterSystem .E6).simple_mul_simple_cancel_left (2 : Fin 6),
    (coxeterSystem .E6).simple_mul_simple_cancel_left (3 : Fin 6),
    (coxeterSystem .E6).simple_mul_simple_cancel_left (4 : Fin 6)]

private lemma weylE6Even_zero_mem (b : Fin 6) :
    e6s 0 * e6s b ∈ ⁅weylE6Even, weylE6Even⁆ := by
  fin_cases b
  · show e6s 0 * e6s 0 ∈ ⁅weylE6Even, weylE6Even⁆
    rw [(coxeterSystem .E6).simple_mul_simple_self (0 : Fin 6)]
    exact Subgroup.one_mem _
  · show e6s 0 * e6s 1 ∈ ⁅weylE6Even, weylE6Even⁆
    rw [e6path1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (edge_mem_commutator (e6M_eq_three 0 2 (by decide))
        (e6M_eq_two 0 1 (by decide)) (e6M_eq_two 2 1 (by decide)))
      (edge_mem_commutator (e6M_eq_three 2 3 (by decide))
        (e6M_eq_two 2 5 (by decide)) (e6M_eq_two 3 5 (by decide))))
      (edge_mem_commutator (e6M_eq_three 3 1 (by decide))
        (e6M_eq_two 3 0 (by decide)) (e6M_eq_two 1 0 (by decide)))
  · show e6s 0 * e6s 2 ∈ ⁅weylE6Even, weylE6Even⁆
    exact edge_mem_commutator (e6M_eq_three 0 2 (by decide))
      (e6M_eq_two 0 1 (by decide)) (e6M_eq_two 2 1 (by decide))
  · show e6s 0 * e6s 3 ∈ ⁅weylE6Even, weylE6Even⁆
    rw [e6path3]
    exact Subgroup.mul_mem _
      (edge_mem_commutator (e6M_eq_three 0 2 (by decide))
        (e6M_eq_two 0 1 (by decide)) (e6M_eq_two 2 1 (by decide)))
      (edge_mem_commutator (e6M_eq_three 2 3 (by decide))
        (e6M_eq_two 2 5 (by decide)) (e6M_eq_two 3 5 (by decide)))
  · show e6s 0 * e6s 4 ∈ ⁅weylE6Even, weylE6Even⁆
    rw [e6path4]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (edge_mem_commutator (e6M_eq_three 0 2 (by decide))
        (e6M_eq_two 0 1 (by decide)) (e6M_eq_two 2 1 (by decide)))
      (edge_mem_commutator (e6M_eq_three 2 3 (by decide))
        (e6M_eq_two 2 5 (by decide)) (e6M_eq_two 3 5 (by decide))))
      (edge_mem_commutator (e6M_eq_three 3 4 (by decide))
        (e6M_eq_two 3 0 (by decide)) (e6M_eq_two 4 0 (by decide)))
  · show e6s 0 * e6s 5 ∈ ⁅weylE6Even, weylE6Even⁆
    rw [e6path5]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (edge_mem_commutator (e6M_eq_three 0 2 (by decide))
        (e6M_eq_two 0 1 (by decide)) (e6M_eq_two 2 1 (by decide)))
      (edge_mem_commutator (e6M_eq_three 2 3 (by decide))
        (e6M_eq_two 2 5 (by decide)) (e6M_eq_two 3 5 (by decide))))
      (edge_mem_commutator (e6M_eq_three 3 4 (by decide))
        (e6M_eq_two 3 0 (by decide)) (e6M_eq_two 4 0 (by decide))))
      (edge_mem_commutator (e6M_eq_three 4 5 (by decide))
        (e6M_eq_two 4 2 (by decide)) (e6M_eq_two 5 2 (by decide)))

private lemma weylE6Even_gen_mem_commutator (a b : Fin 6) :
    e6s a * e6s b ∈ ⁅weylE6Even, weylE6Even⁆ := by
  have h0a : (e6s 0 * e6s a)⁻¹ ∈ ⁅weylE6Even, weylE6Even⁆ :=
    Subgroup.inv_mem _ (weylE6Even_zero_mem a)
  have h := Subgroup.mul_mem _ h0a (weylE6Even_zero_mem b)
  have hid : (e6s 0 * e6s a)⁻¹ * (e6s 0 * e6s b) = e6s a * e6s b := by
    show ((coxeterSystem .E6).simple (0 : Fin 6) * (coxeterSystem .E6).simple a)⁻¹ *
        ((coxeterSystem .E6).simple (0 : Fin 6) * (coxeterSystem .E6).simple b) =
      (coxeterSystem .E6).simple a * (coxeterSystem .E6).simple b
    rw [mul_inv_rev, (coxeterSystem .E6).inv_simple (0 : Fin 6),
      (coxeterSystem .E6).inv_simple a]
    simp only [mul_assoc]
    rw [(coxeterSystem .E6).simple_mul_simple_cancel_left (0 : Fin 6)]
  rwa [hid] at h

private lemma weylE6Even_perfect : ⁅weylE6Even, weylE6Even⁆ = weylE6Even := by
  apply le_antisymm (Subgroup.commutator_le_self _)
  rw [weylE6Even, Subgroup.closure_le]
  rintro x ⟨p, rfl⟩
  exact weylE6Even_gen_mem_commutator p.1 p.2

private lemma weylE6_cover (w : WeylGroup .E6) :
    w ∈ weylE6Even ∨ e6s 0 * w ∈ weylE6Even := by
  induction w using (coxeterSystem .E6).simple_induction_left with
  | one => exact Or.inl (Subgroup.one_mem _)
  | mul_simple_left w i ih =>
    rcases ih with hw | hw
    · right
      rw [← mul_assoc]
      exact Subgroup.mul_mem _ (weylE6Even_gen 0 i) hw
    · left
      have h : e6s i * w = (e6s i * e6s 0) * (e6s 0 * w) := by
        show simple .E6 i * w = (simple .E6 i * simple .E6 (0 : Fin 6)) *
          (simple .E6 (0 : Fin 6) * w)
        rw [mul_assoc, ← mul_assoc (simple .E6 (0 : Fin 6)),
          (coxeterSystem .E6).simple_mul_simple_self (0 : Fin 6), one_mul]
      rw [h]
      exact Subgroup.mul_mem _ (weylE6Even_gen i 0) hw

theorem weylE6_solvable_quotient_card_le_two {Q : Type*} [Group Q]
    (f : WeylGroup .E6 →* Q) (hf : Function.Surjective f) (hQ : IsSolvable Q) :
    Nat.card Q ≤ 2 := by
  haveI : IsSolvable Q := hQ
  have hmap : weylE6Even.map f = ⊥ := by
    by_contra hne
    have hlt : ⁅weylE6Even.map f, weylE6Even.map f⁆ < weylE6Even.map f :=
      @IsSolvable.commutator_lt_of_ne_bot Q _ hQ (weylE6Even.map f) hne
    rw [← Subgroup.map_commutator weylE6Even weylE6Even f, weylE6Even_perfect] at hlt
    exact (lt_irrefl _) hlt
  have hsurj : Function.Surjective
      (fun b : Fin 2 => if b = 0 then (1 : Q) else (f (e6s 0))⁻¹) := by
    intro q
    obtain ⟨w, rfl⟩ := hf q
    rcases weylE6_cover w with hw | hw
    · refine ⟨0, ?_⟩
      have hfw : f w = 1 := by
        have : f w ∈ weylE6Even.map f := Subgroup.mem_map_of_mem f hw
        rw [hmap] at this
        simpa using this
      simp [hfw]
    · refine ⟨1, ?_⟩
      have hfw : f (e6s 0 * w) = 1 := by
        have : f (e6s 0 * w) ∈ weylE6Even.map f := Subgroup.mem_map_of_mem f hw
        rw [hmap] at this
        simpa using this
      rw [map_mul] at hfw
      have hfinv : (f (e6s 0))⁻¹ = f w := mul_eq_one_iff_inv_eq.mp hfw
      simp [hfinv]
  have hcard := Nat.card_le_card_of_surjective
      (fun b : Fin 2 => if b = 0 then (1 : Q) else (f (e6s 0))⁻¹) hsurj
  simpa using hcard

end CFSG.StandardType
