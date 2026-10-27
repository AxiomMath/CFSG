module

public import CFSG.Quasithin.AppendixH.H9.GLBasics
public import CFSG.Quasithin.AppendixH.H9.SylowModel
import CFSG.Quasithin.AppendixH.H9.F2Basic

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

section OrbitLemmas

variable {n : ℕ}

private lemma fst_pairVec_eq_one_iff (a b : Fin n → ZMod 2) : (pairVec a b).1 = 1 ↔ a = 0 := by
  simp [pairVec]

private lemma snd_pairVec_eq_one_iff (a b : Fin n → ZMod 2) : (pairVec a b).2 = 1 ↔ b = 0 := by
  simp [pairVec]

private lemma pairVec_eq_one_iff (a b : Fin n → ZMod 2) : pairVec a b = 1 ↔ a = 0 ∧ b = 0 := by
  rw [pairVec_one, pairVec_inj]

private lemma mem_Oorb_zero {a b : Fin n → ZMod 2} :
    pairVec a b ∈ Oorb n 0 ↔ (a ≠ 0 ∧ b = 0) ∨ (a = 0 ∧ b ≠ 0) := by
  show (pairVec a b ≠ 1 ∧ (pairVec a b ∈ V1n n ∨ pairVec a b ∈ V2n n)) ↔ _
  rw [mem_V1n, mem_V2n, snd_pairVec_eq_one_iff, fst_pairVec_eq_one_iff, Ne, pairVec_eq_one_iff]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]

private lemma mem_Oorb_one {a b : Fin n → ZMod 2} :
    pairVec a b ∈ Oorb n 1 ↔ a ≠ 0 ∧ b ≠ 0 ∧ a ⬝ᵥ b = 0 := by
  show ((pairVec a b).1 ≠ 1 ∧ (pairVec a b).2 ≠ 1 ∧ pairQn n (pairVec a b) = 0) ↔ _
  rw [Ne, Ne, fst_pairVec_eq_one_iff, snd_pairVec_eq_one_iff, pairQn_pairVec]

private lemma mem_Oorb_two {a b : Fin n → ZMod 2} :
    pairVec a b ∈ Oorb n 2 ↔ a ≠ 0 ∧ b ≠ 0 ∧ a ⬝ᵥ b = 1 := by
  show ((pairVec a b).1 ≠ 1 ∧ (pairVec a b).2 ≠ 1 ∧ pairQn n (pairVec a b) = 1) ↔ _
  rw [Ne, Ne, fst_pairVec_eq_one_iff, snd_pairVec_eq_one_iff, pairQn_pairVec]

private lemma Mg_apply_pairVec {g : MulAut (PairN n)} (hg : g ∈ Mg n) (a b : Fin n → ZMod 2) :
    ∃ a' b' : Fin n → ZMod 2, g (pairVec a b) = pairVec a' b' ∧
      (((a' = 0 ↔ a = 0) ∧ (b' = 0 ↔ b = 0)) ∨ ((a' = 0 ↔ b = 0) ∧ (b' = 0 ↔ a = 0))) := by
  rcases mem_Mg_iff.mp hg with hL | ⟨A, rfl⟩
  · obtain ⟨A, rfl⟩ := mem_Lg_iff.mp hL
    exact ⟨_, _, pairActN_pairVec A a b,
      Or.inl ⟨GL_mulVec_eq_zero_iff A a, GL_mulVec_eq_zero_iff (dualGLn n A) b⟩⟩
  · refine ⟨(A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ b,
      ((dualGLn n A : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a, ?_,
      Or.inr ⟨GL_mulVec_eq_zero_iff A b, GL_mulVec_eq_zero_iff (dualGLn n A) a⟩⟩
    rw [MulAut.mul_apply, swapN_pairVec, pairActN_pairVec]

private lemma exists_Mg_apply_V1 {a a' : Fin n → ZMod 2} (ha : a ≠ 0) (ha' : a' ≠ 0) :
    ∃ g ∈ Mg n, g (pairVec a 0) = pairVec a' 0 := by
  obtain ⟨A, hA⟩ := exists_GL_mulVec_eq ha ha'
  refine ⟨pairActN n A, Lg_le_Mg (pairActN_mem_Lg A), ?_⟩
  rw [pairActN_pairVec, hA, Matrix.mulVec_zero]

private lemma exists_Mg_apply_V2 {b b' : Fin n → ZMod 2} (hb : b ≠ 0) (hb' : b' ≠ 0) :
    ∃ g ∈ Mg n, g (pairVec 0 b) = pairVec 0 b' := by
  obtain ⟨A, hA⟩ := exists_GL_mulVec_eq hb hb'
  refine ⟨pairActN n (dualGLn n A), Lg_le_Mg (pairActN_mem_Lg _), ?_⟩
  rw [pairActN_pairVec, dualGLn_dualGLn, hA, Matrix.mulVec_zero]

private lemma transitive_Oorb_zero {x y : PairN n} (hx : x ∈ Oorb n 0) (hy : y ∈ Oorb n 0) :
    ∃ g ∈ Mg n, g x = y := by
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  obtain ⟨a', b', rfl⟩ := pairVec_surj y
  rw [mem_Oorb_zero] at hx hy
  rcases hx with ⟨ha, rfl⟩ | ⟨rfl, hb⟩ <;> rcases hy with ⟨ha', rfl⟩ | ⟨rfl, hb'⟩
  · exact exists_Mg_apply_V1 ha ha'
  · obtain ⟨g, hg, hgx⟩ := exists_Mg_apply_V2 ha hb'
    refine ⟨g * swapN n, Subgroup.mul_mem _ hg swapN_mem_Mg, ?_⟩
    rw [MulAut.mul_apply, swapN_pairVec, hgx]
  · obtain ⟨g, hg, hgx⟩ := exists_Mg_apply_V1 hb ha'
    refine ⟨g * swapN n, Subgroup.mul_mem _ hg swapN_mem_Mg, ?_⟩
    rw [MulAut.mul_apply, swapN_pairVec, hgx]
  · exact exists_Mg_apply_V2 hb hb'

private lemma exists_Mg_apply_pair {a b a' b' : Fin n → ZMod 2} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha' : a' ≠ 0) (hb' : b' ≠ 0) (h : a ⬝ᵥ b = a' ⬝ᵥ b') :
    ∃ g ∈ Mg n, g (pairVec a b) = pairVec a' b' := by
  obtain ⟨A, hA1, hA2⟩ := exists_GL_mulVec_pair ha hb ha' hb'
    (by rw [dotProduct_comm b a, dotProduct_comm b' a', h])
  refine ⟨pairActN n A, Lg_le_Mg (pairActN_mem_Lg A), ?_⟩
  rw [pairActN_pairVec, hA1, hA2]

private lemma transitive_Oorb_one {x y : PairN n} (hx : x ∈ Oorb n 1) (hy : y ∈ Oorb n 1) :
    ∃ g ∈ Mg n, g x = y := by
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  obtain ⟨a', b', rfl⟩ := pairVec_surj y
  rw [mem_Oorb_one] at hx hy
  exact exists_Mg_apply_pair hx.1 hx.2.1 hy.1 hy.2.1 (hx.2.2.trans hy.2.2.symm)

private lemma transitive_Oorb_two {x y : PairN n} (hx : x ∈ Oorb n 2) (hy : y ∈ Oorb n 2) :
    ∃ g ∈ Mg n, g x = y := by
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  obtain ⟨a', b', rfl⟩ := pairVec_surj y
  rw [mem_Oorb_two] at hx hy
  exact exists_Mg_apply_pair hx.1 hx.2.1 hy.1 hy.2.1 (hx.2.2.trans hy.2.2.symm)

private lemma Oorb_invariant (i : Fin 3) {x : PairN n} (hx : x ∈ Oorb n i) {g : MulAut (PairN n)}
    (hg : g ∈ Mg n) : g x ∈ Oorb n i := by
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  obtain ⟨a', b', hgx, hz⟩ := Mg_apply_pairVec hg a b
  have hq := pairQn_of_mem_Mg hg (pairVec a b)
  rw [hgx, pairQn_pairVec, pairQn_pairVec] at hq
  rw [hgx]
  match i, hx with
  | 0, hx =>
    rw [mem_Oorb_zero] at hx ⊢
    rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> tauto
  | 1, hx =>
    rw [mem_Oorb_one] at hx ⊢
    refine ⟨?_, ?_, hq.trans hx.2.2⟩ <;> rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> tauto
  | 2, hx =>
    rw [mem_Oorb_two] at hx ⊢
    refine ⟨?_, ?_, hq.trans hx.2.2⟩ <;> rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> tauto

private lemma exists_mem_Oorb {x : PairN n} (hx : x ≠ 1) : ∃ i : Fin 3, x ∈ Oorb n i := by
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  rw [Ne, pairVec_eq_one_iff] at hx
  by_cases ha : a = 0
  · exact ⟨0, mem_Oorb_zero.mpr (Or.inr ⟨ha, fun hb => hx ⟨ha, hb⟩⟩)⟩
  by_cases hb : b = 0
  · exact ⟨0, mem_Oorb_zero.mpr (Or.inl ⟨ha, hb⟩)⟩
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (a ⬝ᵥ b) with h | h
  · exact ⟨1, mem_Oorb_one.mpr ⟨ha, hb, h⟩⟩
  · exact ⟨2, mem_Oorb_two.mpr ⟨ha, hb, h⟩⟩

private lemma disjoint_Oorb_zero_one : Disjoint (Oorb n 0) (Oorb n 1) := by
  rw [Set.disjoint_left]
  intro x hx0 hx1
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  rw [mem_Oorb_zero] at hx0
  rw [mem_Oorb_one] at hx1
  rcases hx0 with ⟨_, h⟩ | ⟨h, _⟩
  · exact hx1.2.1 h
  · exact hx1.1 h

private lemma disjoint_Oorb_zero_two : Disjoint (Oorb n 0) (Oorb n 2) := by
  rw [Set.disjoint_left]
  intro x hx0 hx1
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  rw [mem_Oorb_zero] at hx0
  rw [mem_Oorb_two] at hx1
  rcases hx0 with ⟨_, h⟩ | ⟨h, _⟩
  · exact hx1.2.1 h
  · exact hx1.1 h

private lemma disjoint_Oorb_one_two : Disjoint (Oorb n 1) (Oorb n 2) := by
  rw [Set.disjoint_left]
  intro x hx0 hx1
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  rw [mem_Oorb_one] at hx0
  rw [mem_Oorb_two] at hx1
  have h := hx0.2.2.symm.trans hx1.2.2
  exact absurd h (by decide)

private lemma disjoint_Oorb {i j : Fin 3} (hij : i ≠ j) : Disjoint (Oorb n i) (Oorb n j) := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact disjoint_Oorb_zero_one
  · exact disjoint_Oorb_zero_two
  · exact disjoint_Oorb_zero_one.symm
  · exact absurd rfl hij
  · exact disjoint_Oorb_one_two
  · exact disjoint_Oorb_zero_two.symm
  · exact disjoint_Oorb_one_two.symm
  · exact absurd rfl hij

private lemma pairQn_eq_zero_of_mem_Oorb_zero {x : PairN n} (hx : x ∈ Oorb n 0) :
    pairQn n x = 0 := by
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  rw [mem_Oorb_zero] at hx
  rw [pairQn_pairVec]
  rcases hx with ⟨_, rfl⟩ | ⟨rfl, _⟩
  · exact dotProduct_zero a
  · exact zero_dotProduct b

end OrbitLemmas

section TwoCentralVectors

private lemma x0_mem_Oorb_one (m : ℕ) (hm : 1 ≤ m) : pairVec (ez m) (ezl m) ∈ Oorb (m + 1) 1 := by
  have hne : (Fin.last m : Fin (m + 1)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  rw [mem_Oorb_one]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp [ez] at this
  · intro h
    have := congrFun h (Fin.last m)
    simp [ezl] at this
  · rw [ezl, dotProduct_single, ez, Pi.single_eq_of_ne hne, zero_mul]

private lemma isTwoCentralVec_x0 (m : ℕ) (hm : 1 ≤ m) :
    IsTwoCentralVec (Mg (m + 1)) (pairVec (ez m) (ezl m)) := by
  refine ⟨T0 (m + 1), isSylowIn_T0 (Nat.succ_pos m), fun s hs => ?_⟩
  have h := (mem_fixV_T0_iff m hm (pairVec (ez m) (ezl m))).mpr (Or.inr rfl)
  exact mem_fixV.mp h s hs

private lemma isTwoCentralVec_of_mem_Oorb_one (m : ℕ) (hm : 1 ≤ m) {x : PairN (m + 1)}
    (hx : x ∈ Oorb (m + 1) 1) : IsTwoCentralVec (Mg (m + 1)) x := by
  obtain ⟨g, hg, hgx⟩ := transitive_Oorb_one (x0_mem_Oorb_one m hm) hx
  rw [← hgx]
  exact (isTwoCentralVec_iff_of_mem hg _).mpr (isTwoCentralVec_x0 m hm)

private lemma mem_Oorb_one_of_isTwoCentralVec (m : ℕ) (hm : 1 ≤ m) {x : PairN (m + 1)}
    (hx1 : x ≠ 1) (h : IsTwoCentralVec (Mg (m + 1)) x) : x ∈ Oorb (m + 1) 1 := by
  obtain ⟨S, hS, hSx⟩ := h
  obtain ⟨l, hl, rfl⟩ := exists_Lg_conj_T0 (Nat.succ_pos m) hS
  have hfix : l⁻¹ x ∈ fixV (T0 (m + 1)) := by
    refine mem_fixV.mpr ?_
    intro s hs
    have hmem := conj_mem_conjAut (g := l) hs
    have h1 : l (s (l⁻¹ x)) = x := hSx _ hmem
    calc s (l⁻¹ x) = l⁻¹ (l (s (l⁻¹ x))) := (MulAut.inv_apply_self _ _ _).symm
      _ = l⁻¹ x := by rw [h1]
  rcases (mem_fixV_T0_iff m hm _).mp hfix with h1 | h1
  · exfalso
    apply hx1
    calc x = l (l⁻¹ x) := (MulAut.apply_inv_self _ l x).symm
      _ = 1 := by rw [h1, map_one]
  · have hx : x = l (pairVec (ez m) (ezl m)) := by
      rw [← h1]
      exact (MulAut.apply_inv_self _ l x).symm
    rw [hx]
    exact Oorb_invariant 1 (x0_mem_Oorb_one m hm) (Lg_le_Mg hl)

end TwoCentralVectors

theorem h91_clause2 (n : ℕ) (hn : 2 ≤ n) :
    ((∀ i : Fin 3, ∀ x ∈ Oorb n i, ∀ g ∈ Mg n, g x ∈ Oorb n i) ∧
      (∀ i : Fin 3, ∀ x ∈ Oorb n i, ∀ y ∈ Oorb n i, ∃ g ∈ Mg n, g x = y) ∧
      (∀ x : PairN n, x ≠ 1 → ∃ i : Fin 3, x ∈ Oorb n i) ∧
      (∀ i j : Fin 3, i ≠ j → Disjoint (Oorb n i) (Oorb n j)) ∧
      (∀ x ∈ Oorb n 0, pairQn n x = 0) ∧
      (∀ x : PairN n, x ≠ 1 → (IsTwoCentralVec (Mg n) x ↔ x ∈ Oorb n 1))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  refine ⟨fun i x hx g hg => Oorb_invariant i hx hg, ?_, fun x hx => exists_mem_Oorb hx,
    fun i j hij => disjoint_Oorb hij, fun x hx => pairQn_eq_zero_of_mem_Oorb_zero hx,
    fun x hx1 => ⟨fun h => mem_Oorb_one_of_isTwoCentralVec m hm hx1 h,
      fun h => isTwoCentralVec_of_mem_Oorb_one m hm h⟩⟩
  intro i
  match i with
  | 0 => exact fun x hx y hy => transitive_Oorb_zero hx hy
  | 1 => exact fun x hx y hy => transitive_Oorb_one hx hy
  | 2 => exact fun x hx y hy => transitive_Oorb_two hx hy

end CFSG.ASVolI.ChH
