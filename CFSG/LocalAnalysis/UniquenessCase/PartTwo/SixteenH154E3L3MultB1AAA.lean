module

public import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

abbrev s16h_l3Vec : Type := Fin 3 → ZMod 2

abbrev s16h_l3Mat : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

def s16h_l3E (i j : Fin 3) : s16h_l3Mat := Matrix.single i j (1 : ZMod 2)

def s16h_l3SingleRow (i : Fin 3) (v : s16h_l3Vec) : s16h_l3Mat :=
  Matrix.of (fun a b => if a = i then v b else 0)

abbrev s16h_l3RowSpace (m : s16h_l3Mat) : Submodule (ZMod 2) s16h_l3Vec :=
  Submodule.span (ZMod 2) (Set.range m)

abbrev s16h_l3RowSub (R : Submodule (ZMod 2) s16h_l3Vec) : AddSubgroup s16h_l3Mat where
  carrier := {h | ∀ i, h i ∈ R}
  add_mem' := fun ha hb i => R.add_mem (ha i) (hb i)
  zero_mem' := fun i => R.zero_mem
  neg_mem' := fun ha i => R.neg_mem (ha i)

@[simp] theorem s16h_l3RowSub_mem {R : Submodule (ZMod 2) s16h_l3Vec} {h : s16h_l3Mat} :
    h ∈ s16h_l3RowSub R ↔ ∀ i, h i ∈ R := Iff.rfl

@[simp] private theorem s16h_l3SingleRow_apply (i a b : Fin 3) (v : s16h_l3Vec) :
    s16h_l3SingleRow i v a b = if a = i then v b else 0 := rfl

private theorem s16h_l3Mat_add_self (m : s16h_l3Mat) : m + m = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [← two_smul (ZMod 2) m, h2, zero_smul]

private theorem s16h_l3SingleRow_zero (i : Fin 3) : s16h_l3SingleRow i 0 = 0 := by
  ext a b
  simp

private theorem s16h_l3SingleRow_add (i : Fin 3) (v w : s16h_l3Vec) :
    s16h_l3SingleRow i (v + w) = s16h_l3SingleRow i v + s16h_l3SingleRow i w := by
  ext a b
  by_cases ha : a = i <;> simp [ha]

private theorem s16h_l3SingleRow_smul (i : Fin 3) (c : ZMod 2) (v : s16h_l3Vec) :
    s16h_l3SingleRow i (c • v) = c • s16h_l3SingleRow i v := by
  ext a b
  by_cases ha : a = i <;> simp [ha]

private theorem s16h_l3E_mul_eq_singleRow (i j : Fin 3) (m : s16h_l3Mat) :
    s16h_l3E i j * m = s16h_l3SingleRow i (m j) := by
  ext a b
  by_cases ha : a = i
  · subst ha
    simp [s16h_l3E]
  · simp [s16h_l3E, ha]

private def s16h_l3OrbitClosure (m : s16h_l3Mat) : AddSubgroup s16h_l3Mat :=
  AddSubgroup.closure (Set.range fun g : GL (Fin 3) (ZMod 2) => (g : s16h_l3Mat) * m)

private theorem s16h_l3E_mul_mem_closure_of_ne (m : s16h_l3Mat) {i j : Fin 3} (hij : i ≠ j) :
    s16h_l3E i j * m ∈ s16h_l3OrbitClosure m := by
  change s16h_l3E i j * m ∈ s16h_l3OrbitClosure m
  have h1 : ((1 : s16h_l3Mat) + s16h_l3E i j) * m ∈ s16h_l3OrbitClosure m := by
    apply AddSubgroup.subset_closure
    refine ⟨Matrix.GeneralLinearGroup.transvection i j hij (1 : ZMod 2), ?_⟩
    simp [s16h_l3E, Matrix.GeneralLinearGroup.transvection, Matrix.transvection]
  have h0 : m ∈ s16h_l3OrbitClosure m := AddSubgroup.subset_closure ⟨1, by simp⟩
  have hmm : m + m = 0 := s16h_l3Mat_add_self m
  have hEq : s16h_l3E i j * m = ((1 : s16h_l3Mat) + s16h_l3E i j) * m + m := by
    rw [Matrix.add_mul, Matrix.one_mul]
    have key : (m + s16h_l3E i j * m) + m = s16h_l3E i j * m := by
      calc (m + s16h_l3E i j * m) + m = (m + m) + s16h_l3E i j * m := by abel
        _ = s16h_l3E i j * m := by rw [hmm, zero_add]
    rw [key]
  rw [hEq]
  exact (s16h_l3OrbitClosure m).add_mem h1 h0

private theorem s16h_l3E_mul_mem_closure_self (m : s16h_l3Mat) (i : Fin 3) :
    s16h_l3E i i * m ∈ s16h_l3OrbitClosure m := by
  obtain ⟨k, hki⟩ : ∃ k : Fin 3, k ≠ i := by
    fin_cases i
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨0, by decide⟩
  have hik : i ≠ k := hki.symm
  let G : GL (Fin 3) (ZMod 2) :=
    Matrix.GeneralLinearGroup.transvection i k hik (1 : ZMod 2) *
      Matrix.GeneralLinearGroup.transvection k i hki (1 : ZMod 2)
  have hGmem : (G : s16h_l3Mat) * m ∈ s16h_l3OrbitClosure m :=
    AddSubgroup.subset_closure ⟨G, rfl⟩
  have h0 : m ∈ s16h_l3OrbitClosure m := AddSubgroup.subset_closure ⟨1, by simp⟩
  have hik_mem : s16h_l3E i k * m ∈ s16h_l3OrbitClosure m :=
    s16h_l3E_mul_mem_closure_of_ne m hik
  have hki_mem : s16h_l3E k i * m ∈ s16h_l3OrbitClosure m :=
    s16h_l3E_mul_mem_closure_of_ne m hki
  have hGmat : (G : s16h_l3Mat) = 1 + s16h_l3E i k + s16h_l3E k i + s16h_l3E i i := by
    simp only [G, Units.val_mul, Matrix.GeneralLinearGroup.transvection, Matrix.transvection,
      s16h_l3E, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.single_mul_single_same, mul_one]
    abel
  have hGmul : (G : s16h_l3Mat) * m =
      m + s16h_l3E i k * m + s16h_l3E k i * m + s16h_l3E i i * m := by
    rw [hGmat, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul]
  have hEq : s16h_l3E i i * m =
      (G : s16h_l3Mat) * m + m + s16h_l3E i k * m + s16h_l3E k i * m := by
    rw [hGmul]
    have key : (m + s16h_l3E i k * m + s16h_l3E k i * m + s16h_l3E i i * m)
        + m + s16h_l3E i k * m + s16h_l3E k i * m
        = (m + m) + (s16h_l3E i k * m + s16h_l3E i k * m)
          + (s16h_l3E k i * m + s16h_l3E k i * m) + s16h_l3E i i * m := by abel
    rw [key, s16h_l3Mat_add_self m, s16h_l3Mat_add_self (s16h_l3E i k * m),
      s16h_l3Mat_add_self (s16h_l3E k i * m)]
    simp
  rw [hEq]
  exact (s16h_l3OrbitClosure m).add_mem
    ((s16h_l3OrbitClosure m).add_mem ((s16h_l3OrbitClosure m).add_mem hGmem h0) hik_mem) hki_mem

private theorem s16h_l3E_mul_mem_closure (m : s16h_l3Mat) (i j : Fin 3) :
    s16h_l3E i j * m ∈ s16h_l3OrbitClosure m := by
  by_cases hij : i = j
  · subst hij
    exact s16h_l3E_mul_mem_closure_self m i
  · exact s16h_l3E_mul_mem_closure_of_ne m hij

private theorem s16h_l3SingleRow_mem_closure (m : s16h_l3Mat) (i : Fin 3) (v : s16h_l3Vec)
    (hv : v ∈ s16h_l3RowSpace m) : s16h_l3SingleRow i v ∈ s16h_l3OrbitClosure m := by
  refine Submodule.span_induction (p := fun x _ => s16h_l3SingleRow i x ∈ s16h_l3OrbitClosure m)
    ?_ ?_ ?_ ?_ hv
  · rintro x ⟨j, rfl⟩
    rw [← s16h_l3E_mul_eq_singleRow i j m]
    exact s16h_l3E_mul_mem_closure m i j
  · rw [s16h_l3SingleRow_zero]
    exact (s16h_l3OrbitClosure m).zero_mem
  · intro x y _ _ ihx ihy
    rw [s16h_l3SingleRow_add]
    exact (s16h_l3OrbitClosure m).add_mem ihx ihy
  · intro c x _ ihx
    rw [s16h_l3SingleRow_smul]
    rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) c with rfl | rfl
    · rw [zero_smul]
      exact (s16h_l3OrbitClosure m).zero_mem
    · rw [one_smul]
      exact ihx

private theorem s16h_l3SingleRow_sum_self (h : s16h_l3Mat) :
    h = ∑ i : Fin 3, s16h_l3SingleRow i (h i) := by
  ext a b
  rw [Matrix.sum_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro i _ hi
    simp [hi.symm]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

theorem s16h_l3RowSub_invariant (R : Submodule (ZMod 2) s16h_l3Vec) :
    ∀ (g : GL (Fin 3) (ZMod 2)), ∀ m ∈ s16h_l3RowSub R,
      (g : s16h_l3Mat) * m ∈ s16h_l3RowSub R := by
  intro g m hm
  rw [s16h_l3RowSub_mem] at hm ⊢
  intro i
  have hrow : ((g : s16h_l3Mat) * m) i = ∑ k, (g i k) • m k := by
    funext j
    rw [Matrix.mul_apply, Finset.sum_apply]
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hrow]
  exact sum_mem fun k _ => Submodule.smul_mem R (g i k) (hm k)

theorem s16h_l3RowSub_mono {R R' : Submodule (ZMod 2) s16h_l3Vec} (h : R ≤ R') :
    s16h_l3RowSub R ≤ s16h_l3RowSub R' := by
  intro m hm
  rw [s16h_l3RowSub_mem] at hm ⊢
  exact fun i => h (hm i)

theorem s16h_l3RowSub_eq_closure_orbit (m : s16h_l3Mat) :
    s16h_l3RowSub (s16h_l3RowSpace m) =
      AddSubgroup.closure (Set.range fun g : GL (Fin 3) (ZMod 2) => (g : s16h_l3Mat) * m) := by
  change s16h_l3RowSub (s16h_l3RowSpace m) = s16h_l3OrbitClosure m
  apply le_antisymm
  · intro h hh
    rw [s16h_l3SingleRow_sum_self h]
    exact sum_mem fun i _ =>
      s16h_l3SingleRow_mem_closure m i (h i) ((s16h_l3RowSub_mem.mp hh) i)
  · apply (AddSubgroup.closure_le _).mpr
    rintro x ⟨g, rfl⟩
    change ∀ i, ((g : s16h_l3Mat) * m) i ∈ s16h_l3RowSpace m
    intro i
    have hrow : ((g : s16h_l3Mat) * m) i = ∑ k, (g i k) • m k := by
      funext j
      rw [Matrix.mul_apply, Finset.sum_apply]
      simp [Pi.smul_apply, smul_eq_mul]
    rw [hrow]
    exact sum_mem fun k _ =>
      Submodule.smul_mem (s16h_l3RowSpace m) (g i k)
        (Submodule.subset_span (Set.mem_range_self k))

theorem s16h_l3RowSpace_ne_bot {m : s16h_l3Mat} (hm : m ≠ 0) : s16h_l3RowSpace m ≠ ⊥ := by
  intro hbot
  apply hm
  ext i j
  have hmem : m i ∈ (⊥ : Submodule (ZMod 2) s16h_l3Vec) := by
    rw [← hbot]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hzero : m i = 0 := by simpa using hmem
  exact congrFun hzero j

theorem s16h_l3RowSub_ne_bot {r : s16h_l3Vec} (hr : r ≠ 0) :
    s16h_l3RowSub (Submodule.span (ZMod 2) {r}) ≠ ⊥ := by
  intro hbot
  have hmems : s16h_l3SingleRow 0 r ∈ s16h_l3RowSub (Submodule.span (ZMod 2) {r}) := by
    change ∀ i, s16h_l3SingleRow 0 r i ∈ Submodule.span (ZMod 2) {r}
    intro i
    by_cases hi : i = 0
    · subst hi
      have hrow : s16h_l3SingleRow 0 r 0 = r := by
        funext j
        simp [s16h_l3SingleRow_apply]
      rw [hrow]
      exact Submodule.mem_span_singleton_self (R := ZMod 2) r
    · have hrow : s16h_l3SingleRow 0 r i = 0 := by
        funext j
        simp [s16h_l3SingleRow_apply, hi]
      rw [hrow]
      exact Submodule.zero_mem _
  rw [hbot] at hmems
  have hzero : s16h_l3SingleRow 0 r = 0 := by simpa using hmems
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, r j ≠ 0 := by
    by_contra h
    apply hr
    ext j
    exact not_not.mp (by intro hj; exact h ⟨j, hj⟩)
  have h0j : s16h_l3SingleRow 0 r 0 j = (0 : s16h_l3Mat) 0 j :=
    congrFun (congrFun hzero 0) j
  exact hj (by simpa using h0j)

theorem s16h_l3SpanSingleton_eq_of_le {r : s16h_l3Vec} (hr : r ≠ 0)
    {S : Submodule (ZMod 2) s16h_l3Vec} (hS : S ≤ Submodule.span (ZMod 2) {r})
    (hne : S ≠ ⊥) : S = Submodule.span (ZMod 2) {r} := by
  obtain ⟨v, hvS, hvne⟩ : ∃ v ∈ S, v ≠ 0 := by
    by_contra h
    apply hne
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hxne
    exact h ⟨x, hx, hxne⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton (R := ZMod 2)).mp (hS hvS)
  have hcne : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_smul] at hc
    exact hvne hc.symm
  rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) c with hc0 | hc1
  · exact absurd hc0 hcne
  · apply le_antisymm hS
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    have hrv : r = v := by rw [hc1, one_smul] at hc; exact hc
    rw [hrv]
    exact hvS

theorem s16h_l3RowSub_injective {r r' : s16h_l3Vec} (hr : r ≠ 0) (hr' : r' ≠ 0)
    (h : s16h_l3RowSub (Submodule.span (ZMod 2) {r}) =
      s16h_l3RowSub (Submodule.span (ZMod 2) {r'})) : r = r' := by
  have hT : s16h_l3SingleRow 0 r ∈ s16h_l3RowSub (Submodule.span (ZMod 2) {r}) := by
    change ∀ i, s16h_l3SingleRow 0 r i ∈ Submodule.span (ZMod 2) {r}
    intro i
    by_cases hi : i = 0
    · subst hi
      have hrow : s16h_l3SingleRow 0 r 0 = r := by
        funext j
        simp [s16h_l3SingleRow_apply]
      rw [hrow]
      exact Submodule.mem_span_singleton_self (R := ZMod 2) r
    · have hrow : s16h_l3SingleRow 0 r i = 0 := by
        funext j
        simp [s16h_l3SingleRow_apply, hi]
      rw [hrow]
      exact Submodule.zero_mem _
  have hT' : s16h_l3SingleRow 0 r ∈ s16h_l3RowSub (Submodule.span (ZMod 2) {r'}) := by
    rw [← h]
    exact hT
  have hrow : r ∈ Submodule.span (ZMod 2) {r'} := by
    have hmem := (s16h_l3RowSub_mem.mp hT') 0
    have heq : s16h_l3SingleRow 0 r 0 = r := by
      funext j
      simp [s16h_l3SingleRow_apply]
    rwa [heq] at hmem
  obtain ⟨a, ha⟩ := (Submodule.mem_span_singleton (R := ZMod 2)).mp hrow
  have ha0 : a ≠ 0 := by
    intro ha0
    rw [ha0, zero_smul] at ha
    exact hr ha.symm
  rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) a with ha0' | ha1
  · exact absurd ha0' ha0
  · rw [ha1, one_smul] at ha
    exact ha.symm

theorem s16h_l3Vec_nonzero_card : Nat.card {r : s16h_l3Vec // r ≠ 0} = 7 := by
  have hV : Nat.card {r : s16h_l3Vec // r ≠ 0} = Nat.card s16h_l3Vec - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    simp
  have hcard : Nat.card s16h_l3Vec = 8 := by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    norm_num
  rw [hV, hcard]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
