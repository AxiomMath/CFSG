module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3U4Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Syl3

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type} [Field K]

private theorem mulAut_pow_apply {G : Type} [Group G] (α : MulAut G) (j : ℕ) (x : G) :
    (α ^ j) x = α^[j] x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih => rw [pow_succ, MulAut.mul_apply, ih, Function.iterate_succ_apply]

private theorem false_of_odd_iterate {G : Type} {f : G → G} {A B : Set G}
    (hAB : Disjoint A B) (hA : f '' A ⊆ B) (hB : f '' B ⊆ A)
    {x : G} (hx : x ∈ A) {j : ℕ} (hj : Odd j) (hfix : f^[j] x = x) : False := by
  obtain ⟨k, rfl⟩ := hj
  have hpair : ∀ k : ℕ, f^[2 * k] x ∈ A ∧ f^[2 * k + 1] x ∈ B := by
    intro k
    induction k with
    | zero =>
      exact ⟨by simpa using hx, by simpa using hA (Set.mem_image_of_mem f hx)⟩
    | succ k ih =>
      have hA' : f^[2 * (k + 1)] x ∈ A := by
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Function.iterate_succ_apply']
        exact hB (Set.mem_image_of_mem f ih.2)
      have hB' : f^[2 * (k + 1) + 1] x ∈ B := by
        rw [show 2 * (k + 1) + 1 = (2 * (k + 1)).succ by rfl, Function.iterate_succ_apply']
        exact hA (Set.mem_image_of_mem f hA')
      exact ⟨hA', hB'⟩
  have hBmem : x ∈ B := by
    rw [← hfix]
    exact (hpair k).2
  exact (Set.disjoint_left.mp hAB hx) hBmem

private theorem bar_eq_self_of_pow_three (h : UnitaryFieldData 2 n K) (hn : Even n)
    {c : Kˣ} (hc : c ^ 3 = 1) : h.bar (c : K) = (c : K) := by
  obtain ⟨m, hm⟩ := three_dvd_two_pow_sub_one hn
  have hcK : (c : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have hq : 2 ^ n = 3 * m + 1 := by omega
  rw [h.bar_apply, hq, pow_add, pow_mul, hcK, one_pow, one_mul, pow_one]

private theorem torusRatio_one_of_bar_fixed {p f r ε : ℕ} {h : UnitaryFieldData p f K}
    {a : Fin r → Kˣ} (hbar : ∀ i, h.bar (a i : K) = (a i : K)) :
    torusRatio h a (1 : Fin ε → Kˣ) = 1 := by
  rw [torusRatio]
  have hprod : (∏ i, (a i : K) / h.bar (a i)) = 1 := by
    rw [Finset.prod_eq_one]
    intro i _
    rw [hbar i, div_self (Units.ne_zero _)]
  rw [hprod]
  simp

private noncomputable def torusElt (h : UnitaryFieldData 2 n K) (hn : Even n)
    (a : Fin 2 → Kˣ) (ha : ∀ i, a i ^ 3 = 1) : hypSU h 2 0 := by
  have hbar : ∀ i, h.bar (a i : K) = (a i : K) :=
    fun i => bar_eq_self_of_pow_three h hn (ha i)
  have hp : torusRatio h a (1 : Fin 0 → Kˣ) = 1 := torusRatio_one_of_bar_fixed hbar
  have hdet : (diagonal (torusEntries h a (1 : Fin 0 → Kˣ)) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K).det = 1 := by
    rw [det_diagonal_torusEntries, hp]
  exact ⟨GeneralLinearGroup.mkOfDetNeZero (diagonal (torusEntries h a (1 : Fin 0 → Kˣ)))
      (by rw [hdet]; exact one_ne_zero),
    diagonal_torusEntries_isometry h a (fun k => k.elim0), hdet⟩

private theorem torusElt_matrix (h : UnitaryFieldData 2 n K) (hn : Even n)
    (a : Fin 2 → Kˣ) (ha : ∀ i, a i ^ 3 = 1) :
    (((torusElt h hn a ha : hypSU h 2 0) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      diagonal (torusEntries h a (1 : Fin 0 → Kˣ)) := by
  simp [torusElt, GeneralLinearGroup.val_mkOfDetNeZero]

private theorem torusElt_mem_torusPow (h : UnitaryFieldData 2 n K) (hn : Even n)
    (a : Fin 2 → Kˣ) (ha : ∀ i, a i ^ 3 = 1) :
    torusElt h hn a ha ∈ torusPow h 2 0 3 :=
  mem_torusPow.mpr ⟨a, ha, torusElt_matrix h hn a ha⟩

private theorem torusElt_eq_iff (h : UnitaryFieldData 2 n K) (hn : Even n)
    {a b : Fin 2 → Kˣ} (ha : ∀ i, a i ^ 3 = 1) (hb : ∀ i, b i ^ 3 = 1) :
    torusElt h hn a ha = torusElt h hn b hb ↔ a = b := by
  constructor
  · intro heq
    have hmat : diagonal (torusEntries h a (1 : Fin 0 → Kˣ)) =
        diagonal (torusEntries h b (1 : Fin 0 → Kˣ)) := by
      rw [← torusElt_matrix h hn a ha, ← torusElt_matrix h hn b hb, heq]
    have hentries := (Matrix.diagonal_eq_diagonal_iff.mp hmat)
    funext i
    exact Units.ext (by simpa [torusEntries] using hentries (Sum.inl i))
  · rintro rfl
    apply Subtype.ext
    apply Units.ext
    rfl

private theorem torusElt_one (h : UnitaryFieldData 2 n K) (hn : Even n)
    (ha : ∀ i, (1 : Fin 2 → Kˣ) i ^ 3 = 1) : torusElt h hn 1 ha = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [torusElt_matrix, Subgroup.coe_one, Units.val_one, ← diagonal_one]
  congr 1
  funext x
  rcases x with i | k | i <;> simp [torusEntries]

private theorem torusElt_eq_one_iff (h : UnitaryFieldData 2 n K) (hn : Even n)
    {a : Fin 2 → Kˣ} (ha : ∀ i, a i ^ 3 = 1) :
    torusElt h hn a ha = 1 ↔ a = 1 := by
  constructor
  · intro h1
    have h' : torusElt h hn a ha =
        torusElt h hn (1 : Fin 2 → Kˣ) (fun i => one_pow 3) := by
      rw [h1, torusElt_one]
    exact (torusElt_eq_iff h hn ha (fun i => one_pow 3)).mp h'
  · rintro rfl
    exact torusElt_one h hn ha

private theorem torusElt_mul (h : UnitaryFieldData 2 n K) (hn : Even n)
    (a b : Fin 2 → Kˣ) (ha : ∀ i, a i ^ 3 = 1) (hb : ∀ i, b i ^ 3 = 1) :
    torusElt h hn a ha * torusElt h hn b hb =
      torusElt h hn (a * b)
        (fun i => by rw [Pi.mul_apply, mul_pow, ha i, hb i, one_mul]) := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, torusElt_matrix, torusElt_matrix, torusElt_matrix,
    diagonal_mul_diagonal]
  congr 1
  funext x
  rcases x with i | k | i <;> simp [torusEntries, map_mul, mul_comm]

private theorem torusElt_inv (h : UnitaryFieldData 2 n K) (hn : Even n)
    (a : Fin 2 → Kˣ) (ha : ∀ i, a i ^ 3 = 1) :
    torusElt h hn a⁻¹ (fun i => by rw [Pi.inv_apply, inv_pow, ha i, inv_one]) =
      (torusElt h hn a ha)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [torusElt_mul]
  exact (torusElt_eq_one_iff h hn _).mpr (funext fun i => by simp)

private theorem eq_torusElt_of_mem_torusPow (h : UnitaryFieldData 2 n K) (hn : Even n)
    {s : hypSU h 2 0} (hs : s ∈ torusPow h 2 0 3) :
    ∃ (a : Fin 2 → Kˣ) (ha : ∀ i, a i ^ 3 = 1), s = torusElt h hn a ha := by
  obtain ⟨a, ha, hmat⟩ := mem_torusPow.mp hs
  refine ⟨a, ha, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [hmat, torusElt_matrix]

private def L0 (h : UnitaryFieldData 2 n K) (hn : Even n) : Set (hypSU h 2 0) :=
  {s | ∃ (a : Fin 2 → Kˣ) (ha : ∀ i, a i ^ 3 = 1), a 1 = 1 ∧ s = torusElt h hn a ha}

private def L1 (h : UnitaryFieldData 2 n K) (hn : Even n) : Set (hypSU h 2 0) :=
  {s | ∃ (a : Fin 2 → Kˣ) (ha : ∀ i, a i ^ 3 = 1), a 0 = 1 ∧ s = torusElt h hn a ha}

private theorem torusElt_mul_apply (h : UnitaryFieldData 2 n K) (hn : Even n)
    (a b : Fin 2 → Kˣ) (ha : ∀ i, a i ^ 3 = 1) (hb : ∀ i, b i ^ 3 = 1)
    (hc : ∀ i, (a * b : Fin 2 → Kˣ) i ^ 3 = 1) :
    torusElt h hn a ha * torusElt h hn b hb = torusElt h hn (a * b) hc := by
  rw [torusElt_mul]

private theorem torusElt_eq_of_eq (h : UnitaryFieldData 2 n K) (hn : Even n)
    {a b : Fin 2 → Kˣ} (ha : ∀ i, a i ^ 3 = 1) (hb : ∀ i, b i ^ 3 = 1)
    (hab : b = a) : torusElt h hn b hb = torusElt h hn a ha :=
  (torusElt_eq_iff h hn hb ha).mpr hab

private theorem torusElt_eq_inv_of_eq_inv (h : UnitaryFieldData 2 n K) (hn : Even n)
    (a : Fin 2 → Kˣ) (ha : ∀ i, a i ^ 3 = 1)
    {b : Fin 2 → Kˣ} (hb : ∀ i, b i ^ 3 = 1) (hab : b = a⁻¹) :
    torusElt h hn b hb = (torusElt h hn a ha)⁻¹ := by
  have hb' : ∀ i, (a⁻¹ : Fin 2 → Kˣ) i ^ 3 = 1 :=
    fun i => by rw [Pi.inv_apply, inv_pow, ha i, inv_one]
  have h1 : torusElt h hn b hb = torusElt h hn a⁻¹ hb' :=
    (torusElt_eq_iff h hn hb hb').mpr hab
  rw [h1, torusElt_inv h hn a ha]

private theorem det_sub_one_torusElt_eq_zero_iff (h : UnitaryFieldData 2 n K) (hn : Even n)
    (a : Fin 2 → Kˣ) (ha : ∀ i, a i ^ 3 = 1) :
    ((((torusElt h hn a ha : hypSU h 2 0) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) - 1).det = 0 ↔
      a 0 = 1 ∨ a 1 = 1 := by
  have hbar : ∀ i, h.bar (a i : K) = (a i : K) :=
    fun i => bar_eq_self_of_pow_three h hn (ha i)
  have hprod : (∏ x : HypIndex 2 0,
      (torusEntries h a (1 : Fin 0 → Kˣ) x - 1)) =
      ((a 0 : K) - 1) * ((a 1 : K) - 1) *
        (((a 0 : K))⁻¹ - 1) * (((a 1 : K))⁻¹ - 1) := by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_two]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, torusEntries, hbar 0, hbar 1]
    ring
  have hx0 : (a 0 : K) - 1 = 0 ↔ a 0 = 1 := by
    rw [sub_eq_zero]
    exact (Units.ext_iff (u := a 0) (v := 1)).symm
  have hx1 : (a 1 : K) - 1 = 0 ↔ a 1 = 1 := by
    rw [sub_eq_zero]
    exact (Units.ext_iff (u := a 1) (v := 1)).symm
  have hy0 : ((a 0 : K))⁻¹ - 1 = 0 ↔ a 0 = 1 := by
    rw [sub_eq_zero, inv_eq_one]
    exact (Units.ext_iff (u := a 0) (v := 1)).symm
  have hy1 : ((a 1 : K))⁻¹ - 1 = 0 ↔ a 1 = 1 := by
    rw [sub_eq_zero, inv_eq_one]
    exact (Units.ext_iff (u := a 1) (v := 1)).symm
  rw [torusElt_matrix]
  rw [← diagonal_one (n := HypIndex 2 0), diagonal_sub, det_diagonal, hprod]
  rw [mul_eq_zero, mul_eq_zero, mul_eq_zero, hx0, hx1, hy0, hy1]
  tauto

private theorem cube_root_sq_add_self_add_one_eq_zero {c : Kˣ} (hc : c ^ 3 = 1) (hc1 : c ≠ 1) :
    (c : K) ^ 2 + (c : K) + 1 = 0 := by
  have hcK : (c : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  have hcne : (c : K) ≠ 1 := by
    intro h
    exact hc1 (Units.ext h)
  have h : ((c : K) - 1) * ((c : K) ^ 2 + (c : K) + 1) = 0 := by
    rw [show ((c : K) - 1) * ((c : K) ^ 2 + (c : K) + 1) = (c : K) ^ 3 - 1 by ring]
    rw [hcK, sub_self]
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hcne)

private theorem cube_root_eq_or_inv {c d : Kˣ} (hc : c ^ 3 = 1) (hd : d ^ 3 = 1)
    (hc1 : c ≠ 1) (hd1 : d ≠ 1) : d = c ∨ d = c⁻¹ := by
  have hc2 := cube_root_sq_add_self_add_one_eq_zero hc hc1
  have hd2 := cube_root_sq_add_self_add_one_eq_zero hd hd1
  have hprod : ((c : K) - (d : K)) * ((c : K) + (d : K) + 1) = 0 := by
    rw [show ((c : K) - (d : K)) * ((c : K) + (d : K) + 1) =
      ((c : K) ^ 2 + (c : K) + 1) - ((d : K) ^ 2 + (d : K) + 1) by ring]
    rw [hc2, hd2, sub_self]
  rcases mul_eq_zero.mp hprod with h | h
  · left
    exact Units.ext (sub_eq_zero.mp h).symm
  · right
    have hsum : (d : K) = -((c : K) + 1) := by linear_combination h
    have hsq : (c : K) ^ 2 + (c : K) = -1 := by linear_combination hc2
    have hmul : (c : K) * (d : K) = 1 := by
      rw [hsum]
      calc (c : K) * -((c : K) + 1) = -((c : K) ^ 2 + (c : K)) := by ring
        _ = 1 := by rw [hsq]; ring
    refine Units.ext ?_
    rw [Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_right hmul

private theorem inv_ne_self_of_pow_three {c : Kˣ} (hc : c ^ 3 = 1) (hc1 : c ≠ 1) :
    c⁻¹ ≠ c := by
  intro h
  have hc2 : c ^ 2 = 1 := by
    rw [pow_two]
    calc c * c = c * c⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel c
  have hc3 : c = 1 := by
    have h' : c = c ^ 3 := by rw [pow_succ, hc2, one_mul]
    rwa [hc] at h'
  exact hc1 hc3

private def firstLine (c : Kˣ) : Fin 2 → Kˣ := fun i => if i = 0 then c else 1

private def secondLine (c : Kˣ) : Fin 2 → Kˣ := fun i => if i = 0 then 1 else c

private theorem torusElt_mem_L0 (h : UnitaryFieldData 2 n K) (hn : Even n)
    {a : Fin 2 → Kˣ} (ha : ∀ i, a i ^ 3 = 1) :
    torusElt h hn a ha ∈ L0 h hn ↔ a 1 = 1 := by
  constructor
  · rintro ⟨b, hb, hb1, heq⟩
    have hab : a = b := (torusElt_eq_iff h hn ha hb).mp heq
    rw [hab]
    exact hb1
  · intro h1
    exact ⟨a, ha, h1, rfl⟩

private theorem torusElt_mem_L1 (h : UnitaryFieldData 2 n K) (hn : Even n)
    {a : Fin 2 → Kˣ} (ha : ∀ i, a i ^ 3 = 1) :
    torusElt h hn a ha ∈ L1 h hn ↔ a 0 = 1 := by
  constructor
  · rintro ⟨b, hb, hb0, heq⟩
    have hab : a = b := (torusElt_eq_iff h hn ha hb).mp heq
    rw [hab]
    exact hb0
  · intro h0
    exact ⟨a, ha, h0, rfl⟩

private theorem L0_subset_torusPow (h : UnitaryFieldData 2 n K) (hn : Even n) :
    L0 h hn ⊆ torusPow h 2 0 3 := by
  rintro s ⟨a, ha, -, rfl⟩
  exact torusElt_mem_torusPow h hn a ha

private theorem L1_subset_torusPow (h : UnitaryFieldData 2 n K) (hn : Even n) :
    L1 h hn ⊆ torusPow h 2 0 3 := by
  rintro s ⟨a, ha, -, rfl⟩
  exact torusElt_mem_torusPow h hn a ha

private theorem disjoint_L0'_L1' (h : UnitaryFieldData 2 n K) (hn : Even n) :
    Disjoint (L0 h hn \ {1}) (L1 h hn \ {1}) := by
  rw [Set.disjoint_left]
  rintro s ⟨hs0, hs1⟩ ⟨ht0, ht1⟩
  rw [Set.mem_singleton_iff] at hs1
  obtain ⟨a, ha, ha1, rfl⟩ := hs0
  obtain ⟨b, hb, hb0, heq⟩ := ht0
  have hab : a = b := (torusElt_eq_iff h hn ha hb).mp heq
  have ha0 : a 0 = 1 := by rw [hab]; exact hb0
  have haeq : a = 1 := by
    funext i
    fin_cases i <;> simp [ha0, ha1]
  exact hs1 (by rw [torusElt_eq_one_iff h hn ha]; exact haeq)

private theorem L0_eq_pair (h : UnitaryFieldData 2 n K) (hn : Even n) {z : hypSU h 2 0}
    (hz : z ∈ L0 h hn) (hz1 : z ≠ 1) : L0 h hn \ {1} = {z, z⁻¹} := by
  obtain ⟨a, ha, ha1, rfl⟩ := hz
  have ha0 : a 0 ≠ 1 := by
    intro h0
    apply hz1
    rw [torusElt_eq_one_iff h hn ha]
    funext i
    fin_cases i <;> simp [h0, ha1]
  ext w
  constructor
  · intro hw
    rw [Set.mem_diff] at hw
    obtain ⟨hwL, hw1⟩ := hw
    rw [Set.mem_singleton_iff] at hw1
    obtain ⟨b, hb, hb1, rfl⟩ := hwL
    have hb0 : b 0 ≠ 1 := by
      intro h0
      apply hw1
      rw [torusElt_eq_one_iff h hn hb]
      funext i
      fin_cases i <;> simp [h0, hb1]
    rcases cube_root_eq_or_inv (ha 0) (hb 0) ha0 hb0 with hb0eq | hb0eq
    · left
      have hb_eq : b = a := by
        funext i
        fin_cases i <;> simp [hb0eq, hb1, ha1]
      exact torusElt_eq_of_eq h hn ha hb hb_eq
    · right
      have hb_eq : b = a⁻¹ := by
        funext i
        fin_cases i <;> simp [hb0eq, hb1, ha1]
      exact torusElt_eq_inv_of_eq_inv h hn a ha hb hb_eq
  · rintro (hzw | hzw)
    · rw [hzw]
      exact ⟨⟨a, ha, ha1, rfl⟩, hz1⟩
    · rw [hzw]
      refine ⟨?_, ?_⟩
      · refine ⟨a⁻¹, fun i => by rw [Pi.inv_apply, inv_pow, ha i, inv_one], by simp [ha1], ?_⟩
        exact (torusElt_inv h hn a ha).symm
      · intro hcontra
        apply hz1
        have := congrArg Inv.inv hcontra
        simpa using this

private theorem L1_eq_pair (h : UnitaryFieldData 2 n K) (hn : Even n) {z : hypSU h 2 0}
    (hz : z ∈ L1 h hn) (hz1 : z ≠ 1) : L1 h hn \ {1} = {z, z⁻¹} := by
  obtain ⟨a, ha, ha0, rfl⟩ := hz
  have ha1 : a 1 ≠ 1 := by
    intro h1
    apply hz1
    rw [torusElt_eq_one_iff h hn ha]
    funext i
    fin_cases i <;> simp [h1, ha0]
  ext w
  constructor
  · intro hw
    rw [Set.mem_diff] at hw
    obtain ⟨hwL, hw1⟩ := hw
    rw [Set.mem_singleton_iff] at hw1
    obtain ⟨b, hb, hb0, rfl⟩ := hwL
    have hb1 : b 1 ≠ 1 := by
      intro h1
      apply hw1
      rw [torusElt_eq_one_iff h hn hb]
      funext i
      fin_cases i <;> simp [h1, hb0]
    rcases cube_root_eq_or_inv (ha 1) (hb 1) ha1 hb1 with hb1eq | hb1eq
    · left
      have hb_eq : b = a := by
        funext i
        fin_cases i <;> simp [hb1eq, hb0, ha0]
      exact torusElt_eq_of_eq h hn ha hb hb_eq
    · right
      have hb_eq : b = a⁻¹ := by
        funext i
        fin_cases i <;> simp [hb1eq, hb0, ha0]
      exact torusElt_eq_inv_of_eq_inv h hn a ha hb hb_eq
  · rintro (hzw | hzw)
    · rw [hzw]
      exact ⟨⟨a, ha, ha0, rfl⟩, hz1⟩
    · rw [hzw]
      refine ⟨?_, ?_⟩
      · refine ⟨a⁻¹, fun i => by rw [Pi.inv_apply, inv_pow, ha i, inv_one], by simp [ha0], ?_⟩
        exact (torusElt_inv h hn a ha).symm
      · intro hcontra
        apply hz1
        have := congrArg Inv.inv hcontra
        simpa using this

private theorem det_zero_iff_mem_union (h : UnitaryFieldData 2 n K) (hn : Even n)
    {s : hypSU h 2 0} (hs : s ∈ torusPow h 2 0 3) :
    ((((s : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) - 1).det = 0) ↔
      s ∈ L0 h hn ∪ L1 h hn := by
  obtain ⟨a, ha, hmat⟩ := mem_torusPow.mp hs
  have hs_eq : s = torusElt h hn a ha := by
    apply Subtype.ext
    apply Units.ext
    rw [hmat, torusElt_matrix]
  subst hs_eq
  rw [det_sub_one_torusElt_eq_zero_iff h hn a ha]
  constructor
  · rintro (h0 | h1)
    · right
      exact ⟨a, ha, h0, rfl⟩
    · left
      exact ⟨a, ha, h1, rfl⟩
  · rintro (hL | hL)
    · exact Or.inr ((torusElt_mem_L0 h hn ha).mp hL)
    · exact Or.inl ((torusElt_mem_L1 h hn ha).mp hL)

private def lineA (h : UnitaryFieldData 2 n K) (hn : Even n) : Set (hypSU h 2 0) :=
  L0 h hn \ {1}

private def lineB (h : UnitaryFieldData 2 n K) (hn : Even n) : Set (hypSU h 2 0) :=
  L1 h hn \ {1}

private theorem mem_lineA_iff (h : UnitaryFieldData 2 n K) (hn : Even n)
    {s : hypSU h 2 0} : s ∈ lineA h hn ↔ s ∈ L0 h hn ∧ s ≠ 1 := by
  rw [lineA, Set.mem_diff, Set.mem_singleton_iff]

private theorem mem_lineB_iff (h : UnitaryFieldData 2 n K) (hn : Even n)
    {s : hypSU h 2 0} : s ∈ lineB h hn ↔ s ∈ L1 h hn ∧ s ≠ 1 := by
  rw [lineB, Set.mem_diff, Set.mem_singleton_iff]

private theorem alpha_union (h : UnitaryFieldData 2 n K) (hn : Even n)
    (α : MulAut (hypSU h 2 0))
    (hT : ∀ s ∈ torusPow h 2 0 3, α s ∈ torusPow h 2 0 3)
    (hdet : ∀ g : hypSU h 2 0,
      ((((α g : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) -
          1).det = 0 ↔
        (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) - 1).det = 0)
    {s : hypSU h 2 0} (hs : s ∈ torusPow h 2 0 3) :
    s ∈ lineA h hn ∪ lineB h hn ↔ α s ∈ lineA h hn ∪ lineB h hn := by
  have key : ∀ u : hypSU h 2 0,
      u ∈ lineA h hn ∪ lineB h hn ↔ u ∈ L0 h hn ∪ L1 h hn ∧ u ≠ 1 := by
    intro u
    constructor
    · intro hu
      rcases hu with hu | hu
      · rw [mem_lineA_iff h hn] at hu
        exact ⟨Or.inl hu.1, hu.2⟩
      · rw [mem_lineB_iff h hn] at hu
        exact ⟨Or.inr hu.1, hu.2⟩
    · rintro ⟨hu | hu, hu1⟩
      · left
        rw [mem_lineA_iff h hn]
        exact ⟨hu, hu1⟩
      · right
        rw [mem_lineB_iff h hn]
        exact ⟨hu, hu1⟩
  rw [key s, key (α s)]
  constructor
  · rintro ⟨hsL, hs1⟩
    have hdet0 : (((s : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) - 1).det = 0 :=
      (det_zero_iff_mem_union h hn hs).mpr hsL
    have hdet1 := (hdet s).mpr hdet0
    refine ⟨(det_zero_iff_mem_union h hn (hT s hs)).mp hdet1, ?_⟩
    intro hαs1
    exact hs1 (α.injective (by rw [hαs1, map_one]))
  · rintro ⟨hαL, hαs1⟩
    have hdet1 : (((α s : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) - 1).det = 0 :=
      (det_zero_iff_mem_union h hn (hT s hs)).mpr hαL
    have hdet0 := (hdet s).mp hdet1
    refine ⟨(det_zero_iff_mem_union h hn hs).mp hdet0, ?_⟩
    intro hs1
    exact hαs1 (by rw [hs1, map_one])

private theorem odd_three_pow (k : ℕ) : Odd (3 ^ k) := by
  simpa using Odd.pow (n := k) (show Odd 3 by norm_num)

private theorem mulAut_iterate_three_pow_eq_self {G : Type} [Group G] (α : MulAut G)
    {k : ℕ} (hk : α ^ (3 ^ k) = 1) (x : G) : α^[3 ^ k] x = x := by
  have h1 : (α ^ (3 ^ k)) x = x := by rw [hk, MulAut.one_apply]
  rwa [mulAut_pow_apply] at h1

private theorem alpha_alpha_mem_lineA (h : UnitaryFieldData 2 n K) (hn : Even n)
    (α : MulAut (hypSU h 2 0))
    (hT : ∀ s ∈ torusPow h 2 0 3, α s ∈ torusPow h 2 0 3)
    (hdet : ∀ g : hypSU h 2 0,
      ((((α g : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) -
          1).det = 0 ↔
        (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) - 1).det = 0)
    {x : hypSU h 2 0} (hxL : x ∈ L0 h hn) (hx1 : x ≠ 1)
    (hxB : α x ∈ lineB h hn) : α (α x) ∈ lineA h hn := by
  have hxmem : x ∈ lineA h hn := by rw [mem_lineA_iff h hn]; exact ⟨hxL, hx1⟩
  have hxT : x ∈ torusPow h 2 0 3 := L0_subset_torusPow h hn hxL
  have hxBmem : α x ∈ lineB h hn := hxB
  rw [mem_lineB_iff h hn] at hxB
  obtain ⟨hαxL, hαx1⟩ := hxB
  have hαxT : α x ∈ torusPow h 2 0 3 := hT x hxT
  have hApair : lineA h hn = {x, x⁻¹} := by rw [lineA]; exact L0_eq_pair h hn hxL hx1
  have hBpair : lineB h hn = {α x, (α x)⁻¹} := by rw [lineB]; exact L1_eq_pair h hn hαxL hαx1
  by_contra hααnot
  have hααUnion : α (α x) ∈ lineA h hn ∪ lineB h hn :=
    (alpha_union h hn α hT hdet hαxT).mp (Or.inr hxBmem)
  have hααB : α (α x) ∈ lineB h hn := by
    rcases hααUnion with hh | hh
    · exact absurd hh hααnot
    · exact hh
  have hααBpair := hααB
  rw [hBpair] at hααBpair
  have hxinvA : x⁻¹ ∈ lineA h hn := by
    rw [hApair]
    exact Or.inr rfl
  rcases hααBpair with hh | hh
  · have h_eq : α x = x := α.injective hh
    exact (Set.disjoint_left.mp (disjoint_L0'_L1' h hn)) hxmem (by rw [← h_eq]; exact hxBmem)
  · have h' : α (α x) = α (x⁻¹) := by
      rw [map_inv]
      exact hh
    have h_eq : α x = x⁻¹ := α.injective h'
    exact (Set.disjoint_left.mp (disjoint_L0'_L1' h hn)) hxinvA (by rw [← h_eq]; exact hxBmem)

private theorem contradiction_of_alpha_maps_lineA_to_lineB (h : UnitaryFieldData 2 n K)
    (hn : Even n) (α : MulAut (hypSU h 2 0)) (hα : ∃ k : ℕ, α ^ (3 ^ k) = 1)
    (hT : ∀ s ∈ torusPow h 2 0 3, α s ∈ torusPow h 2 0 3)
    (hdet : ∀ g : hypSU h 2 0,
      ((((α g : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) -
          1).det = 0 ↔
        (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) - 1).det = 0)
    {x : hypSU h 2 0} (hxL : x ∈ L0 h hn) (hx1 : x ≠ 1)
    (hxB : α x ∈ lineB h hn) : False := by
  have hxmem : x ∈ lineA h hn := by rw [mem_lineA_iff h hn]; exact ⟨hxL, hx1⟩
  have hxT : x ∈ torusPow h 2 0 3 := L0_subset_torusPow h hn hxL
  have hxBmem : α x ∈ lineB h hn := hxB
  rw [mem_lineB_iff h hn] at hxB
  obtain ⟨hαxL, hαx1⟩ := hxB
  have hαxT : α x ∈ torusPow h 2 0 3 := hT x hxT
  have hApair : lineA h hn = {x, x⁻¹} := by rw [lineA]; exact L0_eq_pair h hn hxL hx1
  have hBpair : lineB h hn = {α x, (α x)⁻¹} := by rw [lineB]; exact L1_eq_pair h hn hαxL hαx1
  have hααA := alpha_alpha_mem_lineA h hn α hT hdet hxL hx1 hxBmem
  have hmapsAB : α '' lineA h hn ⊆ lineB h hn := by
    rintro y ⟨a, ha, rfl⟩
    rw [hApair] at ha
    rcases ha with ha | ha
    · rw [ha]
      exact hxBmem
    · rw [ha, hBpair]
      exact Or.inr (map_inv α x)
  have hmapsBA : α '' lineB h hn ⊆ lineA h hn := by
    rintro y ⟨b, hb, rfl⟩
    rw [hBpair] at hb
    rcases hb with hb | hb
    · rw [hb]
      exact hααA
    · rw [hb, map_inv, hApair]
      have hααA' : α (α x) ∈ ({x, x⁻¹} : Set (hypSU h 2 0)) := by rwa [← hApair]
      rcases hααA' with hh | hh
      · right
        rw [hh]
        rfl
      · left
        rw [hh, inv_inv]
  obtain ⟨k, hk⟩ := hα
  exact false_of_odd_iterate (disjoint_L0'_L1' h hn) hmapsAB hmapsBA hxmem
    (odd_three_pow k) (mulAut_iterate_three_pow_eq_self α hk x)

private theorem alpha_mapsTo_lineA (h : UnitaryFieldData 2 n K) (hn : Even n)
    (α : MulAut (hypSU h 2 0)) (hα : ∃ k : ℕ, α ^ (3 ^ k) = 1)
    (hT : ∀ s ∈ torusPow h 2 0 3, α s ∈ torusPow h 2 0 3)
    (hdet : ∀ g : hypSU h 2 0,
      ((((α g : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) -
          1).det = 0 ↔
        (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) - 1).det = 0) :
    Set.MapsTo α (lineA h hn) (lineA h hn) := by
  intro x hx
  by_contra hxnot
  rw [mem_lineA_iff h hn] at hx
  obtain ⟨hxL, hx1⟩ := hx
  have hxT : x ∈ torusPow h 2 0 3 := L0_subset_torusPow h hn hxL
  have hαxUnion : α x ∈ lineA h hn ∪ lineB h hn :=
    (alpha_union h hn α hT hdet hxT).mp (Or.inl (by rw [mem_lineA_iff h hn]; exact ⟨hxL, hx1⟩))
  have hxB : α x ∈ lineB h hn := by
    rcases hαxUnion with hh | hh
    · exact absurd hh hxnot
    · exact hh
  exact contradiction_of_alpha_maps_lineA_to_lineB h hn α hα hT hdet hxL hx1 hxB

private theorem alpha_alpha_mem_lineB (h : UnitaryFieldData 2 n K) (hn : Even n)
    (α : MulAut (hypSU h 2 0))
    (hT : ∀ s ∈ torusPow h 2 0 3, α s ∈ torusPow h 2 0 3)
    (hdet : ∀ g : hypSU h 2 0,
      ((((α g : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) -
          1).det = 0 ↔
        (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) - 1).det = 0)
    {x : hypSU h 2 0} (hxL : x ∈ L1 h hn) (hx1 : x ≠ 1)
    (hxA : α x ∈ lineA h hn) : α (α x) ∈ lineB h hn := by
  have hxmem : x ∈ lineB h hn := by rw [mem_lineB_iff h hn]; exact ⟨hxL, hx1⟩
  have hxT : x ∈ torusPow h 2 0 3 := L1_subset_torusPow h hn hxL
  have hxAmem : α x ∈ lineA h hn := hxA
  rw [mem_lineA_iff h hn] at hxA
  obtain ⟨hαxL, hαx1⟩ := hxA
  have hαxT : α x ∈ torusPow h 2 0 3 := hT x hxT
  have hBpair : lineB h hn = {x, x⁻¹} := by rw [lineB]; exact L1_eq_pair h hn hxL hx1
  have hApair : lineA h hn = {α x, (α x)⁻¹} := by rw [lineA]; exact L0_eq_pair h hn hαxL hαx1
  by_contra hααnot
  have hααUnion : α (α x) ∈ lineA h hn ∪ lineB h hn :=
    (alpha_union h hn α hT hdet hαxT).mp (Or.inl hxAmem)
  have hααA : α (α x) ∈ lineA h hn := by
    rcases hααUnion with hh | hh
    · exact hh
    · exact absurd hh hααnot
  have hααApair := hααA
  rw [hApair] at hααApair
  have hxinvB : x⁻¹ ∈ lineB h hn := by
    rw [hBpair]
    exact Or.inr rfl
  rcases hααApair with hh | hh
  · have h_eq : α x = x := α.injective hh
    exact (Set.disjoint_left.mp (disjoint_L0'_L1' h hn)) (by rw [← h_eq]; exact hxAmem) hxmem
  · have h' : α (α x) = α (x⁻¹) := by
      rw [map_inv]
      exact hh
    have h_eq : α x = x⁻¹ := α.injective h'
    exact (Set.disjoint_left.mp (disjoint_L0'_L1' h hn)) (by rw [← h_eq]; exact hxAmem) hxinvB

private theorem contradiction_of_alpha_maps_lineB_to_lineA (h : UnitaryFieldData 2 n K)
    (hn : Even n) (α : MulAut (hypSU h 2 0)) (hα : ∃ k : ℕ, α ^ (3 ^ k) = 1)
    (hT : ∀ s ∈ torusPow h 2 0 3, α s ∈ torusPow h 2 0 3)
    (hdet : ∀ g : hypSU h 2 0,
      ((((α g : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) -
          1).det = 0 ↔
        (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) - 1).det = 0)
    {x : hypSU h 2 0} (hxL : x ∈ L1 h hn) (hx1 : x ≠ 1)
    (hxA : α x ∈ lineA h hn) : False := by
  have hxmem : x ∈ lineB h hn := by rw [mem_lineB_iff h hn]; exact ⟨hxL, hx1⟩
  have hxT : x ∈ torusPow h 2 0 3 := L1_subset_torusPow h hn hxL
  have hxAmem : α x ∈ lineA h hn := hxA
  rw [mem_lineA_iff h hn] at hxA
  obtain ⟨hαxL, hαx1⟩ := hxA
  have hαxT : α x ∈ torusPow h 2 0 3 := hT x hxT
  have hBpair : lineB h hn = {x, x⁻¹} := by rw [lineB]; exact L1_eq_pair h hn hxL hx1
  have hApair : lineA h hn = {α x, (α x)⁻¹} := by rw [lineA]; exact L0_eq_pair h hn hαxL hαx1
  have hααB := alpha_alpha_mem_lineB h hn α hT hdet hxL hx1 hxAmem
  have hmapsBA : α '' lineB h hn ⊆ lineA h hn := by
    rintro y ⟨a, ha, rfl⟩
    rw [hBpair] at ha
    rcases ha with ha | ha
    · rw [ha]
      exact hxAmem
    · rw [ha, hApair]
      exact Or.inr (map_inv α x)
  have hmapsAB : α '' lineA h hn ⊆ lineB h hn := by
    rintro y ⟨b, hb, rfl⟩
    rw [hApair] at hb
    rcases hb with hb | hb
    · rw [hb]
      exact hααB
    · rw [hb, map_inv, hBpair]
      have hααB' : α (α x) ∈ ({x, x⁻¹} : Set (hypSU h 2 0)) := by rwa [← hBpair]
      rcases hααB' with hh | hh
      · right
        rw [hh]
        rfl
      · left
        rw [hh, inv_inv]
  obtain ⟨k, hk⟩ := hα
  exact false_of_odd_iterate (disjoint_L0'_L1' h hn).symm hmapsBA hmapsAB hxmem
    (odd_three_pow k) (mulAut_iterate_three_pow_eq_self α hk x)

private theorem alpha_mapsTo_lineB (h : UnitaryFieldData 2 n K) (hn : Even n)
    (α : MulAut (hypSU h 2 0)) (hα : ∃ k : ℕ, α ^ (3 ^ k) = 1)
    (hT : ∀ s ∈ torusPow h 2 0 3, α s ∈ torusPow h 2 0 3)
    (hdet : ∀ g : hypSU h 2 0,
      ((((α g : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) -
          1).det = 0 ↔
        (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) - 1).det = 0) :
    Set.MapsTo α (lineB h hn) (lineB h hn) := by
  intro x hx
  by_contra hxnot
  rw [mem_lineB_iff h hn] at hx
  obtain ⟨hxL, hx1⟩ := hx
  have hxT : x ∈ torusPow h 2 0 3 := L1_subset_torusPow h hn hxL
  have hαxUnion : α x ∈ lineA h hn ∪ lineB h hn :=
    (alpha_union h hn α hT hdet hxT).mp (Or.inr (by rw [mem_lineB_iff h hn]; exact ⟨hxL, hx1⟩))
  have hxA : α x ∈ lineA h hn := by
    rcases hαxUnion with hh | hh
    · exact hh
    · exact absurd hh hxnot
  exact contradiction_of_alpha_maps_lineB_to_lineA h hn α hα hT hdet hxL hx1 hxA

private theorem alpha_fixes_lineA (h : UnitaryFieldData 2 n K) (hn : Even n)
    (α : MulAut (hypSU h 2 0)) (hα : ∃ k : ℕ, α ^ (3 ^ k) = 1)
    (hT : ∀ s ∈ torusPow h 2 0 3, α s ∈ torusPow h 2 0 3)
    (hdet : ∀ g : hypSU h 2 0,
      ((((α g : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) -
          1).det = 0 ↔
        (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) - 1).det = 0) :
    ∀ x ∈ lineA h hn, α x = x := by
  intro x hx
  rw [mem_lineA_iff h hn] at hx
  obtain ⟨hxL, hx1⟩ := hx
  have hxmem : x ∈ lineA h hn := by rw [mem_lineA_iff h hn]; exact ⟨hxL, hx1⟩
  have hxA := alpha_mapsTo_lineA h hn α hα hT hdet hxmem
  have hApair := L0_eq_pair h hn hxL hx1
  rw [show lineA h hn = {x, x⁻¹} by rw [lineA]; exact hApair] at hxA
  rcases hxA with hfix | hinv
  · exact hfix
  · exfalso
    obtain ⟨a, ha, ha1, hx_eq⟩ := hxL
    have ha0 : a 0 ≠ 1 := by
      intro h0
      apply hx1
      rw [hx_eq, torusElt_eq_one_iff h hn ha]
      funext i
      fin_cases i <;> simp [h0, ha1]
    have hxinv_ne : x⁻¹ ≠ x := by
      intro heqinv
      have h' : torusElt h hn a⁻¹
          (fun i => by rw [Pi.inv_apply, inv_pow, ha i, inv_one]) = torusElt h hn a ha := by
        rw [hx_eq] at heqinv
        rw [torusElt_inv]
        exact heqinv
      have heq : a⁻¹ = a := (torusElt_eq_iff h hn _ ha).mp h'
      exact inv_ne_self_of_pow_three (ha 0) ha0 (by simpa using congrFun heq 0)
    have hdisj : Disjoint ({x} : Set (hypSU h 2 0)) {x⁻¹} := by
      rw [Set.disjoint_left]
      intro y hy hy'
      rw [Set.mem_singleton_iff] at hy hy'
      exact hxinv_ne (hy.symm.trans hy').symm
    have hmapsA : α '' ({x} : Set (hypSU h 2 0)) ⊆ {x⁻¹} := by
      rintro y ⟨b, hb, rfl⟩
      rw [Set.mem_singleton_iff] at hb
      rw [hb, Set.mem_singleton_iff]
      exact hinv
    have hmapsB : α '' ({x⁻¹} : Set (hypSU h 2 0)) ⊆ {x} := by
      rintro y ⟨b, hb, rfl⟩
      rw [Set.mem_singleton_iff] at hb
      rw [hb, Set.mem_singleton_iff]
      rw [map_inv, hinv, inv_inv]
    obtain ⟨k, hk⟩ := hα
    exact false_of_odd_iterate hdisj hmapsA hmapsB (Set.mem_singleton x)
      (odd_three_pow k) (mulAut_iterate_three_pow_eq_self α hk x)

private theorem alpha_fixes_lineB (h : UnitaryFieldData 2 n K) (hn : Even n)
    (α : MulAut (hypSU h 2 0)) (hα : ∃ k : ℕ, α ^ (3 ^ k) = 1)
    (hT : ∀ s ∈ torusPow h 2 0 3, α s ∈ torusPow h 2 0 3)
    (hdet : ∀ g : hypSU h 2 0,
      ((((α g : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) -
          1).det = 0 ↔
        (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) - 1).det = 0) :
    ∀ x ∈ lineB h hn, α x = x := by
  intro x hx
  rw [mem_lineB_iff h hn] at hx
  obtain ⟨hxL, hx1⟩ := hx
  have hxmem : x ∈ lineB h hn := by rw [mem_lineB_iff h hn]; exact ⟨hxL, hx1⟩
  have hxB := alpha_mapsTo_lineB h hn α hα hT hdet hxmem
  have hBpair := L1_eq_pair h hn hxL hx1
  rw [show lineB h hn = {x, x⁻¹} by rw [lineB]; exact hBpair] at hxB
  rcases hxB with hfix | hinv
  · exact hfix
  · exfalso
    obtain ⟨a, ha, ha0, hx_eq⟩ := hxL
    have ha1 : a 1 ≠ 1 := by
      intro h1
      apply hx1
      rw [hx_eq, torusElt_eq_one_iff h hn ha]
      funext i
      fin_cases i <;> simp [h1, ha0]
    have hxinv_ne : x⁻¹ ≠ x := by
      intro heqinv
      have h' : torusElt h hn a⁻¹
          (fun i => by rw [Pi.inv_apply, inv_pow, ha i, inv_one]) = torusElt h hn a ha := by
        rw [hx_eq] at heqinv
        rw [torusElt_inv]
        exact heqinv
      have heq : a⁻¹ = a := (torusElt_eq_iff h hn _ ha).mp h'
      exact inv_ne_self_of_pow_three (ha 1) ha1 (by simpa using congrFun heq 1)
    have hdisj : Disjoint ({x} : Set (hypSU h 2 0)) {x⁻¹} := by
      rw [Set.disjoint_left]
      intro y hy hy'
      rw [Set.mem_singleton_iff] at hy hy'
      exact hxinv_ne (hy.symm.trans hy').symm
    have hmapsA : α '' ({x} : Set (hypSU h 2 0)) ⊆ {x⁻¹} := by
      rintro y ⟨b, hb, rfl⟩
      rw [Set.mem_singleton_iff] at hb
      rw [hb, Set.mem_singleton_iff]
      exact hinv
    have hmapsB : α '' ({x⁻¹} : Set (hypSU h 2 0)) ⊆ {x} := by
      rintro y ⟨b, hb, rfl⟩
      rw [Set.mem_singleton_iff] at hb
      rw [hb, Set.mem_singleton_iff]
      rw [map_inv, hinv, inv_inv]
    obtain ⟨k, hk⟩ := hα
    exact false_of_odd_iterate hdisj hmapsA hmapsB (Set.mem_singleton x)
      (odd_three_pow k) (mulAut_iterate_three_pow_eq_self α hk x)

private theorem firstLine_cube {c : Kˣ} (hc : c ^ 3 = 1) :
    ∀ i, firstLine c i ^ 3 = 1 := by
  intro i
  rw [firstLine]
  split_ifs with hi
  · exact hc
  · exact one_pow 3

private theorem secondLine_cube {c : Kˣ} (hc : c ^ 3 = 1) :
    ∀ i, secondLine c i ^ 3 = 1 := by
  intro i
  rw [secondLine]
  split_ifs with hi
  · exact one_pow 3
  · exact hc

private theorem alpha_fixes_torusPow (h : UnitaryFieldData 2 n K) (hn : Even n)
    (α : MulAut (hypSU h 2 0)) (hα : ∃ k : ℕ, α ^ (3 ^ k) = 1)
    (hT : ∀ s ∈ torusPow h 2 0 3, α s ∈ torusPow h 2 0 3)
    (hdet : ∀ g : hypSU h 2 0,
      ((((α g : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) -
          1).det = 0 ↔
        (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) - 1).det = 0) :
    ∀ s ∈ torusPow h 2 0 3, α s = s := by
  intro s hs
  obtain ⟨a, ha, rfl⟩ := eq_torusElt_of_mem_torusPow h hn hs
  set x : hypSU h 2 0 := torusElt h hn (firstLine (a 0)) (firstLine_cube (ha 0)) with hxdef
  set y : hypSU h 2 0 := torusElt h hn (secondLine (a 1)) (secondLine_cube (ha 1)) with hydef
  have hxL0 : x ∈ L0 h hn := by
    rw [hxdef, torusElt_mem_L0 h hn]
    simp [firstLine]
  have hyL1 : y ∈ L1 h hn := by
    rw [hydef, torusElt_mem_L1 h hn]
    simp [secondLine]
  have hdecomp : torusElt h hn a ha = x * y := by
    have hfun : firstLine (a 0) * secondLine (a 1) = a := by
      funext i
      fin_cases i <;> simp [firstLine, secondLine]
    have hc : ∀ i, (firstLine (a 0) * secondLine (a 1) : Fin 2 → Kˣ) i ^ 3 = 1 :=
      fun i => by
        rw [Pi.mul_apply, mul_pow, firstLine_cube (ha 0) i, secondLine_cube (ha 1) i, one_mul]
    rw [hxdef, hydef]
    calc torusElt h hn a ha
        = torusElt h hn (firstLine (a 0) * secondLine (a 1)) hc :=
          (torusElt_eq_of_eq h hn ha hc hfun).symm
      _ = torusElt h hn (firstLine (a 0)) (firstLine_cube (ha 0)) *
            torusElt h hn (secondLine (a 1)) (secondLine_cube (ha 1)) :=
          (torusElt_mul_apply h hn (firstLine (a 0)) (secondLine (a 1))
            (firstLine_cube (ha 0)) (secondLine_cube (ha 1)) hc).symm
  have hxfix : α x = x := by
    by_cases hx1 : x = 1
    · rw [hx1, map_one]
    · exact alpha_fixes_lineA h hn α hα hT hdet x (by
        rw [mem_lineA_iff h hn]
        exact ⟨hxL0, hx1⟩)
  have hyfix : α y = y := by
    by_cases hy1 : y = 1
    · rw [hy1, map_one]
    · exact alpha_fixes_lineB h hn α hα hT hdet y (by
        rw [mem_lineB_iff h hn]
        exact ⟨hyL1, hy1⟩)
  rw [hdecomp, map_mul, hxfix, hyfix]

theorem eq_of_mem_torusPow_three (h : UnitaryFieldData 2 n K) (hn : Even n)
    (α : MulAut (hypSU h 2 0)) (hα : ∃ k : ℕ, α ^ (3 ^ k) = 1)
    (hT : ∀ s ∈ torusPow h 2 0 3, α s ∈ torusPow h 2 0 3)
    (hdet : ∀ g : hypSU h 2 0,
      ((((α g : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) -
          1).det = 0 ↔
        (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) - 1).det = 0)
    {s : hypSU h 2 0} (hs : s ∈ torusPow h 2 0 3) : α s = s :=
  alpha_fixes_torusPow h hn α hα hT hdet s hs

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Syl3
