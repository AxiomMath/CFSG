module

public import CFSG.Quasithin.Vol2.Ch10SecA312AH
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL4L5

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open scoped commutatorElement

section Matrices

variable {n : ℕ} {K : Type} [Field K]

theorem entries_of_comm_transvection {g : SpecialLinearGroup (Fin n) K} {i j : Fin n}
    (hij : i ≠ j)
    (h : g * SpecialLinearGroup.transvection hij 1 = SpecialLinearGroup.transvection hij 1 * g) :
    (∀ r, r ≠ i → (g : Matrix (Fin n) (Fin n) K) r i = 0) ∧
      ∀ k, k ≠ j → (g : Matrix (Fin n) (Fin n) K) j k = 0 := by
  have h1 := congrArg (fun x : SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection, mul_add,
    add_mul, mul_one, one_mul, add_right_inj] at h1
  refine ⟨fun r hr => ?_, fun k hk => ?_⟩
  · have := congrFun₂ h1 r j
    rwa [mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ hr, mul_one] at this
  · have := congrFun₂ h1 i k
    rw [mul_single_apply_of_ne _ _ _ _ _ hk, single_mul_apply_same, one_mul] at this
    exact this.symm

theorem entry_eq_one_of_center {z : SpecialLinearGroup (Fin n) K} (hz : z ∈ unitriangular n K)
    (hc : ∀ u ∈ unitriangular n K, z * u = u * z) {r k : Fin n}
    (hrk : ¬ ((r : ℕ) = 0 ∧ (k : ℕ) + 1 = n)) :
    (z : Matrix (Fin n) (Fin n) K) r k = (1 : Matrix (Fin n) (Fin n) K) r k := by
  by_cases hd : r = k
  · subst hd
    rw [hz.2 r, Matrix.one_apply_eq]
  rw [Matrix.one_apply_ne hd]
  by_cases hk : (k : ℕ) + 1 < n
  · have hlt : k < ⟨k + 1, hk⟩ := Fin.mk_lt_mk.2 (by simp)
    exact (entries_of_comm_transvection hlt.ne
      (hc _ (transvection_mem_unitriangular hlt 1))).1 r hd
  · have hr0 : (r : ℕ) ≠ 0 := fun h0 => hrk ⟨h0, by omega⟩
    have hlt : (⟨r - 1, by omega⟩ : Fin n) < r := Fin.mk_lt_mk.2 (by omega)
    exact (entries_of_comm_transvection hlt.ne
      (hc _ (transvection_mem_unitriangular hlt 1))).2 k (Ne.symm hd)

theorem eq_one_of_entries {z : SpecialLinearGroup (Fin n) K}
    (hz : ∀ r k : Fin n, ¬ ((r : ℕ) = 0 ∧ (k : ℕ) + 1 = n) →
      (z : Matrix (Fin n) (Fin n) K) r k = (1 : Matrix (Fin n) (Fin n) K) r k)
    (h0 : ∀ r k : Fin n, (r : ℕ) = 0 → (k : ℕ) + 1 = n → (z : Matrix (Fin n) (Fin n) K) r k = 0)
    (hn : 2 ≤ n) : z = 1 := by
  refine Subtype.ext (Matrix.ext fun r k => ?_)
  by_cases hrk : (r : ℕ) = 0 ∧ (k : ℕ) + 1 = n
  · rw [h0 r k hrk.1 hrk.2, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne]
    intro e
    have := congrArg Fin.val e
    omega
  · exact hz r k hrk

end Matrices

section Blocks

variable {n : ℕ} {K : Type} [Field K]

theorem liftT_mem_perfectCore {I : Set ℕ} {a m : ℕ} (h : a + m ≤ n) (hm3 : 3 ≤ m)
    (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m)) {i j : Fin m} (hij : i ≠ j) :
    (liftT a m h hij : SpecialLinearGroup (Fin n) K) ∈ perfectCore (flagStabilizer n K I) := by
  classical
  set P₀ : Subgroup (SpecialLinearGroup (Fin n) K) :=
    Subgroup.closure {x | ∃ (i j : Fin m) (hij : i ≠ j), x = liftT a m h hij} with hP₀
  have hgen : ∀ (i j : Fin m) (hij : i ≠ j), liftT a m h hij ∈ P₀ := fun i j hij =>
    Subgroup.subset_closure ⟨i, j, hij, rfl⟩
  have hP₀H : P₀ ≤ flagStabilizer n K I := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, j, hij, rfl⟩
    exact liftT_mem_flagStabilizer a m h hno hij
  have h1 : ⁅P₀, P₀⁆ ≤ P₀ := Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have h2 : P₀ ≤ ⁅P₀, P₀⁆ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, j, hij, rfl⟩
    obtain ⟨k, hki, hkj⟩ : ∃ k : Fin m, k ≠ i ∧ k ≠ j := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset (Fin m)) ⊆ {i, j} := fun k _ => by
        by_cases hki : k = i
        · simp [hki]
        · simp [hcon k hki]
      have e1 := Finset.card_le_card hsub
      have e2 := Finset.card_le_two (a := i) (b := j)
      simp only [Finset.card_univ, Fintype.card_fin] at e1
      omega
    have hcomm : ⁅(liftT a m h (Ne.symm hki) : SpecialLinearGroup (Fin n) K),
        (liftT a m h hkj : SpecialLinearGroup (Fin n) K)⁆ = liftT a m h hij := by
      have := SpecialLinearGroup.commutatorElement_transvection
        (blkIdxN_ne (h := h) (Ne.symm hki)) (blkIdxN_ne (h := h) hkj)
        (blkIdxN_ne (h := h) hij) (1 : K) 1
      rw [mul_one] at this
      exact this
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (hgen _ _ _) (hgen _ _ _)
  exact le_perfectCore_of_perfect hP₀H (le_antisymm h1 h2) (hgen i j hij)

theorem liftT_eq (a m : ℕ) (h : a + m ≤ n) {i j : Fin m} (hij : i ≠ j) :
    (liftT a m h hij : SpecialLinearGroup (Fin n) K) =
      SpecialLinearGroup.transvection (blkIdxN_ne (h := h) hij) 1 := rfl

end Blocks

section Middle

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem blkAt_transvection_eq_one {r k : Fin 5} (hrk : r ≠ k) (hr : (r : ℕ) = 0 ∨ (k : ℕ) = 4) :
    blkAt 1 3 (by norm_num) ((SpecialLinearGroup.transvection hrk (1 : K) :
      SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 1 := by
  ext i j
  rw [blkAt_apply, CFSG.LinearGroups.coe_transvection]
  have hi := i.isLt
  have hj := j.isLt
  simp only [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, Fin.ext_iff]
  rcases hr with hr | hr
  · have : ¬ ((r : ℕ) = 1 + i) := by omega
    simp [this, Nat.add_left_cancel_iff]
  · have : ¬ ((k : ℕ) = 1 + j) := by omega
    simp [this, Nat.add_left_cancel_iff]

theorem fin5_mid {k : Fin 5} (h0 : k ≠ 0) (h4 : k ≠ 4) : k = 1 ∨ k = 2 ∨ k = 3 := by
  fin_cases k <;> simp_all

theorem fin5_cases (r : Fin 5) : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by
  fin_cases r <;> simp

variable (hK : Nat.card K = 2) {I : Set ℕ} (h1 : 1 ∈ I) (h4 : 4 ∈ I)
  (hno : ∀ c ∈ I, ¬ (1 < c ∧ c < 1 + 3))

include hK h1 h4 hno in
theorem pCoreOf_middle :
    pCoreOf 2 (perfectCore (flagStabilizer 5 K I)) =
      (bigBlockHom (K := K) I 1 3 (by norm_num) (Or.inr h1) (Or.inr h4)).ker.map
        (perfectCore (flagStabilizer 5 K I)).subtype := by
  classical
  have hcardK : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hcardK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : 1 + 3 ≤ 5 := by norm_num
  have hgs := bigBlockHom_surjective hK h3 le_rfl (Or.inr h1) (Or.inr h4) hno
  have := sl_isSimple_of_card_two hK (m := 3) le_rfl
  have hker : IsPGroup 2 (bigBlockHom (K := K) I 1 3 h3 (Or.inr h1) (Or.inr h4)).ker := by
    intro x
    obtain ⟨k, hk⟩ := isPGroup_unitriangular_charTwo (K := K) (n := 5) (by norm_num)
      ⟨(x.1 : SpecialLinearGroup (Fin 5) K),
        unitriangular_of_bigBlockHom hK le_rfl h3 le_rfl (Or.inr h1) (Or.inr h4) hno x.1 x.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    exact this
  rw [← pCore_two_eq_ker (sl_nonabelian_of_card_two hK le_rfl) _ hgs hker]
  rfl

include hK h1 h4 hno in
theorem transvection_mem_pCoreOf_middle {r k : Fin 5} (hrk : r ≠ k) (l : Fin 5) (hlr : l ≠ r)
    (hlk : l ≠ k) (hl1 : 1 ≤ (l : ℕ)) (hl3 : (l : ℕ) ≤ 3)
    (hcase : ((r : ℕ) = 0 ∧ 1 ≤ (k : ℕ) ∧ (k : ℕ) ≤ 3) ∨
      ((k : ℕ) = 4 ∧ 1 ≤ (r : ℕ) ∧ (r : ℕ) ≤ 3)) :
    SpecialLinearGroup.transvection hrk (1 : K) ∈
      pCoreOf 2 (perfectCore (flagStabilizer 5 K I)) := by
  classical
  set N := perfectCore (flagStabilizer 5 K I) with hN
  have h3 : 1 + 3 ≤ 5 := by norm_num
  have hNnorm : ∀ x ∈ flagStabilizer 5 K I, ∀ y ∈ N, ⁅x, y⁆ ∈ N := fun x hx y hy => by
    have hxN : x ∈ Subgroup.normalizer (N : Set (SpecialLinearGroup (Fin 5) K)) :=
      normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer hx)
    rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 hxN y).1 hy) (inv_mem hy)
  have hmemQ : ∀ {r k : Fin 5} (hrk : r ≠ k), ((r : ℕ) = 0 ∨ (k : ℕ) = 4) →
      (SpecialLinearGroup.transvection hrk (1 : K)) ∈ flagStabilizer 5 K I := by
    intro r k hrk hr
    refine mem_flagStabilizer_of_entries fun p q c hc hq hp => ?_
    have hpq : p ≠ q := fun e => by subst e; omega
    have hp5 := p.isLt
    have hne : ¬ (r = p ∧ k = q) := by
      rintro ⟨rfl, rfl⟩
      omega
    simp [CFSG.LinearGroups.coe_transvection, Matrix.one_apply_ne hpq, hne]
  have hcongr : ∀ {i j i₂ j₂ : Fin 5} (h : i ≠ j) (h₂ : i₂ ≠ j₂), i = i₂ → j = j₂ →
      SpecialLinearGroup.transvection h (1 : K) = SpecialLinearGroup.transvection h₂ 1 := by
    rintro _ _ _ _ _ _ rfl rfl
    rfl
  have hblock : ∀ {i j : Fin 5} (hij : i ≠ j), 1 ≤ (i : ℕ) → (i : ℕ) ≤ 3 → 1 ≤ (j : ℕ) →
      (j : ℕ) ≤ 3 → SpecialLinearGroup.transvection hij (1 : K) ∈ N := by
    intro i j hij hi1 hi3 hj1 hj3
    have hij' : (⟨(i : ℕ) - 1, by omega⟩ : Fin 3) ≠ ⟨(j : ℕ) - 1, by omega⟩ := fun e =>
      hij (Fin.ext (by have := congrArg Fin.val e; simp only at this; omega))
    have hmem := liftT_mem_perfectCore (K := K) (I := I) h3 le_rfl hno hij'
    rw [liftT_eq] at hmem
    rwa [hcongr hij (blkIdxN_ne (h := h3) hij') (Fin.ext (by simp [blkIdxN]; omega))
      (Fin.ext (by simp [blkIdxN]; omega))]
  have hr : (r : ℕ) = 0 ∨ (k : ℕ) = 4 := by
    rcases hcase with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hmemN : SpecialLinearGroup.transvection hrk (1 : K) ∈ N := by
    rcases hcase with ⟨hr0, hk1, hk3⟩ | ⟨hk4, hr1, hr3⟩
    · have hc := hNnorm _ (hmemQ (Ne.symm hlr) (Or.inl hr0)) _ (hblock hlk hl1 hl3 hk1 hk3)
      rwa [SpecialLinearGroup.commutatorElement_transvection (Ne.symm hlr) hlk hrk, one_mul] at hc
    · have hc := hNnorm _ (hmemQ hlk (Or.inr hk4)) _ (hblock (Ne.symm hlr) hr1 hr3 hl1 hl3)
      have hc' : ⁅SpecialLinearGroup.transvection (Ne.symm hlr) (1 : K),
          SpecialLinearGroup.transvection hlk (1 : K)⁆ ∈ N := by
        have h2 := inv_mem hc
        rwa [commutatorElement_inv] at h2
      rwa [SpecialLinearGroup.commutatorElement_transvection (Ne.symm hlr) hlk hrk,
        one_mul] at hc'
  rw [pCoreOf_middle hK h1 h4 hno]
  refine ⟨⟨_, hmemN⟩, ?_, rfl⟩
  show bigBlockHom (K := K) I 1 3 (by norm_num) (Or.inr h1) (Or.inr h4) ⟨_, hmemN⟩ = 1
  refine Subtype.ext ?_
  rw [bigBlockHom_coe]
  exact blkAt_transvection_eq_one hrk hr

include hK h1 h4 hno in
theorem eq_single_of_middle {v : SpecialLinearGroup (Fin 5) K}
    (hv : v ∈ pCoreOf 2 (perfectCore (flagStabilizer 5 K I)))
    (hvc : ∀ u ∈ pCoreOf 2 (perfectCore (flagStabilizer 5 K I)), u * v = v * u) :
    (v : Matrix (Fin 5) (Fin 5) K) =
      1 + Matrix.single 0 4 ((v : Matrix (Fin 5) (Fin 5) K) 0 4) := by
  have T : ∀ {r k : Fin 5} (hrk : r ≠ k) (l : Fin 5), l ≠ r → l ≠ k → 1 ≤ (l : ℕ) →
      (l : ℕ) ≤ 3 →
      (((r : ℕ) = 0 ∧ 1 ≤ (k : ℕ) ∧ (k : ℕ) ≤ 3) ∨ ((k : ℕ) = 4 ∧ 1 ≤ (r : ℕ) ∧ (r : ℕ) ≤ 3)) →
      (∀ q, q ≠ r → (v : Matrix (Fin 5) (Fin 5) K) q r = 0) ∧
        ∀ q, q ≠ k → (v : Matrix (Fin 5) (Fin 5) K) k q = 0 := fun hrk l hlr hlk hl1 hl3 hcase =>
    entries_of_comm_transvection hrk
      (hvc _ (transvection_mem_pCoreOf_middle hK h1 h4 hno hrk l hlr hlk hl1 hl3 hcase)).symm
  have E01 := T (r := 0) (k := 1) (by decide) 2 (by decide) (by decide) (by decide) (by decide)
    (Or.inl ⟨rfl, by decide, by decide⟩)
  have E02 := T (r := 0) (k := 2) (by decide) 1 (by decide) (by decide) (by decide) (by decide)
    (Or.inl ⟨rfl, by decide, by decide⟩)
  have E03 := T (r := 0) (k := 3) (by decide) 1 (by decide) (by decide) (by decide) (by decide)
    (Or.inl ⟨rfl, by decide, by decide⟩)
  have E14 := T (r := 1) (k := 4) (by decide) 2 (by decide) (by decide) (by decide) (by decide)
    (Or.inr ⟨rfl, by decide, by decide⟩)
  have E24 := T (r := 2) (k := 4) (by decide) 1 (by decide) (by decide) (by decide) (by decide)
    (Or.inr ⟨rfl, by decide, by decide⟩)
  have E34 := T (r := 3) (k := 4) (by decide) 1 (by decide) (by decide) (by decide) (by decide)
    (Or.inr ⟨rfl, by decide, by decide⟩)
  have hvU : v ∈ unitriangular 5 K := by
    rw [pCoreOf_middle hK h1 h4 hno] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    exact unitriangular_of_bigBlockHom hK le_rfl (by norm_num) le_rfl (Or.inr h1) (Or.inr h4)
      hno x hx
  have hoff : ∀ r k : Fin 5, r ≠ k → ¬ (r = 0 ∧ k = 4) →
      (v : Matrix (Fin 5) (Fin 5) K) r k = 0 := by
    intro r k hrk h04
    rcases fin5_cases r with rfl | rfl | rfl | rfl | rfl
    · rcases fin5_mid (Ne.symm hrk) (fun h => h04 ⟨rfl, h⟩) with rfl | rfl | rfl
      · exact E14.1 0 (by decide)
      · exact E24.1 0 (by decide)
      · exact E34.1 0 (by decide)
    · exact E01.2 k (Ne.symm hrk)
    · exact E02.2 k (Ne.symm hrk)
    · exact E03.2 k (Ne.symm hrk)
    · exact E14.2 k (Ne.symm hrk)
  ext r k
  rw [Matrix.add_apply, Matrix.single_apply]
  by_cases hrk : r = k
  · subst hrk
    rw [hvU.2 r, Matrix.one_apply_eq]
    have : ¬ ((0 : Fin 5) = r ∧ (4 : Fin 5) = r) := fun ⟨e1, e2⟩ => by
      rw [← e1] at e2; exact absurd e2 (by decide)
    simp [this]
  · rw [Matrix.one_apply_ne hrk, zero_add]
    by_cases h04 : r = 0 ∧ k = 4
    · obtain ⟨rfl, rfl⟩ := h04
      simp
    · have : ¬ ((0 : Fin 5) = r ∧ (4 : Fin 5) = k) := fun h => h04 ⟨h.1.symm, h.2.symm⟩
      rw [hoff r k hrk h04]
      simp [this]

include hK h1 h4 in
theorem comm_single_middle {b : SpecialLinearGroup (Fin 5) K}
    (hb : b ∈ flagStabilizer 5 K I) (c : K) :
    (b : Matrix (Fin 5) (Fin 5) K) * Matrix.single 0 4 c =
      Matrix.single 0 4 c * (b : Matrix (Fin 5) (Fin 5) K) := by
  have hb0 : ∀ r : Fin 5, r ≠ 0 → (b : Matrix (Fin 5) (Fin 5) K) r 0 = 0 := fun r hr =>
    stabilizer_entries (mem_flagStabilizer.1 hb 1 h1) (by simp)
      (by have : (r : ℕ) ≠ 0 := fun h => hr (Fin.ext h); omega)
  have hb4 : ∀ k : Fin 5, k ≠ 4 → (b : Matrix (Fin 5) (Fin 5) K) 4 k = 0 := fun k hk =>
    stabilizer_entries (mem_flagStabilizer.1 hb 4 h4)
      (by have := k.isLt; have : (k : ℕ) ≠ 4 := fun h => hk (Fin.ext h); omega) (by simp)
  have hb00 : (b : Matrix (Fin 5) (Fin 5) K) 0 0 = 1 := by
    rcases eq_zero_or_eq_one_of_card_two hK ((b : Matrix (Fin 5) (Fin 5) K) 0 0) with h | h
    · exfalso
      have := Matrix.det_eq_zero_of_column_eq_zero (A := (b : Matrix (Fin 5) (Fin 5) K))
        (0 : Fin 5) fun r => by
          by_cases hr : r = 0
          · subst hr; exact h
          · exact hb0 r hr
      rw [b.2] at this
      exact one_ne_zero this
    · exact h
  have hb44 : (b : Matrix (Fin 5) (Fin 5) K) 4 4 = 1 := by
    rcases eq_zero_or_eq_one_of_card_two hK ((b : Matrix (Fin 5) (Fin 5) K) 4 4) with h | h
    · exfalso
      have := Matrix.det_eq_zero_of_row_eq_zero (A := (b : Matrix (Fin 5) (Fin 5) K))
        (4 : Fin 5) fun k => by
          by_cases hk : k = 4
          · subst hk; exact h
          · exact hb4 k hk
      rw [b.2] at this
      exact one_ne_zero this
    · exact h
  ext r k
  by_cases hk : k = 4 <;> by_cases hr : r = 0
  · subst hk hr
    rw [mul_single_apply_same, single_mul_apply_same, hb00, hb44, one_mul, mul_one]
  · subst hk
    rw [mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ hr, hb0 r hr, zero_mul]
  · subst hr
    rw [mul_single_apply_of_ne _ _ _ _ _ hk, single_mul_apply_same, hb4 k hk, mul_zero]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hk, single_mul_apply_of_ne _ _ _ _ _ hr]

include hK h1 h4 hno in
theorem comm_of_middle {v : SpecialLinearGroup (Fin 5) K}
    (hv : v ∈ pCoreOf 2 (perfectCore (flagStabilizer 5 K I)))
    (hvc : ∀ u ∈ pCoreOf 2 (perfectCore (flagStabilizer 5 K I)), u * v = v * u)
    {b : SpecialLinearGroup (Fin 5) K} (hb : b ∈ perfectCore (flagStabilizer 5 K I)) :
    b * v = v * b := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    eq_single_of_middle hK h1 h4 hno hv hvc, mul_add, add_mul, mul_one, one_mul,
    comm_single_middle hK h1 h4 (perfectCore_le _ hb)]

end Middle

section Main

variable {K : Type} [Field K] [Finite K]

theorem zcentFor_sl_two (hK : Nat.card K = 2) {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    (hq : CFSG.IsQuasisimple (SpecialLinearGroup (Fin n) K)) :
    ZCentFor (SpecialLinearGroup (Fin n) K) := by
  classical
  have hcardK : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hcardK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 (n := n) (by omega)
  have hT₀ : IsSylowTwoOf (unitriangular n K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  refine ZCentFor.of_sylow _ hT₀ fun B hB hBtop z hzT hz1 hzc hzB => ?_
  have hB' : B ∈ cComp (B ⊔ unitriangular n K) := hB
  have hMne : B ⊔ unitriangular n K ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  have hMns : ¬ Group.IsSolvable ↥(B ⊔ unitriangular n K) := fun hs =>
    not_isSolvable_of_mem_cComp hB'
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ unitriangular n K))
        (Subgroup.inclusion_injective _))
  have hUB : upperTriangular n K ≤ B ⊔ unitriangular n K :=
    (upperTriangular_le_unitriangular hK).trans le_sup_right
  obtain ⟨hMQ, -⟩ := borel_overgroups (B ⊔ unitriangular n K) hUB
  have hIcuts : ∀ c ∈ borelOvergroupCuts (B ⊔ unitriangular n K), 1 ≤ c ∧ c < n := fun c hc => by
    obtain ⟨e1, e2, -⟩ := hc
    exact ⟨e1, e2⟩
  generalize borelOvergroupCuts (B ⊔ unitriangular n K) = I at hMQ hIcuts
  rcases exists_big_or_small (n := n) (I := I) with hsmall | ⟨a, m, h, hm3, ha, hb, hno⟩
  · exfalso
    apply hMns
    rw [isSolvable_iff_perfectCore_eq_bot, hMQ]
    exact perfectCore_eq_bot_of_small hK (by omega) hsmall
  obtain ⟨hBeq, -⟩ := bigBlock_conclusion hK (by omega) hn5 h hm3 ha hb hno hB hMQ
  have hBN : B = perfectCore (flagStabilizer n K I) := hBeq.trans (congrArg perfectCore hMQ)
  subst hBN
  have hzc' : ∀ u ∈ unitriangular n K, z * u = u * z := hzc
  have hzent : ∀ r k : Fin n, ¬ ((r : ℕ) = 0 ∧ (k : ℕ) + 1 = n) →
      (z : Matrix (Fin n) (Fin n) K) r k = (1 : Matrix (Fin n) (Fin n) K) r k :=
    fun r k hrk => entry_eq_one_of_center hzT hzc' hrk
  by_cases ha0 : a = 0
  · exfalso
    subst ha0
    have h01 : (⟨1, by omega⟩ : Fin m) ≠ ⟨0, by omega⟩ := by simp
    have hcomm := hzB _ (liftT_mem_perfectCore (K := K) h hm3 hno h01)
    rw [liftT_eq] at hcomm
    have h2 := (entries_of_comm_transvection (blkIdxN_ne (h := h) h01) hcomm).2
    refine hz1 (eq_one_of_entries hzent (fun r k hr hk => ?_) (by omega))
    have hr' : r = blkIdxN 0 m h ⟨0, by omega⟩ := Fin.ext (by simp [blkIdxN, hr])
    rw [hr']
    exact h2 k (fun e => by have := congrArg Fin.val e; simp [blkIdxN] at this; omega)
  by_cases hbn : a + m = n
  · exfalso
    have hij : (⟨m - 1, by omega⟩ : Fin m) ≠ ⟨m - 2, by omega⟩ := by
      simp only [ne_eq, Fin.mk.injEq]; omega
    have hcomm := hzB _ (liftT_mem_perfectCore (K := K) h hm3 hno hij)
    rw [liftT_eq] at hcomm
    have h2 := (entries_of_comm_transvection (blkIdxN_ne (h := h) hij) hcomm).1
    refine hz1 (eq_one_of_entries hzent (fun r k hr hk => ?_) (by omega))
    have hk' : k = blkIdxN a m h ⟨m - 1, by omega⟩ := Fin.ext (by simp [blkIdxN]; omega)
    rw [hk']
    exact h2 r (fun e => by have := congrArg Fin.val e; simp [blkIdxN] at this; omega)
  obtain ⟨rfl, rfl, rfl⟩ : n = 5 ∧ a = 1 ∧ m = 3 := by omega
  have h1 : 1 ∈ I := by
    rcases ha with ha | ha
    · omega
    · exact ha
  have h4 : 4 ∈ I := by
    rcases hb with hb | hb
    · omega
    · exact hb
  intro v hv hvc _ b hb'
  exact comm_of_middle hK h1 h4 hno hv hvc hb'

theorem zcentFor_of_isPSL_two {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5) (h : IsPSL n 2 1 X) : ZCentFor X := by
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := h
  have hK : Nat.card K = 2 := by simpa using hcard
  let e' : X ≃* SpecialLinearGroup (Fin n) K := e.trans (slEquivStatedProj hK n).symm
  exact ZCentFor.of_mulEquiv e'
    (zcentFor_sl_two hK hn4 hn5 (CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq))

end Main

theorem a312ZCentL45_holds : A312ZCentL45 := by
  intro X _ _ T B hcase hc
  have hq' : CFSG.IsQuasisimple ↥(⊤ : Subgroup X) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hc.1
  rcases hcase with ⟨-, h45, -⟩ | ⟨-, h5, -⟩
  · rcases h45 with h4 | h5
    · exact false_of_zcentFor (ZCentFor.of_top (zcentFor_of_isPSL_two hq' le_rfl
        (by norm_num) h4)) hc
    · exact false_of_zcentFor (ZCentFor.of_top (zcentFor_of_isPSL_two hq' (by norm_num)
        le_rfl h5)) hc
  · exact false_of_zcentFor (ZCentFor.of_top (zcentFor_of_isPSL_two hq' (by norm_num)
      le_rfl h5)) hc

end CFSG.Quasithin.Vol2.Ch10.A312A
