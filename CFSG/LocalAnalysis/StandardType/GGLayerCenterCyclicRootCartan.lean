module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification
public import CFSG.HardMathSupport.Timmesfeld.Proving.SimpleRootsCartan

public section

namespace CFSG.StandardType

namespace LayerCycRoot

@[expose] def KerDetect {ι : Type*} [Fintype ι] (M : Matrix ι ι ℤ) (p : ℕ) (i₀ : ι) : Prop :=
  ∀ x : ι → ZMod p, (∀ j, ∑ i, x i * (M i j : ZMod p) = 0) → x i₀ = 0 → ∀ i, x i = 0

theorem intCast_ne_zero_of_natAbs_le_two {p : ℕ} [hp : Fact p.Prime] (hp2 : 2 < p) {c : ℤ}
    (hc : c ≠ 0) (hc2 : c.natAbs ≤ 2) : (c : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro h
  have h1 : p ∣ c.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr h
    simpa using this
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hc) h1
  omega

theorem eq_zero_of_forcing {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℤ} {p : ℕ}
    [Fact p.Prime] (hp2 : 2 < p) {x : ι → ZMod p} (hx : ∀ j, ∑ i, x i * (M i j : ZMod p) = 0)
    {k j : ι} (hk : M k j ≠ 0) (hk2 : (M k j).natAbs ≤ 2)
    (hS : ∀ i, i ≠ k → M i j ≠ 0 → x i = 0) : x k = 0 := by
  have h := hx j
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at h
  have h0 : ∑ i ∈ Finset.univ.erase k, x i * (M i j : ZMod p) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    by_cases hM : M i j = 0
    · rw [hM, Int.cast_zero, mul_zero]
    · rw [hS i (Finset.ne_of_mem_erase hi) hM, zero_mul]
  rw [h0, add_zero] at h
  exact (mul_eq_zero.1 h).resolve_right (intCast_ne_zero_of_natAbs_le_two hp2 hk hk2)

theorem eq_zero_of_forcing_finset {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℤ}
    {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {x : ι → ZMod p}
    (hx : ∀ j, ∑ i, x i * (M i j : ZMod p) = 0) (S : Finset ι) (hS0 : ∀ i ∈ S, x i = 0)
    {k j : ι} (hk : M k j ≠ 0) (hk2 : (M k j).natAbs ≤ 2)
    (hS : ∀ i, i ≠ k → M i j ≠ 0 → i ∈ S) : x k = 0 :=
  eq_zero_of_forcing hp2 hx hk hk2 fun i hik hM => hS0 i (hS i hik hM)

theorem eq_zero_of_chain {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} {p : ℕ} [Fact p.Prime]
    (hp2 : 2 < p) {x : Fin n → ZMod p} (hx : ∀ j, ∑ i, x i * (M i j : ZMod p) = 0) (m : ℕ)
    (hm : m ≤ n)
    (hband : ∀ (k : ℕ) (hk : k + 1 < m) (i : Fin n), M i ⟨k, by omega⟩ ≠ 0 → i.val ≤ k + 1)
    (hunit : ∀ (k : ℕ) (hk : k + 1 < m), M ⟨k + 1, by omega⟩ ⟨k, by omega⟩ ≠ 0 ∧
      (M ⟨k + 1, by omega⟩ ⟨k, by omega⟩).natAbs ≤ 2)
    (h0 : ∀ i : Fin n, i.val = 0 → x i = 0) : ∀ i : Fin n, i.val < m → x i = 0 := by
  intro i
  induction' hi : i.val using Nat.strong_induction_on with k ih generalizing i
  intro him
  rcases k with _ | k
  · exact h0 i hi
  · have hk1 : k + 1 < m := by omega
    have hik : i = ⟨k + 1, by omega⟩ := Fin.ext hi
    rw [hik]
    refine eq_zero_of_forcing hp2 hx (j := ⟨k, by omega⟩) (hunit k hk1).1 (hunit k hk1).2 ?_
    intro i' hne hM
    have hle := hband k hk1 i' hM
    have hne' : i'.val ≠ k + 1 := fun h => hne (Fin.ext h)
    exact ih i'.val (by omega) i' rfl (by omega)

section Classical

variable {p : ℕ} [Fact p.Prime]

theorem kerDetect_A (hp2 : 2 < p) {n : ℕ} (hn : 0 < n) :
    KerDetect (CartanMatrix.A n) p ⟨0, hn⟩ := by
  intro x hx h0 i
  refine eq_zero_of_chain hp2 hx n le_rfl ?_ ?_ (fun i hi => ?_) i i.2
  · intro k hk i hM
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff] at hM
    split_ifs at hM with h1 h2
    · omega
    · omega
    · exact absurd rfl hM
  · intro k hk
    have h : CartanMatrix.A n ⟨k + 1, by omega⟩ ⟨k, by omega⟩ = -1 := by
      simp [CartanMatrix.A, Fin.ext_iff]
    rw [h]
    decide
  · rw [show i = ⟨0, hn⟩ from Fin.ext hi]
    exact h0

theorem kerDetect_B (hp2 : 2 < p) {n : ℕ} (hn : 0 < n) :
    KerDetect (CartanMatrix.B n) p ⟨0, hn⟩ := by
  intro x hx h0 i
  refine eq_zero_of_chain hp2 hx n le_rfl ?_ ?_ (fun i hi => ?_) i i.2
  · intro k hk i hM
    simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff] at hM
    split_ifs at hM with h1 h2 h3 h4
    · omega
    · omega
    · omega
    · omega
    · exact absurd rfl hM
  · intro k hk
    have h : CartanMatrix.B n ⟨k + 1, by omega⟩ ⟨k, by omega⟩ = -1 := by
      simp [CartanMatrix.B, Fin.ext_iff]
      omega
    rw [h]
    decide
  · rw [show i = ⟨0, hn⟩ from Fin.ext hi]
    exact h0

theorem kerDetect_C (hp2 : 2 < p) {n : ℕ} (hn : 0 < n) :
    KerDetect (CartanMatrix.C n) p ⟨0, hn⟩ := by
  intro x hx h0 i
  refine eq_zero_of_chain hp2 hx n le_rfl ?_ ?_ (fun i hi => ?_) i i.2
  · intro k hk i hM
    simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff] at hM
    split_ifs at hM with h1 h2 h3 h4
    · omega
    · omega
    · omega
    · omega
    · exact absurd rfl hM
  · intro k hk
    simp only [CartanMatrix.C, Matrix.of_apply, Fin.mk.injEq]
    split_ifs <;> simp_all
  · rw [show i = ⟨0, hn⟩ from Fin.ext hi]
    exact h0

theorem kerDetect_D (hp2 : 2 < p) {n : ℕ} (hn : 4 ≤ n) :
    KerDetect (CartanMatrix.D n) p ⟨0, by omega⟩ := by
  classical
  intro x hx h0
  have harm : ∀ i : Fin n, i.val < n - 2 → x i = 0 := by
    refine eq_zero_of_chain hp2 hx (n - 2) (by omega) ?_ ?_ (fun i hi => ?_)
    · intro k hk i hM
      simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff] at hM
      split_ifs at hM with h1 h2 h3 h4 h5 h6
      all_goals omega
    · intro k hk
      have h : CartanMatrix.D n ⟨k + 1, by omega⟩ ⟨k, by omega⟩ = -1 := by
        simp only [CartanMatrix.D, Matrix.of_apply, Fin.mk.injEq, true_and]
        split_ifs <;> omega
      rw [h]
      decide
    · rw [show i = ⟨0, by omega⟩ from Fin.ext hi]
      exact h0
  have hend : ∀ m : ℕ, ∀ hm : m < n, n - 2 ≤ m → x ⟨m, hm⟩ = 0 := by
    intro m hm hm2
    refine eq_zero_of_forcing hp2 hx (j := ⟨m, hm⟩) ?_ ?_ ?_
    · simp [CartanMatrix.D]
    · simp [CartanMatrix.D]
    · intro i hne hM
      refine harm i ?_
      have hne' : i.val ≠ m := fun h => hne (Fin.ext h)
      simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff] at hM
      split_ifs at hM with h1 h2 h3 h4 h5 h6
      all_goals omega
  intro i
  by_cases hi : i.val < n - 2
  · exact harm i hi
  · exact hend i.val i.2 (by omega)

end Classical

section Exceptional

variable {p : ℕ} [Fact p.Prime]

theorem kerDetect_E6 (hp2 : 2 < p) : KerDetect (CartanMatrix.E 6) p 0 := by
  intro x hx h0
  have h2 : x 2 = 0 := eq_zero_of_forcing_finset hp2 hx {0} (by simpa using h0) (k := 2) (j := 0)
    (by decide) (by decide) (by decide)
  have h3 : x 3 = 0 := eq_zero_of_forcing_finset hp2 hx {0, 2} (by simp [h0, h2]) (k := 3)
    (j := 2) (by decide) (by decide) (by decide)
  have h1 : x 1 = 0 := eq_zero_of_forcing_finset hp2 hx {3} (by simp [h3]) (k := 1) (j := 1)
    (by decide) (by decide) (by decide)
  have h4 : x 4 = 0 := eq_zero_of_forcing_finset hp2 hx {1, 2, 3} (by simp [h1, h2, h3])
    (k := 4) (j := 3) (by decide) (by decide) (by decide)
  have h5 : x 5 = 0 := eq_zero_of_forcing_finset hp2 hx {3, 4} (by simp [h3, h4]) (k := 5)
    (j := 4) (by decide) (by decide) (by decide)
  intro i
  fin_cases i <;> assumption

theorem kerDetect_E7 (hp2 : 2 < p) : KerDetect (CartanMatrix.E 7) p 0 := by
  intro x hx h0
  have h2 : x 2 = 0 := eq_zero_of_forcing_finset hp2 hx {0} (by simpa using h0) (k := 2) (j := 0)
    (by decide) (by decide) (by decide)
  have h3 : x 3 = 0 := eq_zero_of_forcing_finset hp2 hx {0, 2} (by simp [h0, h2]) (k := 3)
    (j := 2) (by decide) (by decide) (by decide)
  have h1 : x 1 = 0 := eq_zero_of_forcing_finset hp2 hx {3} (by simp [h3]) (k := 1) (j := 1)
    (by decide) (by decide) (by decide)
  have h4 : x 4 = 0 := eq_zero_of_forcing_finset hp2 hx {1, 2, 3} (by simp [h1, h2, h3])
    (k := 4) (j := 3) (by decide) (by decide) (by decide)
  have h5 : x 5 = 0 := eq_zero_of_forcing_finset hp2 hx {3, 4} (by simp [h3, h4]) (k := 5)
    (j := 4) (by decide) (by decide) (by decide)
  have h6 : x 6 = 0 := eq_zero_of_forcing_finset hp2 hx {4, 5} (by simp [h4, h5]) (k := 6)
    (j := 5) (by decide) (by decide) (by decide)
  intro i
  fin_cases i <;> assumption

theorem kerDetect_E8 (hp2 : 2 < p) : KerDetect (CartanMatrix.E 8) p 0 := by
  intro x hx h0
  have h2 : x 2 = 0 := eq_zero_of_forcing_finset hp2 hx {0} (by simpa using h0) (k := 2) (j := 0)
    (by decide) (by decide) (by decide)
  have h3 : x 3 = 0 := eq_zero_of_forcing_finset hp2 hx {0, 2} (by simp [h0, h2]) (k := 3)
    (j := 2) (by decide) (by decide) (by decide)
  have h1 : x 1 = 0 := eq_zero_of_forcing_finset hp2 hx {3} (by simp [h3]) (k := 1) (j := 1)
    (by decide) (by decide) (by decide)
  have h4 : x 4 = 0 := eq_zero_of_forcing_finset hp2 hx {1, 2, 3} (by simp [h1, h2, h3])
    (k := 4) (j := 3) (by decide) (by decide) (by decide)
  have h5 : x 5 = 0 := eq_zero_of_forcing_finset hp2 hx {3, 4} (by simp [h3, h4]) (k := 5)
    (j := 4) (by decide) (by decide) (by decide)
  have h6 : x 6 = 0 := eq_zero_of_forcing_finset hp2 hx {4, 5} (by simp [h4, h5]) (k := 6)
    (j := 5) (by decide) (by decide) (by decide)
  have h7 : x 7 = 0 := eq_zero_of_forcing_finset hp2 hx {5, 6} (by simp [h5, h6]) (k := 7)
    (j := 6) (by decide) (by decide) (by decide)
  intro i
  fin_cases i <;> assumption

theorem kerDetect_F4 (hp2 : 2 < p) : KerDetect CartanMatrix.F₄ p 0 := by
  intro x hx h0
  have h1 : x 1 = 0 := eq_zero_of_forcing_finset hp2 hx {0} (by simpa using h0) (k := 1) (j := 0)
    (by decide) (by decide) (by decide)
  have h2 : x 2 = 0 := eq_zero_of_forcing_finset hp2 hx {0, 1} (by simp [h0, h1]) (k := 2)
    (j := 1) (by decide) (by decide) (by decide)
  have h3 : x 3 = 0 := eq_zero_of_forcing_finset hp2 hx {1, 2} (by simp [h1, h2]) (k := 3)
    (j := 2) (by decide) (by decide) (by decide)
  intro i
  fin_cases i <;> assumption

theorem kerDetect_G2 (hp2 : 2 < p) : KerDetect (Matrix.transpose CartanMatrix.G₂) p 1 := by
  intro x hx h1
  have h0 : x 0 = 0 := eq_zero_of_forcing_finset hp2 hx {1} (by simpa using h1) (k := 0) (j := 1)
    (by decide) (by decide) (by decide)
  intro i
  fin_cases i <;> assumption

end Exceptional

section Dynkin

variable {p : ℕ} [Fact p.Prime]

open TauCeti in
theorem exists_kerDetect (hp2 : 2 < p) {t : DynkinType} (ht : t.Valid) :
    ∃ i₀ : Fin t.rank, KerDetect t.cartanMatrix p i₀ := by
  cases t with
  | A n =>
    rw [DynkinType.cartanMatrix_A]
    exact ⟨⟨0, DynkinType.valid_A.mp ht⟩, kerDetect_A hp2 _⟩
  | B n =>
    rw [DynkinType.cartanMatrix_B]
    exact ⟨⟨0, show 0 < n by have := DynkinType.valid_B.mp ht; omega⟩, kerDetect_B hp2 _⟩
  | C n =>
    rw [DynkinType.cartanMatrix_C]
    exact ⟨⟨0, show 0 < n by have := DynkinType.valid_C.mp ht; omega⟩, kerDetect_C hp2 _⟩
  | D n =>
    rw [DynkinType.cartanMatrix_D]
    exact ⟨⟨0, show 0 < n by have := DynkinType.valid_D.mp ht; omega⟩,
      kerDetect_D hp2 (DynkinType.valid_D.mp ht)⟩
  | E6 =>
    rw [DynkinType.cartanMatrix_E6]
    exact ⟨(0 : Fin 6), kerDetect_E6 hp2⟩
  | E7 =>
    rw [DynkinType.cartanMatrix_E7]
    exact ⟨(0 : Fin 7), kerDetect_E7 hp2⟩
  | E8 =>
    rw [DynkinType.cartanMatrix_E8]
    exact ⟨(0 : Fin 8), kerDetect_E8 hp2⟩
  | F4 =>
    rw [DynkinType.cartanMatrix_F4]
    exact ⟨(0 : Fin 4), kerDetect_F4 hp2⟩
  | G2 =>
    rw [DynkinType.cartanMatrix_G2]
    exact ⟨(1 : Fin 2), kerDetect_G2 hp2⟩

omit [Fact p.Prime] in
theorem kerDetect_of_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] {A : Matrix ι ι ℤ}
    {M : Matrix κ κ ℤ} (e : ι ≃ κ) (he : ∀ i j, A i j = M (e i) (e j)) {k₀ : κ}
    (h : KerDetect M p k₀) : KerDetect A p (e.symm k₀) := by
  intro x hx h0 i
  have hx' : ∀ j, ∑ k, (x ∘ e.symm) k * (M k j : ZMod p) = 0 := by
    intro j
    rw [← hx (e.symm j)]
    exact (Fintype.sum_equiv e (fun i => x i * (A i (e.symm j) : ZMod p))
      (fun k => (x ∘ e.symm) k * (M k j : ZMod p)) (fun i => by simp [he])).symm
  have h1 := h (x ∘ e.symm) hx' (by simpa using h0) (e i)
  simpa using h1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem exists_kerDetect_simpleRoots
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) (hne : Ψ.Nonempty)
    (hp2 : 2 < p) :
    ∃ β₀ : simpleRoots Ψ, KerDetect (Matrix.of fun β γ : simpleRoots Ψ =>
      corootPair (β : Fin τ.rank → ℤ) γ) p β₀ := by
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ :=
    (CFSG.HardMathSupport.Timmesfeld.Proving.isFiniteType_simpleRoots_corootPair
      hΨ).existsUnique_dynkinType
        (CFSG.HardMathSupport.Timmesfeld.Proving.diagramGraph_simpleRoots_connected hΨ hne)
  obtain ⟨i₀, hi₀⟩ := exists_kerDetect hp2 ht
  exact ⟨e.symm i₀, kerDetect_of_equiv e he hi₀⟩

theorem dvd_of_kerDetect {ι : Type*} [Fintype ι] {M : Matrix ι ι ℤ} {i₀ : ι}
    (h : KerDetect M p i₀) (a : ℕ) : ∀ n : ι → ℤ, (∀ j, (p : ℤ) ^ a ∣ ∑ i, n i * M i j) →
      (p : ℤ) ^ a ∣ n i₀ → ∀ i, (p : ℤ) ^ a ∣ n i := by
  induction a with
  | zero => intro n _ _ i; simp
  | succ a ih =>
    intro n hn h0
    have hpa : (p : ℤ) ∣ (p : ℤ) ^ (a + 1) := dvd_pow_self _ (Nat.succ_ne_zero a)
    have hp : ∀ i, (p : ℤ) ∣ n i := by
      have hx := h (fun i => (n i : ZMod p)) (fun j => by
        have hc : ∑ i, (n i : ZMod p) * (M i j : ZMod p) = ((∑ i, n i * M i j : ℤ) : ZMod p) := by
          push_cast
          rfl
        rw [hc, ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact hpa.trans (hn j)) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 (hpa.trans h0))
      exact fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (hx i)
    choose m hm using hp
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hn' : ∀ j, (p : ℤ) ^ a ∣ ∑ i, m i * M i j := by
      intro j
      have h1 := hn j
      have he : ∑ i, n i * M i j = (p : ℤ) * ∑ i, m i * M i j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hm i, mul_assoc]
      rw [he, pow_succ'] at h1
      exact (mul_dvd_mul_iff_left hp0).1 h1
    have h0' : (p : ℤ) ^ a ∣ m i₀ := by
      have h1 := h0
      rw [hm i₀, pow_succ'] at h1
      exact (mul_dvd_mul_iff_left hp0).1 h1
    intro i
    rw [hm i, pow_succ']
    exact mul_dvd_mul_left _ (ih m hn' h0' i)

end Dynkin

end LayerCycRoot

end CFSG.StandardType

end
