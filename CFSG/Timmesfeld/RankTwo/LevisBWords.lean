module

public import CFSG.Timmesfeld.RankTwo.ModelG2Words

public section

namespace CFSG.Timmesfeld.RankTwo

open CFSG.Timmesfeld.GradedPresentation
open scoped commutatorElement

variable {K : Type*} [CommRing K]

@[expose] def b2Ht : Fin 4 → ℕ := ![1, 2, 3, 1]

@[expose] def b2WordLt : Fin 4 → K → Fin 4 → K → FreeGroup (Σ _ : Fin 4, K)
  | 0, s, 3, t => .of ⟨1, s * t⟩ * .of ⟨2, s ^ 2 * t⟩
  | _, _, _, _ => 1

@[expose] def b2Cm : Fin 4 → K → Fin 4 → K → FreeGroup (Σ _ : Fin 4, K) :=
  hexCm (F := fun _ => K) b2WordLt

theorem rels_b2Cm_of {H : Type*} [Group H] {φ : (Σ _ : Fin 4, K) → H}
    (hadd : ∀ i (c d : K), φ ⟨i, c + d⟩ = φ ⟨i, c⟩ * φ ⟨i, d⟩)
    (h03 : ∀ s t, ⁅φ ⟨0, s⟩, φ ⟨3, t⟩⁆ = φ ⟨1, s * t⟩ * φ ⟨2, s ^ 2 * t⟩)
    (h01 : ∀ s t, Commute (φ ⟨0, s⟩) (φ ⟨1, t⟩)) (h02 : ∀ s t, Commute (φ ⟨0, s⟩) (φ ⟨2, t⟩))
    (h12 : ∀ s t, Commute (φ ⟨1, s⟩) (φ ⟨2, t⟩)) (h13 : ∀ s t, Commute (φ ⟨1, s⟩) (φ ⟨3, t⟩))
    (h23 : ∀ s t, Commute (φ ⟨2, s⟩) (φ ⟨3, t⟩)) :
    ∀ r ∈ rels (b2Cm (K := K)), FreeGroup.lift φ r = 1 := by
  refine rels_hexCm_of hadd fun i j hij s t => ?_
  have hc : ∀ {a b : H}, Commute a b → ⁅a, b⁆ = FreeGroup.lift φ 1 := fun h => by
    rw [map_one, commutatorElement_eq_one_iff_commute]
    exact h
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, Fin.isValue] at hij ⊢ <;>
    first
    | exact absurd hij (by decide)
    | exact hc (h01 s t) | exact hc (h02 s t) | exact hc (h12 s t) | exact hc (h13 s t)
    | exact hc (h23 s t)
    | (rw [h03]; simp [b2WordLt])

theorem b2Cm_mem_above (i : Fin 4) (s : K) (j : Fin 4) (t : K) :
    b2Cm i s j t ∈ above (F := fun _ => K) b2Ht (max (b2Ht i) (b2Ht j)) := by
  refine hexCm_mem_above (F := fun _ => K) (fun i j hij s t => ?_) i s j t
  have hg : ∀ (k : Fin 4) (c : K) (m : ℕ), m < b2Ht k →
      (FreeGroup.of ⟨k, c⟩ : FreeGroup (Σ _ : Fin 4, K)) ∈ above (F := fun _ => K) b2Ht m :=
    fun k c m hm => Subgroup.subset_closure ⟨⟨k, c⟩, hm, rfl⟩
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, Fin.isValue] at hij ⊢ <;>
    first
    | exact absurd hij (by decide)
    | exact one_mem _
    | exact mul_mem (hg _ _ _ (by decide)) (hg _ _ _ (by decide))

@[expose] def a2Ht : Fin 3 → ℕ := ![1, 2, 1]

@[expose] def a2WordLt : Fin 3 → K → Fin 3 → K → FreeGroup (Σ _ : Fin 3, K)
  | 0, s, 2, t => .of ⟨1, s * t⟩
  | _, _, _, _ => 1

@[expose] def a2Cm : Fin 3 → K → Fin 3 → K → FreeGroup (Σ _ : Fin 3, K) :=
  hexCm (F := fun _ => K) a2WordLt

theorem rels_a2Cm_of {H : Type*} [Group H] {φ : (Σ _ : Fin 3, K) → H}
    (hadd : ∀ i (c d : K), φ ⟨i, c + d⟩ = φ ⟨i, c⟩ * φ ⟨i, d⟩)
    (h02 : ∀ s t, ⁅φ ⟨0, s⟩, φ ⟨2, t⟩⁆ = φ ⟨1, s * t⟩)
    (h01 : ∀ s t, Commute (φ ⟨0, s⟩) (φ ⟨1, t⟩)) (h12 : ∀ s t, Commute (φ ⟨1, s⟩) (φ ⟨2, t⟩)) :
    ∀ r ∈ rels (a2Cm (K := K)), FreeGroup.lift φ r = 1 := by
  refine rels_hexCm_of hadd fun i j hij s t => ?_
  have hc : ∀ {a b : H}, Commute a b → ⁅a, b⁆ = FreeGroup.lift φ 1 := fun h => by
    rw [map_one, commutatorElement_eq_one_iff_commute]
    exact h
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, Fin.isValue] at hij ⊢ <;>
    first
    | exact absurd hij (by decide)
    | exact hc (h01 s t) | exact hc (h12 s t)
    | (rw [h02]; simp [a2WordLt])

theorem a2Cm_mem_above (i : Fin 3) (s : K) (j : Fin 3) (t : K) :
    a2Cm i s j t ∈ above (F := fun _ => K) a2Ht (max (a2Ht i) (a2Ht j)) := by
  refine hexCm_mem_above (F := fun _ => K) (fun i j hij s t => ?_) i s j t
  have hg : ∀ (k : Fin 3) (c : K) (m : ℕ), m < a2Ht k →
      (FreeGroup.of ⟨k, c⟩ : FreeGroup (Σ _ : Fin 3, K)) ∈ above (F := fun _ => K) a2Ht m :=
    fun k c m hm => Subgroup.subset_closure ⟨⟨k, c⟩, hm, rfl⟩
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, Fin.isValue] at hij ⊢ <;>
    first
    | exact absurd hij (by decide)
    | exact one_mem _
    | exact hg _ _ _ (by decide)

@[expose] def a1a1Ht : Fin 2 → ℕ := ![1, 1]

@[expose] def a1a1Cm : Fin 2 → K → Fin 2 → K → FreeGroup (Σ _ : Fin 2, K) :=
  fun _ _ _ _ => 1

theorem rels_a1a1Cm_of {H : Type*} [Group H] {φ : (Σ _ : Fin 2, K) → H}
    (hadd : ∀ i (c d : K), φ ⟨i, c + d⟩ = φ ⟨i, c⟩ * φ ⟨i, d⟩)
    (h01 : ∀ s t, Commute (φ ⟨0, s⟩) (φ ⟨1, t⟩)) :
    ∀ r ∈ rels (a1a1Cm (K := K)), FreeGroup.lift φ r = 1 := by
  rintro r (⟨γ, c, d, rfl⟩ | ⟨i, s, j, t, rfl⟩)
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, hadd, mul_inv_cancel]
  · rw [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
      FreeGroup.lift_apply_of, mul_inv_eq_one, a1a1Cm, map_one,
      commutatorElement_eq_one_iff_commute]
    fin_cases i <;> fin_cases j
    · rw [Commute, SemiconjBy, ← hadd, ← hadd, add_comm s t]
    · exact h01 s t
    · exact (h01 t s).symm
    · rw [Commute, SemiconjBy, ← hadd, ← hadd, add_comm s t]

omit [CommRing K] in
theorem a1a1Cm_mem_above (i : Fin 2) (s : K) (j : Fin 2) (t : K) :
    a1a1Cm i s j t ∈ above (F := fun _ => K) a1a1Ht (max (a1a1Ht i) (a1a1Ht j)) :=
  one_mem _

section Twisted

variable (K) in
@[expose] def tb2Par : Fin 4 → Type _
  | 0 => Fin 2 → K
  | 1 => Fin 2 → K
  | 2 => K
  | 3 => K

instance instAddCommGroupTb2Par : ∀ i, AddCommGroup (tb2Par K i)
  | 0 => inferInstanceAs (AddCommGroup (Fin 2 → K))
  | 1 => inferInstanceAs (AddCommGroup (Fin 2 → K))
  | 2 => inferInstanceAs (AddCommGroup K)
  | 3 => inferInstanceAs (AddCommGroup K)

variable (N : (Fin 2 → K) → K) (B : (Fin 2 → K) → (Fin 2 → K) → K)

@[expose] def tb2W01 (p q : Fin 2 → K) : FreeGroup (Σ γ, tb2Par K γ) := .of ⟨2, B p q⟩

@[expose] def tb2W03 (p : Fin 2 → K) (s : K) : FreeGroup (Σ γ, tb2Par K γ) :=
  .of ⟨1, s • p⟩ * .of ⟨2, s * N p⟩

@[expose] def tb2WordLt :
    ∀ (i : Fin 4) (_ : tb2Par K i) (j : Fin 4) (_ : tb2Par K j), FreeGroup (Σ γ, tb2Par K γ)
  | 0, p, 1, q => tb2W01 B p q
  | 0, p, 3, s => tb2W03 N p s
  | _, _, _, _ => 1

@[expose] def tb2Cm :
    ∀ (i : Fin 4) (_ : tb2Par K i) (j : Fin 4) (_ : tb2Par K j), FreeGroup (Σ γ, tb2Par K γ) :=
  hexCm (tb2WordLt N B)

theorem tb2_add_of {H : Type*} [Group H] {φ : (Σ γ, tb2Par K γ) → H}
    (h0 : ∀ c d : Fin 2 → K, φ ⟨0, c + d⟩ = φ ⟨0, c⟩ * φ ⟨0, d⟩)
    (h1 : ∀ c d : Fin 2 → K, φ ⟨1, c + d⟩ = φ ⟨1, c⟩ * φ ⟨1, d⟩)
    (h2 : ∀ c d : K, φ ⟨2, c + d⟩ = φ ⟨2, c⟩ * φ ⟨2, d⟩)
    (h3 : ∀ c d : K, φ ⟨3, c + d⟩ = φ ⟨3, c⟩ * φ ⟨3, d⟩) :
    ∀ i (c d : tb2Par K i), φ ⟨i, c + d⟩ = φ ⟨i, c⟩ * φ ⟨i, d⟩ := by
  intro i c d
  fin_cases i
  exacts [h0 c d, h1 c d, h2 c d, h3 c d]

theorem rels_tb2Cm_of {H : Type*} [Group H] {φ : (Σ γ, tb2Par K γ) → H}
    (hadd : ∀ i (c d : tb2Par K i), φ ⟨i, c + d⟩ = φ ⟨i, c⟩ * φ ⟨i, d⟩)
    (h01 : ∀ p q : Fin 2 → K, ⁅φ ⟨0, p⟩, φ ⟨1, q⟩⁆ = φ ⟨2, B p q⟩)
    (h03 : ∀ (p : Fin 2 → K) (s : K), ⁅φ ⟨0, p⟩, φ ⟨3, s⟩⁆ = φ ⟨1, s • p⟩ * φ ⟨2, s * N p⟩)
    (h02 : ∀ (p : Fin 2 → K) (s : K), Commute (φ ⟨0, p⟩) (φ ⟨2, s⟩))
    (h12 : ∀ (p : Fin 2 → K) (s : K), Commute (φ ⟨1, p⟩) (φ ⟨2, s⟩))
    (h13 : ∀ (p : Fin 2 → K) (s : K), Commute (φ ⟨1, p⟩) (φ ⟨3, s⟩))
    (h23 : ∀ s t : K, Commute (φ ⟨2, s⟩) (φ ⟨3, t⟩)) :
    ∀ r ∈ rels (tb2Cm N B), FreeGroup.lift φ r = 1 := by
  refine rels_hexCm_of hadd fun i j hij s t => ?_
  have hc : ∀ {a b : H}, Commute a b → ⁅a, b⁆ = FreeGroup.lift φ 1 := fun h => by
    rw [map_one, commutatorElement_eq_one_iff_commute]
    exact h
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, Fin.isValue] at hij ⊢ <;>
    first
    | exact absurd hij (by decide)
    | exact hc (h02 s t) | exact hc (h12 s t) | exact hc (h13 s t) | exact hc (h23 s t)
    | exact (h01 s t).trans (by simp [tb2WordLt, tb2W01])
    | exact (h03 s t).trans (by simp [tb2WordLt, tb2W03])

theorem tb2Cm_mem_above (i : Fin 4) (s : tb2Par K i) (j : Fin 4) (t : tb2Par K j) :
    tb2Cm N B i s j t ∈ above b2Ht (max (b2Ht i) (b2Ht j)) := by
  refine hexCm_mem_above (fun i j hij s t => ?_) i s j t
  have hg : ∀ (k : Fin 4) (c : tb2Par K k) (m : ℕ), m < b2Ht k →
      (FreeGroup.of ⟨k, c⟩ : FreeGroup (Σ γ, tb2Par K γ)) ∈ above b2Ht m :=
    fun k c m hm => Subgroup.subset_closure ⟨⟨k, c⟩, hm, rfl⟩
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, Fin.isValue] at hij ⊢ <;>
    first
    | exact absurd hij (by decide)
    | exact one_mem _
    | exact hg _ _ _ (by decide)
    | exact mul_mem (hg _ _ _ (by decide)) (hg _ _ _ (by decide))

variable (K) in
@[expose] def ma1Par : Fin 2 → Type _
  | 0 => K
  | 1 => Fin 2 → K

instance instAddCommGroupMa1Par : ∀ i, AddCommGroup (ma1Par K i)
  | 0 => inferInstanceAs (AddCommGroup K)
  | 1 => inferInstanceAs (AddCommGroup (Fin 2 → K))

variable (K) in
@[expose] def ma1Cm : ∀ (i : Fin 2) (_ : ma1Par K i) (j : Fin 2) (_ : ma1Par K j),
    FreeGroup (Σ γ, ma1Par K γ) :=
  fun _ _ _ _ => 1

theorem rels_ma1Cm_of {H : Type*} [Group H] {φ : (Σ γ, ma1Par K γ) → H}
    (h0 : ∀ c d : K, φ ⟨0, c + d⟩ = φ ⟨0, c⟩ * φ ⟨0, d⟩)
    (h1 : ∀ c d : Fin 2 → K, φ ⟨1, c + d⟩ = φ ⟨1, c⟩ * φ ⟨1, d⟩)
    (h01 : ∀ (s : K) (p : Fin 2 → K), Commute (φ ⟨0, s⟩) (φ ⟨1, p⟩)) :
    ∀ r ∈ rels (ma1Cm K), FreeGroup.lift φ r = 1 := by
  rintro r (⟨γ, c, d, rfl⟩ | ⟨i, s, j, t, rfl⟩)
  · fin_cases γ
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [mul_inv_eq_one]
      exact h0 c d
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [mul_inv_eq_one]
      exact h1 c d
  · rw [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
      FreeGroup.lift_apply_of, mul_inv_eq_one, ma1Cm, map_one,
      commutatorElement_eq_one_iff_commute]
    have hd0 : ∀ s t : K, Commute (φ ⟨0, s⟩) (φ ⟨0, t⟩) := fun s t => by
      rw [Commute, SemiconjBy, ← h0, ← h0, add_comm s t]
    have hd1 : ∀ s t : Fin 2 → K, Commute (φ ⟨1, s⟩) (φ ⟨1, t⟩) := fun s t => by
      rw [Commute, SemiconjBy, ← h1, ← h1, add_comm s t]
    fin_cases i <;> fin_cases j
    · exact hd0 s t
    · exact h01 s t
    · exact (h01 t s).symm
    · exact hd1 s t

omit [CommRing K] in
theorem ma1Cm_mem_above (i : Fin 2) (s : ma1Par K i) (j : Fin 2) (t : ma1Par K j) :
    ma1Cm K i s j t ∈ above a1a1Ht (max (a1a1Ht i) (a1a1Ht j)) :=
  one_mem _

end Twisted

end CFSG.Timmesfeld.RankTwo
