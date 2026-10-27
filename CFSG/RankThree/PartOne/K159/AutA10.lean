module

public import CFSG.RankThree.PartOne.K159.AutCore

public section

namespace CFSG.RankThree.PartOne.K159

@[expose] def mkP (f g : Fin 10 → Fin 10) (h : ∀ i, g (f i) = i ∧ f (g i) = i := by decide) :
    Equiv.Perm (Fin 10) := ⟨f, g, fun i => (h i).1, fun i => (h i).2⟩

@[expose] def aP : Equiv.Perm (Fin 10) :=
  mkP ![1, 2, 3, 4, 0, 5, 6, 7, 8, 9] ![4, 0, 1, 2, 3, 5, 6, 7, 8, 9]

@[expose] def bP : Equiv.Perm (Fin 10) :=
  mkP ![0, 1, 2, 3, 4, 6, 7, 8, 9, 5] ![0, 1, 2, 3, 4, 9, 5, 6, 7, 8]

@[expose] def sP : Equiv.Perm (Fin 10) :=
  mkP ![0, 2, 4, 1, 3, 5, 6, 7, 8, 9] ![0, 3, 1, 4, 2, 5, 6, 7, 8, 9]

@[expose] def tP : Equiv.Perm (Fin 10) :=
  mkP ![5, 6, 7, 8, 9, 0, 1, 2, 3, 4] ![5, 6, 7, 8, 9, 0, 1, 2, 3, 4]

@[expose] def gP : Equiv.Perm (Fin 10) := tP * sP

theorem aP_comm_bP : aP * bP = bP * aP := by decide
theorem aP_pow : aP ^ 5 = 1 := by decide
theorem bP_pow : bP ^ 5 = 1 := by decide
theorem sign_aP : Equiv.Perm.sign aP = 1 := by decide
theorem sign_bP : Equiv.Perm.sign bP = 1 := by decide
theorem sign_gP : Equiv.Perm.sign gP = 1 := by decide +kernel
theorem gP_aP : gP * aP * gP⁻¹ = bP ^ 2 := by decide
theorem gP_bP : gP * bP * gP⁻¹ = aP := by decide

@[expose] def pairP (i j : ℕ) : Equiv.Perm (Fin 10) := aP ^ i * bP ^ j

theorem pairP_mul (i j k l : ℕ) : pairP i j * pairP k l = pairP (i + k) (j + l) := by
  have hc : Commute (bP ^ j) (aP ^ k) :=
    Commute.pow_pow (show Commute bP aP from (aP_comm_bP).symm) j k
  unfold pairP
  calc aP ^ i * bP ^ j * (aP ^ k * bP ^ l) = aP ^ i * (bP ^ j * aP ^ k) * bP ^ l := by
        simp only [mul_assoc]
    _ = aP ^ i * (aP ^ k * bP ^ j) * bP ^ l := by rw [hc.eq]
    _ = aP ^ (i + k) * bP ^ (j + l) := by rw [pow_add, pow_add]; simp only [mul_assoc]

theorem pairP_five (i j : ℕ) : pairP (5 * i) (5 * j) = 1 := by
  unfold pairP
  rw [pow_mul, pow_mul, aP_pow, bP_pow]
  simp

theorem pairP_zero : pairP 0 0 = 1 := by simp [pairP]

@[expose] def uP : Subgroup (Equiv.Perm (Fin 10)) where
  carrier := {x | ∃ i j : ℕ, x = pairP i j}
  mul_mem' := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    exact ⟨i + k, j + l, (pairP_mul i j k l)⟩
  one_mem' := ⟨0, 0, pairP_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨i, j, rfl⟩
    refine ⟨4 * i, 4 * j, ?_⟩
    have h : pairP (4 * i) (4 * j) * pairP i j = 1 := by
      rw [pairP_mul, show 4 * i + i = 5 * i by ring, show 4 * j + j = 5 * j by ring, pairP_five]
    exact (eq_inv_of_mul_eq_one_left h).symm

theorem uP_exp : ∀ u ∈ uP, u ^ 5 = 1 := by
  rintro _ ⟨i, j, rfl⟩
  have : ∀ n : ℕ, pairP i j ^ n = pairP (n * i) (n * j) := by
    intro n
    induction n with
    | zero => simp [pairP_zero]
    | succ n ih => rw [pow_succ, ih, pairP_mul]; congr 1 <;> ring
  rw [this, show 5 * i = 5 * i from rfl]
  exact pairP_five i j

theorem pairP_zero_five (i j : Fin 5) :
    (pairP i j) 0 = ⟨i, by omega⟩ ∧ (pairP i j) 5 = ⟨5 + j, by omega⟩ := by
  revert i j
  decide

theorem card_uP : 25 ≤ Nat.card uP := by
  have hinj : Function.Injective (fun x : Fin 5 × Fin 5 => (⟨pairP x.1 x.2, x.1, x.2, rfl⟩ : uP)) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h1 := congrArg (fun z : uP => (z : Equiv.Perm (Fin 10)) 0) h
    have h2 := congrArg (fun z : uP => (z : Equiv.Perm (Fin 10)) 5) h
    simp only [(pairP_zero_five i j).1, (pairP_zero_five i' j').1, (pairP_zero_five i j).2,
      (pairP_zero_five i' j').2, Fin.mk.injEq] at h1 h2
    have e1 : (i : ℕ) = i' := h1
    have e2 : (j : ℕ) = j' := by omega
    simp [Fin.ext e1, Fin.ext e2]
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

theorem uP_normalized : ∀ u ∈ uP, gP * u * gP⁻¹ ∈ uP := by
  rintro _ ⟨i, j, rfl⟩
  refine ⟨j, 2 * i, ?_⟩
  have h1 : gP * aP ^ i * gP⁻¹ = (bP ^ 2) ^ i := by rw [← gP_aP, conj_pow]
  have h2 : gP * bP ^ j * gP⁻¹ = aP ^ j := by rw [← gP_bP, conj_pow]
  unfold pairP
  calc gP * (aP ^ i * bP ^ j) * gP⁻¹ = (gP * aP ^ i * gP⁻¹) * (gP * bP ^ j * gP⁻¹) := by group
    _ = (bP ^ 2) ^ i * aP ^ j := by rw [h1, h2]
    _ = aP ^ j * bP ^ (2 * i) := by
        rw [← pow_mul, mul_comm 2 i]
        exact (Commute.pow_pow (show Commute bP aP from (aP_comm_bP).symm) (i * 2) j).eq

theorem gP_moves : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → gP ^ k * aP * (gP ^ k)⁻¹ ≠ aP := by
  intro k hk1 hk4
  interval_cases k <;> decide

theorem uP_le_alternating : uP ≤ alternatingGroup (Fin 10) := by
  rintro _ ⟨i, j, rfl⟩
  rw [Equiv.Perm.mem_alternatingGroup]
  unfold pairP
  rw [map_mul, map_pow, map_pow, sign_aP, sign_bP]
  simp

theorem gP_mem_alternating : gP ∈ alternatingGroup (Fin 10) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  exact sign_gP

theorem autWitness_alternating_ten : AutWitness 5 (alternatingGroup (Fin 10)) := by
  have hUA := uP_le_alternating
  refine ⟨uP.subgroupOf (alternatingGroup (Fin 10)), ?_, ?_, ⟨gP, gP_mem_alternating⟩, ?_, ?_⟩
  · rintro ⟨u, hu⟩ hu'
    apply Subtype.ext
    simpa using uP_exp u (Subgroup.mem_subgroupOf.1 hu')
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUA).toEquiv]
    norm_num
    exact card_uP
  · rintro ⟨u, hu⟩ hu'
    exact Subgroup.mem_subgroupOf.2 (by simpa using uP_normalized u (Subgroup.mem_subgroupOf.1 hu'))
  · intro k hk1 hk4
    refine ⟨⟨aP, ?_⟩, ?_, ?_⟩
    · exact (uP_le_alternating ⟨1, 0, by simp [pairP]⟩)
    · exact Subgroup.mem_subgroupOf.2 ⟨1, 0, by simp [pairP]⟩
    · intro h
      apply gP_moves k hk1 hk4
      simpa using congrArg Subtype.val h

end CFSG.RankThree.PartOne.K159
