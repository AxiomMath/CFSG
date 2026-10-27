module

public import CFSG.Quasithin.H13.VolIAltCover

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin CFSG.Quasithin.G6 Subgroup Equiv

@[expose] def a6c012 : ↥(alternatingGroup (Fin 6)) :=
  ⟨swap 0 1 * swap 1 2, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def a6c234 : ↥(alternatingGroup (Fin 6)) :=
  ⟨swap 2 3 * swap 3 4, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def a6c123 : ↥(alternatingGroup (Fin 6)) :=
  ⟨swap 1 2 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def a6s : ↥(alternatingGroup (Fin 6)) :=
  ⟨swap 0 5 * swap 1 2, by rw [Perm.mem_alternatingGroup]; decide⟩

theorem a6c012_pow : a6c012 ^ 3 = 1 := by decide

theorem a6c234_pow : a6c234 ^ 3 = 1 := by decide

theorem a6s_mul_self : a6s * a6s = 1 := by decide

theorem a6c123_five : (a6c123 : Perm (Fin 6)) 5 = 5 := by decide

theorem a6c234_five : (a6c234 : Perm (Fin 6)) 5 = 5 := by decide

theorem a6s_c123_five :
    ((a6s * a6c123 * a6s : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) 5 = 5 := by
  decide

theorem a6s_c234_five :
    ((a6s * a6c234 * a6s : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) 5 = 5 := by
  decide

theorem a6s_inv_five : (a6s : Perm (Fin 6))⁻¹ 5 = 0 := by decide

theorem alt6_words : ∀ σ : ↥(alternatingGroup (Fin 6)), (σ : Perm (Fin 6)) 5 = 5 →
    IsWord6 a6c012 a6c234 σ := by
  unfold IsWord6
  decide +kernel

@[expose] def a6reps : List ↥(alternatingGroup (Fin 6)) :=
  [1, a6c012, a6c012 * a6c012, a6c234 * a6c012 * a6c012, a6c234 * a6c234 * a6c012 * a6c012]

theorem alt6_cosets : ∀ σ : ↥(alternatingGroup (Fin 6)), (σ : Perm (Fin 6)) 5 = 5 ∨
    ∃ h ∈ a6reps, (h : Perm (Fin 6)) 5 = 5 ∧
      (((h * a6s)⁻¹ * σ : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) 5 = 5 := by
  decide +kernel

@[expose] def ev2 (i j : Fin 6) : PermMod 6 :=
  Multiplicative.ofAdd fun k => if k = i ∨ k = j then 1 else 0

@[expose] def comm2 (σ τ : ↥(alternatingGroup (Fin 6))) (a b : PermMod 6) : PermMod 6 :=
  permAct 6 (σ : Perm (Fin 6)) a * a⁻¹ * (permAct 6 (τ : Perm (Fin 6)) b * b⁻¹)

theorem comm2_mem (σ τ : ↥(alternatingGroup (Fin 6))) {a b : PermMod 6} (ha : a ∈ coreMod 6)
    (hb : b ∈ coreMod 6) : comm2 σ τ a b ∈ coreMod 6 :=
  mul_mem (mul_mem (permAct_mem_coreMod _ ha) (inv_mem ha))
    (mul_mem (permAct_mem_coreMod _ hb) (inv_mem hb))

@[expose] def lifts012 : List (PermMod 6) := [1, ev2 0 5, ev2 1 5, ev2 2 5]

@[expose] def lifts123 : List (PermMod 6) := [1, ev2 1 5, ev2 2 5, ev2 3 5]

@[expose] def lifts234 : List (PermMod 6) := [1, ev2 2 5, ev2 3 5, ev2 4 5]

theorem lifts012_mem : ∀ a ∈ lifts012, a ∈ coreMod 6 := by
  simp only [mem_coreMod]
  decide

theorem lifts123_mem : ∀ a ∈ lifts123, a ∈ coreMod 6 := by
  simp only [mem_coreMod]
  decide

theorem lifts234_mem : ∀ a ∈ lifts234, a ∈ coreMod 6 := by
  simp only [mem_coreMod]
  decide

theorem evenOn_six_012_card : (evenOn (0 : Fin 6) 1 2).card = 4 := by decide

theorem evenOn_six_234_card : (evenOn (2 : Fin 6) 3 4).card = 4 := by decide

theorem comm_mem_evenOn_six_012 : ∀ m : PermMod 6,
    permAct 6 (a6c012 : Perm (Fin 6)) m * m⁻¹ ∈ evenOn 0 1 2 := by
  decide

theorem comm_mem_evenOn_six_234 : ∀ m : PermMod 6,
    permAct 6 (a6c234 : Perm (Fin 6)) m * m⁻¹ ∈ evenOn 2 3 4 := by
  decide

theorem coreMod_six_eq : ∀ m : PermMod 6, m ∈ coreMod 6 →
    ∃ a ∈ lifts012, ∃ b ∈ lifts234,
      m = comm2 a6c012 a6c234 a b ∨ m = comm2 a6c012 a6c234 a b * allOnes 6 := by
  simp only [mem_coreMod]
  decide

@[expose] def evenP : Finset (PermMod 6) := Finset.univ.filter fun x =>
  Multiplicative.toAdd x 0 = 0 ∧ Multiplicative.toAdd x 5 = 0 ∧ ∑ i, Multiplicative.toAdd x i = 0

theorem evenP_card : evenP.card = 8 := by decide

theorem mem_coreMod_of_mem_evenP {x : PermMod 6} (hx : x ∈ evenP) : x ∈ coreMod 6 :=
  (Finset.mem_filter.1 hx).2.2.2

theorem evenP_eq : ∀ x ∈ evenP, ∃ a ∈ lifts123, ∃ b ∈ lifts234,
    x = comm2 a6c123 a6c234 a b := by
  decide

theorem evenP_allOnes : ∀ x ∈ evenP, ∀ y ∈ evenP, x * allOnes 6 ≠ y := by decide

theorem coreMod_six_decomp : ∀ x : PermMod 6, x ∈ coreMod 6 → ∃ p ∈ evenP,
    x = p ∨ x = p * allOnes 6 ∨ x = p * ev2 0 1 ∨ x = p * allOnes 6 * ev2 0 1 := by
  simp only [mem_coreMod]
  decide

theorem coreMod_six_five : ∀ m : PermMod 6, m ∈ coreMod 6 →
    Multiplicative.toAdd m 5 = 0 → (Multiplicative.toAdd m 0 = 0 ∧ m ∈ evenP) ∨
      (Multiplicative.toAdd m 0 = 1 ∧ m * ev2 0 1 ∈ evenP) := by
  simp only [mem_coreMod]
  decide

theorem allOnes_six_mem : allOnes 6 ∈ coreMod 6 := by
  rw [mem_coreMod]
  decide

theorem ev2_01_mem : ev2 0 1 ∈ coreMod 6 := by
  rw [mem_coreMod]
  decide

theorem ev2_01_mul_self : ev2 0 1 * ev2 0 1 = 1 := by decide

theorem ev2_01_five : Multiplicative.toAdd (ev2 0 1) 5 = 0 := by decide

theorem allOnes_six_five : Multiplicative.toAdd (allOnes 6) 5 = 1 := rfl

theorem zmod_two_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem orderOf_allOnes_six : orderOf (allOnes 6) = 2 := orderOf_eq_prime (by decide) (by decide)

theorem card_coreMod_six : Nat.card (coreMod 6) = 32 := by
  have h : (coreMod 6 : Set (PermMod 6)) =
      ↑(Finset.univ.filter fun x : PermMod 6 => ∑ i, Multiplicative.toAdd x i = 0) := by
    ext x
    simp [mem_coreMod]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, h, Set.ncard_coe_finset]
  decide

theorem mk_eq_mk_iff_six {m m' : ↥(coreMod 6)} :
    (QuotientGroup.mk m : DnQuot 6) = QuotientGroup.mk m' ↔
      (m' : PermMod 6) = m ∨ (m' : PermMod 6) = m * allOnes 6 := by
  rw [QuotientGroup.eq, mem_subgroupOf, coe_mul, coe_inv, mem_inf]
  constructor
  · rintro ⟨h, -⟩
    rw [mem_zpowers_iff_mem_range_orderOf, orderOf_allOnes_six] at h
    simp only [Finset.mem_image, Finset.mem_range] at h
    obtain ⟨k, hk, hk'⟩ := h
    interval_cases k
    · left
      rw [pow_zero, eq_comm, inv_mul_eq_one] at hk'
      exact hk'.symm
    · right
      rw [pow_one, eq_comm, inv_mul_eq_iff_eq_mul] at hk'
      exact hk'
  · rintro (h | h)
    · rw [h, inv_mul_cancel]
      exact ⟨one_mem _, one_mem _⟩
    · rw [h, inv_mul_cancel_left]
      exact ⟨mem_zpowers _, allOnes_six_mem⟩

theorem mk_allOnes_six :
    (QuotientGroup.mk (⟨allOnes 6, allOnes_six_mem⟩ : ↥(coreMod 6)) : DnQuot 6) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 ⟨mem_zpowers _, allOnes_six_mem⟩)

theorem card_dnQuot_six : Nat.card (DnQuot 6) = 16 := by
  have hle : zpowers (allOnes 6) ≤ coreMod 6 := zpowers_le.2 allOnes_six_mem
  have hN : Nat.card ((zpowers (allOnes 6) ⊓ coreMod 6).subgroupOf (coreMod 6)) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv, inf_eq_left.2 hle,
      Nat.card_zpowers, orderOf_allOnes_six]
  have h := card_eq_card_quotient_mul_card_subgroup
    ((zpowers (allOnes 6) ⊓ coreMod 6).subgroupOf (coreMod 6))
  rw [card_coreMod_six, hN] at h
  show Nat.card (↥(coreMod 6) ⧸ (zpowers (allOnes 6) ⊓ coreMod 6).subgroupOf (coreMod 6)) = 16
  omega

@[expose] def act6 : ↥(alternatingGroup (Fin 6)) →* MulAut ↥(coreMod 6) :=
  (coreAct 6).comp (alternatingGroup (Fin 6)).subtype

theorem act6_apply (σ : ↥(alternatingGroup (Fin 6))) (x : ↥(coreMod 6)) :
    act6 σ x = coreAct 6 (σ : Perm (Fin 6)) x := rfl

theorem coe_act6 (σ : ↥(alternatingGroup (Fin 6))) (x : ↥(coreMod 6)) :
    (act6 σ x : PermMod 6) = permAct 6 (σ : Perm (Fin 6)) x := rfl

theorem act6_allOnes (σ : ↥(alternatingGroup (Fin 6))) :
    act6 σ ⟨allOnes 6, allOnes_six_mem⟩ = ⟨allOnes 6, allOnes_six_mem⟩ := rfl

theorem act6_five {σ : ↥(alternatingGroup (Fin 6))} (hσ : (σ : Perm (Fin 6)) 5 = 5)
    (x : ↥(coreMod 6)) :
    Multiplicative.toAdd (act6 σ x : PermMod 6) 5 = Multiplicative.toAdd (x : PermMod 6) 5 := by
  rw [coe_act6, permAct_apply, Perm.inv_eq_iff_eq.2 hσ.symm]

theorem act6_s_five (x : ↥(coreMod 6)) :
    Multiplicative.toAdd (act6 a6s x : PermMod 6) 5 = Multiplicative.toAdd (x : PermMod 6) 0 := by
  rw [coe_act6, permAct_apply, a6s_inv_five]

end CFSG.Quasithin.H13.VolI
