module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBSp
import all CFSG.LieType.Universal.SymplecticRoots

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CoxeterSystem CFSG.LieType.Universal.Symplectic

section Realize

variable (m : ℕ)

@[expose] def SpRealizes (w : (coxeterMatrix (isFiniteType_cartanC m)).Group)
    (π : Equiv.Perm (Fin m)) (s : Fin m → ℤ) : Prop :=
  ∀ γ, toStd m (weylAction (isFiniteType_cartanC m) w γ) =
    fun b => s (π.symm b) * toStd m γ (π.symm b)

@[expose] def SpIsSign {m : ℕ} (s : Fin m → ℤ) : Prop := ∀ a, s a = 1 ∨ s a = -1

@[expose] def spSgn {m : ℕ} (a : Fin m) : Fin m → ℤ := fun x => if x = a then -1 else 1

@[expose] def spSgnOn {m : ℕ} (S : Finset (Fin m)) : Fin m → ℤ := fun x => if x ∈ S then -1 else 1

variable {m}

theorem spIsSign_one : SpIsSign (1 : Fin m → ℤ) := fun _ => Or.inl rfl

theorem spIsSign_spSgn (a : Fin m) : SpIsSign (spSgn a) := fun x => by
  unfold spSgn
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem spIsSign_spSgnOn (S : Finset (Fin m)) : SpIsSign (spSgnOn S) := fun x => by
  unfold spSgnOn
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem SpIsSign.mul_self {s : Fin m → ℤ} (hs : SpIsSign s) (a : Fin m) : s a * s a = 1 := by
  rcases hs a with h | h <;> rw [h] <;> norm_num

theorem SpIsSign.mul {s t : Fin m → ℤ} (hs : SpIsSign s) (ht : SpIsSign t)
    (π : Equiv.Perm (Fin m)) :
    SpIsSign (fun c => s c * t (π c)) := fun c => by
  show s c * t (π c) = 1 ∨ s c * t (π c) = -1
  rcases hs c with h | h <;> rcases ht (π c) with h' | h' <;> rw [h, h'] <;> norm_num

theorem SpRealizes.congr {w : (coxeterMatrix (isFiniteType_cartanC m)).Group}
    {π π' : Equiv.Perm (Fin m)} {s s' : Fin m → ℤ} (h : SpRealizes m w π s) (hπ : π = π')
    (hs : s = s') : SpRealizes m w π' s' := hπ ▸ hs ▸ h

theorem spRealizes_one : SpRealizes m 1 1 1 := fun γ => by
  rw [map_one, Module.End.one_apply]
  funext b
  change toStd m γ b = 1 * toStd m γ b
  rw [one_mul]

theorem SpRealizes.mul {w₁ w₂ : (coxeterMatrix (isFiniteType_cartanC m)).Group}
    {π₁ π₂ : Equiv.Perm (Fin m)} {s₁ s₂ : Fin m → ℤ} (h₁ : SpRealizes m w₁ π₁ s₁)
    (h₂ : SpRealizes m w₂ π₂ s₂) :
    SpRealizes m (w₁ * w₂) (π₁ * π₂) (fun c => s₂ c * s₁ (π₂ c)) := fun γ => by
  rw [weylAction_mul_apply, h₁, h₂]
  funext b
  simp only [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  ring

theorem SpRealizes.mul_one {w₁ w₂ : (coxeterMatrix (isFiniteType_cartanC m)).Group}
    {π₁ π₂ : Equiv.Perm (Fin m)} (h₁ : SpRealizes m w₁ π₁ 1) (h₂ : SpRealizes m w₂ π₂ 1) :
    SpRealizes m (w₁ * w₂) (π₁ * π₂) 1 :=
  (h₁.mul h₂).congr rfl (by funext c; simp)

theorem SpRealizes.inv {w : (coxeterMatrix (isFiniteType_cartanC m)).Group}
    {π : Equiv.Perm (Fin m)} {s : Fin m → ℤ} (h : SpRealizes m w π s) (hs : SpIsSign s) :
    SpRealizes m w⁻¹ π⁻¹ (fun c => s (π.symm c)) := fun γ => by
  have key := h (weylAction (isFiniteType_cartanC m) w⁻¹ γ)
  rw [weylAction_apply_inv_apply] at key
  funext b
  have e := congrFun key (π b)
  simp only [Equiv.symm_apply_apply] at e
  simp only [Equiv.Perm.inv_def, Equiv.symm_symm, Equiv.symm_apply_apply]
  rw [e, ← mul_assoc, hs.mul_self, one_mul]

theorem SpRealizes.inv_one {w : (coxeterMatrix (isFiniteType_cartanC m)).Group}
    {π : Equiv.Perm (Fin m)} (h : SpRealizes m w π 1) : SpRealizes m w⁻¹ π⁻¹ 1 :=
  (h.inv spIsSign_one).congr rfl (by funext c; simp)

theorem spRealizes_simple_of_lt {k : Fin m} (h : k.val + 1 < m) :
    SpRealizes m ((coxeterMatrix (isFiniteType_cartanC m)).toCoxeterSystem.simple k)
      (Equiv.swap k ⟨k.val + 1, h⟩) 1 := fun γ => by
  rw [weylAction_simple, toStd_reflection, stdRefl_of_lt m h]
  funext b
  simp [Equiv.symm_swap]

theorem spRealizes_simple_of_not_lt {k : Fin m} (h : ¬ k.val + 1 < m) :
    SpRealizes m ((coxeterMatrix (isFiniteType_cartanC m)).toCoxeterSystem.simple k) 1
      (spSgn k) := fun γ => by
  rw [weylAction_simple, toStd_reflection, stdRefl_of_not_lt m h]
  funext b
  change (if b = k then -1 else 1) * toStd m γ b = spSgn k b * toStd m γ b
  rfl

theorem SpRealizes.inj {w w' : (coxeterMatrix (isFiniteType_cartanC m)).Group}
    {π : Equiv.Perm (Fin m)} {s : Fin m → ℤ} (h : SpRealizes m w π s)
    (h' : SpRealizes m w' π s) : w = w' :=
  weylAction_injective (isFiniteType_cartanC m)
    (LinearMap.ext fun γ => SpExtras.toStd_inj ((h γ).trans (h' γ).symm))

theorem exists_spRealizes (w : (coxeterMatrix (isFiniteType_cartanC m)).Group) :
    ∃ (π : Equiv.Perm (Fin m)) (s : Fin m → ℤ), SpIsSign s ∧ SpRealizes m w π s := by
  induction w using (coxeterMatrix (isFiniteType_cartanC m)).toCoxeterSystem.simple_induction_left
    with
  | one => exact ⟨1, 1, spIsSign_one, spRealizes_one⟩
  | mul_simple_left w k ih =>
    obtain ⟨π, s, hs, h⟩ := ih
    by_cases hk : k.val + 1 < m
    · exact ⟨_, _, hs.mul spIsSign_one π, (spRealizes_simple_of_lt hk).mul h⟩
    · exact ⟨_, _, hs.mul (spIsSign_spSgn k) π, (spRealizes_simple_of_not_lt hk).mul h⟩

theorem SpRealizes.fix {w : (coxeterMatrix (isFiniteType_cartanC m)).Group}
    {π : Equiv.Perm (Fin m)} {s : Fin m → ℤ} (h : SpRealizes m w π s) {γ : Fin m → ℤ}
    (hγ : ∀ b, s (π.symm b) * toStd m γ (π.symm b) = toStd m γ b) :
    weylAction (isFiniteType_cartanC m) w γ = γ :=
  SpExtras.toStd_inj (by rw [h γ]; funext b; exact hγ b)

end Realize

section Levi

variable (n : ℕ)

@[expose] def spLeviJ : Finset (Fin (n + 1)) := Finset.univ.filter fun j => 1 ≤ j.val

@[expose] def spLeviWeyl : Subgroup (coxeterMatrix (isFiniteType_cartanC (n + 1))).Group :=
  Subgroup.closure ((coxeterMatrix (isFiniteType_cartanC (n + 1))).toCoxeterSystem.simple ''
    (spLeviJ n : Set (Fin (n + 1))))

variable {n}

theorem mem_spLeviJ {j : Fin (n + 1)} : j ∈ spLeviJ n ↔ 1 ≤ j.val := by
  simp [spLeviJ]

theorem simple_mem_spLeviW {j : Fin (n + 1)} (hj : 1 ≤ j.val) :
    (coxeterMatrix (isFiniteType_cartanC (n + 1))).toCoxeterSystem.simple j ∈ spLeviWeyl n :=
  Subgroup.subset_closure ⟨j, mem_spLeviJ.mpr hj, rfl⟩

theorem exists_spLeviW_swap_adj (x y : Fin (n + 1)) (hxy : y.val = x.val + 1) (hx : 1 ≤ x.val) :
    ∃ v ∈ spLeviWeyl n, SpRealizes (n + 1) v (Equiv.swap x y) 1 := by
  have hlt : x.val + 1 < n + 1 := by have := y.isLt; omega
  have e : (⟨x.val + 1, hlt⟩ : Fin (n + 1)) = y := Fin.ext (by simp [hxy])
  exact ⟨_, simple_mem_spLeviW hx, e ▸ spRealizes_simple_of_lt hlt⟩

theorem exists_spLeviW_swap_of_lt : ∀ (d : ℕ) (x y : Fin (n + 1)), y.val = x.val + d + 1 →
    1 ≤ x.val → ∃ v ∈ spLeviWeyl n, SpRealizes (n + 1) v (Equiv.swap x y) 1 := by
  intro d
  induction d with
  | zero => exact fun x y hxy hx => exists_spLeviW_swap_adj x y (by omega) hx
  | succ d ih =>
    intro x y hxy hx
    let y' : Fin (n + 1) := ⟨x.val + d + 1, by omega⟩
    obtain ⟨w₁, hw₁, h₁⟩ := ih x y' rfl hx
    obtain ⟨w₂, hw₂, h₂⟩ := exists_spLeviW_swap_adj y' y (by simp only [y']; omega)
      (by simp only [y']; omega)
    have hx1 : x ≠ y' := fun h => by
      have := congrArg Fin.val h
      simp only [y'] at this
      omega
    have hx2 : x ≠ y := fun h => by
      have := congrArg Fin.val h
      omega
    have key : Equiv.swap x y = Equiv.swap y' y * Equiv.swap x y' * Equiv.swap y' y := by
      have := Equiv.swap_apply_apply (Equiv.swap y' y) x y'
      rw [Equiv.swap_apply_of_ne_of_ne hx1 hx2, Equiv.swap_apply_left, Equiv.swap_inv] at this
      exact this
    refine ⟨w₂ * w₁ * w₂, mul_mem (mul_mem hw₂ hw₁) hw₂, ?_⟩
    rw [key]
    exact (h₂.mul_one h₁).mul_one h₂

theorem exists_spLeviW_swap (x y : Fin (n + 1)) (hx : 1 ≤ x.val) (hy : 1 ≤ y.val) :
    ∃ v ∈ spLeviWeyl n, SpRealizes (n + 1) v (Equiv.swap x y) 1 := by
  rcases lt_trichotomy x.val y.val with h | h | h
  · exact exists_spLeviW_swap_of_lt (y.val - x.val - 1) x y (by omega) hx
  · obtain rfl : x = y := Fin.ext h
    exact ⟨1, one_mem _, spRealizes_one.congr (by rw [Equiv.swap_self, Equiv.Perm.one_def])
      rfl⟩
  · rw [Equiv.swap_comm]
    exact exists_spLeviW_swap_of_lt (x.val - y.val - 1) y x (by omega) hy

theorem exists_spLeviW_sgn_last (hn : 1 ≤ n) :
    ∃ v ∈ spLeviWeyl n, SpRealizes (n + 1) v 1 (spSgn (Fin.last n)) :=
  ⟨_, simple_mem_spLeviW (by simp; omega),
    spRealizes_simple_of_not_lt (k := Fin.last n) (by simp)⟩

theorem exists_spLeviW_sgn (hn : 1 ≤ n) (a : Fin (n + 1)) (ha : 1 ≤ a.val) :
    ∃ v ∈ spLeviWeyl n, SpRealizes (n + 1) v 1 (spSgn a) := by
  obtain ⟨z, hz, hzr⟩ := exists_spLeviW_sgn_last hn
  obtain ⟨v, hv, hvr⟩ := exists_spLeviW_swap a (Fin.last n) ha (by simp; omega)
  refine ⟨v * z * v, mul_mem (mul_mem hv hz) hv, ((hvr.mul hzr).mul hvr).congr ?_ ?_⟩
  · rw [mul_one, Equiv.swap_mul_self]
  · funext c
    simp [spSgn, Equiv.swap_apply_eq_iff]

theorem exists_spLeviW_sgnOn (hn : 1 ≤ n) (S : Finset (Fin (n + 1))) (hS : ∀ a ∈ S, 1 ≤ a.val) :
    ∃ v ∈ spLeviWeyl n, SpRealizes (n + 1) v 1 (spSgnOn S) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, spRealizes_one.congr rfl (by funext c; simp [spSgnOn])⟩
  | insert a S ha ih =>
    obtain ⟨v, hv, hvr⟩ := ih fun b hb => hS b (Finset.mem_insert_of_mem hb)
    obtain ⟨z, hz, hzr⟩ := exists_spLeviW_sgn hn a (hS a (Finset.mem_insert_self a S))
    refine ⟨v * z, mul_mem hv hz, (hvr.mul hzr).congr (mul_one 1) ?_⟩
    funext c
    simp only [spSgn, spSgnOn, Finset.mem_insert, Equiv.Perm.one_apply]
    by_cases hca : c = a
    · subst hca
      simp [ha]
    · by_cases hcS : c ∈ S
      · simp [hca, hcS]
      · simp [hca, hcS]

theorem exists_spLeviW_perm : ∀ (k : ℕ) (π : Equiv.Perm (Fin (n + 1))), π.support.card ≤ k →
    π 0 = 0 → ∃ v ∈ spLeviWeyl n, SpRealizes (n + 1) v π 1 := by
  intro k
  induction k with
  | zero =>
    intro π hπ _
    have : π = 1 := Equiv.Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp (by omega))
    subst this
    exact ⟨1, one_mem _, spRealizes_one⟩
  | succ k ih =>
    intro π hπ h0
    by_cases h1 : π = 1
    · subst h1
      exact ⟨1, one_mem _, spRealizes_one⟩
    obtain ⟨x, hx⟩ : ∃ x, π x ≠ x := by
      by_contra hne
      push Not at hne
      exact h1 (Equiv.ext hne)
    have hx0 : x ≠ 0 := fun e => hx (by rw [e, h0])
    have hπx0 : π x ≠ 0 := fun e => hx0 (π.injective (e.trans h0.symm))
    have hcard := Equiv.Perm.card_support_swap_mul hx
    have h0' : (Equiv.swap x (π x) * π) 0 = 0 := by
      rw [Equiv.Perm.mul_apply, h0, Equiv.swap_apply_of_ne_of_ne hx0.symm hπx0.symm]
    obtain ⟨v, hv, hvr⟩ := ih _ (by omega) h0'
    have hx1 : 1 ≤ x.val := by
      have := Fin.val_ne_of_ne hx0
      simp only [Fin.val_zero] at this
      omega
    have hπx1 : 1 ≤ (π x).val := by
      have := Fin.val_ne_of_ne hπx0
      simp only [Fin.val_zero] at this
      omega
    obtain ⟨u, hu, hur⟩ := exists_spLeviW_swap x (π x) hx1 hπx1
    refine ⟨u * v, mul_mem hu hv, (hur.mul_one hvr).congr ?_ rfl⟩
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul]

theorem exists_spLeviW_of_fix (hn : 1 ≤ n) {π : Equiv.Perm (Fin (n + 1))} {s : Fin (n + 1) → ℤ}
    (hs : SpIsSign s) (hπ : π 0 = 0) (hs0 : s 0 = 1) :
    ∃ v ∈ spLeviWeyl n, SpRealizes (n + 1) v π s := by
  obtain ⟨u, hu, hur⟩ := exists_spLeviW_perm π.support.card π le_rfl hπ
  let S : Finset (Fin (n + 1)) := Finset.univ.filter fun a => s a = -1
  have hS : ∀ a ∈ S, 1 ≤ a.val := by
    intro a ha
    have ha' : s a = -1 := (Finset.mem_filter.mp ha).2
    by_contra h
    have : a = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    rw [this, hs0] at ha'
    norm_num at ha'
  obtain ⟨z, hz, hzr⟩ := exists_spLeviW_sgnOn hn S hS
  refine ⟨u * z, mul_mem hu hz, (hur.mul hzr).congr (mul_one π) ?_⟩
  funext c
  simp only [spSgnOn, Pi.one_apply, mul_one, S, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hs c with h | h <;> simp [h]

theorem spRealizes_simple_zero (hn : 1 ≤ n) :
    SpRealizes (n + 1) ((coxeterMatrix (isFiniteType_cartanC (n + 1))).toCoxeterSystem.simple 0)
      (Equiv.swap 0 ⟨1, by omega⟩) 1 := by
  have h : (0 : Fin (n + 1)).val + 1 < n + 1 := by simp; omega
  have e : (⟨(0 : Fin (n + 1)).val + 1, h⟩ : Fin (n + 1)) = ⟨1, by omega⟩ := Fin.ext (by simp)
  exact e ▸ spRealizes_simple_of_lt h

theorem exists_spZeroSwap (hn : 1 ≤ n) (c : Fin (n + 1)) (hc : 1 ≤ c.val) :
    ∃ v ∈ spLeviWeyl n, SpRealizes (n + 1) v (Equiv.swap ⟨1, by omega⟩ c) 1 ∧
      SpRealizes (n + 1)
        (v * (coxeterMatrix (isFiniteType_cartanC (n + 1))).toCoxeterSystem.simple 0 * v⁻¹)
        (Equiv.swap 0 c) 1 := by
  obtain ⟨v, hv, hvr⟩ := exists_spLeviW_swap ⟨1, by omega⟩ c (by simp) hc
  refine ⟨v, hv, hvr, ((hvr.mul_one (spRealizes_simple_zero hn)).mul_one hvr.inv_one).congr ?_ rfl⟩
  have h01 : (0 : Fin (n + 1)) ≠ ⟨1, by omega⟩ := fun e => by
    have := congrArg Fin.val e
    simp at this
  have h0c : (0 : Fin (n + 1)) ≠ c := fun e => by
    have := congrArg Fin.val e
    simp at this
    omega
  rw [← Equiv.swap_apply_apply, Equiv.swap_apply_of_ne_of_ne h01 h0c, Equiv.swap_apply_left]

theorem exists_spZeroSign (hn : 1 ≤ n) :
    ∃ z : (coxeterMatrix (isFiniteType_cartanC (n + 1))).Group,
      SpRealizes (n + 1) z 1 (spSgn 0) := by
  obtain ⟨v, -, -, hu⟩ := exists_spZeroSwap hn (Fin.last n) (by simp; omega)
  obtain ⟨t, -, htr⟩ := exists_spLeviW_sgn_last hn
  refine ⟨_, ((hu.mul htr).mul hu.inv_one).congr (by rw [mul_one, mul_inv_cancel]) ?_⟩
  funext c
  simp [spSgn, Equiv.swap_inv, Equiv.swap_apply_eq_iff]

theorem spLevi_decomp (hn : 1 ≤ n) {w : (coxeterMatrix (isFiniteType_cartanC (n + 1))).Group}
    {π : Equiv.Perm (Fin (n + 1))} {s : Fin (n + 1) → ℤ} (hs : SpIsSign s)
    (h : SpRealizes (n + 1) w π s) :
    ∃ u z : (coxeterMatrix (isFiniteType_cartanC (n + 1))).Group,
      (u = 1 ∨ SpRealizes (n + 1) u (Equiv.swap 0 (π 0)) 1) ∧
      (z = 1 ∨ SpRealizes (n + 1) z 1 (spSgn 0)) ∧ z * u * w ∈ spLeviWeyl n := by
  obtain ⟨u, hu, hur⟩ : ∃ u : (coxeterMatrix (isFiniteType_cartanC (n + 1))).Group,
      (u = 1 ∨ SpRealizes (n + 1) u (Equiv.swap 0 (π 0)) 1) ∧
        SpRealizes (n + 1) u (Equiv.swap 0 (π 0)) 1 := by
    by_cases h0 : π 0 = 0
    · refine ⟨1, Or.inl rfl, spRealizes_one.congr ?_ rfl⟩
      rw [h0, Equiv.swap_self, Equiv.Perm.one_def]
    · have hc : 1 ≤ (π 0).val := by
        have := Fin.val_ne_of_ne h0
        simp only [Fin.val_zero] at this
        omega
      obtain ⟨v, -, -, hvr⟩ := exists_spZeroSwap hn (π 0) hc
      exact ⟨_, Or.inr hvr, hvr⟩
  have huw := hur.mul h
  have hπ0 : (Equiv.swap 0 (π 0) * π) 0 = 0 := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  have hsg : SpIsSign (fun c => s c * (1 : Fin (n + 1) → ℤ) (π c)) := hs.mul spIsSign_one π
  rcases hs 0 with hs0 | hs0
  · obtain ⟨v, hv, hvr⟩ := exists_spLeviW_of_fix hn hsg hπ0 (by simp [hs0])
    refine ⟨u, 1, hu, Or.inl rfl, ?_⟩
    rw [one_mul, huw.inj hvr]
    exact hv
  · obtain ⟨z, hz⟩ := exists_spZeroSign hn
    have hzuw := hz.mul huw
    obtain ⟨v, hv, hvr⟩ := exists_spLeviW_of_fix (π := 1 * (Equiv.swap 0 (π 0) * π))
      (s := fun c => s c * (1 : Fin (n + 1) → ℤ) (π c) * spSgn 0 ((Equiv.swap 0 (π 0) * π) c)) hn
      (hsg.mul (spIsSign_spSgn 0) _) (by rw [one_mul]; exact hπ0)
      (by simp only [hπ0, hs0, spSgn, Pi.one_apply]; norm_num)
    refine ⟨u, z, hu, Or.inr hz, ?_⟩
    rw [mul_assoc, hzuw.inj hvr]
    exact hv

end Levi
