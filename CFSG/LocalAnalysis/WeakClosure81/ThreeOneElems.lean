module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv

namespace ThreeOne

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {σ : Perm Ω}

private lemma mem_centralizer_of_conj_eq {p : Perm Ω} (h : σ * p * σ⁻¹ = p) :
    p ∈ Subgroup.centralizer {σ} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc p * σ = (σ * p * σ⁻¹) * σ := by rw [h]
    _ = σ * p := by rw [mul_assoc, inv_mul_cancel, mul_one]

private lemma commute_swap_swap_of (hσ : ∀ x, σ (σ x) = x) {a b : Ω} (ha : σ a ≠ a)
    (hb : σ b ≠ b) (hab : a ≠ b) (hbσa : b ≠ σ a) :
    Commute (swap a b) (swap (σ a) (σ b)) := by
  have haσb : a ≠ σ b := by
    intro h
    exact hbσa (by rw [← hσ b, ← congrArg σ h])
  have hσaσb : σ a ≠ σ b := fun h => hab (σ.injective h)
  have hnodup : [a, b, σ a, σ b].Nodup := by
    refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_,
      List.nodup_singleton _⟩⟩⟩
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
      exact ⟨hab, ha.symm, haσb⟩
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
      exact ⟨hbσa, hb.symm⟩
    · simp only [List.mem_singleton]
      exact hσaσb
  exact (Equiv.Perm.disjoint_swap_swap hnodup).commute

theorem swap_apply_mem_centralizer (hσ : ∀ x, σ (σ x) = x) (a : Ω) :
    swap a (σ a) ∈ Subgroup.centralizer {σ} := by
  apply mem_centralizer_of_conj_eq
  rw [← swap_apply_apply σ a (σ a), hσ a, swap_comm (σ a) a]

theorem swap_mul_swap_mem_centralizer (hσ : ∀ x, σ (σ x) = x) {a b : Ω} (ha : σ a ≠ a)
    (hb : σ b ≠ b) : swap a b * swap (σ a) (σ b) ∈ Subgroup.centralizer {σ} := by
  apply mem_centralizer_of_conj_eq
  have hconj : σ * (swap a b * swap (σ a) (σ b)) * σ⁻¹
      = swap (σ a) (σ b) * swap a b := by
    calc σ * (swap a b * swap (σ a) (σ b)) * σ⁻¹
        = (σ * swap a b * σ⁻¹) * (σ * swap (σ a) (σ b) * σ⁻¹) := by
          rw [← MulAut.conj_apply, map_mul]
          simp only [MulAut.conj_apply]
      _ = swap (σ a) (σ b) * swap (σ (σ a)) (σ (σ b)) := by
          rw [← swap_apply_apply σ a b, ← swap_apply_apply σ (σ a) (σ b)]
      _ = swap (σ a) (σ b) * swap a b := by rw [hσ a, hσ b]
  rw [hconj]
  by_cases hab : a = b
  · subst hab; simp
  by_cases hbσa : b = σ a
  · subst hbσa; rw [hσ a, swap_comm (σ a) a]
  · exact (commute_swap_swap_of hσ ha hb hab hbσa).eq.symm

theorem swap_mul_swap_apply_mem_inf (hσ : ∀ x, σ (σ x) = x) {H : Subgroup (Perm Ω)}
    (hA : alternatingGroup Ω ≤ H) {a b : Ω} (ha : σ a ≠ a) (hb : σ b ≠ b) :
    swap a (σ a) * swap b (σ b) ∈ H ⊓ Subgroup.centralizer {σ} := by
  rw [Subgroup.mem_inf]
  refine ⟨hA ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap ha.symm,
      Equiv.Perm.sign_swap hb.symm]
    simp
  · exact mul_mem (swap_apply_mem_centralizer hσ a) (swap_apply_mem_centralizer hσ b)

theorem swap_mul_swap_mem_inf (hσ : ∀ x, σ (σ x) = x) {H : Subgroup (Perm Ω)}
    (hA : alternatingGroup Ω ≤ H) {a b : Ω} (ha : σ a ≠ a) (hb : σ b ≠ b) :
    swap a b * swap (σ a) (σ b) ∈ H ⊓ Subgroup.centralizer {σ} := by
  rw [Subgroup.mem_inf]
  refine ⟨hA ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap',
      Equiv.Perm.sign_swap']
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg hab, if_neg (fun h => hab (σ.injective h))]
      simp
  · exact swap_mul_swap_mem_centralizer hσ ha hb

theorem exists_mem_inf_apply_eq (hσ : ∀ x, σ (σ x) = x) {H : Subgroup (Perm Ω)}
    (hA : alternatingGroup Ω ≤ H) {x y : Ω} (hx : σ x ≠ x) (hy : σ y ≠ y)
    (hr : ∃ r, σ r ≠ r ∧ r ≠ x ∧ r ≠ σ x) :
    ∃ g ∈ H ⊓ Subgroup.centralizer {σ}, g x = y := by
  by_cases hyx : y = x
  · subst hyx
    exact ⟨1, by rw [Subgroup.mem_inf]; exact ⟨one_mem H, one_mem _⟩, rfl⟩
  by_cases hyσx : y = σ x
  · obtain ⟨r, hrσ, hrx, hrσx⟩ := hr
    refine ⟨swap x (σ x) * swap r (σ r),
      swap_mul_swap_apply_mem_inf hσ hA hx hrσ, ?_⟩
    rw [hyσx, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hrx.symm ?_,
      Equiv.swap_apply_left]
    intro h
    exact hrσx (by rw [← hσ r, ← congrArg σ h])
  · refine ⟨swap x y * swap (σ x) (σ y), swap_mul_swap_mem_inf hσ hA hx hy, ?_⟩
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hx.symm ?_,
      Equiv.swap_apply_left]
    intro h
    exact hyσx (by rw [← hσ y, ← congrArg σ h])

theorem exists_mem_inf_apply_eq_of_apply_eq (hσ : ∀ x, σ (σ x) = x) {H : Subgroup (Perm Ω)}
    (hA : alternatingGroup Ω ≤ H) {x y z : Ω} (hy : σ y ≠ y) (hz : σ z ≠ z) (hyx : y ≠ x)
    (hyx' : y ≠ σ x) (hzx : z ≠ x) (hzx' : z ≠ σ x)
    (hr : ∃ r, σ r ≠ r ∧ r ≠ x ∧ r ≠ σ x ∧ r ≠ y ∧ r ≠ σ y) :
    ∃ g ∈ H ⊓ Subgroup.centralizer {σ}, g x = x ∧ g y = z := by
  by_cases hzy : z = y
  · subst hzy
    exact ⟨1, by rw [Subgroup.mem_inf]; exact ⟨one_mem H, one_mem _⟩, rfl, rfl⟩
  by_cases hzσy : z = σ y
  · subst hzσy
    obtain ⟨r, hrσ, hrx, hrσx, hry, hrσy⟩ := hr
    have hxσr : x ≠ σ r := by
      intro h
      exact hrσx (by rw [← hσ r, ← congrArg σ h])
    have hyσr : y ≠ σ r := by
      intro h
      exact hrσy (by rw [← hσ r, ← congrArg σ h])
    have hxσy : x ≠ σ y := by
      intro h
      exact hyx' (by rw [← hσ y, ← congrArg σ h])
    refine ⟨swap y (σ y) * swap r (σ r),
      swap_mul_swap_apply_mem_inf hσ hA hy hrσ, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hrx.symm hxσr,
        Equiv.swap_apply_of_ne_of_ne hyx.symm hxσy]
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hry.symm hyσr,
        Equiv.swap_apply_left]
  · have hyσz : y ≠ σ z := by
      intro h
      exact hzσy (by rw [← hσ z, ← congrArg σ h])
    have hxσy : x ≠ σ y := by
      intro h
      exact hyx' (by rw [← hσ y, ← congrArg σ h])
    have hxσz : x ≠ σ z := by
      intro h
      exact hzx' (by rw [← hσ z, ← congrArg σ h])
    refine ⟨swap y z * swap (σ y) (σ z), swap_mul_swap_mem_inf hσ hA hy hz, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxσy hxσz,
        Equiv.swap_apply_of_ne_of_ne hyx.symm hzx.symm]
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hy.symm hyσz,
        Equiv.swap_apply_left]

theorem apply_eq_of_mem_centralizer {α : Ω} (hα : σ α = α) (hfix : ∀ x, x ≠ α → σ x ≠ x)
    {g : Perm Ω} (hg : g ∈ Subgroup.centralizer {σ}) : g α = α := by
  have hcomm : g * σ = σ * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have h : σ (g α) = g α := by
    calc σ (g α) = (σ * g) α := rfl
      _ = (g * σ) α := by rw [hcomm]
      _ = g (σ α) := rfl
      _ = g α := by rw [hα]
  by_contra hne
  exact (hfix (g α) hne) h

end ThreeOne

end CFSG.LocalAnalysis.WeakClosure81

end
