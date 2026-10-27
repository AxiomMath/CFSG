module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.Quasithin.Kleidman.VBOdd

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem perm_pair_fin :
    ∀ m m' : Equiv.Perm (Fin 5), m * m = 1 → m' * m' = 1 →
      (∃ ω : Fin 5, m ω = ω ∧ ∀ U, m U = U → U = ω) →
      (∃ ω : Fin 5, m' ω = ω ∧ ∀ U, m' U = U → U = ω) →
      m ≠ m' → m * m' = m' * m →
      ∃ U : Fin 5, m U ≠ U ∧ m' U ≠ U ∧ m U ≠ m' U := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem perm_two_cycles_fin :
    ∀ m : Equiv.Perm (Fin 5), m * m = 1 →
      (∃ ω : Fin 5, m ω = ω ∧ ∀ U, m U = U → U = ω) →
      ∃ a b : Fin 5, m a ≠ a ∧ m b ≠ b ∧ b ≠ a ∧ b ≠ m a := by
  decide +kernel

theorem unique_fix_transport {Ω : Type*} (e : Ω ≃ Fin 5) (m : Equiv.Perm Ω)
    (h : ∃ ω, m ω = ω ∧ ∀ U, m U = U → U = ω) :
    ∃ ω : Fin 5, e.permCongrHom m ω = ω ∧ ∀ U, e.permCongrHom m U = U → U = ω := by
  obtain ⟨ω, hω, hu⟩ := h
  have hφ : ∀ x : Ω, e.permCongrHom m (e x) = e (m x) := by
    intro x
    simp [Equiv.permCongr_apply]
  refine ⟨e ω, by rw [hφ, hω], ?_⟩
  intro U hU
  obtain ⟨x, rfl⟩ := e.surjective U
  rw [hφ] at hU
  have hx : m x = x := e.injective hU
  rw [hu x hx]

theorem perm_pair_of_one_fixed {Ω : Type*} [Finite Ω] (hΩ : Nat.card Ω = 5)
    (m m' : Equiv.Perm Ω) (hm2 : m * m = 1) (hm'2 : m' * m' = 1)
    (hm : ∃ ω, m ω = ω ∧ ∀ U, m U = U → U = ω) (hm' : ∃ ω, m' ω = ω ∧ ∀ U, m' U = U → U = ω)
    (hne : m ≠ m') (hcomm : m * m' = m' * m) :
    ∃ U, m U ≠ U ∧ m' U ≠ U ∧ m U ≠ m' U := by
  classical
  have : Fintype Ω := Fintype.ofFinite Ω
  have hc : Fintype.card Ω = 5 := by rw [← Nat.card_eq_fintype_card]; exact hΩ
  let e : Ω ≃ Fin 5 := Fintype.equivFinOfCardEq hc
  let φ : Equiv.Perm Ω ≃* Equiv.Perm (Fin 5) := e.permCongrHom
  have hφ : ∀ (p : Equiv.Perm Ω) (x : Ω), φ p (e x) = e (p x) := by
    intro p x
    simp [φ, Equiv.permCongr_apply]
  obtain ⟨U, h1, h2, h3⟩ := perm_pair_fin (φ m) (φ m')
    (by rw [← map_mul, hm2, map_one])
    (by rw [← map_mul, hm'2, map_one])
    (unique_fix_transport e m hm) (unique_fix_transport e m' hm')
    (fun h => hne (φ.injective h))
    (by rw [← map_mul, ← map_mul, hcomm])
  obtain ⟨x, rfl⟩ := e.surjective U
  simp only [hφ] at h1 h2 h3
  refine ⟨x, fun h => h1 (by rw [h]), fun h => h2 (by rw [h]), fun h => h3 (by rw [h])⟩

theorem perm_two_cycles_of_one_fixed {Ω : Type*} [Finite Ω] (hΩ : Nat.card Ω = 5)
    (m : Equiv.Perm Ω) (hm2 : m * m = 1) (hm : ∃ ω, m ω = ω ∧ ∀ U, m U = U → U = ω) :
    ∃ a b : Ω, m a ≠ a ∧ m b ≠ b ∧ b ≠ a ∧ b ≠ m a := by
  classical
  have : Fintype Ω := Fintype.ofFinite Ω
  have hc : Fintype.card Ω = 5 := by rw [← Nat.card_eq_fintype_card]; exact hΩ
  let e : Ω ≃ Fin 5 := Fintype.equivFinOfCardEq hc
  let φ : Equiv.Perm Ω ≃* Equiv.Perm (Fin 5) := e.permCongrHom
  have hφ : ∀ (p : Equiv.Perm Ω) (x : Ω), φ p (e x) = e (p x) := by
    intro p x
    simp [φ, Equiv.permCongr_apply]
  obtain ⟨a, b, ha, hb, hba, hbma⟩ := perm_two_cycles_fin (φ m)
    (by rw [← map_mul, hm2, map_one])
    (unique_fix_transport e m hm)
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  simp only [hφ] at ha hb hbma
  refine ⟨x, y, fun h => ha (by rw [h]), fun h => hb (by rw [h]), fun h => hba (by rw [h]),
    fun h => hbma (by rw [h])⟩

end CFSG.Quasithin.Kleidman.VBOdd

end
