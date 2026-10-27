module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P510Base

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem cen_conj_iff {g z : G} {S S' : Subgroup G} (hS : ∀ h, h ∈ S' ↔ g⁻¹ * h * g ∈ S) :
    g * z * g⁻¹ ∈ Cen (S' : Set G) ↔ z ∈ Cen (S : Set G) := by
  have e1 : ∀ w : G, g⁻¹ * (g * w * g⁻¹) * g = w := fun w => by group
  have e2 : ∀ w : G, g * (g⁻¹ * w * g) * g⁻¹ = w := fun w => by group
  constructor
  · rintro ⟨hm, hc⟩
    refine ⟨by simpa [e1] using (hS _).1 hm, fun h hh => ?_⟩
    have := hc (g * h * g⁻¹) ((hS _).2 (by rw [e1]; exact hh))
    have h2 := congrArg (fun w => g⁻¹ * w * g) this
    have e3 : g⁻¹ * (g * h * g⁻¹ * (g * z * g⁻¹)) * g = h * z := by group
    have e4 : g⁻¹ * (g * z * g⁻¹ * (g * h * g⁻¹)) * g = z * h := by group
    simp only [e3, e4] at h2
    exact h2
  · rintro ⟨hm, hc⟩
    refine ⟨(hS _).2 (by rw [e1]; exact hm), fun h hh => ?_⟩
    have := hc (g⁻¹ * h * g) ((hS _).1 hh)
    have h2 := congrArg (fun w => g * w * g⁻¹) this
    have e3 : g * (g⁻¹ * h * g * z) * g⁻¹ = h * (g * z * g⁻¹) := by group
    have e4 : g * (z * (g⁻¹ * h * g)) * g⁻¹ = g * z * g⁻¹ * h := by group
    simp only [e3, e4] at h2
    exact h2

theorem conj_fix_iff (g h : G) (v : V) : (g⁻¹ * h * g) • v = v ↔ h • (g • v) = g • v := by
  rw [mul_smul, mul_smul, inv_smul_eq_iff]

namespace Line

variable (ℓ : Line Γ)

theorem isCore_iff {z : G} {a b : ℤ} :
    ℓ.IsCore z a b ↔ a < b ∧ (∀ i, a ≤ i → i < b → z ∈ Cen (ℓ.edgeStab (G := G) i : Set G)) ∧
      z ∉ Cen (ℓ.edgeStab (G := G) (a - 1) : Set G) ∧ z ∉ Cen (ℓ.edgeStab (G := G) b : Set G) := by
  have hf0 : ∀ i, z ∈ Cen (ℓ.edgeStab (G := G) i : Set G) →
      z • ℓ.vert i = ℓ.vert i ∧ z • ℓ.vert (i + 1) = ℓ.vert (i + 1) :=
    fun i hi => (ℓ.mem_edgeStab_iff).1 hi.1
  constructor
  · rintro ⟨hab, -, hc, h1, h2⟩
    exact ⟨hab, hc, fun h => h1 ⟨(hf0 _ h).1, h⟩, fun h => h2 ⟨(hf0 _ h).1, h⟩⟩
  · rintro ⟨hab, hc, h1, h2⟩
    refine ⟨hab, fun i hi1 hi2 => ?_, hc, fun h => h1 h.2, fun h => h2 h.2⟩
    by_cases h : i < b
    · exact (hf0 i (hc i hi1 h)).1
    · have hib : i = b := by omega
      have := (hf0 (b - 1) (hc (b - 1) (by omega) (by omega))).2
      rw [show b - 1 + 1 = b by omega] at this
      rw [hib]
      exact this

theorem edgeStab_conj_trans {g : G} {s : ℤ} (hv : ∀ i, g • ℓ.vert i = ℓ.vert (i + s)) (i : ℤ)
    (h : G) :
    h ∈ ℓ.edgeStab (G := G) (i + s) ↔ g⁻¹ * h * g ∈ ℓ.edgeStab (G := G) i := by
  rw [ℓ.mem_edgeStab_iff, ℓ.mem_edgeStab_iff, conj_fix_iff, conj_fix_iff, hv, hv,
    add_right_comm i 1 s]

theorem edgeStab_conj_refl {g : G} {c : ℤ} (hv : ∀ i, g • ℓ.vert i = ℓ.vert (c - i)) (i : ℤ)
    (h : G) :
    h ∈ ℓ.edgeStab (G := G) (c - i - 1) ↔ g⁻¹ * h * g ∈ ℓ.edgeStab (G := G) i := by
  rw [ℓ.mem_edgeStab_iff, ℓ.mem_edgeStab_iff, conj_fix_iff, conj_fix_iff, hv, hv,
    show c - i - 1 + 1 = c - i by ring, show c - (i + 1) = c - i - 1 by ring]
  exact and_comm

theorem conj_fix {g z : G} {σ : ℤ → ℤ} (hv : ∀ i, g • ℓ.vert i = ℓ.vert (σ i)) (i : ℤ) :
    σ i ∈ ℓ.fixIdx (g * z * g⁻¹) ↔ i ∈ ℓ.fixIdx z := by
  show (g * z * g⁻¹) • ℓ.vert (σ i) = ℓ.vert (σ i) ↔ z • ℓ.vert i = ℓ.vert i
  rw [← hv i, mul_smul, mul_smul, inv_smul_smul, smul_left_cancel_iff]

theorem isCoreFix_conj_trans {g z : G} {s a b tL tR : ℤ}
    (hv : ∀ i, g • ℓ.vert i = ℓ.vert (i + s)) (h : ℓ.IsCoreFix z a b tL tR) :
    ℓ.IsCoreFix (g * z * g⁻¹) (a + s) (b + s) (tL + s) (tR + s) := by
  have hcen : ∀ i, g * z * g⁻¹ ∈ Cen (ℓ.edgeStab (G := G) (i + s) : Set G) ↔
      z ∈ Cen (ℓ.edgeStab (G := G) i : Set G) := fun i =>
    cen_conj_iff (ℓ.edgeStab_conj_trans hv i)
  obtain ⟨hab, hc, h1, h2⟩ := (ℓ.isCore_iff).1 h.core
  refine ⟨fun j => ?_, (ℓ.isCore_iff).2 ⟨by omega, fun i hi1 hi2 => ?_, ?_, ?_⟩⟩
  · have := ℓ.conj_fix hv (j - s) (z := z)
    rw [sub_add_cancel] at this
    rw [this, h.fix]
    omega
  · have := (hcen (i - s)).2 (hc (i - s) (by omega) (by omega))
    rwa [sub_add_cancel] at this
  · intro hh
    have := (hcen (a - 1)).1 (by rwa [show a - 1 + s = a + s - 1 by ring])
    exact h1 this
  · intro hh
    exact h2 ((hcen b).1 hh)

theorem isCoreFix_conj_refl {g z : G} {c a b tL tR : ℤ}
    (hv : ∀ i, g • ℓ.vert i = ℓ.vert (c - i)) (h : ℓ.IsCoreFix z a b tL tR) :
    ℓ.IsCoreFix (g * z * g⁻¹) (c - b) (c - a) (c - tR) (c - tL) := by
  have hcen : ∀ i, g * z * g⁻¹ ∈ Cen (ℓ.edgeStab (G := G) (c - i - 1) : Set G) ↔
      z ∈ Cen (ℓ.edgeStab (G := G) i : Set G) := fun i =>
    cen_conj_iff (ℓ.edgeStab_conj_refl hv i)
  obtain ⟨hab, hc, h1, h2⟩ := (ℓ.isCore_iff).1 h.core
  refine ⟨fun j => ?_, (ℓ.isCore_iff).2 ⟨by omega, fun i hi1 hi2 => ?_, ?_, ?_⟩⟩
  · have := ℓ.conj_fix hv (c - j) (z := z)
    rw [sub_sub_cancel] at this
    rw [this, h.fix]
    omega
  · have := (hcen (c - i - 1)).2 (hc (c - i - 1) (by omega) (by omega))
    rwa [show c - (c - i - 1) - 1 = i by ring] at this
  · intro hh
    have := (hcen b).1 (by rwa [show c - b - 1 = c - b - 1 from rfl])
    exact h2 this
  · intro hh
    have := (hcen (a - 1)).1 (by rwa [show c - (a - 1) - 1 = c - a by ring])
    exact h1 this

end Line

end CFSG.Quasithin.Fan86
