module

public import CFSG.Quasithin.H13.GoldschmidtU43Trans

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

@[expose] def PerpPerp (v : V4) : Prop :=
  ∀ w : V4, (∀ c : V4, bq c v = 0 → bq c w = 0) → w = 0 ∨ w = v

instance (v : V4) : Decidable (PerpPerp v) :=
  inferInstanceAs (Decidable (∀ w : V4, (∀ c : V4, bq c v = 0 → bq c w = 0) → w = 0 ∨ w = v))

theorem perp_perp : ∀ v : V4, PerpPerp v := by
  decide +kernel

namespace Hyp

variable {z : G} (h : Hyp z)
include h

theorem eq_of_θ_eq {x t : G} (hx : x ∈ Uz z) (ht : t ∈ Uz z)
    (hθ : h.θ ⟨x, hx⟩ = h.θ ⟨t, ht⟩) : x = t ∨ x = z * t := by
  have h1 : h.θ (⟨x, hx⟩ * ⟨t, ht⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, hθ]
    exact mul_inv_cancel _
  rcases (h.θ_eq_one_iff _).1 h1 with h2 | h2
  · left
    have : x * t⁻¹ = 1 := by simpa using h2
    exact mul_inv_eq_one.mp this
  · right
    have : x * t⁻¹ = z := by simpa using h2
    calc x = (x * t⁻¹) * t := by group
      _ = z * t := by rw [this]

theorem z_mem_conjugate {g : G} (ht : g⁻¹ * z * g ∈ Uz z)
    (hI : Nat.card ↥(Uz z ⊓ CFSG.conjugate (Uz z) g) = 4) : z ∈ CFSG.conjugate (Uz z) g := by
  set t : G := g⁻¹ * z * g with ht_def
  have ht2 : t * t = 1 := by
    calc t * t = g⁻¹ * (z * z) * g := by rw [ht_def]; group
      _ = 1 := by rw [h.sq_z]; group
  have ht1 : t ≠ 1 := by
    intro h1
    apply h.z_ne_one
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [← ht_def, h1]; group
  set I : Subgroup G := Uz z ⊓ CFSG.conjugate (Uz z) g with hI_def
  have hIt : t ∈ I := ⟨ht, mem_conjugate_iff.mpr (by
    have : g * t * g⁻¹ = z := by rw [ht_def]; group
    rw [this]
    exact h.z_mem)⟩
  have hIcomm : ∀ x ∈ I, x * t = t * x := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ Uz z := mem_conjugate_iff.mp hx.2
    have h2 := h.z_comm h1
    calc x * t = g⁻¹ * ((g * x * g⁻¹) * z) * g := by rw [ht_def]; group
      _ = g⁻¹ * (z * (g * x * g⁻¹)) * g := by rw [← h2]
      _ = t * x := by rw [ht_def]; group
  by_contra hzI
  have hzI' : z ∉ I := fun hz => hzI hz.2
  have hnorm : ∀ c ∈ Uz z, c * t = t * c → ∀ x ∈ I, c * x * c⁻¹ ∈ I := by
    intro c hc hct x hx
    refine Subgroup.mem_inf.mpr ⟨(Uz z).mul_mem ((Uz z).mul_mem hc hx.1) ((Uz z).inv_mem hc), ?_⟩
    rw [mem_conjugate_iff]
    have hgc : g * c * g⁻¹ ∈ Hz z := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * c * g⁻¹ * z = g * (c * t) * g⁻¹ := by rw [ht_def]; group
        _ = g * (t * c) * g⁻¹ := by rw [hct]
        _ = z * (g * c * g⁻¹) := by rw [ht_def]; group
    have hx' : g * x * g⁻¹ ∈ Uz z := mem_conjugate_iff.mp hx.2
    have key := (Subgroup.mem_normalizer_iff.mp (Hz_le_normalizer z hgc) (g * x * g⁻¹)).mp hx'
    have e : g * (c * x * c⁻¹) * g⁻¹ = (g * c * g⁻¹) * (g * x * g⁻¹) * (g * c * g⁻¹)⁻¹ := by
      group
    rw [e]
    exact key
  have hperp : ∀ x (hx : x ∈ I) c (hc : c ∈ Uz z), c * t = t * c →
      bq (Multiplicative.toAdd (h.θ ⟨c, hc⟩)) (Multiplicative.toAdd (h.θ ⟨x, hx.1⟩)) = 0 := by
    intro x hx c hc hct
    by_contra hb
    have hb1 : bq (Multiplicative.toAdd (h.θ ⟨c, hc⟩)) (Multiplicative.toAdd (h.θ ⟨x, hx.1⟩)) = 1 :=
      (zmod_two_cases _).resolve_left hb
    have hcomm := h.comm_eq ⟨c, hc⟩ ⟨x, hx.1⟩
    rw [hb1, zp_one] at hcomm
    apply hzI'
    rw [← hcomm]
    exact mul_mem (hnorm c hc hct x hx) (inv_mem hx)
  have hsub : ∀ x ∈ I, x = 1 ∨ x = z ∨ x = t ∨ x = z * t := by
    intro x hx
    have hp := perp_perp (Multiplicative.toAdd (h.θ ⟨t, ht⟩))
      (Multiplicative.toAdd (h.θ ⟨x, hx.1⟩)) (fun c' hc' => by
        obtain ⟨c, hc⟩ := h.θ_surj (Multiplicative.ofAdd c')
        have hcc : bq (Multiplicative.toAdd (h.θ c)) (Multiplicative.toAdd (h.θ ⟨t, ht⟩)) = 0 := by
          rw [hc, toAdd_ofAdd]
          exact hc'
        have hct : (c : G) * t = t * c := by
          have := h.comm_eq c ⟨t, ht⟩
          rw [hcc, zp_zero] at this
          calc (c : G) * t = ((c : G) * t * (c : G)⁻¹ * t⁻¹) * (t * c) := by group
            _ = t * c := by
              rw [show ((⟨t, ht⟩ : ↥(Uz z)) : G) = t from rfl] at this
              rw [this, one_mul]
        have := hperp x hx c c.2 hct
        rw [hc, toAdd_ofAdd] at this
        exact this)
    rcases hp with h0 | h0
    · rcases (h.θ_eq_one_iff ⟨x, hx.1⟩).1 (Multiplicative.toAdd.injective (by simpa using h0))
        with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · rcases h.eq_of_θ_eq hx.1 ht (Multiplicative.toAdd.injective h0) with h1 | h1
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr h1))
  have hsub' : ∀ x ∈ I, x = 1 ∨ x = t := by
    intro x hx
    rcases hsub x hx with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact absurd (h1 ▸ hx) hzI'
    · exact Or.inr h1
    · exfalso
      apply hzI'
      have : z = x * t⁻¹ := by rw [h1]; group
      rw [this]
      exact mul_mem hx (inv_mem hIt)
  have hle : Set.ncard (I : Set G) ≤ 2 := by
    refine (Set.ncard_le_ncard (t := ({1, t} : Set G)) (fun x hx => ?_) (Set.toFinite _)).trans ?_
    · rcases hsub' x hx with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    · exact (Set.ncard_insert_le 1 {t}).trans (by simp)
  have hc : Nat.card ↥I = (I : Set G).ncard := Nat.card_coe_set_eq (I : Set G)
  omega

theorem conj_ne_one (g : G) : g⁻¹ * z * g ≠ 1 := by
  intro h1
  apply h.z_ne_one
  calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem conj_sq (g : G) : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
  calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
    _ = 1 := by rw [h.sq_z]; group

theorem mem_inf_iff [Finite G] {g : G} (ht : g⁻¹ * z * g ∈ Uz z) (htz : g⁻¹ * z * g ≠ z)
    (hI : Nat.card ↥(Uz z ⊓ CFSG.conjugate (Uz z) g) = 4) (x : G) :
    x ∈ Uz z ⊓ CFSG.conjugate (Uz z) g ↔
      x = 1 ∨ x = z ∨ x = g⁻¹ * z * g ∨ x = z * (g⁻¹ * z * g) := by
  classical
  set t : G := g⁻¹ * z * g with ht_def
  have hzI : z ∈ Uz z ⊓ CFSG.conjugate (Uz z) g := ⟨h.z_mem, h.z_mem_conjugate ht hI⟩
  have htI : t ∈ Uz z ⊓ CFSG.conjugate (Uz z) g := ⟨ht, mem_conjugate_iff.mpr (by
    have : g * t * g⁻¹ = z := by rw [ht_def]; group
    rw [this]
    exact h.z_mem)⟩
  have ht1 : t ≠ 1 := h.conj_ne_one g
  have hz1 : z ≠ 1 := h.z_ne_one
  have hzt1 : z * t ≠ 1 := by
    intro h1
    apply htz
    calc t = z * (z * t) := by rw [← mul_assoc, h.sq_z, one_mul]
      _ = z := by rw [h1, mul_one]
  have hzt2 : z * t ≠ z := by
    intro h1
    apply ht1
    calc t = z * (z * t) := by rw [← mul_assoc, h.sq_z, one_mul]
      _ = 1 := by rw [h1, h.sq_z]
  have hzt3 : z * t ≠ t := by
    intro h1
    apply hz1
    calc z = (z * t) * t⁻¹ := by group
      _ = 1 := by rw [h1]; group
  constructor
  · intro hx
    set S : Finset G := {1, z, t, z * t} with hS_def
    have hS : S.card = 4 := by
      have n1 : (1 : G) ∉ ({z, t, z * t} : Finset G) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hz1.symm, ht1.symm, hzt1.symm⟩
      have n2 : z ∉ ({t, z * t} : Finset G) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨htz.symm, hzt2.symm⟩
      have n3 : t ∉ ({z * t} : Finset G) := by
        simp only [Finset.mem_singleton]
        exact hzt3.symm
      rw [hS_def, Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
        Finset.card_insert_of_notMem n3, Finset.card_singleton]
    have hsub : (S : Set G) ⊆ ((Uz z ⊓ CFSG.conjugate (Uz z) g : Subgroup G) : Set G) := by
      intro y hy
      simp only [hS_def, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact hzI
      · exact htI
      · exact Subgroup.mul_mem _ hzI htI
    have hc : Nat.card ↥(Uz z ⊓ CFSG.conjugate (Uz z) g) =
        ((Uz z ⊓ CFSG.conjugate (Uz z) g : Subgroup G) : Set G).ncard :=
      Nat.card_coe_set_eq _
    have heq := Set.eq_of_subset_of_ncard_le hsub (by
      rw [Set.ncard_coe_finset, hS, ← hc, hI]) (Set.toFinite _)
    have hxS : x ∈ (S : Set G) := by rw [heq]; exact hx
    simpa [hS_def] using hxS
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact hzI
    · exact htI
    · exact Subgroup.mul_mem _ hzI htI

theorem exists_swap [Finite G] : ∃ t w : G, t ∈ Uz z ∧ t ≠ z ∧ t ≠ 1 ∧ t * t = 1 ∧
    w⁻¹ * z * w = t ∧ w⁻¹ * t * w = z ∧
    ∀ x : G, x ∈ Uz z ⊓ CFSG.conjugate (Uz z) w ↔ x = 1 ∨ x = z ∨ x = t ∨ x = z * t := by
  obtain ⟨g, ht, htz, hI⟩ := h.exists_g
  have hzg := h.z_mem_conjugate ht hI
  have ht' : g * z * g⁻¹ ∈ Uz z := mem_conjugate_iff.mp hzg
  have ht1 := h.conj_ne_one g
  have ht2 := h.conj_sq g
  have ht1' : g * z * g⁻¹ ≠ 1 := by
    intro h1
    apply h.z_ne_one
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  have ht2' : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h.sq_z]; group
  have htz' : g * z * g⁻¹ ≠ z := by
    intro h1
    apply htz
    calc g⁻¹ * z * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [h1]
      _ = z := by group
  obtain ⟨x, hxH, hx⟩ := h.exists_conj ht ht1 htz ht2 ht' ht1' htz' ht2'
  have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hxH
  refine ⟨g⁻¹ * z * g, x⁻¹ * g, ht, htz, ht1, ht2, ?_, ?_, ?_⟩
  · calc (x⁻¹ * g)⁻¹ * z * (x⁻¹ * g) = g⁻¹ * (x * z * x⁻¹) * g := by group
      _ = g⁻¹ * z * g := by rw [hxz]; group
  · calc (x⁻¹ * g)⁻¹ * (g⁻¹ * z * g) * (x⁻¹ * g) = g⁻¹ * (x * (g⁻¹ * z * g) * x⁻¹) * g := by group
      _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [hx]
      _ = z := by group
  · intro y
    have e : y ∈ CFSG.conjugate (Uz z) (x⁻¹ * g) ↔ y ∈ CFSG.conjugate (Uz z) g := by
      rw [mem_conjugate_iff, mem_conjugate_iff]
      have hn := Subgroup.mem_normalizer_iff.mp (Hz_le_normalizer z (inv_mem hxH))
        (g * y * g⁻¹)
      rw [inv_inv] at hn
      have e2 : x⁻¹ * g * y * (x⁻¹ * g)⁻¹ = x⁻¹ * (g * y * g⁻¹) * x := by group
      rw [e2]
      exact hn.symm
    rw [Subgroup.mem_inf, e]
    exact Subgroup.mem_inf.symm.trans (h.mem_inf_iff ht htz hI y)

end Hyp

end CFSG.Quasithin.H13.U43
