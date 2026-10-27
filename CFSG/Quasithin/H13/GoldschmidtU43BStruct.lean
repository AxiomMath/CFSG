module

public import CFSG.Quasithin.H13.GoldschmidtU43BNorm

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

abbrev Bg (z t : G) : Subgroup G := Hz z ⊓ Subgroup.centralizer ({t} : Set G)

abbrev N1g (z t : G) : Subgroup G := Uz z ⊓ Subgroup.centralizer ({t} : Set G)

abbrev N2g (z t w : G) : Subgroup G := CFSG.conjugate (N1g z t) w

theorem card_conj (H : Subgroup G) (g : G) : Nat.card ↥(CFSG.conjugate H g) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

structure Swap (z t w : G) : Prop where
  hyp : Hyp z
  ht : t ∈ S z
  w1 : w⁻¹ * z * w = t
  w2 : w⁻¹ * t * w = z
  inter : ∀ x : G, x ∈ Uz z ⊓ CFSG.conjugate (Uz z) w ↔ x = 1 ∨ x = z ∨ x = t ∨ x = z * t

theorem Hyp.exists_swap_data {z : G} [Finite G] (h : Hyp z) {t : G} (ht : t ∈ S z) :
    ∃ w, Swap z t w := by
  obtain ⟨w, h1, h2, h3⟩ := h.exists_swap' ht
  exact ⟨w, h, ht, h1, h2, h3⟩

namespace Swap

variable {z t w : G}

theorem cm (d : Swap z t w) : Comm2 z t := d.hyp.comm2 d.ht

theorem w1' (d : Swap z t w) : w * z * w⁻¹ = t := by
  calc w * z * w⁻¹ = w * (w⁻¹ * t * w) * w⁻¹ := by rw [d.w2]
    _ = t := by group

theorem w2' (d : Swap z t w) : w * t * w⁻¹ = z := by
  calc w * t * w⁻¹ = w * (w⁻¹ * z * w) * w⁻¹ := by rw [d.w1]
    _ = z := by group

theorem conj_mem_B {g : G} (hz : g⁻¹ * z * g = t) (ht : g⁻¹ * t * g = z) {x : G}
    (hx : x ∈ Bg z t) : g * x * g⁻¹ ∈ Bg z t := by
  have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hx.1
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
  have hgt : g * t * g⁻¹ = z := by
    calc g * t * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hz]
      _ = z := by group
  have hgz : g * z * g⁻¹ = t := by
    calc g * z * g⁻¹ = g * (g⁻¹ * t * g) * g⁻¹ := by rw [ht]
      _ = t := by group
  refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
    Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  · calc g * x * g⁻¹ * z = g * x * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = g * (x * t) * g⁻¹ := by rw [hz]; group
      _ = g * (t * x) * g⁻¹ := by rw [hxt]
      _ = (g * t * g⁻¹) * (g * x * g⁻¹) := by group
      _ = z * (g * x * g⁻¹) := by rw [hgt]
  · calc g * x * g⁻¹ * t = g * x * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = g * (x * z) * g⁻¹ := by rw [ht]; group
      _ = g * (z * x) * g⁻¹ := by rw [hxz]
      _ = (g * z * g⁻¹) * (g * x * g⁻¹) := by group
      _ = t * (g * x * g⁻¹) := by rw [hgz]

theorem conj_w_mem_B (d : Swap z t w) {x : G} (hx : x ∈ Bg z t) : w * x * w⁻¹ ∈ Bg z t :=
  conj_mem_B d.w1 d.w2 hx

theorem conj_winv_mem_B (d : Swap z t w) {x : G} (hx : x ∈ Bg z t) : w⁻¹ * x * w ∈ Bg z t := by
  have := conj_mem_B (g := w⁻¹) (by simpa using d.w1') (by simpa using d.w2') hx
  simpa using this

theorem w_sq_mem_B (d : Swap z t w) : w * w ∈ Bg z t := by
  have hz : w * w * z = z * (w * w) := by
    calc w * w * z = w * (w * z * w⁻¹) * w := by group
      _ = w * t * w := by rw [d.w1']
      _ = (w * t * w⁻¹) * w * w := by group
      _ = z * (w * w) := by rw [d.w2']; group
  have ht : w * w * t = t * (w * w) := by
    calc w * w * t = w * (w * t * w⁻¹) * w := by group
      _ = w * z * w := by rw [d.w2']
      _ = (w * z * w⁻¹) * w * w := by group
      _ = t * (w * w) := by rw [d.w1']; group
  exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hz,
    Subgroup.mem_centralizer_singleton_iff.mpr ht⟩

theorem N1_le_B : N1g z t ≤ Bg z t := fun _ hx => ⟨Uz_le_Hz z hx.1, hx.2⟩

theorem mem_N2 (x : G) : x ∈ N2g z t w ↔ w * x * w⁻¹ ∈ N1g z t := mem_conjugate_iff

theorem N2_le_B (d : Swap z t w) : N2g z t w ≤ Bg z t := by
  intro x hx
  have h1 : w * x * w⁻¹ ∈ Bg z t := N1_le_B ((mem_N2 x).1 hx)
  have h2 := d.conj_winv_mem_B h1
  have e : w⁻¹ * (w * x * w⁻¹) * w = x := by group
  rwa [e] at h2

theorem N1_normal {x n : G} (hx : x ∈ Bg z t) (hn : n ∈ N1g z t) : x * n * x⁻¹ ∈ N1g z t := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp (Hz_le_normalizer z hx.1) n).mp hn.1,
    Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
  have hnt : n * t = t * n := Subgroup.mem_centralizer_singleton_iff.mp hn.2
  have h1 : x⁻¹ * t * x = t := by
    calc x⁻¹ * t * x = x⁻¹ * (t * x) := by group
      _ = x⁻¹ * (x * t) := by rw [hxt]
      _ = t := by group
  have h2 : x * t * x⁻¹ = t := by
    calc x * t * x⁻¹ = (t * x) * x⁻¹ := by rw [hxt]
      _ = t := by group
  calc x * n * x⁻¹ * t = x * n * (x⁻¹ * t * x) * x⁻¹ := by group
    _ = x * (n * t) * x⁻¹ := by rw [h1]; group
    _ = x * (t * n) * x⁻¹ := by rw [hnt]
    _ = (x * t * x⁻¹) * (x * n * x⁻¹) := by group
    _ = t * (x * n * x⁻¹) := by rw [h2]

theorem N2_normal (d : Swap z t w) {x m : G} (hx : x ∈ Bg z t) (hm : m ∈ N2g z t w) :
    x * m * x⁻¹ ∈ N2g z t w := by
  rw [mem_N2] at hm ⊢
  have h1 := N1_normal (d.conj_w_mem_B hx) hm
  have : w * (x * m * x⁻¹) * w⁻¹ = (w * x * w⁻¹) * (w * m * w⁻¹) * (w * x * w⁻¹)⁻¹ := by group
  rw [this]
  exact h1

theorem mem_N1_inf_N2 (d : Swap z t w) (x : G) : x ∈ N1g z t ⊓ N2g z t w ↔ x ∈ Vg z t := by
  have hp := d.cm
  rw [hp.mem_Vg_iff₄]
  constructor
  · rintro ⟨h1, h2⟩
    have : x ∈ Uz z ⊓ CFSG.conjugate (Uz z) w :=
      Subgroup.mem_inf.mpr ⟨h1.1, mem_conjugate_iff.mpr (((mem_N2 x).1 h2).1)⟩
    exact (d.inter x).1 this
  · intro hx
    have hV : ∀ y, (y = 1 ∨ y = z ∨ y = t ∨ y = z * t) → y ∈ N1g z t := by
      intro y hy
      have hyU : y ∈ Uz z := by
        rcases hy with rfl | rfl | rfl | rfl
        · exact one_mem _
        · exact d.hyp.z_mem
        · exact d.ht.1
        · exact mul_mem d.hyp.z_mem d.ht.1
      refine ⟨hyU, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      rcases hy with rfl | rfl | rfl | rfl
      · simp
      · exact hp.comm
      · rfl
      · calc z * t * t = z * (t * t) := by group
          _ = z := by rw [hp.sq_t, mul_one]
          _ = z * (t * t) := by rw [hp.sq_t, mul_one]
          _ = (z * t) * t := by group
          _ = (t * z) * t := by rw [hp.comm]
          _ = t * (z * t) := by group
    refine ⟨hV x hx, (mem_N2 x).2 ?_⟩
    have hx' : w * x * w⁻¹ = 1 ∨ w * x * w⁻¹ = z ∨ w * x * w⁻¹ = t ∨ w * x * w⁻¹ = z * t := by
      rcases hx with rfl | rfl | rfl | rfl
      · left; group
      · right; right; left; exact d.w1'
      · right; left; exact d.w2'
      · right; right; right
        calc w * (z * t) * w⁻¹ = (w * z * w⁻¹) * (w * t * w⁻¹) := by group
          _ = z * t := by rw [d.w1', d.w2', hp.comm]
    exact hV _ hx'

end Swap

end CFSG.Quasithin.H13.U43
