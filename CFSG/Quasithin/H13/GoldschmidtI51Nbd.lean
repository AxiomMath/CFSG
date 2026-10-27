module

public import CFSG.Quasithin.H13.GoldschmidtI51GQLoc

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {D : DType} {Gs : Fin 3 → Subgroup G}

@[expose] def Nbd (Gs : Fin 3 → Subgroup G) : Set G :=
  {g | ∃ a ∈ Gs 0, ∃ s ∈ Gs 1, ∃ c ∈ Gs 0, g = a * s * c}

omit [Finite G] in
theorem G0_mul_Nbd {a n : G} (ha : a ∈ Gs 0) (hn : n ∈ Nbd Gs) : a * n ∈ Nbd Gs := by
  obtain ⟨x, hx, s, hs, c, hc, rfl⟩ := hn
  exact ⟨a * x, (Gs 0).mul_mem ha hx, s, hs, c, hc, by group⟩

omit [Finite G] in
theorem Nbd_mul_G0 {a n : G} (ha : a ∈ Gs 0) (hn : n ∈ Nbd Gs) : n * a ∈ Nbd Gs := by
  obtain ⟨x, hx, s, hs, c, hc, rfl⟩ := hn
  exact ⟨x, hx, s, hs, c * a, (Gs 0).mul_mem hc ha, by group⟩

omit [Finite G] in
theorem G0_sub_Nbd {g : G} (hg : g ∈ Gs 0) : g ∈ Nbd Gs :=
  ⟨g, hg, 1, (Gs 1).one_mem, 1, (Gs 0).one_mem, by group⟩

omit [Finite G] in
theorem G1_sub_Nbd {g : G} (hg : g ∈ Gs 1) : g ∈ Nbd Gs :=
  ⟨1, (Gs 0).one_mem, g, hg, 1, (Gs 0).one_mem, by group⟩

omit [Finite G] in
theorem Nbd_inv {n : G} (hn : n ∈ Nbd Gs) : n⁻¹ ∈ Nbd Gs := by
  obtain ⟨x, hx, s, hs, c, hc, rfl⟩ := hn
  exact ⟨c⁻¹, (Gs 0).inv_mem hc, s⁻¹, (Gs 1).inv_mem hs, x⁻¹, (Gs 0).inv_mem hx, by group⟩

theorem G2_sub_Nbd (hD : IsDSystem D Gs) {g : G} (hg : g ∈ Gs 2) : g ∈ Nbd Gs := by
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := loc2_fano hD g hg
  exact ⟨a, ha.1, b, hb.1, c, hc.1, rfl⟩

theorem near_collinear {Gs : Fin 3 → Subgroup G} (hD : IsDSystem D Gs) {u s t : G}
    (hu : Nr Gs u) (hs : s ∈ Gs 1) (ht : t ∈ Gs 1) : s⁻¹ * u * t ∈ Nbd Gs := by
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hu
  obtain ⟨x1, hx1, x2, hx2, hsa⟩ :=
    loc1_prod2 hD (s⁻¹ * a) ((Gs 1).mul_mem ((Gs 1).inv_mem hs) ha.2)
  obtain ⟨y2, hy2, y1, hy1, hct⟩ := loc1_prod2' hD (c * t) ((Gs 1).mul_mem hc.2 ht)
  have e : s⁻¹ * (a * b * c) * t = x1 * (x2 * b * y2) * y1 := by
    calc s⁻¹ * (a * b * c) * t = (s⁻¹ * a) * b * (c * t) := by group
      _ = (x1 * x2) * b * (y2 * y1) := by rw [hsa, hct]
      _ = x1 * (x2 * b * y2) * y1 := by group
  rw [e]
  have h2 : x2 * b * y2 ∈ Gs 2 :=
    (Gs 2).mul_mem ((Gs 2).mul_mem hx2.2 hb.2) hy2.2
  exact Nbd_mul_G0 hy1.1 (G0_mul_Nbd hx1.1 (G2_sub_Nbd hD h2))

end CFSG.Quasithin.H13.I51
