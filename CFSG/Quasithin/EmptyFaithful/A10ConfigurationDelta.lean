module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationLocal
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationModel
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationFacts
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationClasses

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin S4 Wc

theorem D3_iff : ∀ w : Wc, D3 w = true ↔
    (w ≠ 1 ∧ w * w = 1 ∧ (w ∈ M1h ∨ w ∈ M2h) ∧ w ∉ A1) := by decide +kernel

theorem D4_iff : ∀ w : Wc, D4 w = true ↔
    (w.e = false ∧ D3 ⟨w.a, 1, false⟩ = true ∧ D3 ⟨1, w.b, false⟩ = true) := by decide +kernel

theorem D5_iff : ∀ w : Wc, D5 w = true ↔
    (w.e = false ∧ ((D3 ⟨w.a, 1, false⟩ = true ∧ D2 ⟨1, w.b, false⟩ = true) ∨
      (D2 ⟨w.a, 1, false⟩ = true ∧ D3 ⟨1, w.b, false⟩ = true))) := by decide +kernel

theorem M1h_eq : ∀ w ∈ M1h, w = ⟨w.a, 1, false⟩ := by
  rintro ⟨a, b, e⟩ ⟨he, -, hb⟩
  have he' : e = false := he
  subst he'
  have : b = 1 := Subgroup.mem_bot.1 hb
  subst this
  rfl

theorem M2h_eq : ∀ w ∈ M2h, w = ⟨1, w.b, false⟩ := by
  rintro ⟨a, b, e⟩ ⟨he, ha, -⟩
  have he' : e = false := he
  subst he'
  have : a = 1 := Subgroup.mem_bot.1 ha
  subst this
  rfl

theorem mem_M1h_mk (a : S4) : (⟨a, 1, false⟩ : Wc) ∈ M1h :=
  ⟨rfl, Subgroup.mem_top _, Subgroup.one_mem _⟩

theorem mem_M2h_mk (b : S4) : (⟨1, b, false⟩ : Wc) ∈ M2h :=
  ⟨rfl, Subgroup.one_mem _, Subgroup.mem_top _⟩

theorem mk_mul_mk (a b : S4) : (⟨a, 1, false⟩ : Wc) * ⟨1, b, false⟩ = ⟨a, b, false⟩ := by
  refine Wc.ext ?_ ?_ rfl <;> simp [mul_false]

theorem mk_mul_mk' (a b : S4) : (⟨1, b, false⟩ : Wc) * ⟨a, 1, false⟩ = ⟨a, b, false⟩ := by
  refine Wc.ext ?_ ?_ rfl <;> simp [mul_false]

variable {G : Type*} [Group G]

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

@[expose] def Δ₁ : Set G := conjClassIn M E.z
@[expose] def Δ₂ : Set G := conjClassIn M E.t
@[expose] def Δ₃ : Set G := {x | x ≠ 1 ∧ x * x = 1 ∧ (x ∈ E.M₁ ∨ x ∈ E.M₂) ∧ x ∉ E.A}
@[expose] def Δ₄ : Set G :=
  {x | ∃ i₁ ∈ E.M₁, ∃ i₂ ∈ E.M₂, i₁ ∈ E.Δ₃ ∧ i₂ ∈ E.Δ₃ ∧ x = i₁ * i₂}
@[expose] def Δ₅ : Set G :=
  {x | ∃ i j : G, ((i ∈ E.M₁ ∧ i ∈ E.Δ₃ ∧ j ∈ E.M₂ ∧ j ∈ E.Δ₂) ∨
    (i ∈ E.M₂ ∧ i ∈ E.Δ₃ ∧ j ∈ E.M₁ ∧ j ∈ E.Δ₂)) ∧ x = i * j}
theorem mem_map_ι {S : Subgroup Wc} {w : Wc} : E.ι w ∈ S.map E.ι ↔ w ∈ S :=
  Subgroup.mem_map_iff_mem E.injective

theorem ι_sq_eq_one {w : Wc} : E.ι w * E.ι w = 1 ↔ w * w = 1 := by
  rw [← map_mul, ← map_one E.ι]
  exact E.injective.eq_iff

theorem ι_eq_one {w : Wc} : E.ι w = 1 ↔ w = 1 := by
  rw [← map_one E.ι]
  exact E.injective.eq_iff

theorem Δ₁_eq_image : E.Δ₁ = E.ι '' {w | D1 w = true} := by
  unfold Δ₁ z
  rw [E.conjClassIn_M]
  congr 1
  ext y
  exact cls_z0 y

theorem Δ₂_eq_image : E.Δ₂ = E.ι '' {w | D2 w = true} := by
  unfold Δ₂ t
  rw [E.conjClassIn_M]
  congr 1
  ext y
  exact cls_t0 y

theorem Δ₃_eq_image : E.Δ₃ = E.ι '' {w | D3 w = true} := by
  ext x
  constructor
  · rintro ⟨hx1, hx2, hx3, hx4⟩
    have hxM : x ∈ M := by
      rcases hx3 with h | h
      · obtain ⟨w, -, rfl⟩ := h
        exact E.mem_M.2 ⟨w, rfl⟩
      · obtain ⟨w, -, rfl⟩ := h
        exact E.mem_M.2 ⟨w, rfl⟩
    obtain ⟨w, rfl⟩ := E.mem_M.1 hxM
    refine ⟨w, ?_, rfl⟩
    show D3 w = true
    rw [D3_iff]
    refine ⟨fun h => hx1 (by rw [h, map_one]), E.ι_sq_eq_one.1 hx2, ?_, fun h => hx4 ⟨w, h, rfl⟩⟩
    rcases hx3 with h | h
    · exact Or.inl ((E.mem_map_ι).1 h)
    · exact Or.inr ((E.mem_map_ι).1 h)
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := (D3_iff w).1 hw
    refine ⟨fun h => h1 (E.ι_eq_one.1 h), E.ι_sq_eq_one.2 h2, ?_, fun h => h4 ((E.mem_map_ι).1 h)⟩
    rcases h3 with h | h
    · exact Or.inl (Subgroup.mem_map_of_mem _ h)
    · exact Or.inr (Subgroup.mem_map_of_mem _ h)

theorem exists_of_mem_M₁ {x : G} (hx : x ∈ E.M₁) : ∃ a : S4, x = E.ι ⟨a, 1, false⟩ := by
  obtain ⟨w, hw, rfl⟩ := hx
  exact ⟨w.a, by rw [← M1h_eq w hw]⟩

theorem exists_of_mem_M₂ {x : G} (hx : x ∈ E.M₂) : ∃ b : S4, x = E.ι ⟨1, b, false⟩ := by
  obtain ⟨w, hw, rfl⟩ := hx
  exact ⟨w.b, by rw [← M2h_eq w hw]⟩

theorem ι_mk_mem_M₁ (a : S4) : E.ι ⟨a, 1, false⟩ ∈ E.M₁ := Subgroup.mem_map_of_mem _ (mem_M1h_mk a)
theorem ι_mk_mem_M₂ (b : S4) : E.ι ⟨1, b, false⟩ ∈ E.M₂ := Subgroup.mem_map_of_mem _ (mem_M2h_mk b)

theorem mem_Δ₃_iff {w : Wc} : E.ι w ∈ E.Δ₃ ↔ D3 w = true := by
  rw [E.Δ₃_eq_image]
  constructor
  · rintro ⟨w', hw', h⟩
    have := E.injective h
    rw [← this]
    exact hw'
  · intro h
    exact ⟨w, h, rfl⟩

theorem mem_Δ₂_iff {w : Wc} : E.ι w ∈ E.Δ₂ ↔ D2 w = true := by
  rw [E.Δ₂_eq_image]
  constructor
  · rintro ⟨w', hw', h⟩
    have := E.injective h
    rw [← this]
    exact hw'
  · intro h
    exact ⟨w, h, rfl⟩

theorem Δ₄_eq_image : E.Δ₄ = E.ι '' {w | D4 w = true} := by
  ext x
  constructor
  · rintro ⟨i₁, hi₁, i₂, hi₂, h₁, h₂, rfl⟩
    obtain ⟨a, rfl⟩ := E.exists_of_mem_M₁ hi₁
    obtain ⟨b, rfl⟩ := E.exists_of_mem_M₂ hi₂
    refine ⟨⟨a, b, false⟩, ?_, ?_⟩
    · show D4 ⟨a, b, false⟩ = true
      rw [D4_iff]
      exact ⟨rfl, E.mem_Δ₃_iff.1 h₁, E.mem_Δ₃_iff.1 h₂⟩
    · rw [← map_mul, mk_mul_mk]
  · rintro ⟨w, hw, rfl⟩
    have hw' := (D4_iff w).1 hw
    refine ⟨E.ι ⟨w.a, 1, false⟩, E.ι_mk_mem_M₁ _, E.ι ⟨1, w.b, false⟩, E.ι_mk_mem_M₂ _,
      E.mem_Δ₃_iff.2 hw'.2.1, E.mem_Δ₃_iff.2 hw'.2.2, ?_⟩
    rw [← map_mul, mk_mul_mk]
    congr 1
    exact Wc.ext rfl rfl hw'.1

theorem Δ₅_eq_image : E.Δ₅ = E.ι '' {w | D5 w = true} := by
  ext x
  constructor
  · rintro ⟨i, j, hij | hij, rfl⟩
    · obtain ⟨hi₁, hi₃, hj₂, hj₂'⟩ := hij
      obtain ⟨a, rfl⟩ := E.exists_of_mem_M₁ hi₁
      obtain ⟨b, rfl⟩ := E.exists_of_mem_M₂ hj₂
      refine ⟨⟨a, b, false⟩, ?_, ?_⟩
      · show D5 ⟨a, b, false⟩ = true
        rw [D5_iff]
        exact ⟨rfl, Or.inl ⟨E.mem_Δ₃_iff.1 hi₃, E.mem_Δ₂_iff.1 hj₂'⟩⟩
      · rw [← map_mul, mk_mul_mk]
    · obtain ⟨hi₂, hi₃, hj₁, hj₂'⟩ := hij
      obtain ⟨b, rfl⟩ := E.exists_of_mem_M₂ hi₂
      obtain ⟨a, rfl⟩ := E.exists_of_mem_M₁ hj₁
      refine ⟨⟨a, b, false⟩, ?_, ?_⟩
      · show D5 ⟨a, b, false⟩ = true
        rw [D5_iff]
        exact ⟨rfl, Or.inr ⟨E.mem_Δ₂_iff.1 hj₂', E.mem_Δ₃_iff.1 hi₃⟩⟩
      · rw [← map_mul]
        have : (⟨1, b, false⟩ : Wc) * ⟨a, 1, false⟩ = ⟨a, b, false⟩ := mk_mul_mk' a b
        rw [this]
  · rintro ⟨w, hw, rfl⟩
    have hw' := (D5_iff w).1 hw
    have hw'e : w = ⟨w.a, w.b, false⟩ := Wc.ext rfl rfl hw'.1
    rcases hw'.2 with ⟨h3, h2⟩ | ⟨h2, h3⟩
    · refine ⟨E.ι ⟨w.a, 1, false⟩, E.ι ⟨1, w.b, false⟩, Or.inl ⟨E.ι_mk_mem_M₁ _,
        E.mem_Δ₃_iff.2 h3, E.ι_mk_mem_M₂ _, E.mem_Δ₂_iff.2 h2⟩, ?_⟩
      rw [← map_mul, mk_mul_mk, ← hw'e]
    · refine ⟨E.ι ⟨1, w.b, false⟩, E.ι ⟨w.a, 1, false⟩, Or.inr ⟨E.ι_mk_mem_M₂ _,
        E.mem_Δ₃_iff.2 h3, E.ι_mk_mem_M₁ _, E.mem_Δ₂_iff.2 h2⟩, ?_⟩
      rw [← map_mul, mk_mul_mk', ← hw'e]

theorem Δ₄_isClass : ∃ u ∈ E.Δ₄, E.Δ₄ = conjClassIn M u := by
  refine ⟨E.ι u4, ?_, ?_⟩
  · rw [E.Δ₄_eq_image]
    exact ⟨u4, by decide +kernel, rfl⟩
  · rw [E.conjClassIn_M, E.Δ₄_eq_image]
    congr 1
    ext y
    exact (cls_u4 y).symm

theorem conj_mem_A2_of_mem_Th {v w : Wc} (hv : v ∈ Th) (hw : w ∈ A2) : v⁻¹ * w * v ∈ A2 := by
  have := (Subgroup.mem_normalizer_iff.mp (Th_le_normalizer_A2 (Th.inv_mem hv)) w).mp hw
  simpa using this

end Emb

end CFSG.Quasithin.A10
