module

public import CFSG.Quasithin.EmptyFaithful.S152He5Over

public section

namespace CFSG.Quasithin

namespace IndexTwo

variable {P Y : Type*} [Group P] [Group Y]

@[expose] def extSub (c : P →* Y) (τ : Y) (φ : P ≃* P) (hφ : ∀ g, c (φ g) = τ * c g * τ⁻¹)
    (R : Subgroup P) (hsq : τ * τ ∈ R.map c) (hinv : ∀ g, g ∈ R ↔ φ g ∈ R) : Subgroup Y where
  carrier := {y | y ∈ R.map c ∨ y * τ⁻¹ ∈ R.map c}
  one_mem' := Or.inl (Subgroup.one_mem _)
  mul_mem' := by
    have hconj : ∀ r ∈ R.map c, τ * r * τ⁻¹ ∈ R.map c := by
      rintro _ ⟨g, hg, rfl⟩
      exact ⟨φ g, (hinv g).mp hg, hφ g⟩
    have hconj' : ∀ r ∈ R.map c, τ⁻¹ * r * τ ∈ R.map c := by
      rintro _ ⟨g, hg, rfl⟩
      refine ⟨φ.symm g, (hinv _).mpr (by simpa using hg), ?_⟩
      have := hφ (φ.symm g)
      rw [MulEquiv.apply_symm_apply] at this
      rw [this]; group
    intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl ((R.map c).mul_mem ha hb)
    · refine Or.inr ?_
      rw [mul_assoc]
      exact (R.map c).mul_mem ha hb
    · refine Or.inr ?_
      have : a * b * τ⁻¹ = (a * τ⁻¹) * (τ * b * τ⁻¹) := by group
      rw [this]
      exact (R.map c).mul_mem ha (hconj b hb)
    · refine Or.inl ?_
      have : a * b = (a * τ⁻¹) * (τ * (b * τ⁻¹) * τ⁻¹) * (τ * τ) := by group
      rw [this]
      exact (R.map c).mul_mem ((R.map c).mul_mem ha (hconj _ hb)) hsq
  inv_mem' := by
    have hconj' : ∀ r ∈ R.map c, τ⁻¹ * r * τ ∈ R.map c := by
      rintro _ ⟨g, hg, rfl⟩
      refine ⟨φ.symm g, (hinv _).mpr (by simpa using hg), ?_⟩
      have := hφ (φ.symm g)
      rw [MulEquiv.apply_symm_apply] at this
      rw [this]; group
    intro a ha
    rcases ha with ha | ha
    · exact Or.inl ((R.map c).inv_mem ha)
    · refine Or.inr ?_
      have h1 : (a * τ⁻¹)⁻¹ ∈ R.map c := (R.map c).inv_mem ha
      have h2 := hconj' _ h1
      have h3 : (τ * τ)⁻¹ ∈ R.map c := (R.map c).inv_mem hsq
      have : a⁻¹ * τ⁻¹ = (τ⁻¹ * (a * τ⁻¹)⁻¹ * τ) * (τ * τ)⁻¹ := by group
      rw [this]
      exact (R.map c).mul_mem h2 h3

end IndexTwo

open IndexTwo

variable {P Y : Type*} [Group P] [Group Y]

theorem OverBool2.of_index_two (c : P →* Y) (hc : Function.Injective c) (τ : Y) (φ : P ≃* P)
    (hφ : ∀ g, c (φ g) = τ * c g * τ⁻¹) (hτN : τ ∉ c.range)
    (hY : ∀ y : Y, y ∈ c.range ∨ y * τ⁻¹ ∈ c.range) {T : Subgroup Y} (hτT : τ ∈ T)
    {U : Subgroup P} (hU : T.comap c = U) {R₁ R₂ : Subgroup P} (h1 : U < R₁) (h2 : U < R₂)
    (h12 : ¬ R₁ ≤ R₂) (h21 : ¬ R₂ ≤ R₁)
    (hinv₁ : ∀ g, g ∈ R₁ ↔ φ g ∈ R₁) (hinv₂ : ∀ g, g ∈ R₂ ↔ φ g ∈ R₂)
    (hcl : ∀ R : Subgroup P, U ≤ R → (∀ g, g ∈ R ↔ φ g ∈ R) →
      R = U ∨ R = R₁ ∨ R = R₂ ∨ R = ⊤) : OverBool2 T := by
  have hτ2N : τ * τ ∈ c.range := by
    rcases hY (τ * τ) with h | h
    · exact h
    · exfalso
      apply hτN
      simpa using h
  have hτ2 : ∀ S : Subgroup Y, τ ∈ S → ∃ g, c g = τ * τ ∧ c g ∈ S := by
    intro S hS
    obtain ⟨g, hg⟩ := hτ2N
    exact ⟨g, hg, hg ▸ S.mul_mem hS hS⟩
  have hsqU : ∀ R : Subgroup P, U ≤ R → τ * τ ∈ R.map c := by
    intro R hR
    obtain ⟨g, hg, hgT⟩ := hτ2 T hτT
    exact ⟨g, hR (hU ▸ hgT), hg⟩
  have hcomapmem : ∀ (S : Subgroup Y) (y : Y), y ∈ c.range → y ∈ S → y ∈ (S.comap c).map c := by
    rintro S y ⟨g, rfl⟩ hy
    exact ⟨g, hy, rfl⟩
  have hreflect : ∀ S S' : Subgroup Y, τ ∈ S → τ ∈ S' → S.comap c ≤ S'.comap c → S ≤ S' := by
    intro S S' hτS hτS' hle y hy
    rcases hY y with hyN | hyN
    · obtain ⟨g, rfl⟩ := hyN
      exact hle hy
    · obtain ⟨g, hg⟩ := hyN
      have hgS : c g ∈ S := by rw [hg]; exact S.mul_mem hy (S.inv_mem hτS)
      have : c g ∈ S' := hle hgS
      have : y = c g * τ := by rw [hg]; group
      rw [this]
      exact S'.mul_mem ‹c g ∈ S'› hτS'
  have hinvS : ∀ S : Subgroup Y, τ ∈ S → ∀ g, g ∈ S.comap c ↔ φ g ∈ S.comap c := by
    intro S hτS g
    change c g ∈ S ↔ c (φ g) ∈ S
    rw [hφ g]
    constructor
    · intro h
      exact S.mul_mem (S.mul_mem hτS h) (S.inv_mem hτS)
    · intro h
      have := S.mul_mem (S.mul_mem (S.inv_mem hτS) h) hτS
      simpa [mul_assoc] using this
  have hext : ∀ (R : Subgroup P) (hRU : U ≤ R) (hinv : ∀ g, g ∈ R ↔ φ g ∈ R),
      ∃ C : Subgroup Y, T ≤ C ∧ C.comap c = R := by
    intro R hRU hinv
    refine ⟨extSub c τ φ hφ R (hsqU R hRU) hinv, ?_, ?_⟩
    · intro t ht
      rcases hY t with hyN | hyN
      · obtain ⟨g, rfl⟩ := hyN
        exact Or.inl ⟨g, hRU (hU ▸ ht), rfl⟩
      · obtain ⟨g, hg⟩ := hyN
        have hgT : c g ∈ T := by rw [hg]; exact T.mul_mem ht (T.inv_mem hτT)
        exact Or.inr ⟨g, hRU (hU ▸ hgT), hg⟩
    · ext g
      constructor
      · intro hg
        rcases (show c g ∈ R.map c ∨ c g * τ⁻¹ ∈ R.map c from hg) with h | h
        · obtain ⟨g', hg', hgg⟩ := h
          exact hc hgg ▸ hg'
        · exfalso
          apply hτN
          obtain ⟨g', -, hg'⟩ := h
          refine ⟨g'⁻¹ * g, ?_⟩
          rw [map_mul, map_inv, hg']
          group
      · intro hg
        exact Or.inl ⟨g, hg, rfl⟩
  obtain ⟨C₁, hTC₁, hC₁⟩ := hext R₁ h1.le hinv₁
  obtain ⟨C₂, hTC₂, hC₂⟩ := hext R₂ h2.le hinv₂
  have hτC₁ : τ ∈ C₁ := hTC₁ hτT
  have hτC₂ : τ ∈ C₂ := hTC₂ hτT
  refine ⟨C₁, C₂, ?_, ?_, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne hTC₁ fun hEq => ?_
    have : U = R₁ := by rw [← hU, hEq, hC₁]
    exact h1.ne this
  · refine lt_of_le_of_ne hTC₂ fun hEq => ?_
    have : U = R₂ := by rw [← hU, hEq, hC₂]
    exact h2.ne this
  · intro hle
    exact h12 (by rw [← hC₁, ← hC₂]; exact Subgroup.comap_mono hle)
  · intro hle
    exact h21 (by rw [← hC₁, ← hC₂]; exact Subgroup.comap_mono hle)
  · intro S hTS
    have hτS : τ ∈ S := hTS hτT
    have hUS : U ≤ S.comap c := hU ▸ Subgroup.comap_mono hTS
    rcases hcl (S.comap c) hUS (hinvS S hτS) with h | h | h | h
    · exact Or.inl (le_antisymm (hreflect S T hτS hτT (by rw [h, hU])) hTS)
    · exact Or.inr (Or.inl (le_antisymm (hreflect S C₁ hτS hτC₁ (by rw [h, hC₁]))
        (hreflect C₁ S hτC₁ hτS (by rw [h, hC₁]))))
    · exact Or.inr (Or.inr (Or.inl (le_antisymm (hreflect S C₂ hτS hτC₂ (by rw [h, hC₂]))
        (hreflect C₂ S hτC₂ hτS (by rw [h, hC₂])))))
    · refine Or.inr (Or.inr (Or.inr (eq_top_iff.mpr ?_)))
      exact hreflect ⊤ S (Subgroup.mem_top τ) hτS (by rw [Subgroup.comap_top, h])

end CFSG.Quasithin
