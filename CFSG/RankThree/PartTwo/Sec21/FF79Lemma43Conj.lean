module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43Gen

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G]

private theorem cen_inv (x : G) : Cen x⁻¹ = Cen x := by
  ext c
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => by simpa using (Commute.inv_right (show Commute c x⁻¹ from h)).eq,
    fun h => (Commute.inv_right (show Commute c x from h)).eq⟩

theorem Good43.inv {σ x : G} (h : Good43 σ x) : Good43 σ x⁻¹ := by
  unfold Good43 at h ⊢
  rwa [cen_inv]

theorem Good43.of_mul_eq_one {σ x y : G} (hxy : x * y = 1) (h : Good43 σ x) : Good43 σ y := by
  rw [eq_inv_of_mul_eq_one_right hxy]; exact h.inv

theorem good43_map (φ : G ≃* G) {σ x : G} (h : Good43 σ x) : Good43 (φ σ) (φ x) := by
  have hcen : ∀ {x y : G}, y ∈ Cen x ↔ φ y ∈ Cen (φ x) := by
    intro x y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
      ← map_mul, ← map_mul, φ.injective.eq_iff]
  intro Q hQ hQle hQn
  let Q' : Subgroup G := Q.comap φ.toMonoidHom
  have hQ' : IsPGroup 2 Q' := by
    intro y
    obtain ⟨k, hk⟩ := hQ ⟨φ y, y.2⟩
    refine ⟨k, Subtype.ext (φ.injective ?_)⟩
    have := congrArg Subtype.val hk
    simpa [map_pow] using this
  have hmem : ∀ y ∈ Q', φ y ∈ Q := fun y hy => hy
  have hle : Q' ≤ Cen x ⊓ Cen σ := by
    intro y hy
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp (hQle (hmem y hy))
    exact Subgroup.mem_inf.mpr ⟨hcen.mpr h1, hcen.mpr h2⟩
  have hn : ∀ c ∈ Cen x ⊓ Cen σ, ∀ y ∈ Q', c * y * c⁻¹ ∈ Q' := by
    intro c hc y hy
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hc
    have := hQn (φ c) (Subgroup.mem_inf.mpr ⟨hcen.mp h1, hcen.mp h2⟩) (φ y) (hmem y hy)
    show φ (c * y * c⁻¹) ∈ Q
    simpa using this
  have key := h Q' hQ' hle hn
  intro q hq
  have hq' : φ.symm q ∈ Q' := by
    show φ (φ.symm q) ∈ Q
    simpa using hq
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (key hq')
  refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
  rw [← map_zpow, hi]
  simp

theorem good43_conj {σ x : G} (n : G) (h : Good43 (n⁻¹ * σ * n) x) :
    Good43 σ (n * x * n⁻¹) := by
  have := good43_map (MulAut.conj n) h
  rw [MulAut.conj_apply, MulAut.conj_apply] at this
  have e : n * (n⁻¹ * σ * n) * n⁻¹ = σ := by group
  rwa [e] at this

end CFSG.RankThree.PartTwo.Sec21.FF79
