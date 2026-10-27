module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)

@[expose] def KAdjConcl {G : Type} [Group G] (Kstar : Subgroup G) (t : G) (r m : ℕ) : Prop :=
  ∃ X₁ X₂ : Subgroup G, X₁ ≤ Kstar ∧ X₂ ≤ Kstar ∧
    (∀ N : Subgroup G, N ≤ Kstar → Kstar ≤ Subgroup.normalizer (N : Set G) →
        X₁ ≤ N → X₂ ≤ N → N = Kstar) ∧
    ∀ X : Subgroup G, (X = X₁ ∨ X = X₂) →
      IsSLn ↥X 2 m ∧ t ∈ Subgroup.normalizer (X : Set G) ∧
        ∃ d ∈ X, orderOf d = r ∧ ∀ x ∈ X, t * x * t⁻¹ = d * x * d⁻¹

private lemma isSLn_of_mulEquiv_A01 {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n a : ℕ}
    (h : IsSLn X n a) : IsSLn Y n a := by
  obtain ⟨K, hKf, hKfin, hcard, ⟨e'⟩⟩ := h
  exact ⟨K, hKf, hKfin, hcard, ⟨e.symm.trans e'⟩⟩

private lemma closure_map_A01 {G G' : Type} [Group G] [Group G'] (φ : G ≃* G')
    {Kstar X₁ X₂ : Subgroup G}
    (hN : ∀ N : Subgroup G, N ≤ Kstar → Kstar ≤ Subgroup.normalizer (N : Set G) →
      X₁ ≤ N → X₂ ≤ N → N = Kstar) :
    ∀ N' : Subgroup G', N' ≤ Kstar.map φ.toMonoidHom →
      Kstar.map φ.toMonoidHom ≤ Subgroup.normalizer (N' : Set G') →
      X₁.map φ.toMonoidHom ≤ N' → X₂.map φ.toMonoidHom ≤ N' →
      N' = Kstar.map φ.toMonoidHom := by
  intro N' hle hnorm hX₁ hX₂
  have hcomp : (φ.symm.toMonoidHom).comp φ.toMonoidHom = MonoidHom.id G := by
    ext x; simp
  have hcomp' : (φ.toMonoidHom).comp φ.symm.toMonoidHom = MonoidHom.id G' := by
    ext x; simp
  have hback : ∀ A : Subgroup G, (A.map φ.toMonoidHom).map φ.symm.toMonoidHom = A := by
    intro A; rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  have hback' : ∀ A : Subgroup G', (A.map φ.symm.toMonoidHom).map φ.toMonoidHom = A := by
    intro A; rw [Subgroup.map_map, hcomp', Subgroup.map_id]
  have h1 : N'.map φ.symm.toMonoidHom ≤ Kstar := by
    have h := Subgroup.map_mono (f := φ.symm.toMonoidHom) hle
    rwa [hback Kstar] at h
  have h2 : Kstar ≤ Subgroup.normalizer (N'.map φ.symm.toMonoidHom : Set G) := by
    have h := Subgroup.map_mono (f := φ.symm.toMonoidHom) hnorm
    rw [Subgroup.map_normalizer_eq_of_bijective (f := φ.symm.toMonoidHom) N' φ.symm.bijective,
      hback Kstar] at h
    exact h
  have h3 : X₁ ≤ N'.map φ.symm.toMonoidHom := by
    have h := Subgroup.map_mono (f := φ.symm.toMonoidHom) hX₁
    rwa [hback X₁] at h
  have h4 : X₂ ≤ N'.map φ.symm.toMonoidHom := by
    have h := Subgroup.map_mono (f := φ.symm.toMonoidHom) hX₂
    rwa [hback X₂] at h
  have hkey := hN (N'.map φ.symm.toMonoidHom) h1 h2 h3 h4
  have hfin := congrArg (fun A : Subgroup G => A.map φ.toMonoidHom) hkey
  rwa [hback' N'] at hfin

private lemma clause_map_A01 {G G' : Type} [Group G] [Group G'] (φ : G ≃* G')
    {Y : Subgroup G} {t : G} {r m : ℕ}
    (h : IsSLn ↥Y 2 m ∧ t ∈ Subgroup.normalizer (Y : Set G) ∧
      ∃ d ∈ Y, orderOf d = r ∧ ∀ x ∈ Y, t * x * t⁻¹ = d * x * d⁻¹) :
    IsSLn ↥(Y.map φ.toMonoidHom) 2 m ∧
      φ t ∈ Subgroup.normalizer (Y.map φ.toMonoidHom : Set G') ∧
      ∃ d ∈ Y.map φ.toMonoidHom, orderOf d = r ∧
        ∀ x ∈ Y.map φ.toMonoidHom, φ t * x * (φ t)⁻¹ = d * x * d⁻¹ := by
  obtain ⟨hSL, ht, d, hd, hdord, hconj⟩ := h
  refine ⟨isSLn_of_mulEquiv_A01 (φ.subgroupMap Y) hSL, ?_, ?_⟩
  · rw [← Subgroup.map_normalizer_eq_of_bijective (f := φ.toMonoidHom) Y φ.bijective]
    exact Subgroup.mem_map_of_mem φ.toMonoidHom ht
  · refine ⟨φ d, Subgroup.mem_map_of_mem φ.toMonoidHom hd, ?_, ?_⟩
    · rw [MulEquiv.orderOf_eq φ d, hdord]
    · rintro _ ⟨x, hx, rfl⟩
      simpa only [map_mul, map_inv, MulEquiv.coe_toMonoidHom] using congrArg φ (hconj x hx)

theorem kAdjConcl_map {G G' : Type} [Group G] [Group G'] (φ : G ≃* G')
    {Kstar : Subgroup G} {t : G} {r m : ℕ} (h : KAdjConcl Kstar t r m) :
    KAdjConcl (Kstar.map φ.toMonoidHom) (φ t) r m := by
  obtain ⟨X₁, X₂, h₁, h₂, hN, hX⟩ := h
  refine ⟨X₁.map φ.toMonoidHom, X₂.map φ.toMonoidHom, Subgroup.map_mono h₁,
    Subgroup.map_mono h₂, closure_map_A01 φ hN, ?_⟩
  intro X hXmem
  rcases hXmem with rfl | rfl
  · exact clause_map_A01 φ (hX X₁ (Or.inl rfl))
  · exact clause_map_A01 φ (hX X₂ (Or.inr rfl))

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
