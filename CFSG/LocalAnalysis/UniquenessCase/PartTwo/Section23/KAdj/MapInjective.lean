module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Concl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)

private lemma comap_le_of_le_map_E01 {G G' : Type} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) {Kstar : Subgroup G} {X' : Subgroup G'} (h : X' ≤ Kstar.map f) :
    X'.comap f ≤ Kstar := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (h (Subgroup.mem_comap.mp hx))
  rw [← hf hyx]
  exact hy

private lemma isSLn_of_mulEquiv_E01 {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n a : ℕ}
    (h : IsSLn X n a) : IsSLn Y n a := by
  obtain ⟨K, hKf, hKfin, hcard, ⟨e'⟩⟩ := h
  exact ⟨K, hKf, hKfin, hcard, ⟨e.symm.trans e'⟩⟩

private lemma kAdjData_comap_E01 {G G' : Type} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) {t : G} {r m : ℕ} {X' : Subgroup G'} (hX' : X' ≤ f.range)
    (h : IsSLn ↥X' 2 m ∧ f t ∈ Subgroup.normalizer (X' : Set G') ∧
      ∃ d ∈ X', orderOf d = r ∧ ∀ x ∈ X', f t * x * (f t)⁻¹ = d * x * d⁻¹) :
    IsSLn ↥(X'.comap f) 2 m ∧
      t ∈ Subgroup.normalizer ((X'.comap f : Subgroup G) : Set G) ∧
      ∃ d ∈ X'.comap f, orderOf d = r ∧
        ∀ x ∈ X'.comap f, t * x * t⁻¹ = d * x * d⁻¹ := by
  obtain ⟨hSL, ht, d', hd'mem, hd'ord, hconj'⟩ := h
  have hiso : ↥(X'.comap f) ≃* ↥X' :=
    (Subgroup.equivMapOfInjective (X'.comap f) f hf).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hX'))
  refine ⟨isSLn_of_mulEquiv_E01 hiso.symm hSL, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_comap, Subgroup.mem_comap]
    have hx' : f x ∈ X' ↔ f (t * x * t⁻¹) ∈ X' := by
      rw [map_mul, map_mul, map_inv]
      exact Subgroup.mem_normalizer_iff.mp ht (f x)
    exact hx'
  · have hd'mem' : d' ∈ (X'.comap f).map f := by
      rw [Subgroup.map_comap_eq_self hX']
      exact hd'mem
    obtain ⟨d, hdmem, hfd⟩ := Subgroup.mem_map.mp hd'mem'
    refine ⟨d, hdmem, ?_, ?_⟩
    · have hord : orderOf (f d) = r := by rw [hfd]; exact hd'ord
      exact (orderOf_injective f hf d).symm.trans hord
    · intro x hx
      have hx' : f x ∈ X' := Subgroup.mem_comap.mp hx
      apply hf
      simpa only [map_mul, map_inv, hfd] using hconj' (f x) hx'

private lemma closure_comap_E01 {G G' : Type} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) {Kstar : Subgroup G} {X₁' X₂' : Subgroup G'}
    (hX₁' : X₁' ≤ Kstar.map f) (hX₂' : X₂' ≤ Kstar.map f)
    (hcl : ∀ N' : Subgroup G', N' ≤ Kstar.map f →
      Kstar.map f ≤ Subgroup.normalizer (N' : Set G') → X₁' ≤ N' → X₂' ≤ N' →
      N' = Kstar.map f) :
    ∀ N : Subgroup G, N ≤ Kstar → Kstar ≤ Subgroup.normalizer (N : Set G) →
      X₁'.comap f ≤ N → X₂'.comap f ≤ N → N = Kstar := by
  intro N hN hnorm hX₁ hX₂
  have hN' : N.map f ≤ Kstar.map f := Subgroup.map_mono hN
  have hnorm' : Kstar.map f ≤ Subgroup.normalizer (N.map f : Set G') :=
    (Subgroup.map_mono (f := f) hnorm).trans (Subgroup.le_normalizer_map (H := N) f)
  have hX₁'map : X₁' ≤ N.map f := by
    have h : (X₁'.comap f).map f ≤ N.map f := Subgroup.map_mono hX₁
    rw [Subgroup.map_comap_eq_self (hX₁'.trans (Subgroup.map_le_range f Kstar))] at h
    exact h
  have hX₂'map : X₂' ≤ N.map f := by
    have h : (X₂'.comap f).map f ≤ N.map f := Subgroup.map_mono hX₂
    rw [Subgroup.map_comap_eq_self (hX₂'.trans (Subgroup.map_le_range f Kstar))] at h
    exact h
  exact Subgroup.map_injective hf (hcl (N.map f) hN' hnorm' hX₁'map hX₂'map)

theorem kAdjConcl_of_map_injective {G G' : Type} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) {Kstar : Subgroup G} {t : G} {r m : ℕ}
    (h : KAdjConcl (Kstar.map f) (f t) r m) : KAdjConcl Kstar t r m := by
  obtain ⟨X₁', X₂', h₁, h₂, hcl, hX⟩ := h
  refine ⟨X₁'.comap f, X₂'.comap f, comap_le_of_le_map_E01 f hf h₁,
    comap_le_of_le_map_E01 f hf h₂, ?_, ?_⟩
  · exact closure_comap_E01 f hf h₁ h₂ hcl
  · intro X hXmem
    rcases hXmem with rfl | rfl
    · exact kAdjData_comap_E01 f hf (h₁.trans (Subgroup.map_le_range f Kstar))
        (hX X₁' (Or.inl rfl))
    · exact kAdjData_comap_E01 f hf (h₂.trans (Subgroup.map_le_range f Kstar))
        (hX X₂' (Or.inr rfl))

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
