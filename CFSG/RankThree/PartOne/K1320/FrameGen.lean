module

public import CFSG.RankThree.PartOne.K1320.Chain
public import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.PartOne

theorem conjBy_eq_self_of_mem' {G : Type} [Group G] {x : G} {L : Subgroup G} (hx : x ∈ L) :
    conjBy x L = L := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using L.mul_mem (L.mul_mem hx hy) (L.inv_mem hx)
  · intro y hy
    refine ⟨x⁻¹ * y * x, L.mul_mem (L.mul_mem (L.inv_mem hx) hy) hx, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem sup_eq_of_cover {G : Type} [Group G] {L : Subgroup G} {P M : Type} [Group P] [Group M]
    (ε : ↥L →* P) (hεi : Function.Injective ε) (hεs : Function.Surjective ε) (q : M →* P)
    (hq : Function.Surjective q) {K₀ K₁ : Subgroup G} (h₀ : K₀ ≤ L) (h₁ : K₁ ≤ L)
    {B₀ B₁ : Subgroup M} (hgen : B₀ ⊔ B₁ = ⊤) (hm₀ : (K₀.subgroupOf L).map ε = B₀.map q)
    (hm₁ : (K₁.subgroupOf L).map ε = B₁.map q) : K₀ ⊔ K₁ = L := by
  have hjoin : K₀.subgroupOf L ⊔ K₁.subgroupOf L = ⊤ := by
    refine Subgroup.map_injective hεi ?_
    rw [Subgroup.map_sup, hm₀, hm₁, ← Subgroup.map_sup, hgen, ← MonoidHom.range_eq_map,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hq, MonoidHom.range_eq_top.mpr hεs]
  refine le_antisymm (sup_le h₀ h₁) ?_
  intro y hy
  have hy' : (⟨y, hy⟩ : L) ∈ K₀.subgroupOf L ⊔ K₁.subgroupOf L := by
    rw [hjoin]
    exact Subgroup.mem_top _
  have h1 := Subgroup.mem_map_of_mem L.subtype hy'
  rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le h₀,
    Subgroup.map_subgroupOf_eq_of_le h₁] at h1

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem kZero_le_of_reflection (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E)
    {t : MulAut E} (ht : t ∈ reflectionSet p E) (htL : t ∈ torusImage E L) : kZero p E t ≤ L :=
  kZero_le_of_mem_torusImage h selected_prime_elements_normalize_theta_components htL
    (hF13.reflection t ht).1

omit [Finite G] in
theorem kZero_sup_of_pair {r₀ r₁ s s' : MulAut E} (hgen : kZero p E r₀ ⊔ kZero p E r₁ = L)
    (hconj : ∃ (x : G) (_ : x ∈ L) (hxE : x ∈ Subgroup.normalizer (E : Set G)),
      (s = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹ ∧
        s' = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹) ∨
      (s = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹ ∧
        s' = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹)) :
    kZero p E s ⊔ kZero p E s' = L := by
  obtain ⟨x, hxL, hxE, hcase⟩ := hconj
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, kZero_conj p r₀ hxE, kZero_conj p r₁ hxE, ← conjBy_sup, hgen,
      conjBy_eq_self_of_mem' hxL]
  · rw [h1, h2, kZero_conj p r₁ hxE, kZero_conj p r₀ hxE, ← conjBy_sup, sup_comm, hgen,
      conjBy_eq_self_of_mem' hxL]

end CFSG.RankThree.PartOne.K1320
