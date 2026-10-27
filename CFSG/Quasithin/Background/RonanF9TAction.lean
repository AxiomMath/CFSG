module

public import CFSG.Quasithin.Background.G2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage

public section

namespace CFSG.Quasithin.RonanF9T

open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type*} [Group G]

noncomputable def tildeHom (X N : Subgroup G) (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    ↥X →* SecQuot (Subgroup.normalizer (N : Set G)) N :=
  (secMk (Subgroup.normalizer (N : Set G)) N).comp (Subgroup.inclusion hXN)

theorem tildeHom_mem (X N : Subgroup G) (hXN : X ≤ Subgroup.normalizer (N : Set G)) (x : ↥X) :
    tildeHom X N hXN x ∈ tildeOf N X :=
  secMk_mem_secImg (A := Subgroup.normalizer (N : Set G)) (B := N)
    (x := Subgroup.inclusion hXN x) x.2

theorem tildeHom_surjective (X N : Subgroup G) (hXN : X ≤ Subgroup.normalizer (N : Set G))
    (p : SecQuot (Subgroup.normalizer (N : Set G)) N) (hp : p ∈ tildeOf N X) :
    ∃ x : ↥X, tildeHom X N hXN x = p := by
  obtain ⟨a, ha, rfl⟩ := mem_secImg.1 hp
  exact ⟨⟨a, ha⟩, rfl⟩

theorem tilde_le_normalizer (X U N : Subgroup G) (hXU : X ≤ Subgroup.normalizer (U : Set G))
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    tildeOf N X ≤ Subgroup.normalizer ((tildeOf N U : Subgroup _) : Set _) := by
  intro p hp
  obtain ⟨a, ha, rfl⟩ := mem_secImg.1 hp
  exact secMk_mem_normalizer_secImg (A := Subgroup.normalizer (N : Set G)) (B := N)
    (X := U) (a := a) (hXU ha)

private theorem comm_mem_iff {N : Subgroup G} {x u : G}
    (hx : x ∈ Subgroup.normalizer (N : Set G)) (hu : u ∈ Subgroup.normalizer (N : Set G)) :
    (u * x)⁻¹ * (x * u) ∈ N ↔ x * u * x⁻¹ * u⁻¹ ∈ N := by
  have hg : u * x ∈ Subgroup.normalizer (N : Set G) := Subgroup.mul_mem _ hu hx
  rw [Subgroup.mem_normalizer_iff''.1 hg (x * u * x⁻¹ * u⁻¹)]
  have h : (u * x)⁻¹ * (x * u * x⁻¹ * u⁻¹) * (u * x) = (u * x)⁻¹ * (x * u) := by group
  rw [h]

theorem exists_hom_range_autOn (X U N : Subgroup G) (hXU : X ≤ Subgroup.normalizer (U : Set G))
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hUN : U ≤ Subgroup.normalizer (N : Set G)) :
    ∃ ρ : ↥X →* MulAut ↥(tildeOf N U),
      ρ.range = autOn (tildeOf N X) (tildeOf N U) ∧
      ∀ x : ↥X, ρ x = 1 ↔ ∀ u ∈ U, (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ N := by
  have hP := tilde_le_normalizer X U N hXU hXN
  let π : ↥X →* ↥(tildeOf N X) := (tildeHom X N hXN).codRestrict _ (tildeHom_mem X N hXN)
  have hπ : Function.Surjective π := by
    rintro ⟨p, hp⟩
    obtain ⟨x, hx⟩ := tildeHom_surjective X N hXN p hp
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨(Setup.rho (tildeOf N U) (tildeOf N X) hP).comp π, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hπ, ← MonoidHom.range_eq_map,
      Setup.range_rho]
  · intro x
    show Setup.rho _ _ hP (π x) = 1 ↔ _
    rw [Setup.rho_eq_one_iff hP (π x), Subgroup.mem_centralizer_iff]
    constructor
    · intro h u hu
      have hv : secMk (Subgroup.normalizer (N : Set G)) N ⟨u, hUN hu⟩ ∈ tildeOf N U :=
        secMk_mem_secImg hu
      have h1 := h _ hv
      have h2 : secMk (Subgroup.normalizer (N : Set G)) N
            (⟨u, hUN hu⟩ * Subgroup.inclusion hXN x) =
          secMk (Subgroup.normalizer (N : Set G)) N
            (Subgroup.inclusion hXN x * ⟨u, hUN hu⟩) := by
        rw [map_mul, map_mul]; exact h1
      exact (comm_mem_iff (hXN x.2) (hUN hu)).1 (secMk_eq_secMk_iff.1 h2)
    · intro h v hv
      obtain ⟨ua, hua, rfl⟩ := mem_secImg.1 hv
      have h3 := (comm_mem_iff (hXN x.2) ua.2).2 (h _ hua)
      show secMk (Subgroup.normalizer (N : Set G)) N ua *
          secMk (Subgroup.normalizer (N : Set G)) N (Subgroup.inclusion hXN x) =
        secMk (Subgroup.normalizer (N : Set G)) N (Subgroup.inclusion hXN x) *
          secMk (Subgroup.normalizer (N : Set G)) N ua
      rw [← map_mul, ← map_mul]
      exact secMk_eq_secMk_iff.2 h3

end CFSG.Quasithin.RonanF9T
