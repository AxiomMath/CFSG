module

public import CFSG.Quasithin.Recognition.Kleidman.F204.W2FFU1

public section

namespace CFSG.Quasithin.Kleidman.F204

open Subgroup

theorem mem_of_map_mem_of_ker {L N : Type*} [Group L] [Group N] (H : Subgroup L) (φ : L →* N)
    (hker : ∀ l : L, φ l = 1 → l ∈ H) (l : L) (hl : φ l ∈ H.map φ) : l ∈ H := by
  obtain ⟨h, hh, hφ⟩ := Subgroup.mem_map.mp hl
  have hk : h⁻¹ * l ∈ H := hker _ (by rw [map_mul, map_inv, hφ, inv_mul_cancel])
  simpa using H.mul_mem hh hk

theorem centralises_iff_phi_eq_one {G : Type*} [Group G] {V L : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (φ : L →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ)
    (hker : ∀ l : L, φ l = 1 → (l : G) ∈ Subgroup.centralizer (V : Set G))
    (hCL : ∀ v ∈ V, (∀ l : L, v * (l : G) = (l : G) * v) → v = 1)
    (hV1 : ∃ v ∈ V, v ≠ 1) (l : L) :
    (∀ v ∈ V, v * (l : G) = (l : G) * v) ↔ φ l = 1 := by
  classical
  let H : Subgroup L := (Subgroup.centralizer (V : Set G)).comap L.subtype
  have hmem : ∀ m : L, m ∈ H ↔ ∀ v ∈ V, v * (m : G) = (m : G) * v := by
    intro m
    exact Subgroup.mem_centralizer_iff
  have hnormal : H.Normal := by
    refine ⟨fun m hm g => ?_⟩
    rw [hmem] at hm ⊢
    intro v hv
    have hg : (g : G)⁻¹ * v * (g : G) ∈ V := by
      refine (Subgroup.mem_normalizer_iff.mp (hLV g.2) _).mpr ?_
      have e : (g : G) * ((g : G)⁻¹ * v * (g : G)) * (g : G)⁻¹ = v := by group
      rw [e]
      exact hv
    have hw := hm _ hg
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have e1 : v * ((g : G) * (m : G) * (g : G)⁻¹)
        = (g : G) * (((g : G)⁻¹ * v * (g : G)) * (m : G)) * (g : G)⁻¹ := by group
    have e2 : ((g : G) * (m : G) * (g : G)⁻¹) * v
        = (g : G) * ((m : G) * ((g : G)⁻¹ * v * (g : G))) * (g : G)⁻¹ := by group
    rw [e1, e2, hw]
  have hker' : ∀ k : L, φ k = 1 → k ∈ H := fun k hk =>
    (hmem k).mpr fun v hv => Subgroup.mem_centralizer_iff.mp (hker k hk) v hv
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have := Subgroup.Normal.map hnormal φ hφ
  rcases Subgroup.Normal.eq_bot_or_eq_top (H.map φ) with hb | ht
  · constructor
    · intro hc
      have h2 : φ l ∈ H.map φ := Subgroup.mem_map_of_mem φ ((hmem l).mpr hc)
      rw [hb, Subgroup.mem_bot] at h2
      exact h2
    · intro hφl
      exact (hmem l).mp (hker' l hφl)
  · exfalso
    have hall : ∀ m : L, m ∈ H := fun m =>
      mem_of_map_mem_of_ker H φ hker' m (by rw [ht]; exact Subgroup.mem_top _)
    obtain ⟨v, hv, hne⟩ := hV1
    exact hne (hCL v hv fun m => (hmem m).mp (hall m) v hv)

theorem fixed_inf_eq_bot {G : Type*} [Group G] {V L : Subgroup G}
    (φ : L →* alternatingGroup (Fin 5))
    (hker : ∀ l : L, φ l = 1 → (l : G) ∈ Subgroup.centralizer (V : Set G))
    (hCL : ∀ v ∈ V, (∀ l : L, v * (l : G) = (l : G) * v) → v = 1)
    {A₁ A₂ : Subgroup L} (hsup : A₁.map φ ⊔ A₂.map φ = ⊤)
    (v : G) (hv : v ∈ V) (h1 : ∀ a ∈ A₁, v * (a : G) = (a : G) * v)
    (h2 : ∀ a ∈ A₂, v * (a : G) = (a : G) * v) : v = 1 := by
  classical
  let S : Subgroup L := (Subgroup.centralizer ({v} : Set G)).comap L.subtype
  have hmemS : ∀ m : L, m ∈ S ↔ v * (m : G) = (m : G) * v := by
    intro m
    show (m : G) ∈ Subgroup.centralizer ({v} : Set G) ↔ _
    rw [Subgroup.mem_centralizer_iff]
    simp
  have hkerS : ∀ k : L, φ k = 1 → k ∈ S := fun k hk =>
    (hmemS k).mpr (Subgroup.mem_centralizer_iff.mp (hker k hk) v hv)
  have hA1 : A₁ ≤ S := fun a ha => (hmemS a).mpr (h1 a ha)
  have hA2 : A₂ ≤ S := fun a ha => (hmemS a).mpr (h2 a ha)
  have htop : S.map φ = ⊤ := by
    apply eq_top_iff.mpr
    rw [← hsup, ← Subgroup.map_sup]
    exact Subgroup.map_mono (sup_le hA1 hA2)
  have hall : ∀ m : L, m ∈ S := fun m =>
    mem_of_map_mem_of_ker S φ hkerS m (by rw [htop]; exact Subgroup.mem_top _)
  exact hCL v hv fun m => (hmemS m).mp (hall m)

theorem klein_fixed_inf_eq_bot {G : Type*} [Group G] {V L : Subgroup G}
    (φ : L →* alternatingGroup (Fin 5))
    (hker : ∀ l : L, φ l = 1 → (l : G) ∈ Subgroup.centralizer (V : Set G))
    (hCL : ∀ v ∈ V, (∀ l : L, v * (l : G) = (l : G) * v) → v = 1)
    {A₁ A₂ : Subgroup L} (h₁ : Nat.card (A₁.map φ) = 4) (h₂ : Nat.card (A₂.map φ) = 4)
    (hne : A₁.map φ ≠ A₂.map φ) (v : G) (hv : v ∈ V)
    (k1 : ∀ a ∈ A₁, v * (a : G) = (a : G) * v) (k2 : ∀ a ∈ A₂, v * (a : G) = (a : G) * v) :
    v = 1 :=
  fixed_inf_eq_bot φ hker hCL (klein_sup_eq_top h₁ h₂ hne) v hv k1 k2

end CFSG.Quasithin.Kleidman.F204

end
