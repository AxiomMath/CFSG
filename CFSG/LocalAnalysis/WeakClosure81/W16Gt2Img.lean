module

public import CFSG.LocalAnalysis.WeakClosure81.W18PackMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.SignalizerFunctorTheorem.Quadratic
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace ModDataE

variable {J E : Subgroup G} (M : ModDataE J E)

private theorem ker_eq_inf_centralizer :
    M.ρ.ker = (J ⊓ centralizer (E : Set G)).subgroupOf J := by
  ext j
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨j.2, (M.ρ_eq_one_iff j).1 h⟩, fun h => (M.ρ_eq_one_iff j).2 h.2⟩

theorem ρ_mem_img_iff {S : Subgroup G} (hS : S ≤ J) {x : G} (hx : x ∈ J) :
    M.ρ ⟨x, hx⟩ ∈ M.img S ↔ x ∈ S ⊔ (J ⊓ centralizer (E : Set G)) := by
  have hker := M.ker_eq_inf_centralizer
  unfold img
  rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, hker,
    ← Subgroup.subgroupOf_sup hS inf_le_left]
  exact Subgroup.mem_subgroupOf

theorem img_le_img_iff {S T : Subgroup G} (hS : S ≤ J) (hT : T ≤ J) :
    M.img S ≤ M.img T ↔ S ≤ T ⊔ (J ⊓ centralizer (E : Set G)) := by
  constructor
  · intro h s hs
    exact (M.ρ_mem_img_iff hT (hS hs)).1 (h (M.mem_img.2 ⟨⟨s, hS hs⟩, hs, rfl⟩))
  · intro h r hr
    obtain ⟨j, hjS, rfl⟩ := M.mem_img.1 hr
    exact (M.ρ_mem_img_iff hT j.2).2 (h hjS)

theorem exists_normal_preimage_of_pGroup {A : Subgroup (LGL 2 M.W)} (hA : A ≤ M.img J)
    (hAn : (A.subgroupOf (M.img J)).Normal) (hAp : IsPGroup 2 A) :
    ∃ X : Subgroup G, J ⊓ centralizer (E : Set G) ≤ X ∧ X ≤ J ∧ (X.subgroupOf J).Normal ∧
      (∃ k : ℕ, (J ⊓ centralizer (E : Set G)).relIndex X = 2 ^ k) ∧ M.img X = A := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, hXJ, hCX, hXimg⟩ := M.exists_preimage (A := J) le_rfl hA
  have hXY : X = (A.comap M.ρ).map J.subtype := by
    apply le_antisymm
    · intro x hx
      refine Subgroup.mem_map.2 ⟨⟨x, hXJ hx⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap, ← hXimg]
      exact M.mem_img.2 ⟨⟨x, hXJ hx⟩, hx, rfl⟩
    · intro y hy
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hy
      rw [Subgroup.mem_comap] at hj
      have h1 : (j : G) ∈ X ⊔ (J ⊓ centralizer (E : Set G)) :=
        (M.ρ_mem_img_iff hXJ j.2).1 (by rwa [hXimg])
      rwa [sup_eq_left.2 hCX] at h1
  have hconjA : ∀ {g a : LGL 2 M.W}, g ∈ M.img J → a ∈ A → g * a * g⁻¹ ∈ A := by
    intro g a hg ha
    have h := hAn.conj_mem (⟨a, hA ha⟩ : ↥(M.img J))
      (by rwa [Subgroup.mem_subgroupOf]) (⟨g, hg⟩ : ↥(M.img J))
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  refine ⟨X, hCX, hXJ, ?_, ?_, hXimg⟩
  · rw [Subgroup.normal_subgroupOf_iff hXJ]
    intro h k hh hk
    rw [hXY]
    refine Subgroup.mem_map.2 ⟨⟨k, hk⟩ * ⟨h, hXJ hh⟩ * ⟨k, hk⟩⁻¹, ?_, rfl⟩
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hconjA (M.mem_img.2 ⟨⟨k, hk⟩, hk, rfl⟩) (by
      rw [← hXimg]
      exact M.mem_img.2 ⟨⟨h, hXJ hh⟩, hh, rfl⟩)
  · obtain ⟨k, hk⟩ := hAp.exists_card_eq
    refine ⟨k, ?_⟩
    have hsub : (J ⊓ centralizer (E : Set G)).subgroupOf X =
        (centralizer (E : Set G)).subgroupOf X := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨hXJ x.2, h⟩⟩
    have hrel : (J ⊓ centralizer (E : Set G)).relIndex X = Nat.card A := by
      rw [Subgroup.relIndex, hsub]
      change (centralizer (E : Set G)).relIndex X = Nat.card A
      rw [← M.card_img hXJ, hXimg]
    rw [hrel, hk]

end ModDataE

end CFSG.LocalAnalysis.WeakClosure81

end
