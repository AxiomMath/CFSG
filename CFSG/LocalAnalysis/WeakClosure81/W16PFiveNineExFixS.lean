module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineExFix
public import CFSG.LocalAnalysis.WeakClosure81.W19ModE

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

namespace ExCfg

variable {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X} {p : ℕ}

private lemma inf_centralizer_map_comap_eq
    (hZ : ∀ q : ↥(conjClosure V H),
      φ q ∈ (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype →
      (q : G) ∈ centralizer (conjClosure V₀ (conjClosure V H) : Set G))
    (hK : ∀ q : ↥(conjClosure V H), φ q ∈ fusionOddCore X →
      (q : G) ∈ centralizer (conjClosure V₀ (conjClosure V H) : Set G) →
      φ q ∈ (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype) :
    centralizer (conjClosure V₀ (conjClosure V H) : Set G) ⊓
        Subgroup.map (conjClosure V H).subtype (Subgroup.comap φ (fusionOddCore X)) =
      Subgroup.map (conjClosure V H).subtype
        (Subgroup.comap φ ((Subgroup.center ↥(fusionOddCore X)).map
          (fusionOddCore X).subtype)) := by
  ext g
  constructor
  · intro hg
    obtain ⟨hgC, hgS⟩ := Subgroup.mem_inf.mp hg
    rw [Subgroup.mem_map] at hgS
    obtain ⟨k, hkN, rfl⟩ := hgS
    rw [Subgroup.mem_comap] at hkN
    rw [Subgroup.mem_map]
    exact ⟨k, Subgroup.mem_comap.mpr (hK k hkN hgC), rfl⟩
  · intro hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨k, hkZ, rfl⟩ := hg
    rw [Subgroup.mem_comap] at hkZ
    refine Subgroup.mem_inf.mpr ⟨hZ k hkZ, ?_⟩
    rw [Subgroup.mem_map]
    exact ⟨k, Subgroup.mem_comap.mpr
      (Subgroup.map_subtype_le (Subgroup.center ↥(fusionOddCore X)) hkZ), rfl⟩

theorem card_img_comap_eq (c : ExCfg M V₀ V U S H φ p)
    (D : ModDataE (conjClosure V H) (conjClosure V₀ (conjClosure V H)))
    (hZ : ∀ q : ↥(conjClosure V H),
      φ q ∈ (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype →
      (q : G) ∈ centralizer (conjClosure V₀ (conjClosure V H) : Set G))
    (hK : ∀ q : ↥(conjClosure V H), φ q ∈ fusionOddCore X →
      (q : G) ∈ centralizer (conjClosure V₀ (conjClosure V H) : Set G) →
      φ q ∈ (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype) :
    Nat.card (D.img (Subgroup.map (conjClosure V H).subtype
      (Subgroup.comap φ (fusionOddCore X)))) = p ^ 2 := by
  have hS : Subgroup.map (conjClosure V H).subtype
      (Subgroup.comap φ (fusionOddCore X)) ≤ conjClosure V H :=
    Subgroup.map_subtype_le _
  rw [D.card_img hS]
  rw [← Subgroup.inf_relIndex_right
    (centralizer (conjClosure V₀ (conjClosure V H) : Set G))
    (Subgroup.map (conjClosure V H).subtype (Subgroup.comap φ (fusionOddCore X)))]
  rw [inf_centralizer_map_comap_eq hZ hK]
  rw [Subgroup.relIndex_map_map_of_injective
    (f := (conjClosure V H).subtype) (hf := (conjClosure V H).subtype_injective)]
  rw [Subgroup.relIndex_comap]
  rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top_of_surjective φ c.bar.surjective,
    top_inf_eq]
  haveI := c.extra
  have hZc_le : (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype ≤
      fusionOddCore X := Subgroup.map_subtype_le _
  have hZc_card : Nat.card ((Subgroup.center ↥(fusionOddCore X)).map
      (fusionOddCore X).subtype) = p := by
    rw [Subgroup.card_subtype]
    exact IsExtraspecial.center_order_p p ↥(fusionOddCore X)
  have hrel : ((Subgroup.center ↥(fusionOddCore X)).map
        (fusionOddCore X).subtype).relIndex (fusionOddCore X) *
        Nat.card ((Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype) =
      Nat.card (fusionOddCore X) := by
    have h := Subgroup.relIndex_mul_card
      (H := (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype)
      (K := fusionOddCore X)
    rwa [inf_eq_left.mpr hZc_le] at h
  have hrelp : ((Subgroup.center ↥(fusionOddCore X)).map
        (fusionOddCore X).subtype).relIndex (fusionOddCore X) * p = p ^ 2 * p := by
    calc ((Subgroup.center ↥(fusionOddCore X)).map
          (fusionOddCore X).subtype).relIndex (fusionOddCore X) * p
        = ((Subgroup.center ↥(fusionOddCore X)).map
            (fusionOddCore X).subtype).relIndex (fusionOddCore X) *
              Nat.card ((Subgroup.center ↥(fusionOddCore X)).map
                (fusionOddCore X).subtype) := by rw [hZc_card]
      _ = Nat.card (fusionOddCore X) := hrel
      _ = p ^ 3 := c.card
      _ = p ^ 2 * p := by ring
  exact Nat.eq_of_mul_eq_mul_right c.prime.pos hrelp

end ExCfg

end CFSG.LocalAnalysis.WeakClosure81

end
