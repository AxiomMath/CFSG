module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.Quasithin.Vol2.Ch11SecAFactsFlag
public import CFSG.Quasithin.Vol2.Ch11SecAFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Quasithin.Vol2.Ch11.SecA (IsFlagW stabW mem_stabW)

variable {W : Type} [CommGroup W]

theorem isFlagW_fixedPoint (H : Subgroup (MulAut W)) (S : Sylow 2 ↥H) (q : ℕ) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    Nat.card (CFSG.fixedPointSubgroup ↥S W) = q →
      IsFlagW H ((S : Subgroup ↥H).map H.subtype) ⊥ q 1 (CFSG.fixedPointSubgroup ↥S W) := by
  intro hcard
  refine ⟨bot_le, ?_, ?_, ?_⟩
  · intro φ _ hcomm u hu
    rw [FixedPoints.mem_subgroup] at hu ⊢
    intro s
    change ((s : ↥H) : MulAut W) (φ u) = φ u
    have h1 : φ (((s : ↥H) : MulAut W) u) = ((s : ↥H) : MulAut W) (φ u) := by
      have h2 := hcomm (s : ↥H) (s : ↥H).2 u
      rw [Subgroup.mem_bot] at h2
      exact mul_inv_eq_one.mp h2
    have hsu : ((s : ↥H) : MulAut W) u = u := hu ⟨s, s.2⟩
    rw [← h1, hsu]
  · rw [Subgroup.relIndex_bot_left, hcard, pow_one]
  · intro p hp
    rw [Subgroup.mem_map] at hp
    obtain ⟨s, hs, rfl⟩ := hp
    rw [mem_stabW]
    intro u
    constructor
    · intro hu
      change (s : MulAut W) u ∈ CFSG.fixedPointSubgroup ↥S W
      have hsu : (s : MulAut W) u = u :=
        (FixedPoints.mem_subgroup (↥S) W u).mp hu ⟨s, hs⟩
      rwa [hsu]
    · intro hsu
      have hfix : u = (s : MulAut W) u := by
        have h1 : (⟨s, hs⟩⁻¹ : ↥S) • ((s : MulAut W) u) = (s : MulAut W) u :=
          (FixedPoints.mem_subgroup (↥S) W ((s : MulAut W) u)).mp hsu _
        have h2 : (⟨s, hs⟩⁻¹ : ↥S) • ((s : MulAut W) u) = u := by
          rw [show (s : MulAut W) u = ((⟨s, hs⟩ : ↥S) : MulAut W) u from rfl]
          exact inv_smul_smul _ _
        rw [h2] at h1
        exact h1
      rwa [hfix]

theorem isSylowTwoOf_map [Finite W] (H : Subgroup (MulAut W)) (S : Sylow 2 ↥H) :
    CFSG.QuasithinUnique.IsSylowTwoOf ((S : Subgroup ↥H).map H.subtype) H := by
  have hsub : ((S : Subgroup ↥H).map H.subtype).subgroupOf H = (S : Subgroup ↥H) := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  refine ⟨Subgroup.map_subtype_le (S : Subgroup ↥H), ?_, ?_⟩
  · exact S.isPGroup'.of_equiv
      (Subgroup.equivMapOfInjective (S : Subgroup ↥H) H.subtype H.subtype_injective)
  · rw [hsub]
    exact S.not_dvd_index

theorem pointStab_map_eq (H : Subgroup (MulAut W)) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    (pointStab H S).map H.subtype = H ⊓ stabW (CFSG.fixedPointSubgroup ↥S W) := by
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨h, hh, rfl⟩ := hx
    have hh' : h ∈ MulAction.stabilizer ↥H
        ((CFSG.fixedPointSubgroup ↥S W : Subgroup W) : Set W) := hh
    rw [Subgroup.mem_inf]
    refine ⟨h.2, ?_⟩
    rw [mem_stabW]
    intro u
    have hb := hh'
    rw [MulAction.mem_stabilizer_set] at hb
    exact (hb u).symm
  · intro hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxH, hxS⟩ := hx
    refine Subgroup.mem_map.2 ⟨⟨x, hxH⟩, ?_, rfl⟩
    show (⟨x, hxH⟩ : ↥H) ∈ MulAction.stabilizer ↥H
      ((CFSG.fixedPointSubgroup ↥S W : Subgroup W) : Set W)
    rw [MulAction.mem_stabilizer_set]
    intro b
    rw [mem_stabW] at hxS
    exact (hxS b).symm

theorem pow_two_eq_one_of_natEquiv {ι K : Type} [Field K] [CharP K 2]
    (e : W ≃* Multiplicative (ι → K)) (w : W) : w ^ 2 = 1 := by
  have h2 : (2 : ℕ) • (Multiplicative.toAdd (e w)) = 0 := by
    funext i
    simpa using CharTwo.two_nsmul (Multiplicative.toAdd (e w) i)
  apply e.injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, h2]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
