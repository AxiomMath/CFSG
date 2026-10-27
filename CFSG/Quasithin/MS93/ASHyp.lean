module

public import CFSG.Quasithin.MS93.SkHyp
public import CFSG.Quasithin.MS93.ASGroup
public import CFSG.Quasithin.MS93.ASSimple

public section

namespace CFSG.Quasithin.MS93

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G]

theorem isQuasisimple_of_rankTwo (hS : RankTwoLieSimple) {L : Subgroup G} (hL : ⁅L, L⁆ = L)
    (h : IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) :
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hperfL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
  have hP : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) := inferInstance
  have hsimp := hS _ h
  refine ⟨hP, hsimp, ?_⟩
  by_contra hab
  simp only [not_exists, ne_eq, not_not] at hab
  have hc : IsMulCommutative ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    ⟨⟨hab⟩⟩
  have hs : Subsingleton ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    Group.IsPerfect.subsingleton_of_isMulCommutative
  exact (not_subsingleton_iff_nontrivial.mpr hsimp.toNontrivial) hs

variable [Finite G]

theorem puHyp_of_msPair_of_simple (hS : RankTwoLieSimple) {G₀ R L : Subgroup G}
    (h : IsMSPair G₀ R) (hL : L ∈ cComp G₀) (hG : (G₀ : Set G) = (L : Set G) * (R : Set G)) :
    PUHyp G₀ R L := by
  have hLeq := isMSPair_eq_oddGen h hL hG
  have h2 := isMSPair_isPGroup_and_pCoreOf_le h
  have hne := isMSPair_ne_bot h
  obtain ⟨⟨hsqtk, hC, L', hL', hG', hrank⟩, -, hP⟩ := id h
  have hLL : L' = L := (isMSPair_eq_oddGen h hL' hG').trans hLeq.symm
  subst hLL
  have hnorm : G₀ ≤ Subgroup.normalizer (L' : Set G) := by
    rw [hLeq]
    exact le_normalizer_oddGen G₀
  exact
    { le := le_of_coe_eq_mul_right hG
      isPGroup := h2.1
      ne_bot := hne
      noChar := hP
      pCore_le := h2.2
      charTwo := hC
      L_le := le_of_coe_eq_mul_left hG
      le_normalizer := hnorm
      eq_sup := eq_sup_of_coe_eq_mul hG
      perfect := hL.2.1
      quasisimple := isQuasisimple_of_rankTwo hS hL.2.1 hrank
      rankTwo := hrank
      sqtk := hsqtk }

theorem puHyp_of_msPair
    {G₀ R L : Subgroup G}
    (h : IsMSPair G₀ R) (hL : L ∈ cComp G₀) (hG : (G₀ : Set G) = (L : Set G) * (R : Set G)) :
    PUHyp G₀ R L :=
  puHyp_of_msPair_of_simple rankTwoLieSimple_holds h hL hG

theorem isOddRadical_of_msPair {G₀ R : Subgroup G} (hRG : R ≤ G₀)
    (ha : ∃ H' : Subgroup G, H' < G₀ ∧ ¬ 2 ∣ H'.relIndex G₀ ∧ R = pCoreOf 2 H') :
    IsOddRadical G₀ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H', hlt, hodd, hR⟩ := ha
  have hHG : H' ≤ G₀ := hlt.le
  have hHN : H' ≤ G₀ ⊓ Subgroup.normalizer (R : Set G) := by
    refine le_inf hHG ?_
    rw [hR]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H'
  have hNodd : ¬ 2 ∣ (Subgroup.normalizer (R : Set G)).relIndex G₀ := by
    intro h2
    apply hodd
    have hdvd : (G₀ ⊓ Subgroup.normalizer (R : Set G)).relIndex G₀ ∣ H'.relIndex G₀ :=
      Subgroup.relIndex_dvd_of_le_left G₀ hHN
    rw [Subgroup.inf_relIndex_left] at hdvd
    exact h2.trans hdvd
  refine ⟨le_antisymm ?_ ?_, hNodd⟩
  ·
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_inf hRG Subgroup.le_normalizer)
      inf_le_right ?_
    rw [hR]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H'
  ·
    rw [hR]
    set N := G₀ ⊓ Subgroup.normalizer (pCoreOf 2 H' : Set G) with hN
    have hHN' : H' ≤ N := by rw [hN, ← hR]; exact hHN
    have hle : pCoreOf 2 N ≤ H' := by
      have hodd' : ¬ 2 ∣ H'.relIndex N := by
        intro h2
        apply hodd
        rw [← Subgroup.relIndex_mul_relIndex H' N G₀ hHN' inf_le_left]
        exact h2.trans (dvd_mul_right _ _)
      exact pCoreOf_le_of_odd_relIndex hHN' hodd'
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle
      (hHN'.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)

end CFSG.Quasithin.MS93
