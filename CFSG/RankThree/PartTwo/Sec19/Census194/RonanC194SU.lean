module

public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Core
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Unitary
public import CFSG.LocalAnalysis.SectionRank.EvenCover.CoverMap
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic
public import CFSG.RankThree.PartOne.S12.ModelTransport
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Extremal
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.RankThree.PartTwo.Sec19.Item194Used

public section

namespace CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

open CFSG CFSG.RankThree.PartTwo.Sec19

theorem evenSU_central_odd_extension_splitting_stated
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (hn : 2 ≤ n) (he : Even n) {E : Type*} [Group E] [Finite E]
    {π : E →* CFSG.Open.StatedSU n (2 ^ f) K} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    ∃ s : CFSG.Open.StatedSU n (2 ^ f) K →* E, (∀ g, π (s g) = g) ∧
      ∀ τ : CFSG.Open.StatedSU n (2 ^ f) K →* E, (∀ g, π (τ g) = g) → τ = s := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ε := CFSG.LieType.Universal.Unitary.equivStatedSU hK n
  set π' := ε.symm.toMonoidHom.comp π with hπ'
  have hker : π'.ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hπ', MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  have hπ's : Function.Surjective π' := ε.symm.surjective.comp hπ
  obtain ⟨s', hs', huniq, -⟩ :=
    CFSG.SectionRank.EvenCover.even_su_central_odd_extension_splitting hK hn he hπ's
      (hker ▸ hcen) (hker ▸ hodd)
  refine ⟨s'.comp ε.symm.toMonoidHom, fun g => ?_, fun τ hτ => ?_⟩
  · have h := hs' (ε.symm g)
    rw [hπ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact ε.symm.injective h
  · have h := huniq (τ.comp ε.toMonoidHom) fun g => by
      rw [hπ', MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.coe_toMonoidHom, hτ, MulEquiv.symm_apply_apply]
    ext g
    have := congrArg (· (ε.symm g)) h
    simpa using this

theorem evenSU_perfect_odd_cover_map
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (hn : 2 ≤ n) (he : Even n) {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (hodd : Odd (Nat.card (Subgroup.center L)))
    (e : L ⧸ Subgroup.center L ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU n (2 ^ f) K)) :
    ∃ φ : CFSG.Open.StatedSU n (2 ^ f) K →* L, Function.Surjective φ ∧
      φ.ker ≤ (CFSG.Open.StatedScalars (Fin n) K).subgroupOf (CFSG.Open.StatedSU n (2 ^ f) K) ∧
      ((CFSG.Open.StatedScalars (Fin n) K).subgroupOf (CFSG.Open.StatedSU n (2 ^ f) K)).map φ
        = Subgroup.center L := by
  obtain ⟨hsurj, hcen, hdvd⟩ := CFSG.SectionRank.EvenCover.pullbackFst_centralQuotientMap e
  obtain ⟨σ, hσ, -⟩ := evenSU_central_odd_extension_splitting_stated hK hn he hsurj hcen
    (Odd.of_dvd_nat hodd hdvd)
  exact CFSG.SectionRank.EvenCover.perfect_cover_map_of_section e σ hσ

theorem idPSU_holds :
    Census194IdPSU := by
  intro Y _ _ f hR hm hf
  have hproj := CFSG.RankThree.PartOne.projSU_of_statedClassicalModel hm
  obtain ⟨⟨-, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  haveI hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hchar : CharP K 2 :=
    CFSG.SectionRank.ClassicalOdd.charP_of_card (f := f * 2) (by rw [hK, pow_mul])
  haveI : Group.IsPerfect Y := hR.quasisimple.1
  have hodd : Odd (Nat.card (Subgroup.center Y)) := odd_card_center_of_pCore_eq_bot hR.pCore_two
  obtain ⟨φ, -, -, hmap⟩ :=
    evenSU_perfect_odd_cover_map (n := 4) hK (by norm_num) (by decide) hodd e
  have hcen : Subgroup.center Y = ⊥ := by
    rw [CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSU_four_eq_bot (K := K) (2 ^ f),
      Subgroup.map_bot] at hmap
    exact hmap.symm
  obtain ⟨e'⟩ := hproj
  have hiso := (mulEquivQuotientCenterOfEqBot hcen).trans e'
  rcases hf with rfl | rfl
  · exact Or.inr (Or.inl ⟨hiso⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hiso⟩))

end CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194
