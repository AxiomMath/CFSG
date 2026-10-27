module

public import CFSG.RankThree.PartTwo.Sec15.Item15Steps
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofDefs
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Proof1521

omit [Finite G] in
theorem commutator_zpowers_eq_of_subset_mul {S K : Subgroup G} {c : G} (hSK : S ≤ K)
    (hK : (K : Set G) ⊆ (S : Set G) * (Subgroup.centralizer ({c} : Set G) : Set G)) :
    ⁅K, Subgroup.zpowers c⁆ = ⁅S, Subgroup.zpowers c⁆ := by
  refine le_antisymm ?_ (Subgroup.commutator_mono hSK le_rfl)
  refine Subgroup.commutator_le.mpr fun k hk g hg => ?_
  obtain ⟨s, hs, z, hz, rfl⟩ := Set.mem_mul.mp (hK hk)
  have hzc : Commute z c := Subgroup.mem_centralizer_singleton_iff.mp hz
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hzg : z * g = g * z := by
    rw [← hn]
    exact (hzc.zpow_right n).eq
  have hcomm : ⁅s * z, g⁆ = ⁅s, g⁆ := by
    calc
      ⁅s * z, g⁆ = s * (z * g) * z⁻¹ * s⁻¹ * g⁻¹ := by
        rw [commutatorElement_def]
        group
      _ = s * (g * z) * z⁻¹ * s⁻¹ * g⁻¹ := by rw [hzg]
      _ = ⁅s, g⁆ := by
        rw [commutatorElement_def]
        group
  rw [hcomm]
  exact Subgroup.commutator_mem_commutator hs hg

omit [Finite G] in
theorem le_normalizer_commutator_of_subset_mul {S K : Subgroup G} {c : G} (hSK : S ≤ K)
    (hK : (K : Set G) ⊆ (S : Set G) * (Subgroup.centralizer ({c} : Set G) : Set G)) :
    K ≤ Subgroup.normalizer ((⁅S, Subgroup.zpowers c⁆ : Subgroup G) : Set G) := by
  rw [← commutator_zpowers_eq_of_subset_mul hSK hK]
  exact Subgroup.normalizer_commutator_ge_left K (Subgroup.zpowers c)

theorem pCoreOf_two_le_of_mem_qStar {A : Subgroup G} (hA : Late.IsE27 A)
    (h146 : Item146 A (lB A)) {Y S : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    (hO : CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A)) : CFSG.Open.pCoreOf 2 Y ≤ S := by
  obtain ⟨⟨hSq, -⟩, hSpi⟩ := hS.prop
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hSpi
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hSO : S ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    hSY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hSOq : S ⊔ CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) :=
    sup_mem_scriptQ_of_item146 hA h146 hSq hO hSO
  have hSOpi : S ⊔ CFSG.Open.pCoreOf 2 Y ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨hSOq, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
      (IsPGroup.to_sup_of_normal_right' hS2 hO2 hSO)⟩
  exact le_sup_right.trans (hS.2 hSOpi le_sup_left)

theorem data1519_map_conj {A L : Subgroup G} {p : ℕ} {P : Subgroup G}
    (hP : Data1519 A (lB A) L p P) {g : G} (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) :
    Data1519 A (lB A) L p (P.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hp, hp3, hm, hEA, hcard, hPq, hbound⟩ := hP
  refine ⟨hp, hp3, hm, ?_, ?_, ?_, hbound⟩
  · exact CFSG.Open.IsElemAbelian.map hEA (MulAut.conj g).toMonoidHom
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  · have h := CFSG.RankThree.PartTwo.Sec17.HeadProof.map_conj_mem_scriptQPi hgA hPq
    rwa [CFSG.RankThree.PartTwo.Late.map_conj_eq_of_mem_normalizer hgL] at h

end Proof1521

end CFSG.RankThree.PartTwo.Sec15
