module

import CFSG.RankThree.PartTwo.Sec14.Ronan148BA6Sylow
import CFSG.GroupTheory.Commutator.SubgroupOf
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem exists_prime_lift {H L : Subgroup G} (hLH : L ≤ H)
    {As : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)}
    (hAs : As ≤ (L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))
    (hp : (Nat.card As).Prime) (hp2 : Nat.card As ≠ 2) :
    ∃ A : Subgroup G, A ≤ L ∧ Nat.card A = Nat.card As ∧
      (A.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) = As := by
  have hpp : Fact (Nat.card As).Prime := ⟨hp⟩
  have hp2' : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).exists_card_eq
  have hnotdvd : ¬ Nat.card As ∣ Nat.card ↥(CFSG.pCore 2 ↥H) := by
    intro hdvd
    rw [hk] at hdvd
    have h2 : Nat.card As ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact hp.ne_one h
    · exact hp2 h
  have hAsp : IsPGroup (Nat.card As) ↥As := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [pow_one]
  obtain ⟨P, hPU, hPp, hPmap, hPcard⟩ :=
    CFSG.RankThree.PartTwo.Sec14.Ronan148B.exists_le_map_eq_of_le_map hnotdvd hAs hAsp
  refine ⟨P.map H.subtype, ?_, ?_, ?_⟩
  · calc P.map H.subtype ≤ (L.subgroupOf H).map H.subtype := Subgroup.map_mono hPU
      _ = L ⊓ H := Subgroup.subgroupOf_map_subtype L H
      _ = L := inf_eq_left.mpr hLH
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hPcard]
  · have hP : (P.map H.subtype).subgroupOf H = P :=
      Subgroup.comap_map_eq_self (f := H.subtype) (H := P) (by simp)
    rw [hP, hPmap]

theorem normalizer_map_le_map {H A : Subgroup G} (hAH : A ≤ H) (hp : (Nat.card A).Prime)
    (hp2 : Nat.card A ≠ 2) :
    normalizer (((A.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) :
        Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ≤
      ((H ⊓ normalizer (A : Set G)).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
  have hpp : Fact (Nat.card A).Prime := ⟨hp⟩
  have hp2' : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAp : IsPGroup (Nat.card A) ↥(A.subgroupOf H) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [pow_one]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  have hAp' : Fact (IsPGroup (Nat.card A) ↥(A.subgroupOf H)) := ⟨hAp⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).exists_card_eq
  have hcop2 : Nat.Coprime (Nat.card A) 2 :=
    (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hcop : Nat.Coprime (Nat.card A) (Nat.card ↥(CFSG.pCore 2 ↥H)) := by
    rw [hk]
    exact hcop2.pow_right k
  have hEq := CFSG.normalizer_map_quotient_eq_map_normalizer (Nat.card A)
    (A.subgroupOf H) (CFSG.pCore 2 ↥H)
    (inferInstance : (CFSG.pCore 2 ↥H).Normal) hcop
  dsimp only at hEq
  have hnorm : normalizer ((A.subgroupOf H) : Set ↥H) =
      (H ⊓ normalizer (A : Set G)).subgroupOf H := by
    have h := CFSG.QuasithinUnique.map_subtype_normalizer (K := H) (X := A) hAH
    rw [← h]
    exact (Subgroup.comap_map_eq_self (f := H.subtype)
      (H := normalizer ((A.subgroupOf H) : Set ↥H)) (by simp)).symm
  rw [hEq, hnorm]

omit [Finite G] in
theorem normalizer_map_le_map_of_le {H R : Subgroup G} (hRH : R ≤ H)
    (hQR : CFSG.Open.pCoreOf 2 H ≤ R) :
    normalizer (((R.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) :
        Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ≤
      ((H ⊓ normalizer (R : Set G)).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).ker ≤ R.subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    intro n hn
    exact hQR (Subgroup.mem_map_of_mem H.subtype hn)
  have hcomap : (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (R.subgroupOf H)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) = R.subgroupOf H :=
    Subgroup.comap_map_eq_self hker
  intro g hg
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) g
  have hy : y ∈ normalizer ((R.subgroupOf H) : Set ↥H) := by
    have h1 : y ∈ Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
        (Subgroup.normalizer ((Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
          (R.subgroupOf H) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
          Set (↥H ⧸ CFSG.pCore 2 ↥H))) := hg
    rw [Subgroup.comap_normalizer_eq_of_surjective _
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H)), hcomap] at h1
    exact h1
  have hyG : (y : G) ∈ H ⊓ normalizer (R : Set G) := by
    have hm := CFSG.QuasithinUnique.map_subtype_normalizer (K := H) (X := R) hRH
    have h2 : (y : G) ∈ (normalizer ((R.subgroupOf H) : Set ↥H)).map H.subtype :=
      Subgroup.mem_map_of_mem H.subtype hy
    rwa [hm] at h2
  exact Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
    (Subgroup.mem_subgroupOf.mpr hyG)

omit [Finite G] in
theorem map_le_normalizer_map {H L W : Subgroup G} (hW : W ≤ normalizer (L : Set G)) :
    (W.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ≤
      normalizer (((L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) :
        Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
  CFSG.GroupTheory.map_subgroupOf_le_normalizer (M := H) (B := W) (X := L)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) hW

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
