module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937Defs
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Marking
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerCore
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType.NbrU63

open CFSG CFSG.Assembly CFSG.StandardType

variable {G : Type} [Group G]

theorem innerDiagOnLab_of_label {p : ℕ} {Bs K : Subgroup G}
    (hM : GGInnerDiagOnLabel GGNbrInner937U63Label p Bs K) :
    GGInnerDiagOnLab GGUnitDvd63Label p Bs K := by
  refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hM
  obtain ⟨hlab, hBN, hBI⟩ := hP
  refine ⟨hlab, ?_, hBN, hBI⟩
  obtain ⟨⟨ht, -, hpn, -⟩, -, -⟩ := hlab
  refine Or.inr (Or.inl ⟨?_, ?_, hpn⟩)
  · rw [ht]
    exact fun h => h
  · rw [ht]
    decide

variable [Finite G]

theorem card_range_ggGamma_mul_card_inf {Bs K : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card (ggGamma K hN).range * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) =
      Nat.card Bs := by
  have h1 := TableB.card_range_mul_card_ker (ggGamma K hN)
  have hker : (ggGamma K hN).ker = (Subgroup.centralizer (K : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff]
  have e : Nat.card ↥((Subgroup.centralizer (K : Set G)).subgroupOf Bs) =
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := by
    rw [← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rwa [hker, e] at h1

theorem card_rank_of_lt {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hlt : Nat.card (ggGamma K hN).range < 3 ^ 4) :
    Nat.card B = 3 ^ 4 ∧ LargeEvenTwoLocalRank 3 G ≤ 4 ∧
      Nat.card (ggGamma K hN).range = 3 ^ 3 := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBBs.trans hN
  have hS : LargeEvenSHat 3 B y K := hnb.1
  have hcB := card_range_ggGamma_mul_of_sHat hp hS hBN
  have hle : (ggGamma K hBN).range ≤ (ggGamma K hN).range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBBs b.2⟩, rfl⟩
  have hcle : Nat.card (ggGamma K hBN).range ≤ Nat.card (ggGamma K hN).range :=
    Subgroup.card_le_of_le hle
  have hBc : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hcfg.1.2.2.2.2.2.2.1.1.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank 3 G := hcfg.1.2.2.2.2.2.1.2.2.2
  have hm : LargeEvenTwoLocalRank 3 G = 4 := by
    by_contra hne
    have h5 : 3 ^ 5 ≤ Nat.card B := by
      rw [hBc]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hB4 : Nat.card B = 3 ^ 4 := by rw [hBc, hm]
  refine ⟨hB4, hm.le, ?_⟩
  have h27 : 3 ^ 3 ≤ Nat.card (ggGamma K hN).range := by
    have : Nat.card (ggGamma K hBN).range = 3 ^ 3 := by
      rw [hB4] at hcB
      omega
    omega
  have hBs3 : IsPGroup 3 Bs := fun g => ⟨1, Subtype.ext (by simpa using hBs.2 g g.2)⟩
  have hr3 : IsPGroup 3 (ggGamma K hN).range :=
    hBs3.of_surjective (ggGamma K hN).rangeRestrict (ggGamma K hN).rangeRestrict_surjective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hr3
  rw [hk] at hlt h27 ⊢
  have h1 : 3 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp h27
  have h2 : k < 4 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  rw [show k = 3 by omega]

end CFSG.StandardType.NbrU63

end
