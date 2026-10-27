module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bNorm2
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem a7_eNineF_conj_vOneF : ∀ i j : Fin 3, ∀ m : Fin 4, ∃ m' : Fin 4,
    KFacts.KP2.eNineF i j * KFacts.KP2.vOneF m * (KFacts.KP2.eNineF i j)⁻¹ =
      KFacts.KP2.vOneF m' := by
  decide +kernel

theorem a7_conj_mem_vOne_iff {g v : Equiv.Perm (Fin 7)} (hg : g ∈ KFacts.KP2.eNine) :
    g * v * g⁻¹ ∈ KFacts.KP2.vOne ↔ v ∈ KFacts.KP2.vOne := by
  have key : ∀ g ∈ KFacts.KP2.eNine, ∀ w ∈ KFacts.KP2.vOne,
      g * w * g⁻¹ ∈ KFacts.KP2.vOne := by
    rintro _ ⟨i, j, rfl⟩ _ ⟨m, rfl⟩
    obtain ⟨m', hm'⟩ := a7_eNineF_conj_vOneF i j m
    exact ⟨m', hm'⟩
  constructor
  · intro h
    have h' := key g⁻¹ (inv_mem hg) _ h
    have e : g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v := by group
    rwa [e] at h'
  · exact key g hg v

theorem a7_vOne_le_alternatingGroup : KFacts.KP2.vOne ≤ alternatingGroup (Fin 7) := by
  rintro _ ⟨m, rfl⟩
  exact (KFacts.KP2.vOneF_spec m).2

theorem a7_eNine_le_normalizer_vOne :
    KFacts.KP2.eNine.subgroupOf (alternatingGroup (Fin 7)) ≤
      Subgroup.normalizer
        ((KFacts.KP2.vOne.subgroupOf (alternatingGroup (Fin 7)) :
          Subgroup (alternatingGroup (Fin 7))) : Set (alternatingGroup (Fin 7))) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact (a7_conj_mem_vOne_iff (Subgroup.mem_subgroupOf.1 hx)).symm

theorem a7_card : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] <;>
    norm_num [Nat.factorial]

theorem a7_card_mulAut :
    Nat.card (MulAut (alternatingGroup (Fin 7))) = 5040 := by
  rw [← Nat.card_congr (MulEquiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num))).toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem a7_card_eNine :
    Nat.card (KFacts.KP2.eNine.subgroupOf (alternatingGroup (Fin 7))) = 9 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe KFacts.KP2.eNine_le_alternatingGroup).toEquiv,
    KFacts.KP2.card_eNine]

theorem a7_factorization_three : (Nat.card (alternatingGroup (Fin 7))).factorization 3 = 2 := by
  rw [a7_card, show (2520 : ℕ) = 3 ^ 2 * 280 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow
      Nat.prime_three, Finsupp.add_apply, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem norm2_alt7 : Norm2 (alternatingGroup (Fin 7)) := by
  have h4 : 4 ≤ Nat.card (Fin 7) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hZ : Subgroup.center (alternatingGroup (Fin 7)) = ⊥ :=
    alternatingGroup.center_eq_bot h4
  have hAut : Nat.card (MulAut (alternatingGroup (Fin 7))) ≤
      2 * Nat.card (alternatingGroup (Fin 7)) := by
    rw [a7_card_mulAut, a7_card] <;> norm_num
  have hcard : Nat.card (KFacts.KP2.eNine.subgroupOf (alternatingGroup (Fin 7))) =
      3 ^ (Nat.card (alternatingGroup (Fin 7))).factorization 3 := by
    rw [a7_factorization_three, a7_card_eNine] <;> norm_num
  have hleA : KFacts.KP2.vOne ≤ alternatingGroup (Fin 7) := a7_vOne_le_alternatingGroup
  have hcardV : Nat.card (KFacts.KP2.vOne.subgroupOf (alternatingGroup (Fin 7))) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hleA).toEquiv, KFacts.KP2.card_vOne]
  have hV0 : KFacts.KP2.vOne.subgroupOf (alternatingGroup (Fin 7)) ≠ ⊥ := by
    intro h
    have h1 := hcardV
    rw [h, Subgroup.card_bot] at h1
    norm_num at h1
  have hV2 : IsPGroup 2 (KFacts.KP2.vOne.subgroupOf (alternatingGroup (Fin 7))) :=
    IsPGroup.of_card (n := 2) (hcardV.trans (by norm_num))
  refine Norm2.of_inner hZ hAut (Sylow.ofCard (p := 3)
    (KFacts.KP2.eNine.subgroupOf (alternatingGroup (Fin 7))) hcard) ?_
  intro B hBS _
  exact ⟨KFacts.KP2.vOne.subgroupOf (alternatingGroup (Fin 7)), hV0, hV2,
    hBS.trans a7_eNine_le_normalizer_vOne⟩

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
