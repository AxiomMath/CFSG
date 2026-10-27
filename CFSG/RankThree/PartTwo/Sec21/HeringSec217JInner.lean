module

public import CFSG.RankThree.PartTwo.Sec21.Item223KFactsProofInsp
public import CFSG.RankThree.PartTwo.Sec21.Item211Res3ProofON

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

theorem j217_le_card_inf_of_inner {G : Type} [Group G] [Finite G] {A J : Subgroup G}
    (hAe : IsElemAbelian 3 A) (hmax : ∀ B : Subgroup G, IsElemAbelian 3 B → A ≤ B → B = A)
    (hAN : A ≤ Subgroup.normalizer (J : Set G))
    (hZ : Subgroup.center (lBar J) = ⊥) (hin : ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x J)
    (hAC : Nat.card (A ⊓ Sec4.thetaQuotCentralizer J : Subgroup G) ≤ 3)
    (hA81 : Nat.card A = 3 ^ 4) : 27 ≤ Nat.card (A ⊓ J : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  set β := Item223KFactsProof.innerHom hAN hin hZ with hβ
  have hB3 : ∀ b : A, b ^ 3 = 1 := fun b => Subtype.ext (by simpa using hAe.2 _ b.2)
  have hBc : ∀ b b' : A, b * b' = b' * b := fun b b' =>
    Subtype.ext (congrArg Subtype.val (hAe.1.is_comm.comm b b'))
  have hexp : ∀ z ∈ β.range, z ^ 3 = 1 := by
    rintro _ ⟨b, rfl⟩
    rw [← map_pow, hB3, map_one]
  have hker : Nat.card β.ker ≤ 3 := by
    have hle : (β.ker).map A.subtype ≤ A ⊓ Sec4.thetaQuotCentralizer J := by
      rintro _ ⟨b, hb, rfl⟩
      exact ⟨b.2, Item223KFactsProof.mem_thetaQuotCentralizer_of_mem_ker hAN hin hZ hb⟩
    rw [← Subgroup.card_map_of_injective A.subtype_injective]
    exact (Subgroup.card_le_of_le hle).trans hAC
  have hprod : Nat.card β.ker * Nat.card β.range = 81 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, hA81]
    norm_num
  have h27 : 27 ≤ Nat.card β.range := by
    have hpos : 0 < Nat.card β.ker := Nat.card_pos
    interval_cases (Nat.card β.ker) <;> omega
  have hlift : β.range ≤
      (A.subgroupOf J).map (QuotientGroup.mk' (aschbacherSolvableCore 3 J)) := by
    rintro _ ⟨b, rfl⟩
    have hfix : ∀ a (ha : a ∈ A), Item211Res2Proof.barAct J ⟨a, hAN ha⟩ (β b) = β b := by
      intro a ha
      have h1 := Item223KFactsProof.innerHom_conj hAN hin hZ ⟨a, ha⟩ (β b)
      have h2 : β ⟨a, ha⟩ * β b = β b * β ⟨a, ha⟩ := by
        rw [← map_mul, ← map_mul, hBc]
      have h3 : β ⟨a, ha⟩ * β b * (β ⟨a, ha⟩)⁻¹ = β b := by
        rw [h2]
        group
      exact h1.symm.trans h3
    obtain ⟨y, hy3, hyA, hyx⟩ :=
      Item211Res3Proof.exists_lift_of_fixed hAe hAN (hexp _ ⟨b, rfl⟩) hfix
    have hyA' : (y : G) ∈ A := Item211Res3Proof.mem_of_commute_of_maximal hAe hmax hy3 hyA
    have hyF : ((y : J) : lBar J) ∈
        (A.subgroupOf J).map (QuotientGroup.mk' (aschbacherSolvableCore 3 J)) :=
      ⟨y, Subgroup.mem_subgroupOf.mpr hyA', rfl⟩
    have hbz : β b ∈ Subgroup.zpowers ((y : J) : lBar J) := hyx ▸ Subgroup.mem_zpowers _
    exact Subgroup.zpowers_le.2 hyF hbz
  have hP3 : IsPGroup 3 (A.subgroupOf J) := hA3.comap_subtype
  have hcardmap := Item211Res3Proof.card_map_of_injOn _ _
    (CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hP3)
  have hle := Subgroup.card_le_of_le hlift
  rw [hcardmap] at hle
  have hcardinf : Nat.card (A ⊓ J : Subgroup G) = Nat.card (A.subgroupOf J) := by
    rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_subtype]
  rw [hcardinf]
  exact h27.trans hle

end CFSG.RankThree.PartTwo.Sec21
