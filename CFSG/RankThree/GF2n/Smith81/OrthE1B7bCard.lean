module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

theorem b7b_card_map_mul_card_ker {H Γ : Type*} [Group H] [Group Γ] (ρ : H →* Γ)
    (L : Subgroup H) : Nat.card (L.map ρ) * Nat.card ↥(L ⊓ ρ.ker) = Nat.card L := by
  rw [inf_comm, ← Subgroup.relIndex_ker]
  exact Subgroup.relIndex_mul_card ρ.ker L

theorem b7b_card_sup_mul_card_inf {G : Type*} [Group G] {A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hN : (B.subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2
      (sup_le hA Subgroup.le_normalizer)
  have h1 := Subgroup.relIndex_sup_right (A.subgroupOf (A ⊔ B)) (B.subgroupOf (A ⊔ B))
  rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
    Subgroup.relIndex_subgroupOf le_rfl, Subgroup.relIndex_subgroupOf le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card B (A ⊔ B)
  have h3 := Subgroup.relIndex_mul_card B A
  rw [inf_eq_left.2 le_sup_right, h1] at h2
  rw [← h2, ← h3, inf_comm B A]
  ring

theorem b7b_card_LB_of_split (hSplit : RtSplitStatement)
    {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G} (hH : E1Hyp M Q Z B t) :
    Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ 3 := by
  obtain ⟨hNL, hNX, hNXR, hXnorm, -, hLdec, hcardLX, -, -⟩ := hSplit G M Q Z B t hH
  have hcardN : Nat.card (Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z := hH.case.2.1
  have hnorm : Nt M (LB M Q B) t ≤
      Subgroup.normalizer ((LB M Q B ⊓ E1Xpre M Q B t : Subgroup G) : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun n hn x hx => ?_
    have hnR : n ∈ Rt M (LB M Q B) t := hNXR ▸ Subgroup.mem_sup_left hn
    exact ⟨(LB M Q B).mul_mem ((LB M Q B).mul_mem (hNL hn) hx.1) ((LB M Q B).inv_mem (hNL hn)),
      hXnorm n hnR x hx.2⟩
  have hinf : Nt M (LB M Q B) t ⊓ (LB M Q B ⊓ E1Xpre M Q B t) = Q := by
    rw [← inf_assoc, inf_eq_left.2 hNL, hNX]
  have hprod := b7b_card_sup_mul_card_inf hnorm
  rw [← hLdec, hinf, hcardN, hcardLX] at hprod
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hQpos ?_
  rw [hprod]
  ring

end CFSG.RankThree.GF2n.Smith81.Smith23E1

end
