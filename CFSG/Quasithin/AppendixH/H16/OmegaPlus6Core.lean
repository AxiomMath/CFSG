module

public import CFSG.LargeExtraspecial.O62Basic
public import CFSG.LargeExtraspecial.S45QOmegaMinus

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16.OmegaPlus6

open Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62
  CFSG.RankThree.OrthogonalInvolutions

theorem finrank_V₀ : finrank (ZMod 2) V₀ = 6 := Module.finrank_fin_fun (ZMod 2)

private theorem card_filter_qPlus_zero : (Finset.univ.filter (fun v : V₀ =>
    v 0 * v 1 + v 2 * v 3 + v 4 * v 5 = 0)).card = 36 := by
  decide +kernel

theorem ncard_qPlus_zero : {v : V₀ | qPlus v = 0}.ncard = 36 := by
  rw [Set.ncard_eq_toFinset_card']
  simp only [qPlus_apply, Set.toFinset_ofPred]
  exact card_filter_qPlus_zero

theorem card_orthogonalGroup_qPlus :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup qPlus) = 40320 := by
  have h := S12DW.card_orthogonalGroup_mul_ncard_eq qPlus_nondegenerate (m := 3)
    (by rw [finrank_V₀])
  have h2 : 2 ^ (3 ^ 2) * ∏ j ∈ Finset.Icc 1 3, (2 ^ (2 * j) - 1) = 1451520 := by decide
  rw [h2, ncard_qPlus_zero] at h
  omega

theorem card_omegaGroup_qPlus :
    Nat.card (omegaGroup qPlus qPlus_nondegenerate) = 20160 := by
  have h := S12DW.card_orthogonalGroup_eq qPlus_nondegenerate
  rw [card_orthogonalGroup_qPlus] at h
  omega

theorem commutator_le_of_card_eq_two_mul {G : Type*} [Group G] [Finite G] (O I : Subgroup G)
    (hIO : I ≤ O) (hc : Nat.card O = 2 * Nat.card I) : ⁅O, O⁆ ≤ I := by
  classical
  set H : Subgroup O := I.subgroupOf O with hH
  have hHcard : Nat.card H = Nat.card I :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIO).toEquiv
  have hpos : 0 < Nat.card I := Nat.card_pos
  have hidx : H.index = 2 := by
    have h1 := Subgroup.card_mul_index H
    rw [hHcard, hc] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, mul_comm])
  haveI : H.Normal := Subgroup.normal_of_index_eq_two hidx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Nat.card (O ⧸ H) = 2 := by rw [← Subgroup.index_eq_card]; exact hidx
  haveI : IsCyclic (O ⧸ H) := isCyclic_of_prime_card hq
  have hcomm : _root_.commutator O ≤ H :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := H)).mp inferInstance
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  have h := hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top (⟨a, ha⟩ : O))
    (Subgroup.mem_top (⟨b, hb⟩ : O)))
  rw [hH, Subgroup.mem_subgroupOf] at h
  exact h

theorem commutator_omegaGroup_qPlus :
    ⁅omegaGroup qPlus qPlus_nondegenerate, omegaGroup qPlus qPlus_nondegenerate⁆ =
      omegaGroup qPlus qPlus_nondegenerate := by
  set Ω := omegaGroup qPlus qPlus_nondegenerate with hΩ
  have hsimple : IsSimpleGroup Ω :=
    S45Q.isSimpleGroup_omegaGroup_of_six_le qPlus_nondegenerate (by rw [finrank_V₀])
  have hnonab : ¬ IsMulCommutative Ω := by
    intro hc
    have hp := (Group.is_simple_iff_prime_card (α := Ω)).mp hsimple
    rw [hΩ, card_omegaGroup_qPlus] at hp
    norm_num at hp
  have htop : _root_.commutator Ω = ⊤ := by
    rcases (instNormalCommutator Ω).eq_bot_or_eq_top with h | h
    · exact absurd ((commutator_eq_bot_iff Ω).mp h) hnonab
    · exact h
  have h1 := Subgroup.map_commutator (⊤ : Subgroup Ω) (⊤ : Subgroup Ω) Ω.subtype
  rw [Subgroup.map_top, Subgroup.range_subtype] at h1
  rw [_root_.commutator] at htop
  rw [htop, Subgroup.map_top, Subgroup.range_subtype] at h1
  exact h1.symm

theorem commutator_orthogonalGroup_qPlus :
    ⁅TauCeti.QuadraticMap.orthogonalGroup qPlus, TauCeti.QuadraticMap.orthogonalGroup qPlus⁆ =
      omegaGroup qPlus qPlus_nondegenerate := by
  haveI : Finite (V₀ ≃ₗ[ZMod 2] V₀) := finite_linearEquiv
  apply le_antisymm
  · exact commutator_le_of_card_eq_two_mul _ _ (omegaGroup_le qPlus qPlus_nondegenerate)
      (by rw [card_orthogonalGroup_qPlus, card_omegaGroup_qPlus])
  · calc omegaGroup qPlus qPlus_nondegenerate
        = ⁅omegaGroup qPlus qPlus_nondegenerate, omegaGroup qPlus qPlus_nondegenerate⁆ :=
          commutator_omegaGroup_qPlus.symm
      _ ≤ _ := Subgroup.commutator_mono (omegaGroup_le qPlus qPlus_nondegenerate)
          (omegaGroup_le qPlus qPlus_nondegenerate)

theorem eq_omegaGroup_of_card (I : Subgroup (V₀ ≃ₗ[ZMod 2] V₀))
    (hI : I ≤ TauCeti.QuadraticMap.orthogonalGroup qPlus) (hc : Nat.card I = 20160) :
    I = omegaGroup qPlus qPlus_nondegenerate := by
  haveI : Finite (V₀ ≃ₗ[ZMod 2] V₀) := finite_linearEquiv
  have h1 : omegaGroup qPlus qPlus_nondegenerate ≤ I := by
    rw [← commutator_orthogonalGroup_qPlus]
    exact commutator_le_of_card_eq_two_mul _ _ hI (by rw [card_orthogonalGroup_qPlus, hc])
  exact (Subgroup.eq_of_le_of_card_ge h1 (by rw [card_omegaGroup_qPlus, hc])).symm

end CFSG.ASVolI.H16.OmegaPlus6
