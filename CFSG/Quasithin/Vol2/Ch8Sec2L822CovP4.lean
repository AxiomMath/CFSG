module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovP1
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin.H13

private theorem sq_mem_alternatingGroup_perm5_cv (x : Equiv.Perm (Fin 5)) :
    x ^ 2 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup, map_pow, Int.units_sq]

private theorem alternatingGroup_perm5_le_of_normal_cv (N : Subgroup (Equiv.Perm (Fin 5))) [N.Normal]
    (h2 : ∀ x : Equiv.Perm (Fin 5), ∃ k : ℕ, x ^ 2 ^ k ∈ N) :
    alternatingGroup (Fin 5) ≤ N := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin 5))) with hM | hM
  · exfalso
    have hsq : ∀ z ∈ N, z ^ 2 = 1 := by
      intro z hz
      rcases Classical.em (z ∈ alternatingGroup (Fin 5)) with hzA | hzA
      · have hmem : (⟨z, hzA⟩ : ↥(alternatingGroup (Fin 5))) ∈ N.subgroupOf (alternatingGroup (Fin 5)) :=
          Subgroup.mem_subgroupOf.2 hz
        rw [hM, Subgroup.mem_bot] at hmem
        have hz1 : z = 1 := congrArg Subtype.val hmem
        rw [hz1, one_pow]
      · have hmem : (⟨z ^ 2, sq_mem_alternatingGroup_perm5_cv z⟩ : ↥(alternatingGroup (Fin 5))) ∈
            N.subgroupOf (alternatingGroup (Fin 5)) :=
          Subgroup.mem_subgroupOf.2 (N.pow_mem hz 2)
        rw [hM, Subgroup.mem_bot] at hmem
        exact congrArg Subtype.val hmem
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨c, hc⟩ : ∃ c : Equiv.Perm (Fin 5), c = List.formPerm [0, 1, 2, 3, 4] := ⟨_, rfl⟩
    have hc5 : c ^ 5 = 1 := by
      rw [hc]
      decide
    have hc1 : c ≠ 1 := by
      rw [hc]
      decide
    have hord : orderOf c = 5 := orderOf_eq_prime hc5 hc1
    obtain ⟨k, hk⟩ := h2 c
    have hk2 : c ^ 2 ^ (k + 1) = 1 := by
      rw [pow_succ, pow_mul]
      exact hsq _ hk
    have hdvd : orderOf c ∣ 2 ^ (k + 1) := orderOf_dvd_of_pow_eq_one hk2
    rw [hord] at hdvd
    have h52 : 5 ∣ 2 := (by norm_num : Nat.Prime 5).dvd_of_dvd_pow hdvd
    omega
  ·
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥(alternatingGroup (Fin 5))) ∈ N.subgroupOf (alternatingGroup (Fin 5)) := by
      rw [hM]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hmem

theorem twoResidual_perm5_cv :
    CFSG.Quasithin.twoResidual (⊤ : Subgroup (Equiv.Perm (Fin 5))) = alternatingGroup (Fin 5) := by
  apply le_antisymm
  ·
    apply CFSG.Quasithin.twoResidual_le_of_isTwoQuotient le_top
    · exact (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge
    · intro x _
      exact ⟨1, sq_mem_alternatingGroup_perm5_cv x⟩
  ·
    intro x hx
    rw [CFSG.Quasithin.mem_twoResidual_iff]
    intro N _ hN h2
    haveI : N.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hN)
    exact alternatingGroup_perm5_le_of_normal_cv N (fun y => by
      obtain ⟨k, hk⟩ := h2 y (Subgroup.mem_top y)
      exact ⟨k, hk⟩) hx

end CFSG.Quasithin.H13
