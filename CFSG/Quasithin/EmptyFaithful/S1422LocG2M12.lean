module

public import CFSG.Quasithin.EmptyFaithful.S1422LocOdd

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

@[expose] def M12AmalgamE8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H L2 : Subgroup G), CaseM12 H L2 →
    ∃ E : Subgroup G, E ≤ pCoreOf 2 H ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 ∧
      L2 ≤ Subgroup.normalizer (E : Set G) ∧
      ∀ V : Subgroup G, V ≤ pCoreOf 2 H → Nat.card V = 4 → L2 ≤ Subgroup.normalizer (V : Set G) →
        V ≤ E

@[expose] def G2AmalgamE8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H L2 : Subgroup G), CaseG2 H L2 →
    IsQ8Sq ↥(pCoreOf 2 H) ∧
    ∃ E : Subgroup G, E ≤ pCoreOf 2 H ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 ∧
      L2 ≤ Subgroup.normalizer (E : Set G) ∧
      ∀ V : Subgroup G, V ≤ pCoreOf 2 H → Nat.card V = 4 → L2 ≤ Subgroup.normalizer (V : Set G) →
        V ≤ E

namespace Setting1422

variable {G : Type} [Group G] [Finite G] {T M Y H : Subgroup G}

theorem index_H_eq_three (S : Setting1422 T M Y H) (hq : IsL2Quot 1 (oTwoQuot ↥H)) :
    (T.subgroupOf H).index = 3 := by
  have h6 : Nat.card (OTwoQuot H) = 2 ^ 1 * 3 := by
    have : Nat.card (oTwoQuot ↥H) = 6 := by rw [hq.card le_rfl]; norm_num
    exact this
  exact index_sylow_eq_of_card_quot S.isSylow_H (by decide) h6

theorem eq_one_of_odd_of_mem_pCoreOf {X : Subgroup G} {x : G} (hx : x ∈ pCoreOf 2 X)
    (hodd : Odd (orderOf x)) : x = 1 := by
  have hp := CFSG.LieType.BorelTits.pCoreOf_isPGroup (G := G) 2 X
  obtain ⟨k, hk⟩ := hp ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (by rcases hodd with ⟨j, hj⟩; omega))))
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hdvd)

theorem eq_Mc_of_Q8Sq (S : Setting1422 T M Y H) (hV : VZ T M ≤ pCoreOf 2 H)
    (hQ : IsQ8Sq ↥(pCoreOf 2 H)) (hq : IsL2Quot 1 (oTwoQuot ↥H))
    {E : Subgroup G} (hEQ : E ≤ pCoreOf 2 H) (hEa : IsElemAbelian 2 E) (hE8 : Nat.card E = 8)
    (hEN : Y ⊔ T ≤ Subgroup.normalizer (E : Set G))
    (hVE : ∀ V : Subgroup G, V ≤ pCoreOf 2 H → Nat.card V = 4 →
      Y ⊔ T ≤ Subgroup.normalizer (V : Set G) → V ≤ E) :
    H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  obtain ⟨z, hz, hz1, hz2, hZ⟩ := S.exists_z
  have hzcen : z ∈ centerOf (pCoreOf 2 H) := by
    obtain ⟨P, hP⟩ := S.exists_sylow
    exact omegaOneCenter_le_centerOf_pCoreOf H P (hP ▸ S.T_le_H) S.charTwo_H (hP ▸ hz)
  have hzQ : z ∈ pCoreOf 2 H := hzcen.1
  obtain ⟨hcard, A, B, ⟨hAB, hgen⟩, ⟨eA⟩, ⟨eB⟩⟩ := hQ
  let d : S143.Q8SqData ↥(pCoreOf 2 H) := ⟨A, B, hAB, hgen, eA, eB, hcard⟩
  obtain ⟨c, hc1, hc2, hcc, hcen⟩ := S1422Loc.exists_central_involution d
  have hzc : (⟨z, hzQ⟩ : ↥(pCoreOf 2 H)) = c := by
    have hz' : ∀ y : ↥(pCoreOf 2 H), (⟨z, hzQ⟩ : ↥(pCoreOf 2 H)) * y = y * ⟨z, hzQ⟩ := by
      intro y
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hzcen.2 (y : G) y.2).symm
    rcases hcen _ hz' with h | h
    · exact absurd (congrArg Subtype.val h) hz1
    · exact h
  have hcomm : ∀ x ∈ pCoreOf 2 H, ∀ y ∈ pCoreOf 2 H,
      x * y * x⁻¹ * y⁻¹ ∈ quasithinOmegaOneCenter T := by
    intro x hx y hy
    have h1 := d.commutator_mem_center ⟨x, hx⟩ ⟨y, hy⟩
    have h2 : (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ : ↥(pCoreOf 2 H)) = 1 ∨
        (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ : ↥(pCoreOf 2 H)) = c :=
      hcen _ (fun w => (Subgroup.mem_center_iff.mp h1 w).symm)
    rcases h2 with h | h
    · have : x * y * x⁻¹ * y⁻¹ = 1 := congrArg Subtype.val h
      rw [this]; exact Subgroup.one_mem _
    · have : x * y * x⁻¹ * y⁻¹ = z := by
        have := congrArg Subtype.val h
        rw [← hzc] at this
        exact this
      rw [this]; exact hz
  have hMcN := S.Mc_le_normalizer_pCoreOf_H hcomm
  have hQeq := S.pCoreOf_H_eq_Mc hcomm
  have hCU : ∀ x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G), Odd (orderOf x) →
      (∀ u ∈ pCoreOf 2 H, x * u = u * x) → x = 1 := by
    intro x hx hodd hxc
    have hx' : x ∈ pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :=
      S.charTwo_Mc ⟨hx, Subgroup.mem_centralizer_iff.mpr fun u hu => (hxc u (hQeq ▸ hu)).symm⟩
    exact eq_one_of_odd_of_mem_pCoreOf hx' hodd
  have hVE' : VZ T M ≤ E := by
    refine hVE _ hV S.hyp.rank_two ?_
    exact S.YT_le_M.trans (le_normalizer_conjClosure _ _)
  exact S.eq_Mc_of_E ⟨hcard, A, B, ⟨hAB, hgen⟩, ⟨eA⟩, ⟨eB⟩⟩ hEQ hEa hE8 hEN hVE' hMcN hCU
    (S.index_H_eq_three hq)

theorem m12_local (hVQ : Stage1426VleQ) (hE : M12AmalgamE8)
    (S : Setting1422 T M Y H) (hC : CaseM12 H (Y ⊔ T)) :
    H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  obtain ⟨E, hEQ, hEa, hE8, hEN, hVE⟩ := hE G H (Y ⊔ T) hC
  exact S.eq_Mc_of_Q8Sq (hVQ G T M S.hyp H S.star) hC.2.2.1 hC.2.1 hEQ hEa hE8 hEN hVE

theorem g2_local (hVQ : Stage1426VleQ) (hE : G2AmalgamE8)
    (S : Setting1422 T M Y H) (hC : CaseG2 H (Y ⊔ T)) :
    H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  obtain ⟨hQ8, E, hEQ, hEa, hE8, hEN, hVE⟩ := hE G H (Y ⊔ T) hC
  exact S.eq_Mc_of_Q8Sq (hVQ G T M S.hyp H S.star) hQ8 hC.2.1 hEQ hEa hE8 hEN hVE

end Setting1422

end CFSG.Quasithin
