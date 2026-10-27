module

public import CFSG.Quasithin.Background.RonanH143QL

public section

open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.RonanH143

open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf

noncomputable def sgnQ : ↥(MY mog22 Qstd) →* ℤˣ := Equiv.Perm.sign.comp (piQ mog22)

noncomputable def Asgn : Subgroup P24 := sgnQ.ker.map (MY mog22 Qstd).subtype

theorem asg_mem_ker_iff (x : ↥(MY mog22 Qstd)) :
    x ∈ sgnQ.ker ↔ Equiv.Perm.sign (piQ mog22 x) = 1 :=
  MonoidHom.mem_ker

theorem asg_sign_sig1 : Equiv.Perm.sign sig1 = 1 := by
  decide +kernel

theorem asg_sign_siga2 : Equiv.Perm.sign siga2 = 1 := by
  decide +kernel

theorem asg_mem_ker_of_smul (g : P24) (hg : g ∈ MY mog22 Qstd) (σ : Equiv.Perm (Fin 5))
    (h : ∀ i, g • Zq i = Zq (σ i)) (hσ : Equiv.Perm.sign σ = 1) :
    (⟨g, hg⟩ : ↥(MY mog22 Qstd)) ∈ sgnQ.ker := by
  rw [asg_mem_ker_iff, piQ_eq_of_smul ⟨g, hg⟩ σ h]
  exact hσ

theorem Asgn_le_MQ : Asgn ≤ MY mog22 Qstd := by
  unfold Asgn
  exact Subgroup.map_subtype_le _

theorem mem_Asgn_iff {g : P24} :
    g ∈ Asgn ↔ ∃ h : g ∈ MY mog22 Qstd, Equiv.Perm.sign (piQ mog22 ⟨g, h⟩) = 1 := by
  unfold Asgn
  constructor
  · intro hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
    exact ⟨y.2, (asg_mem_ker_iff y).1 hy⟩
  · rintro ⟨h, hs⟩
    exact Subgroup.mem_map.2 ⟨⟨g, h⟩, (asg_mem_ker_iff ⟨g, h⟩).2 hs, rfl⟩

theorem NQ_le_Asgn : NQ ≤ Asgn := by
  intro n hn
  have hM : n ∈ MY mog22 Qstd := NQ_le_MY_Q le_rfl hn
  refine mem_Asgn_iff.2 ⟨hM, ?_⟩
  have h1 : piQ mog22 ⟨n, hM⟩ = 1 := by
    refine piQ_eq_of_smul ⟨n, hM⟩ 1 (fun i => ?_)
    rw [Equiv.Perm.one_apply]
    exact nq_fix_Zq n hn i
  rw [h1, map_one]

theorem g1_mem_Asgn : g1Perm ∈ Asgn := by
  have hM : g1Perm ∈ MY mog22 Qstd := g1Perm_mem_MY g1Perm_mem_mog22
  refine mem_Asgn_iff.2 ⟨hM, ?_⟩
  rw [piQ_eq_of_smul ⟨g1Perm, hM⟩ sig1 g1_smul_Zq]
  exact asg_sign_sig1

theorem a2_mem_Asgn : a2Perm ∈ Asgn := by
  have hM : a2Perm ∈ MY mog22 Qstd := a2Perm_mem_MY a2Perm_mem_mog22
  refine mem_Asgn_iff.2 ⟨hM, ?_⟩
  rw [piQ_eq_of_smul ⟨a2Perm, hM⟩ siga2 a2_smul_Zq]
  exact asg_sign_siga2

theorem asg_sgnQ_range_eq_top : sgnQ.range = ⊤ := by
  rw [eq_top_iff]
  intro u _
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact MonoidHom.mem_range.2 ⟨1, map_one sgnQ⟩
  · have hsw : Equiv.swap (0 : Fin 5) 1 ∈ (piQ mog22).range := by
      rw [piQ_range_top g1Perm_mem_mog22 g2Perm_mem_mog22]
      exact Subgroup.mem_top _
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 hsw
    refine MonoidHom.mem_range.2 ⟨g, ?_⟩
    show Equiv.Perm.sign (piQ mog22 g) = -1
    rw [hg, Equiv.Perm.sign_swap (show (0 : Fin 5) ≠ 1 by decide)]

theorem card_Asgn :
    Nat.card Asgn = 960 := by
  have h1 : Nat.card Asgn = Nat.card sgnQ.ker := by
    unfold Asgn
    exact Subgroup.card_map_of_injective (MY mog22 Qstd).subtype_injective
  have hindex : sgnQ.ker.index = 2 := by
    rw [Subgroup.index_ker, asg_sgnQ_range_eq_top, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  have hmul := Subgroup.card_mul_index (H := sgnQ.ker)
  rw [hindex, card_MY_Q_L] at hmul
  rw [h1]
  omega

theorem asg_F1_surj : ∀ t : Fin 16, ∃ s : Fin 16, xorF (tab F1 s) s = t := by
  decide +kernel

theorem asg_alt5_comm :
    ⁅alternatingGroup (Fin 5), alternatingGroup (Fin 5)⁆ = alternatingGroup (Fin 5) := by
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hK : ⁅(⊤ : Subgroup ↥(alternatingGroup (Fin 5))),
      (⊤ : Subgroup ↥(alternatingGroup (Fin 5)))⁆ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ⁅(⊤ : Subgroup ↥(alternatingGroup (Fin 5))),
          (⊤ : Subgroup ↥(alternatingGroup (Fin 5)))⁆ with h | h
    · exfalso
      have ha : Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2 ∈ alternatingGroup (Fin 5) :=
        Equiv.Perm.mem_alternatingGroup.2 (by decide)
      have hb : Equiv.swap (0 : Fin 5) 1 * Equiv.swap 3 4 ∈ alternatingGroup (Fin 5) :=
        Equiv.Perm.mem_alternatingGroup.2 (by decide)
      have hc := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top (⟨_, ha⟩ : ↥(alternatingGroup (Fin 5))))
        (Subgroup.mem_top (⟨_, hb⟩ : ↥(alternatingGroup (Fin 5))))
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      have hne : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) * (Equiv.swap 0 1 * Equiv.swap 3 4) ≠
          (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 3 4) * (Equiv.swap 0 1 * Equiv.swap 1 2) := by
        decide +kernel
      exact hne (congrArg Subtype.val hc)
    · exact h
  have h := congrArg (Subgroup.map (alternatingGroup (Fin 5)).subtype) hK
  rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h

theorem asg_map_ker_eq_alt5 : sgnQ.ker.map (piQ mog22) = alternatingGroup (Fin 5) := by
  ext σ
  constructor
  · intro hσ
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hσ
    exact Equiv.Perm.mem_alternatingGroup.2 ((asg_mem_ker_iff x).1 hx)
  · intro hσ
    have hσR : σ ∈ (piQ mog22).range := by
      rw [piQ_range_top g1Perm_mem_mog22 g2Perm_mem_mog22]
      exact Subgroup.mem_top σ
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hσR
    refine Subgroup.mem_map.2 ⟨x, (asg_mem_ker_iff x).2 ?_, hx⟩
    rw [hx]
    exact Equiv.Perm.mem_alternatingGroup.1 hσ

theorem asg_NQ_le_comm :
    NQ.subgroupOf (MY mog22 Qstd) ≤ ⁅sgnQ.ker, sgnQ.ker⁆ := by
  intro y hy
  obtain ⟨t, ht⟩ := mem_NQ_iff.1 (Subgroup.mem_subgroupOf.1 hy)
  obtain ⟨s, hs⟩ := asg_F1_surj t
  have hg1M : g1Perm ∈ MY mog22 Qstd := g1Perm_mem_MY g1Perm_mem_mog22
  have hnM : nqPerm s ∈ MY mog22 Qstd := NQ_le_MY_Q le_rfl (mem_NQ_iff.2 ⟨s, rfl⟩)
  have hg : (⟨g1Perm, hg1M⟩ : ↥(MY mog22 Qstd)) ∈ sgnQ.ker :=
    asg_mem_ker_of_smul g1Perm hg1M sig1 g1_smul_Zq asg_sign_sig1
  have hn : (⟨nqPerm s, hnM⟩ : ↥(MY mog22 Qstd)) ∈ sgnQ.ker :=
    asg_mem_ker_of_smul (nqPerm s) hnM 1 (fun i => by
      rw [Equiv.Perm.one_apply]
      exact nq_smul_Zq s i) (map_one Equiv.Perm.sign)
  have hval : ⁅g1Perm, nqPerm s⁆ = nqPerm t := by
    rw [commutatorElement_def, conj_g1_nq s, inv_eq_of_mul_eq_one_right (nqPerm_sq s),
      nqPerm_mul, hs]
  have key : ⁅(⟨g1Perm, hg1M⟩ : ↥(MY mog22 Qstd)), (⟨nqPerm s, hnM⟩ : ↥(MY mog22 Qstd))⁆ = y := by
    apply Subtype.ext
    exact (map_commutatorElement (MY mog22 Qstd).subtype
      (⟨g1Perm, hg1M⟩ : ↥(MY mog22 Qstd)) ⟨nqPerm s, hnM⟩).trans (hval.trans ht.symm)
  rw [← key]
  exact Subgroup.commutator_mem_commutator hg hn

theorem asg_comm_ker :
    ⁅sgnQ.ker, sgnQ.ker⁆ = sgnQ.ker := by
  have hC5 : (⁅sgnQ.ker, sgnQ.ker⁆).map (piQ mog22) = alternatingGroup (Fin 5) := by
    rw [Subgroup.map_commutator, asg_map_ker_eq_alt5, asg_alt5_comm]
  refine le_antisymm (A3.commutator_self_le _) ?_
  intro x hx
  have hφx : piQ mog22 x ∈ alternatingGroup (Fin 5) :=
    Equiv.Perm.mem_alternatingGroup.2 ((asg_mem_ker_iff x).1 hx)
  rw [← hC5] at hφx
  obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.1 hφx
  have hk : c⁻¹ * x ∈ (piQ mog22).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcx, inv_mul_cancel]
  rw [ker_piQ_L] at hk
  have hmul := mul_mem hc (asg_NQ_le_comm hk)
  rwa [mul_inv_cancel_left] at hmul

theorem Asgn_perfect :
    ⁅Asgn, Asgn⁆ = Asgn := by
  calc ⁅Asgn, Asgn⁆ = (⁅sgnQ.ker, sgnQ.ker⁆).map (MY mog22 Qstd).subtype := by
        unfold Asgn
        rw [Subgroup.map_commutator]
    _ = sgnQ.ker.map (MY mog22 Qstd).subtype := by rw [asg_comm_ker]
    _ = Asgn := rfl

theorem asg_commutator_MY_le :
    ⁅MY mog22 Qstd, MY mog22 Qstd⁆ ≤ Asgn := by
  refine Subgroup.commutator_le.2 fun g hg h hh => ?_
  have hmem : ⁅(⟨g, hg⟩ : ↥(MY mog22 Qstd)), (⟨h, hh⟩ : ↥(MY mog22 Qstd))⁆ ∈ sgnQ.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  unfold Asgn
  exact Subgroup.mem_map.2 ⟨_, hmem, map_commutatorElement (MY mog22 Qstd).subtype
    (⟨g, hg⟩ : ↥(MY mog22 Qstd)) ⟨h, hh⟩⟩

theorem perfectCore_MQ :
    perfectCore (MY mog22 Qstd) = Asgn := by
  refine le_antisymm ?_ (le_perfectCore_of_perfect Asgn_le_MQ Asgn_perfect)
  calc perfectCore (MY mog22 Qstd) ≤ derivedSeriesOf (MY mog22 Qstd) 1 :=
        perfectCore_le_derivedSeriesOf _ 1
    _ = ⁅MY mog22 Qstd, MY mog22 Qstd⁆ := rfl
    _ ≤ Asgn := asg_commutator_MY_le

end CFSG.Quasithin.RonanH143
