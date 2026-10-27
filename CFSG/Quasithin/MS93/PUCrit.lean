module

public import CFSG.Quasithin.MS93.PUBase
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Open CFSG.QuasithinUnique

universe u

variable {G : Type u} [Group G] {T M : Subgroup G} (hTM : T ≤ M)

theorem PU.omegaOneCenterOf_le_centerOf (K : Subgroup G) :
    omegaOneCenterOf K ≤ centerOf K := by
  rw [omegaOneCenterOf, omegaOneOf, Subgroup.closure_le]
  exact fun _ hx => hx.1

include hTM in
theorem PU.omegaOneCenterOf_le_pCoreOf (hO : pCoreOf 2 M ≤ T) (hC : CharTwo M) :
    omegaOneCenterOf T ≤ pCoreOf 2 M := by
  refine le_trans ?_ hC
  intro z hz
  have hzc := PU.omegaOneCenterOf_le_centerOf T hz
  refine ⟨hTM hzc.1, Subgroup.mem_centralizer_iff.2 fun p hp => ?_⟩
  exact Subgroup.mem_centralizer_iff.1 hzc.2 p (hO hp)

include hTM in
theorem normalClosureIn_le_normalCoreIn [Finite G] (hT : IsPGroup 2 T) (hO : pCoreOf 2 M ≤ T)
    (hC : CharTwo M) : normalClosureIn M (omegaOneCenterOf T) ≤ normalCoreIn M T := by
  rw [normalCoreIn_eq_pCoreOf hTM hT hO]
  exact normalClosureIn_le_of (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 M)).2
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
    (inf_le_left.trans (PU.omegaOneCenterOf_le_pCoreOf hTM hO hC))

theorem puAmalgam.zm_le_qv [Finite G] (hT : IsPGroup 2 T) (hO : pCoreOf 2 M ≤ T) (hC : CharTwo M)
    {α : Vtx (puAmalgam hTM)} (hα : IsMVtx _ α) : ZM _ α ≤ Qv _ α := by
  rw [zm_eq_puTrans hTM hα, qv_eq_puTrans hTM hα]
  exact puTrans_mono hTM (normalClosureIn_le_normalCoreIn hTM hT hO hC) α

theorem PU.omegaOneCenterOf_ne_bot [Finite G] (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    omegaOneCenterOf T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).2 hT1
  have hZ : Nontrivial (Subgroup.center ↥T) := hT.center_nontrivial
  obtain ⟨n, hn, hcard⟩ := ((hT.to_subgroup (Subgroup.center ↥T)).nontrivial_iff_card).1 hZ
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥T) 2
    (by rw [hcard]; exact dvd_pow_self 2 hn.ne')
  intro hbot
  have hmem : ((z : ↥T) : G) ∈ omegaOneCenterOf T := by
    apply Subgroup.subset_closure
    refine ⟨⟨(z : ↥T).2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩, ?_⟩
    · exact congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨h, hh⟩)
    · have h2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
      have h3 := congrArg (fun w : Subgroup.center ↥T => ((w : ↥T) : G)) h2
      simpa using h3
  rw [hbot, Subgroup.mem_bot] at hmem
  have hz1 : z = 1 := Subtype.ext (Subtype.ext hmem)
  rw [hz1, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem puAmalgam.critDist_pos [Finite G] (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hP : ∀ C : Subgroup G, C ≤ T → C ≠ ⊥ → (C.subgroupOf T).Characteristic →
      ¬ M ≤ Subgroup.normalizer (C : Set G))
    (hO : pCoreOf 2 M ≤ T) (hC : CharTwo M) : 0 < critDist (puAmalgam hTM) := by
  have hf : (puAmalgam hTM).IsFaithful := (hyp20_puAmalgam hTM hT hT1 hP).faithful
  have hne : {n | ∃ α α' : Vtx (puAmalgam hTM), IsMVtx _ α ∧
      (puAmalgam hTM).treeGraph.dist α α' = n ∧ ¬ ZM _ α ≤ Qv _ α'}.Nonempty := by
    by_contra hcon
    have hall : ∀ w, ZM (puAmalgam hTM) (baseA _) ≤ Qv _ w := by
      intro w
      by_contra hw
      exact hcon ⟨_, baseA _, w, PU.isMVtx_baseA _, rfl, hw⟩
    have hbot := PU.eq_bot_of_le_qv _ hf hall
    have hZH : ZH (puAmalgam hTM) (baseB _) ≤ ZM _ (baseA _) :=
      le_iSup₂ (f := fun ρ (_ : ρ ∈ (puAmalgam hTM).treeGraph.neighborSet (baseA _)) =>
        ZH (puAmalgam hTM) ρ) (baseB _) (adj_baseA_baseB _)
    rw [hbot, le_bot_iff, puAmalgam.zh_baseB,
      imM_eq_bot_iff hTM ((PU.omegaOneCenterOf_le T).trans hTM)] at hZH
    exact PU.omegaOneCenterOf_ne_bot hT hT1 hZH
  have h0 : 0 ∉ {n | ∃ α α' : Vtx (puAmalgam hTM), IsMVtx _ α ∧
      (puAmalgam hTM).treeGraph.dist α α' = n ∧ ¬ ZM _ α ≤ Qv _ α'} := by
    rintro ⟨α, α', hα, hd, hnot⟩
    rw [(PU.treeGraph_connected _).dist_eq_zero_iff] at hd
    subst hd
    exact hnot (puAmalgam.zm_le_qv hTM hT hO hC hα)
  rw [critDist]
  exact Nat.pos_of_ne_zero fun h => h0 (h ▸ Nat.sInf_mem hne)

end CFSG.Quasithin.MS93
