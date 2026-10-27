module

public import CFSG.Quasithin.MS93.S5Q2UC
public import CFSG.Quasithin.MS93.S5BAux

public section

namespace CFSG.Quasithin.MS93.S5Q2.UC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

variable (h : PUHyp M T L)

theorem not_cX_le_centralizer_jOff (hd : S5.IsSp4Data M T L 1 F a)
    (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G))
    (hJo : ¬ S5.vIm h.le a (S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _)) ≤
      commutator (MSP.Sp4 F))
    {ρ ε : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) (hρε : (puAmalgam h.le).treeGraph.Adj ρ ε) :
    ¬ XM _ ρ ⊓ Subgroup.centralizer (puTrans h.le L ρ : Set (puAmalgam h.le).Universal) ≤
      Subgroup.centralizer (S5.jOff h.le L 2 ρ ε : Set (puAmalgam h.le).Universal) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl, rfl⟩ := exists_smul_base_edge _ hρ hρε
  rw [cX_smul h, S5B.jOff_smul h.le hLn, PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff]
  intro hle
  obtain ⟨_, ⟨j, hj, rfl⟩, hjo⟩ := Set.not_subset.1 hJo
  have hjst : (puAmalgam h.le).ofA j ∈ stab _ (baseA (puAmalgam h.le)) := by
    rw [puAmalgam.stab_baseA]
    exact ⟨j, Subgroup.mem_subgroupOf.2 j.2, rfl⟩
  apply hC
  intro c hc
  refine S5Q2.mem_centralizer_of_commute h hd hjo hc ?_
  have h1 : (puAmalgam h.le).ofA ⟨c, Xq_le M hc.1⟩ ∈ XM _ (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) := by
    rw [cX_baseA h]
    exact ⟨⟨c, Xq_le M hc.1⟩, Subgroup.mem_subgroupOf.2 hc, rfl⟩
  have h2 := Subgroup.mem_centralizer_iff.1 (hle h1) _ hj
  have h3 : j * ⟨c, Xq_le M hc.1⟩ = ⟨c, Xq_le M hc.1⟩ * j :=
    (puAmalgam h.le).ofA_injective (by rw [map_mul, map_mul]; exact h2)
  exact congrArg Subtype.val h3

theorem cX_inf_centralizer_jOff_le_stabCenter (hd : S5.IsSp4Data M T L 1 F a)
    (hJo : ¬ S5.vIm h.le a (S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _)) ≤
      commutator (MSP.Sp4 F))
    {ρ ε : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) (hρε : (puAmalgam h.le).treeGraph.Adj ρ ε) :
    XM _ ρ ⊓ Subgroup.centralizer (puTrans h.le L ρ : Set (puAmalgam h.le).Universal) ⊓
        Subgroup.centralizer (S5.jOff h.le L 2 ρ ε : Set (puAmalgam h.le).Universal) ≤
      stabCenter _ ρ := by
  by_cases hC : Zq M L ≤ Subgroup.centralizer (M : Set G)
  · exact inf_le_left.trans (S5Q2.xm_inf_centralizer_le_stabCenter h hC hρ)
  · exact cX_inf_centralizer_le_stabCenter h hd hρ
      ((S5B.jOff_le_qv h.le L _ _ _).trans (qv_le_stab_of_adj _ hρε.symm))
      (not_cX_le_centralizer_jOff h hd hC hJo hρ hρε)

theorem xm_inf_centralizer_jOff_le_of_odd (hd : S5.IsSp4Data M T L 1 F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L)
    (hJo : ¬ S5.vIm h.le a (S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _)) ≤
      commutator (MSP.Sp4 F))
    {ρ ε : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) (hρε : (puAmalgam h.le).treeGraph.Adj ρ ε) :
    XM _ ρ ⊓ Subgroup.centralizer (S5.jOff h.le L 2 ρ ε : Set (puAmalgam h.le).Universal) ≤
      S5.uSub h.le L ρ ⊔ (XM _ ρ ⊓ stabCenter _ ρ) := by
  by_cases hC : Zq M L ≤ Subgroup.centralizer (M : Set G)
  · refine inf_le_left.trans ?_
    conv_lhs => rw [S5Q2.xm_eq_uSub_sup_centralizer h hXU hρ]
    exact sup_le_sup_left (le_inf inf_le_left
      (S5Q2.xm_inf_centralizer_le_stabCenter h hC hρ)) _
  · exact xm_inf_centralizer_le_of_not_le h hd hXU hρ
      ((S5B.jOff_le_qv h.le L _ _ _).trans (qv_le_stab_of_adj _ hρε.symm))
      (not_cX_le_centralizer_jOff h hd hC hJo hρ hρε)

end CFSG.Quasithin.MS93.S5Q2.UC
