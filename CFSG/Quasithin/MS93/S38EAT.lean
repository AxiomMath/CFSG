module

public import CFSG.Quasithin.MS93.S38EAZ
public import CFSG.Quasithin.MS93.S38EPU

public section

namespace CFSG.Quasithin.MS93.S38EA

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S38E
  CFSG.Quasithin.Fan86.Univ
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem four_le_card_commutator_base (h : PUHyp M T L)
    (hcase : IsHatA6U M T L ∨ IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) 1)
    (hnSp4 : ¬ IsSp4U M T L) (hb2 : 2 < critDist (puAmalgam h.le))
    {z : (puAmalgam h.le).Universal} (hzB : z ∈ Qv (puAmalgam h.le) (baseB _))
    (hzA : z ∉ Qv (puAmalgam h.le) (baseA _)) :
    4 ≤ Nat.card ↥⁅ZM (puAmalgam h.le) (baseA _), Subgroup.zpowers z⁆ := by
  rw [puAmalgam.qv_baseB] at hzB
  obtain ⟨t, htT, rfl⟩ := hzB
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at htT
  have htO : (t : G) ∉ pCoreOf 2 M := fun ht => hzA (by
    rw [puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le]
    exact ⟨t, Subgroup.mem_subgroupOf.mpr ht, rfl⟩)
  have h4 := four_le_relIndex h hcase hnSp4 htT htO
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have htM : Subgroup.zpowers (t : G) ≤ M := (Subgroup.zpowers_le).mpr t.2
  have hzp : imM h.le (Subgroup.zpowers (t : G)) =
      Subgroup.zpowers ((puAmalgam h.le).ofA t) := by
    rw [imM, ← MonoidHom.map_zpowers,
      show Subgroup.zpowers (t : G) = (Subgroup.zpowers t).map M.subtype from
        (MonoidHom.map_zpowers M.subtype t).symm, PU.map_subtype_subgroupOf]
  have hrel := relIndex_centralizer_imM_eq h.le hUM htM
  rw [hzp] at hrel
  have hUZ : imM h.le (Uq M T L) ≤ ZM (puAmalgam h.le) (baseA _) := by
    rw [puAmalgam.zm_baseA]
    exact imM_mono h.le (Uq_le_Z0q h.L_le)
  have hZab := commutator_zm_eq_bot (puAmalgam h.le) h.hyp20 hb2 (isMVtx_baseA _)
    (isMVtx_baseA _) (by simp)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hZab
  have hab : ∀ a ∈ imM h.le (Uq M T L), ∀ b ∈ imM h.le (Uq M T L), a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hZab (hUZ ha)) b (hUZ hb)).symm
  have key : ∀ m : ↥M, ∀ y ∈ imM h.le (Uq M T L),
      (puAmalgam h.le).ofA m * y * ((puAmalgam h.le).ofA m)⁻¹ ∈ imM h.le (Uq M T L) := by
    rintro m _ ⟨u, hu, rfl⟩
    refine ⟨m * u * m⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hu ⊢
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_Uq h.le_normalizer m.2) u).mp hu
  have hN : (puAmalgam h.le).ofA t ∈
      Subgroup.normalizer (imM h.le (Uq M T L) : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key t x, fun hx => ?_⟩
    have := key t⁻¹ _ hx
    simpa [mul_assoc] using this
  have : Finite ↥(imM h.le (Uq M T L)) := finite_imM' h.le _
  have hc := relIndex_le_card_commutator hab hN
  rw [hrel] at hc
  have hle : ⁅imM h.le (Uq M T L), Subgroup.zpowers ((puAmalgam h.le).ofA t)⁆ ≤
      ⁅ZM (puAmalgam h.le) (baseA _), Subgroup.zpowers ((puAmalgam h.le).ofA t)⁆ :=
    Subgroup.commutator_mono hUZ le_rfl
  have hZn : Subgroup.zpowers ((puAmalgam h.le).ofA t) ≤
      Subgroup.normalizer (ZM (puAmalgam h.le) (baseA _) : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.zpowers_le]
    refine stab_le_normalizer_zm _ (baseA _) ?_
    rw [puAmalgam.stab_baseA]
    exact ⟨t, Subgroup.mem_subgroupOf.mpr t.2, rfl⟩
  have : Finite ↥(ZM (puAmalgam h.le) (baseA _)) := by
    rw [puAmalgam.zm_baseA]
    exact finite_imM' h.le _
  have : Finite ↥⁅ZM (puAmalgam h.le) (baseA _), Subgroup.zpowers ((puAmalgam h.le).ofA t)⁆ :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hZn))
  exact h4.trans (hc.trans (Subgroup.card_le_of_le hle))

theorem four_le_card_commutator_baseA (h : PUHyp M T L)
    (hcase : IsHatA6U M T L ∨ IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) 1)
    (hnSp4 : ¬ IsSp4U M T L) (hb2 : 2 < critDist (puAmalgam h.le))
    {γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hγA : ¬ ZM (puAmalgam h.le) γ ≤ Qv (puAmalgam h.le) (baseA _))
    (hγB : (puAmalgam h.le).treeGraph.dist γ (baseB _) < critDist (puAmalgam h.le)) :
    4 ≤ Nat.card ↥⁅ZM (puAmalgam h.le) γ, ZM (puAmalgam h.le) (baseA _)⁆ := by
  obtain ⟨z, hzZ, hzA⟩ := Set.not_subset.mp hγA
  have hγQ : ZM (puAmalgam h.le) γ ≤ Qv (puAmalgam h.le) (baseB _) :=
    zm_le_qv_of_dist_lt _ hγ hγB
  have h4 := four_le_card_commutator_base h hcase hnSp4 hb2 (hγQ hzZ) hzA
  have hle : ⁅ZM (puAmalgam h.le) (baseA _), Subgroup.zpowers z⁆ ≤
      ⁅ZM (puAmalgam h.le) γ, ZM (puAmalgam h.le) (baseA _)⁆ := by
    rw [Subgroup.commutator_comm (ZM (puAmalgam h.le) γ)]
    exact Subgroup.commutator_mono le_rfl ((Subgroup.zpowers_le).mpr hzZ)
  have hZn : ZM (puAmalgam h.le) γ ≤
      Subgroup.normalizer (ZM (puAmalgam h.le) (baseA _) : Set (puAmalgam h.le).Universal) :=
    (hγQ.trans (qv_le_stab_of_adj _ (adj_baseA_baseB _).symm)).trans
      (stab_le_normalizer_zm _ (baseA _))
  have : Finite ↥(ZM (puAmalgam h.le) (baseA _)) := by
    rw [puAmalgam.zm_baseA]
    exact finite_imM' h.le _
  have : Finite ↥⁅ZM (puAmalgam h.le) γ, ZM (puAmalgam h.le) (baseA _)⁆ := by
    rw [Subgroup.commutator_comm]
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hZn))
  exact h4.trans (Subgroup.card_le_of_le hle)

theorem four_le_card_commutator_zm (h : PUHyp M T L)
    (hcase : IsHatA6U M T L ∨ IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) 1)
    (hnSp4 : ¬ IsSp4U M T L) (hb : critDist (puAmalgam h.le) = 4)
    {γ δ : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ δ) :
    4 ≤ Nat.card ↥⁅ZM (puAmalgam h.le) γ, ZM (puAmalgam h.le) δ⁆ := by
  have hd : (puAmalgam h.le).treeGraph.dist γ δ = 4 := hc.2.1.trans hb
  have hδ : IsMVtx _ δ :=
    ((even_dist_iff _ γ δ).mp (by rw [hd]; decide)).mp hc.1
  have hδγ : (puAmalgam h.le).treeGraph.dist δ γ = 4 := by rw [tdist_comm]; exact hd
  have hadj : (puAmalgam h.le).treeGraph.Adj δ (geo _ δ γ 1) := adj_geo_one _ (by omega)
  have hνγ : (puAmalgam h.le).treeGraph.dist (geo _ δ γ 1) γ = 3 := by
    rw [dist_geo_right _ (by omega), hδγ]
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ hδ (isMVtx_baseA _)
  have hadj' : (puAmalgam h.le).treeGraph.Adj (baseA _) (g • geo _ δ γ 1) := by
    rw [← hg]
    exact (adj_smul _ g _ _).mpr hadj
  obtain ⟨g', hg', hg'ν⟩ := exists_mem_stab_smul _ hadj' (adj_baseA_baseB _)
  have hkδ : (g' * g) • δ = baseA _ := by rw [mul_smul, hg, (mem_stab _).mp hg']
  have hkν : (g' * g) • geo _ δ γ 1 = baseB _ := by rw [mul_smul, hg'ν]
  have hc' : IsCritical _ ((g' * g) • γ) (baseA _) := by
    rw [← hkδ, isCritical_smul]
    exact hc
  have hdB : (puAmalgam h.le).treeGraph.dist ((g' * g) • γ) (baseB _) <
      critDist (puAmalgam h.le) := by
    rw [← hkν, MS93.dist_smul, tdist_comm, hνγ, hb]
    norm_num
  have h4 := four_le_card_commutator_baseA h hcase hnSp4 (by omega) hc'.1 hc'.2.2 hdB
  rw [← hkδ, zm_smul, zm_smul, ← Subgroup.map_commutator,
    Subgroup.card_map_of_injective (MulAut.conj (g' * g)).injective] at h4
  exact h4

end CFSG.Quasithin.MS93.S38EA
