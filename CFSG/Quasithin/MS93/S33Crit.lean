module

public import CFSG.Quasithin.MS93.S33F2
public import CFSG.Quasithin.MS93.S33Trans

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem uq_subgroupOf_normal (h : PUHyp M T L) : ((Uq M T L).subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Uq_le h.L_le)).2
    (le_normalizer_Uq h.le_normalizer)

theorem qv_inf_centralizer_puTrans (h : PUHyp M T L) {δ ρ : Vtx (puAmalgam h.le)}
    (hδ : IsMVtx _ δ) (hδρ : (puAmalgam h.le).treeGraph.Adj δ ρ) :
    Qv _ ρ ⊓ Subgroup.centralizer (puTrans h.le (Uq M T L) δ : Set (puAmalgam h.le).Universal) =
      Qv _ δ := by
  obtain ⟨g, rfl, rfl⟩ :=
    exists_smul_edge_of_isMVtx _ (PU.isMVtx_baseA _) (adj_baseA_baseB _) hδ hδρ
  rw [qv_smul, puTrans_smul h.le (uq_subgroupOf_normal h), qv_smul, ← centralizer_map_mulEquiv,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    puTrans_baseA h.le (uq_subgroupOf_normal h),
    puAmalgam.qv_baseB, ← imM_inf_centralizer h.le T (Uq_le h.L_le), inf_centralizer_Uq h,
    puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le]

theorem relIndex_qv_zm_ne_two_of_four (h : PUHyp M T L)
    (hfour : ∀ m ∈ M, ¬ Uq M T L ≤ Subgroup.centralizer ({m} : Set G) →
      4 ≤ (Subgroup.centralizer ({m} : Set G)).relIndex (Uq M T L))
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) (baseA _) α') :
    (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) ≠ 2 := by
  intro hrel
  have hb := h.critDist_pos
  have h20 := h.hyp20
  have hC := h.centHyp
  set Q' := pre h.le (Qv (puAmalgam h.le) α') with hQ'
  have hrelM : Q'.relIndex (Z0q M T) = 2 := by
    rw [hQ', relIndex_pre h.le _ (Z0q_le M T), ← puAmalgam.zm_baseA]
    exact hrel
  have hrelU : Q'.relIndex (Uq M T L) ≤ 2 := by
    rw [← hrelM]
    exact Subgroup.relIndex_le_of_le_right (Uq_le_Z0q h.L_le) (by rw [hrelM]; norm_num)
  have hc' := ms22_iii _ h20 hb hC hc
  obtain ⟨w, hwZ, hwQ⟩ := IsConcreteLE.not_le_iff_exists.mp hc'.2.2
  have hd : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  have hρadj : (puAmalgam h.le).treeGraph.Adj (baseA _) (geo _ (baseA _) α' 1) :=
    adj_geo_one _ (by rw [hd]; exact hb)
  have hZρ : ZM (puAmalgam h.le) α' ≤ Qv _ (geo _ (baseA _) α' 1) := by
    refine zm_le_qv_of_dist_lt _ (hc.isMVtx_right _ h20) ?_
    rw [SimpleGraph.dist_comm, dist_geo_right _ (by rw [hd]; exact hb), hd]
    omega
  have hwS : w ∈ stab (puAmalgam h.le) (baseA _) := qv_le_stab_of_adj _ hρadj.symm (hZρ hwZ)
  rw [puAmalgam.stab_baseA, imM_self] at hwS
  obtain ⟨m, rfl⟩ := hwS
  have hQC : Q' ≤ Subgroup.centralizer ({(m : G)} : Set G) := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := (mem_pre_iff' h.le).1 hx
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff.mp hy]
    have h1 := Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20
      (hc.isMVtx_right _ h20) hwZ) _ hx'
    rw [← map_mul, ← map_mul] at h1
    exact (congrArg Subtype.val ((puAmalgam h.le).ofA_injective h1)).symm
  have hle : (Subgroup.centralizer ({(m : G)} : Set G)).relIndex (Uq M T L) ≤ 2 :=
    (Subgroup.relIndex_le_of_le_left hQC Subgroup.index_ne_zero_of_finite).trans hrelU
  have hnt : ¬ Uq M T L ≤ Subgroup.centralizer ({(m : G)} : Set G) := by
    intro hU
    apply hwQ
    rw [← qv_inf_centralizer_puTrans h (PU.isMVtx_baseA _) hρadj,
      puTrans_baseA h.le (uq_subgroupOf_normal h)]
    refine ⟨hZρ hwZ, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    obtain ⟨u, hu, rfl⟩ := hx
    have h1 := Subgroup.mem_centralizer_iff.mp (hU (Subgroup.mem_subgroupOf.mp hu)) m rfl
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h1.symm
  have h4 := hfour m m.2 hnt
  omega


section SL3

variable {F : Type} [Field F] [Fintype F] {a : ↥L →* ↥(StatedSL 3 F)}
  {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → Fin 3 → F)}

theorem relIndex_qv_zm_ne_two (h : PUHyp M T L) (ha : Function.Surjective a)
    (hβ : Function.Surjective β) (hβker : β.ker = (⊥ : Subgroup G).subgroupOf (Uq M T L))
    (hβα : ∀ (l : ↥L) (u v : ↥(Uq M T L)), (v : G) = l * u * l⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (a l : GL (Fin 3) F)).mulVec (Multiplicative.toAdd (β u) i))
    (hF : 4 ≤ Fintype.card F) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) (baseA _) α') :
    (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) ≠ 2 :=
  relIndex_qv_zm_ne_two_of_four h
    (fun _ hm hnt => four_le_relIndex_centralizer h ha hβ hβker hβα hF hm hnt) hc

end SL3

end CFSG.Quasithin.MS93.S33
