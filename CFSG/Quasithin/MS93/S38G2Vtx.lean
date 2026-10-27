module

public import CFSG.Quasithin.MS93.S38G2Crit
public import CFSG.Quasithin.MS93.S38G2Nat
public import CFSG.Quasithin.MS93.S38G2Codim

public section

namespace CFSG.Quasithin.MS93.S38G

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.H13 CFSG.Quasithin.MS93
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem commutator_Z0q_M_le (h : PUHyp M T L) : ⁅Z0q M T, M⁆ ≤ Uq M T L := by
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have key : M ≤ cRel (Z0q M T) (Uq M T L) := by
    refine h.eq_sup.le.trans (sup_le (fun l hl => ⟨hUn (h.L_le hl), fun z hz => ?_⟩)
      (fun t ht => ⟨hUn (h.le ht), fun z hz => ?_⟩))
    · rw [← commutatorElement_inv]
      exact (Uq M T L).inv_mem (Subgroup.commutator_mem_commutator hz hl)
    · rw [← commutatorElement_inv]
      exact (Uq M T L).inv_mem
        (commutator_Z0q_le_Uq h le_rfl (Subgroup.commutator_mem_commutator hz ht))
  rw [Subgroup.commutator_le]
  intro z hz m hm
  rw [← commutatorElement_inv]
  exact (Uq M T L).inv_mem ((key hm).2 z hz)

theorem finite_stab (h : PUHyp M T L) {γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) :
    Finite ↥(stab (puAmalgam h.le) γ) := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hγ
  rw [stab_smul, puAmalgam.stab_baseA]
  have : Finite ↥(imM h.le M) := Finite.of_surjective _
    (Subgroup.equivMapOfInjective _ _ (puAmalgam h.le).ofA_injective).surjective
  exact Finite.of_surjective _
    (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).surjective

theorem lt_perf (h : PUHyp M T L) {γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) :
    ⁅puTrans h.le L γ, puTrans h.le L γ⁆ = puTrans h.le L γ := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hγ
  rw [puTrans_smul h.le (l_normal h), ← Subgroup.map_commutator, puTrans_baseA h.le (l_normal h),
    ← S33.imM_commutator h.le h.L_le h.L_le, h.perfect]

theorem lt_sup (h : PUHyp M T L) {γ ρ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hγρ : (puAmalgam h.le).treeGraph.Adj γ ρ) :
    stab (puAmalgam h.le) γ = puTrans h.le L γ ⊔ Qv (puAmalgam h.le) ρ := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_of_isMVtx _ (PU.isMVtx_baseA _) (adj_baseA_baseB _)
    hγ hγρ
  rw [stab_smul, puTrans_smul h.le (l_normal h), qv_smul, ← Subgroup.map_sup,
    puAmalgam.stab_baseA, puTrans_baseA h.le (l_normal h), puAmalgam.qv_baseB,
    ← S33.imM_sup h.le h.L_le h.le, ← h.eq_sup]

theorem ut_le (h : PUHyp M T L) {γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) :
    puTrans h.le (Uq M T L) γ ≤ ZM (puAmalgam h.le) γ := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hγ
  rw [puTrans_smul h.le (uq_normal h), zm_smul, puTrans_baseA h.le (uq_normal h),
    puAmalgam.zm_baseA h.le]
  exact Subgroup.map_mono (imM_mono h.le (Uq_le_Z0q h.L_le))

theorem wt_eq (h : PUHyp M T L) {γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) :
    puTrans h.le (Uq M T L ⊓ Zq M L) γ = puTrans h.le (Uq M T L) γ ⊓
      Subgroup.centralizer (puTrans h.le L γ : Set (puAmalgam h.le).Universal) := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hγ
  rw [puTrans_smul_baseA (uqzq_normal h), puTrans_smul_baseA (uq_normal h),
    puTrans_smul_baseA (l_normal h), PU.centralizer_map_mulEquiv,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← imM_inf_centralizer h.le _ h.L_le,
    ← h.Uq_inf_Zq]

theorem zm_comm (h : PUHyp M T L) {γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) :
    ⁅ZM (puAmalgam h.le) γ, stab (puAmalgam h.le) γ⁆ ≤ puTrans h.le (Uq M T L) γ := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hγ
  rw [zm_smul, stab_smul, ← Subgroup.map_commutator, puTrans_smul h.le (uq_normal h),
    puAmalgam.zm_baseA h.le, puAmalgam.stab_baseA, ← S33.imM_commutator h.le (Z0q_le M T) le_rfl,
    puTrans_baseA h.le (uq_normal h)]
  exact Subgroup.map_mono (imM_mono h.le (commutator_Z0q_M_le h))

theorem xm_eq (h : PUHyp M T L) (hX : Xq M = Z0q M T) {γ : Vtx (puAmalgam h.le)}
    (hγ : IsMVtx _ γ) : XM (puAmalgam h.le) γ = ZM (puAmalgam h.le) γ := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hγ
  rw [xm_smul, zm_smul, h.xm_baseA_eq, puAmalgam.zm_baseA h.le, hX]

namespace G2Rep

variable {h : PUHyp M T L} {f : IntMod (Uq M T L) h.isElemAbelian_Uq →* ModQ}
  {φ : ↥M →* ↥(quasithinG2 (ZMod 2))}

theorem natHyp_at
    (hR : G2Rep h f φ) {γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) :
    NatHyp (stab (puAmalgam h.le) γ) (puTrans h.le L γ) (Qv (puAmalgam h.le) γ) := by
  have hbase : NatHyp (stab (puAmalgam h.le) (baseA _)) (puTrans h.le L (baseA _))
      (Qv (puAmalgam h.le) (baseA _)) := by
    rw [puAmalgam.stab_baseA, puTrans_baseA h.le (l_normal h),
      puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le]
    let e₀ : ↥M →* ↥(imM h.le M) := (puAmalgam h.le).ofA.codRestrict (imM h.le M)
      fun m => ⟨m, Subgroup.mem_subgroupOf.mpr m.2, rfl⟩
    have he₀ : Function.Bijective e₀ := by
      refine ⟨fun a b hab => (puAmalgam h.le).ofA_injective (congrArg Subtype.val hab), ?_⟩
      rintro ⟨_, m, -, rfl⟩
      exact ⟨m, rfl⟩
    refine NatHyp.of_equiv (MulEquiv.ofBijective e₀ he₀) (fun x => ?_) (fun x => ?_) hR.natHyp
    · exact (S33.ofA_mem_imM_iff h.le x).symm
    · exact (S33.ofA_mem_imM_iff h.le x).symm
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hγ
  rw [stab_smul, puTrans_smul h.le (l_normal h), qv_smul]
  exact NatHyp.of_equiv (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective)
    (fun _ => conj_mem_map_conj_iff.symm) (fun _ => conj_mem_map_conj_iff.symm) hbase

theorem commOff_base (hR : G2Rep h f φ) :
    ∃ D : Subgroup (puAmalgam h.le).Universal, Qv (puAmalgam h.le) (baseA _) ≤ D ∧
      D ≤ Qv (puAmalgam h.le) (baseB _) ∧ (Qv (puAmalgam h.le) (baseA _)).relIndex D ≤ 2 ∧
      ∀ x ∈ offJoin (puAmalgam h.le) (baseA _) (baseB _),
        ∀ y ∈ offJoin (puAmalgam h.le) (baseA _) (baseB _), ⁅x, y⁆ ∈ D := by
  obtain ⟨K, D, hKT, hQK, hQD, hDT, hidx, hEK, hKc⟩ := hR.exists_comm_D
  have hQ := puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le
  have hJ : offJoin (puAmalgam h.le) (baseA _) (baseB _) ≤ imM h.le K := by
    refine sup_le (iSup₂_le fun ε hε => ?_) (by rw [hQ]; exact imM_mono h.le hQK)
    obtain ⟨E, hET, hEim, -, hoff⟩ := hR.exists_off hε.1 hε.2
    rw [← hEim]
    exact imM_mono h.le (hEK E hET hoff)
  refine ⟨imM h.le D, by rw [hQ]; exact imM_mono h.le hQD,
    by rw [puAmalgam.qv_baseB]; exact imM_mono h.le hDT, ?_, fun x hx y hy => ?_⟩
  · rw [hQ, S33.relIndex_imM h.le (hDT.trans h.le)]
    exact hidx
  · obtain ⟨a, ha, rfl⟩ := hJ hx
    obtain ⟨b, hb, rfl⟩ := hJ hy
    rw [← map_commutatorElement]
    exact (S33.ofA_mem_imM_iff h.le _).mpr
      (hKc _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb))

theorem commOff (hR : G2Rep h f φ) {γ ρ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hγρ : (puAmalgam h.le).treeGraph.Adj γ ρ) :
    ∃ D : Subgroup (puAmalgam h.le).Universal, Qv (puAmalgam h.le) γ ≤ D ∧
      D ≤ Qv (puAmalgam h.le) ρ ∧ (Qv (puAmalgam h.le) γ).relIndex D ≤ 2 ∧
      ∀ x ∈ offJoin (puAmalgam h.le) γ ρ, ∀ y ∈ offJoin (puAmalgam h.le) γ ρ, ⁅x, y⁆ ∈ D := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_of_isMVtx _ (PU.isMVtx_baseA _) (adj_baseA_baseB _)
    hγ hγρ
  obtain ⟨D, hQD, hDT, hidx, hc⟩ := hR.commOff_base
  have hJ : offJoin (puAmalgam h.le) (g • baseA _) (g • baseB _) ≤
      (offJoin (puAmalgam h.le) (baseA _) (baseB _)).map (MulAut.conj g).toMonoidHom := by
    refine sup_le (iSup₂_le fun ε hε => ?_) ?_
    · have hε' : IsCritical (puAmalgam h.le) (baseA _) (g⁻¹ • ε) ∧
          geo (puAmalgam h.le) (baseA _) (g⁻¹ • ε) 1 = baseB _ := by
        refine ⟨?_, ?_⟩
        · have := (isCritical_smul _ g⁻¹ _ _).mpr hε.1
          rwa [inv_smul_smul] at this
        · have := geo_smul _ g⁻¹ (g • baseA (puAmalgam h.le)) ε 1
          rw [inv_smul_smul, hε.2, inv_smul_smul] at this
          exact this
      have e : ε = g • (g⁻¹ • ε) := by rw [smul_inv_smul]
      rw [e, zm_smul]
      exact Subgroup.map_mono (le_sup_of_le_left (le_iSup₂_of_le (g⁻¹ • ε) hε' le_rfl))
    · rw [qv_smul]
      exact Subgroup.map_mono le_sup_right
  refine ⟨D.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, fun x hx y hy => ?_⟩
  · rw [qv_smul]
    exact Subgroup.map_mono hQD
  · rw [qv_smul]
    exact Subgroup.map_mono hDT
  · rw [qv_smul, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hidx
  · obtain ⟨a, ha, rfl⟩ := hJ hx
    obtain ⟨b, hb, rfl⟩ := hJ hy
    rw [← map_commutatorElement]
    exact ⟨_, hc a ha b hb, rfl⟩

end G2Rep

end CFSG.Quasithin.MS93.S38G
