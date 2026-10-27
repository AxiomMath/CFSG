module

public import CFSG.Quasithin.MS93.S5Q2X
public import CFSG.Quasithin.MS93.S5BBasic

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S5Q2

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section InM

theorem exists_not_mem_commutator (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    {E₀ : Subgroup G} (hE₀M : E₀ ≤ M) (hE₀2 : IsPGroup 2 E₀) (hE₀O : ¬ E₀ ≤ pCoreOf 2 M)
    (hrel : (Subgroup.centralizer (E₀ : Set G)).relIndex (Uq M T L) ≤ 2) :
    ∃ z : ↥M, (z : G) ∈ E₀ ∧ a z ∉ commutator (MSP.Sp4 F) := by
  obtain ⟨z, hzE, hzO⟩ := Set.not_subset.1 hE₀O
  refine ⟨⟨z, hE₀M hzE⟩, hzE, not_mem_commutator_of_relIndex_le_two h hd ?_ hzO ?_⟩
  · obtain ⟨e, he⟩ := hE₀2 ⟨z, hzE⟩
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  · refine le_trans (Subgroup.relIndex_le_of_le_left ?_ Subgroup.FiniteIndex.index_ne_zero) hrel
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzE)

theorem relIndex_pCoreOf_le_two (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    {E₀ : Subgroup G} (hE₀M : E₀ ≤ M) (hE₀2 : IsPGroup 2 E₀)
    (hrel : (Subgroup.centralizer (E₀ : Set G)).relIndex (Uq M T L) ≤ 2) :
    (pCoreOf 2 M).relIndex E₀ ≤ 2 := by
  by_cases hE₀O : E₀ ≤ pCoreOf 2 M
  · rw [Subgroup.relIndex_eq_one.2 hE₀O]
    omega
  obtain ⟨p, hp, hfix⟩ := (S5B.relIndex_centralizer_M h hd hE₀M hE₀2 hE₀O).2
    (by rw [pow_one]; exact hrel)
  have h3 : Module.finrank F (MSP.fixSp ((E₀.subgroupOf M).map a)) = 3 := by
    have h1 := MSP.finrank_perp p
    have h2 : Module.finrank F p = 1 := hp
    rw [hfix]
    omega
  obtain ⟨p', hp', -, hĒ⟩ := MSP.exists_point_of_finrank_fixSp_three h3
  have hF : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hd.2.1, pow_one]
  have hcardE : Nat.card ↥((E₀.subgroupOf M).map a) ≤ 2 := by
    have := Subgroup.card_le_of_le hĒ
    rwa [MSP.card_xPoint hp', hF] at this
  have hker : a.ker ⊓ E₀.subgroupOf M ≤ (pCoreOf 2 M).subgroupOf M := by
    rintro z ⟨hz, hzE⟩
    obtain ⟨n, hn⟩ := hE₀2 ⟨z, Subgroup.mem_subgroupOf.1 hzE⟩
    exact Subgroup.mem_subgroupOf.2 (S5B.mem_pCoreOf_of_ker h hd (MonoidHom.mem_ker.1 hz)
      ⟨n, by simpa using congrArg Subtype.val hn⟩)
  rw [← Subgroup.relIndex_subgroupOf hE₀M]
  calc ((pCoreOf 2 M).subgroupOf M).relIndex (E₀.subgroupOf M)
      ≤ (a.ker ⊓ E₀.subgroupOf M).relIndex (E₀.subgroupOf M) :=
        Subgroup.relIndex_le_of_le_left hker Subgroup.FiniteIndex.index_ne_zero
    _ = Nat.card ↥((E₀.subgroupOf M).map a) := by
        rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_ker]
    _ ≤ 2 := hcardE

theorem xq_inf_centralizer_le_of_relIndex (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {E₀ : Subgroup G} (hE₀M : E₀ ≤ M) (hE₀2 : IsPGroup 2 E₀)
    (hE₀O : ¬ E₀ ≤ pCoreOf 2 M)
    (hrel : (Subgroup.centralizer (E₀ : Set G)).relIndex (Uq M T L) ≤ 2) :
    Xq M ⊓ Subgroup.centralizer (E₀ : Set G) ≤
      Uq M T L ⊔ (Zq M L ⊓ Subgroup.centralizer (M : Set G)) := by
  obtain ⟨z, hzE, hz⟩ := exists_not_mem_commutator h hd hE₀M hE₀2 hE₀O hrel
  exact (inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzE))).trans
    (xq_inf_centralizer_le h hd hXU hz)

theorem zq_inf_centralizer_le_of_relIndex (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    {E₀ : Subgroup G} (hE₀M : E₀ ≤ M) (hE₀2 : IsPGroup 2 E₀) (hE₀O : ¬ E₀ ≤ pCoreOf 2 M)
    (hrel : (Subgroup.centralizer (E₀ : Set G)).relIndex (Uq M T L) ≤ 2) :
    Zq M L ⊓ Subgroup.centralizer (E₀ : Set G) ≤ Subgroup.centralizer (M : Set G) := by
  obtain ⟨z, hzE, hz⟩ := exists_not_mem_commutator h hd hE₀M hE₀2 hE₀O hrel
  rintro c ⟨hc, hcE⟩
  exact mem_centralizer_of_commute h hd hz hc (Subgroup.mem_centralizer_iff.1 hcE _ hzE)

end InM

section Vertex

private theorem map_stabCenter_le {A B C : Type} [Group A] [Group C] [Group B]
    (X : GoldAmalgam A C B) (g : X.Universal) (δ : Vtx X) :
    (stabCenter X δ).map (MulAut.conj g).toMonoidHom ≤ stabCenter X (g • δ) := by
  rintro _ ⟨z, hz, rfl⟩
  have hzs := (S5B.stabCenter_le_inf δ hz).1
  have hzc := (S5B.stabCenter_le_inf δ hz).2
  have hgz : (MulAut.conj g).toMonoidHom z ∈ stab X (g • δ) := by
    rw [stab_smul]
    exact ⟨z, hzs, rfl⟩
  refine ⟨⟨_, hgz⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext ?_, rfl⟩
  have hy : g⁻¹ * (y : X.Universal) * g ∈ stab X δ := (mem_stab_smul X).1 y.2
  have hyz := Subgroup.mem_centralizer_iff.1 hzc _ hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul]
  calc (y : X.Universal) * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [hyz]
    _ = g * z * g⁻¹ * y := by group

variable (h : PUHyp M T L)

theorem relIndex_qv_le_two (hd : S5.IsSp4Data M T L 1 F a) {ρ : Vtx (puAmalgam h.le)}
    (hρ : IsMVtx _ ρ) {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ stab _ ρ)
    (hE2 : IsPGroup 2 E)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L ρ) ≤ 2) :
    (Qv _ ρ).relIndex E ≤ 2 := by
  by_cases hEQ : E ≤ Qv _ ρ
  · rw [Subgroup.relIndex_eq_one.2 hEQ]
    omega
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hρ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  obtain ⟨hE₀2, -⟩ := S5B.isPGroup_not_le_of_smul h g hE₀M hE2 hEQ
  rw [S5B.relIndex_centralizer_smul h g hE₀M] at hrel
  rw [qv_smul, S5B.qv_baseA_eq h,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    S5B.relIndex_imM h.le hE₀M]
  exact relIndex_pCoreOf_le_two h hd hE₀M hE₀2 hrel

theorem xm_inf_centralizer_le (hd : S5.IsSp4Data M T L 1 F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ)
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ stab _ ρ) (hE2 : IsPGroup 2 E)
    (hEQ : ¬ E ≤ Qv _ ρ)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L ρ) ≤ 2) :
    XM _ ρ ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) ≤
      S5.uSub h.le L ρ ⊔ (XM _ ρ ⊓ stabCenter _ ρ) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hρ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  obtain ⟨hE₀2, hE₀O⟩ := S5B.isPGroup_not_le_of_smul h g hE₀M hE2 hEQ
  rw [S5B.relIndex_centralizer_smul h g hE₀M] at hrel
  have key := xq_inf_centralizer_le_of_relIndex h hd hXU hE₀M hE₀2 hE₀O hrel
  have hle1 : Uq M T L ≤ M := Uq_le h.L_le
  have hle2 : Zq M L ⊓ Subgroup.centralizer (M : Set G) ≤ M :=
    inf_le_left.trans (inf_le_left.trans (Xq_le M))
  have h1 : imM h.le (Xq M ⊓ Subgroup.centralizer (E₀ : Set G)) ≤
      imM h.le (Uq M T L) ⊔ (XM _ (baseA (puAmalgam h.le)) ⊓ stabCenter _ (baseA _)) := by
    refine (imM_mono h.le key).trans ?_
    rw [S5B.imM_sup_of_le h.le hle1 hle2]
    refine sup_le_sup_left ?_ _
    rw [S5B.xm_baseA_eq h, S5B.stabCenter_baseA, ← imM_inf]
    exact imM_mono h.le (le_inf (inf_le_left.trans inf_le_left) (le_inf hle2 inf_le_right))
  rw [imM_inf_centralizer h.le _ hE₀M, ← S5B.xm_baseA_eq h, ← S5B.uSub_baseA h] at h1
  have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h1
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← xm_smul,
    ← PU.centralizer_map_mulEquiv, Subgroup.map_sup,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← xm_smul,
    ← S5B.uSub_smul h.le hLn] at h2
  exact h2.trans (sup_le_sup_left (inf_le_inf_left _ (map_stabCenter_le _ g _)) _)

theorem xm_inf_centralizer_le_zm (hd : S5.IsSp4Data M T L 1 F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ)
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ stab _ ρ) (hE2 : IsPGroup 2 E)
    (hEQ : ¬ E ≤ Qv _ ρ)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L ρ) ≤ 2) :
    XM _ ρ ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) ≤ ZM _ ρ := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hρ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  obtain ⟨hE₀2, hE₀O⟩ := S5B.isPGroup_not_le_of_smul h g hE₀M hE2 hEQ
  rw [S5B.relIndex_centralizer_smul h g hE₀M] at hrel
  have key := (xq_inf_centralizer_le_of_relIndex h hd hXU hE₀M hE₀2 hE₀O hrel).trans
    (sup_le (Uq_le_Z0q h.L_le) (zq_inf_centralizer_le_z0q h))
  have h1 := imM_mono h.le key
  rw [imM_inf_centralizer h.le _ hE₀M, ← S5B.xm_baseA_eq h, ← puAmalgam.zm_baseA h.le] at h1
  have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h1
  rwa [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← xm_smul,
    ← PU.centralizer_map_mulEquiv, ← zm_smul] at h2

theorem xm_inf_dSub_inf_centralizer_le (hd : S5.IsSp4Data M T L 1 F a)
    {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ ρ) (hE2 : IsPGroup 2 E) (hEQ : ¬ E ≤ Qv _ ρ)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L ρ) ≤ 2) :
    XM _ ρ ⊓ S5.dSub h.le L ρ ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) ≤
      stabCenter _ ρ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hρ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  obtain ⟨hE₀2, hE₀O⟩ := S5B.isPGroup_not_le_of_smul h g hE₀M hE2 hEQ
  rw [S5B.relIndex_centralizer_smul h g hE₀M] at hrel
  have key := zq_inf_centralizer_le_of_relIndex h hd hE₀M hE₀2 hE₀O hrel
  have h1 : imM h.le (Xq M ⊓ Dq M L ⊓ Subgroup.centralizer (E₀ : Set G)) ≤
      stabCenter _ (baseA (puAmalgam h.le)) := by
    rw [S5B.stabCenter_baseA]
    exact imM_mono h.le fun x hx => ⟨Xq_le M hx.1.1, key ⟨⟨hx.1.1, hx.1.2.2⟩, hx.2⟩⟩
  rw [imM_inf_centralizer h.le _ hE₀M, imM_inf, ← S5B.xm_baseA_eq h, ← S5B.dSub_baseA h] at h1
  have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h1
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← xm_smul, ← S5B.dSub_smul h.le hLn,
    ← PU.centralizer_map_mulEquiv] at h2
  exact h2.trans (map_stabCenter_le _ g _)

end Vertex

section Critical

variable (h : PUHyp M T L)

private theorem relIndex_centralizer_zm_le_baseA {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α') :
    (Subgroup.centralizer (ZM _ α' : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L (baseA _)) ≤ (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) := by
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ h.hyp20
  have : Finite ↥(ZM (puAmalgam h.le) (baseA _)) := by
    rw [puAmalgam.zm_baseA h.le]
    exact S5B.finite_imM h.le _
  have hsub : Qv _ α' ⊓ ZM _ (baseA (puAmalgam h.le)) ≤
      Subgroup.centralizer (ZM _ α' : Set (puAmalgam h.le).Universal) := by
    rintro y ⟨hyQ, -⟩
    exact Subgroup.mem_centralizer_iff.2 fun w hw =>
      (Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ h.hyp20 hα' hw) y hyQ).symm
  calc (Subgroup.centralizer (ZM _ α' : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L (baseA _))
      ≤ (Subgroup.centralizer (ZM _ α' : Set (puAmalgam h.le).Universal)).relIndex
        (ZM _ (baseA (puAmalgam h.le))) := by
        refine Subgroup.relIndex_le_of_le_right ?_ Subgroup.FiniteIndex.index_ne_zero
        rw [S5B.uSub_baseA h, puAmalgam.zm_baseA h.le]
        exact imM_mono h.le (Uq_le_Z0q h.L_le)
    _ ≤ (Qv _ α' ⊓ ZM _ (baseA (puAmalgam h.le))).relIndex (ZM _ (baseA (puAmalgam h.le))) :=
        Subgroup.relIndex_le_of_le_left hsub Subgroup.FiniteIndex.index_ne_zero
    _ = (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) := Subgroup.inf_relIndex_right _ _

theorem relIndex_centralizer_zm_le {ρ ρ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ ρ ρ') :
    (Subgroup.centralizer (ZM _ ρ' : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L ρ) ≤ (Qv _ ρ').relIndex (ZM _ ρ) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hc.1
  obtain ⟨ρ'', rfl⟩ : ∃ ρ'', ρ' = g • ρ'' := ⟨g⁻¹ • ρ', by rw [smul_inv_smul]⟩
  have hc'' : IsCritical _ (baseA (puAmalgam h.le)) ρ'' := (isCritical_smul _ g _ _).1 hc
  have key := relIndex_centralizer_zm_le_baseA h hc''
  rwa [S5B.uSub_smul h.le hLn, zm_smul, PU.centralizer_map_mulEquiv, qv_smul, zm_smul,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

theorem zm_le_stab_isPGroup_not_le {ρ ρ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ ρ ρ') :
    ZM _ ρ' ≤ stab _ ρ ∧ IsPGroup 2 (ZM _ ρ') ∧ ¬ ZM _ ρ' ≤ Qv _ ρ := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hρ' : IsMVtx _ ρ' := hc.isMVtx_right _ hyp
  have hc' := ms22_iii _ hyp hb0 h.centHyp hc
  refine ⟨zm_le_stab_of_isCritical _ hyp hb0 hc, ?_, hc'.2.2⟩
  have hadj := adj_geo_one_of_isCritical _ hb0 hc'
  have hnot : ¬ IsMVtx _ (geo _ ρ' ρ 1) := (isMVtx_iff_of_adj _ hadj).1 hρ'
  exact (isPGroup_qv _ hyp hnot).to_le (zm_le_qv_of_dist_lt _ hρ' (by
    rw [dist_eq_one_of_adj _ hadj]; have := two_le_critDist _ hyp hb0; omega))

theorem relIndex_qv_zm_le_two (hd : S5.IsSp4Data M T L 1 F a) {ρ ρ' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ ρ ρ') (hidx : (Qv _ ρ').relIndex (ZM _ ρ) ≤ 2) :
    (Qv _ ρ).relIndex (ZM _ ρ') ≤ 2 := by
  obtain ⟨hE, hE2, -⟩ := zm_le_stab_isPGroup_not_le h hc
  exact relIndex_qv_le_two h hd hc.1 hE hE2 ((relIndex_centralizer_zm_le h hc).trans hidx)

theorem xm_inf_centralizer_zm_le (hd : S5.IsSp4Data M T L 1 F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {ρ ρ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ ρ ρ')
    (hidx : (Qv _ ρ').relIndex (ZM _ ρ) ≤ 2) :
    XM _ ρ ⊓ Subgroup.centralizer (ZM _ ρ' : Set (puAmalgam h.le).Universal) ≤
      S5.uSub h.le L ρ ⊔ (XM _ ρ ⊓ stabCenter _ ρ) := by
  obtain ⟨hE, hE2, hEQ⟩ := zm_le_stab_isPGroup_not_le h hc
  exact xm_inf_centralizer_le h hd hXU hc.1 hE hE2 hEQ
    ((relIndex_centralizer_zm_le h hc).trans hidx)

theorem xm_inf_centralizer_zm_le_zm (hd : S5.IsSp4Data M T L 1 F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {ρ ρ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ ρ ρ')
    (hidx : (Qv _ ρ').relIndex (ZM _ ρ) ≤ 2) :
    XM _ ρ ⊓ Subgroup.centralizer (ZM _ ρ' : Set (puAmalgam h.le).Universal) ≤ ZM _ ρ := by
  obtain ⟨hE, hE2, hEQ⟩ := zm_le_stab_isPGroup_not_le h hc
  exact xm_inf_centralizer_le_zm h hd hXU hc.1 hE hE2 hEQ
    ((relIndex_centralizer_zm_le h hc).trans hidx)

end Critical

section Split

theorem xq_inf_centralizer_eq (h : PUHyp M T L) {k : ℕ} (hd : S5.IsSp4Data M T L k F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {J₀ : Subgroup G} (hJ₀M : J₀ ≤ M) :
    Xq M ⊓ Subgroup.centralizer (J₀ : Set G) =
      Uq M T L ⊓ Subgroup.centralizer (J₀ : Set G) ⊔
        Zq M L ⊓ Subgroup.centralizer (J₀ : Set G) := by
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hZn : M ≤ Subgroup.normalizer (Zq M L : Set G) := le_normalizer_Zq h.le_normalizer
  refine le_antisymm ?_ (sup_le (inf_le_inf_right _ h.Uq_le_Xq) (inf_le_inf_right _ inf_le_left))
  rintro x ⟨hxX, hxJ⟩
  have hZU : Zq M L ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    (inf_le_left.trans (Xq_le M)).trans (le_normalizer_Uq h.le_normalizer)
  have hx' : x ∈ ((Uq M T L ⊔ Zq M L : Subgroup G) : Set G) := hXU ▸ hxX
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZU] at hx'
  obtain ⟨u, hu, c, hc, rfl⟩ := hx'
  have huX : u ∈ Xq M := h.Uq_le_Xq hu
  have hboth : ∀ j ∈ J₀, j * u * j⁻¹ = u ∧ j * c * j⁻¹ = c := by
    intro j hj
    have hjM := hJ₀M hj
    have hjx : j * (u * c) = (u * c) * j := Subgroup.mem_centralizer_iff.1 hxJ j hj
    have hc' : j * c * j⁻¹ ∈ Zq M L := (Subgroup.mem_normalizer_iff.1 (hZn hjM) c).1 hc
    have hprod : (j * u * j⁻¹) * (j * c * j⁻¹) = u * c := by
      calc (j * u * j⁻¹) * (j * c * j⁻¹) = j * (u * c) * j⁻¹ := by group
        _ = u * c := by rw [hjx, mul_inv_cancel_right]
    have hcomm : j * u * j⁻¹ * u⁻¹ = c * (j * c * j⁻¹)⁻¹ := by
      have h1 : j * u * j⁻¹ = u * c * (j * c * j⁻¹)⁻¹ := by
        rw [← hprod, mul_inv_cancel_right]
      rw [h1]
      have h2 : u * (c * (j * c * j⁻¹)⁻¹) = (c * (j * c * j⁻¹)⁻¹) * u :=
        mul_comm_of_mem_Xq huX (mul_mem hc.1 (inv_mem hc'.1))
      calc u * c * (j * c * j⁻¹)⁻¹ * u⁻¹ = u * (c * (j * c * j⁻¹)⁻¹) * u⁻¹ := by group
        _ = c * (j * c * j⁻¹)⁻¹ := by rw [h2, mul_inv_cancel_right]
    have hL : j * u * j⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
      rw [hcomm]
      exact (mul_mem hc (inv_mem hc')).2
    have hju : j * u * j⁻¹ = u := hlift j hjM u hu hL
    refine ⟨hju, ?_⟩
    rw [hju] at hprod
    exact mul_left_cancel hprod
  refine Subgroup.mul_mem_sup ⟨hu, Subgroup.mem_centralizer_iff.2 fun j hj => ?_⟩
    ⟨hc, Subgroup.mem_centralizer_iff.2 fun j hj => ?_⟩
  · calc j * u = j * u * j⁻¹ * j := by group
      _ = u * j := by rw [(hboth j hj).1]
  · calc j * c = j * c * j⁻¹ * j := by group
      _ = c * j := by rw [(hboth j hj).2]

end Split

section EdgeT

theorem zq_le_centralizer_of_two_le (h : PUHyp M T L) {k : ℕ} (hd : S5.IsSp4Data M T L k F a)
    (hk : 2 ≤ k) : Zq M L ≤ Subgroup.centralizer (M : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  refine (S5B.eq_sup_pCoreOf h hd hk).le.trans (sup_le ?_ ?_)
  · exact Subgroup.le_centralizer_iff.1 inf_le_right
  · refine Subgroup.le_centralizer_iff.1 (inf_le_left.trans ?_)
    exact (PU.omegaOneCenterOf_le_centerOf (pCoreOf 2 M)).trans inf_le_right

theorem exists_mem_T_not_mem_commutator (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a) :
    ∃ t : ↥M, (t : G) ∈ T ∧ a t ∉ commutator (MSP.Sp4 F) := by
  have hF : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hd.2.1, pow_one]
  obtain ⟨c⟩ := MSP.nonempty_ringEquiv_of_card_two hF
  by_contra hne
  push Not at hne
  have hT : (T.subgroupOf M).map a ≤ commutator (MSP.Sp4 F) := by
    rintro _ ⟨t, ht, rfl⟩
    exact hne t (Subgroup.mem_subgroupOf.1 ht)
  have htop : (⊤ : Subgroup ↥M) = L.subgroupOf M ⊔ T.subgroupOf M := by
    rw [← Subgroup.subgroupOf_sup h.L_le h.le, ← h.eq_sup, Subgroup.subgroupOf_self]
  have hle : (⊤ : Subgroup (MSP.Sp4 F)) ≤ commutator (MSP.Sp4 F) := by
    rw [← Subgroup.map_top_of_surjective a hd.2.2.1, htop, Subgroup.map_sup,
      map_L_eq_commutator h hd]
    exact sup_le le_rfl hT
  have hidx := MSP.index_commutator c
  rw [top_le_iff.1 hle, Subgroup.index_top] at hidx
  omega

theorem zq_inf_centralizer_T_le (h : PUHyp M T L) {k : ℕ} (hd : S5.IsSp4Data M T L k F a) :
    Zq M L ⊓ Subgroup.centralizer (T : Set G) ≤ Subgroup.centralizer (M : Set G) := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by have := hd.1; omega
    obtain ⟨t, htT, hto⟩ := exists_mem_T_not_mem_commutator h hd
    have heq := inf_centralizer_eq_of_not_mem h hd h.le htT hto
    rw [heq]
    exact inf_le_right
  · exact inf_le_left.trans (zq_le_centralizer_of_two_le h hd hk)

theorem xm_inf_centralizer_inf_centralizer_qv_le (h : PUHyp M T L) {k : ℕ}
    (hd : S5.IsSp4Data M T L k F a) {ρ ε : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ)
    (hρε : (puAmalgam h.le).treeGraph.Adj ρ ε) :
    XM _ ρ ⊓ Subgroup.centralizer (puTrans h.le L ρ : Set (puAmalgam h.le).Universal) ⊓
        Subgroup.centralizer (Qv _ ε : Set (puAmalgam h.le).Universal) ≤ stabCenter _ ρ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl, rfl⟩ := exists_smul_base_edge _ hρ hρε
  have h1 : XM _ (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) ⊓
      Subgroup.centralizer (Qv _ (baseB (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) ≤
      stabCenter _ (baseA (puAmalgam h.le)) := by
    rw [S5B.xm_baseA_eq h, S5B.puTrans_L_baseA h, puAmalgam.qv_baseB,
      ← imM_inf_centralizer h.le _ h.L_le, ← imM_inf_centralizer h.le _ h.le,
      S5B.stabCenter_baseA]
    exact imM_mono h.le (le_inf (inf_le_left.trans (inf_le_left.trans (Xq_le M)))
      (zq_inf_centralizer_T_le h hd))
  have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h1
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← xm_smul, ← PU.centralizer_map_mulEquiv,
    ← puTrans_smul h.le hLn, ← PU.centralizer_map_mulEquiv, ← qv_smul] at h2
  exact h2.trans (map_stabCenter_le _ g _)

end EdgeT

section XU

theorem xm_eq_uSub_sup_centralizer (h : PUHyp M T L) (hXU : Xq M = Uq M T L ⊔ Zq M L)
    {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) :
    XM _ ρ = S5.uSub h.le L ρ ⊔ XM _ ρ ⊓
      Subgroup.centralizer (puTrans h.le L ρ : Set (puAmalgam h.le).Universal) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hρ
  have e0 : XM _ (baseA (puAmalgam h.le)) = S5.uSub h.le L (baseA _) ⊔
      XM _ (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) := by
    rw [S5B.uSub_baseA h, S5B.puTrans_L_baseA h, S5B.xm_baseA_eq h,
      ← imM_inf_centralizer h.le _ h.L_le,
      ← S5B.imM_sup_of_le h.le (Uq_le h.L_le) (inf_le_left.trans (Xq_le M))]
    conv_lhs => rw [hXU]
  rw [xm_smul, S5B.uSub_smul h.le hLn, puTrans_smul h.le hLn, PU.centralizer_map_mulEquiv,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← Subgroup.map_sup, ← e0]

theorem xm_inf_centralizer_le_stabCenter (h : PUHyp M T L)
    (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G)) {ρ : Vtx (puAmalgam h.le)}
    (hρ : IsMVtx _ ρ) :
    XM _ ρ ⊓ Subgroup.centralizer (puTrans h.le L ρ : Set (puAmalgam h.le).Universal) ≤
      stabCenter _ ρ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hρ
  have h1 : XM _ (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) ≤
      stabCenter _ (baseA (puAmalgam h.le)) := by
    rw [S5B.xm_baseA_eq h, S5B.puTrans_L_baseA h, ← imM_inf_centralizer h.le _ h.L_le,
      S5B.stabCenter_baseA]
    exact imM_mono h.le (le_inf (inf_le_left.trans (Xq_le M)) hZc)
  have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h1
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← xm_smul,
    ← PU.centralizer_map_mulEquiv, ← puTrans_smul h.le hLn] at h2
  exact h2.trans (map_stabCenter_le _ g _)

theorem xm_inf_dSub_inf_centralizer_le_of_mem (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) {z : (puAmalgam h.le).Universal}
    (hz : z ∈ stab _ ρ) (hz2 : z ^ 2 = 1) (hzQ : z ∉ Qv _ ρ)
    (hrel : (Subgroup.centralizer ({z} : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L ρ) ≤ 2) :
    XM _ ρ ⊓ S5.dSub h.le L ρ ⊓ Subgroup.centralizer ({z} : Set (puAmalgam h.le).Universal) ≤
      stabCenter _ ρ := by
  have hCE := Subgroup.centralizer_closure ({z} : Set (puAmalgam h.le).Universal)
  rw [← hCE] at hrel ⊢
  have hz2' : z ^ 2 ^ 1 = 1 := by rw [pow_one]; exact hz2
  refine xm_inf_dSub_inf_centralizer_le h hd hρ
    ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hz)) ?_
    (fun hle => hzQ (hle (Subgroup.subset_closure rfl))) hrel
  rintro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_closure_singleton.1 hg
  refine ⟨1, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2', one_zpow]

end XU

end S5Q2

end CFSG.Quasithin.MS93
