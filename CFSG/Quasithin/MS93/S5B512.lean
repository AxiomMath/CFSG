module

public import CFSG.Quasithin.MS93.S5B58
public import CFSG.Quasithin.MS93.S310Stmt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S5B

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section Transport

omit [Fintype F] in
theorem exists_mem_stab_of_mem_lam {h : PUHyp M T L} {q : ℕ}
    {α' δ μ : Vtx (puAmalgam h.le)} (hμ : μ ∈ S5.lam h q a α' δ) :
    ∃ y ∈ stab _ (baseA (puAmalgam h.le)), μ = y • δ := by
  obtain ⟨g, x, hg, hx, -, hμeq⟩ := hμ
  have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
  rcases hμeq with rfl | rfl
  · exact ⟨g⁻¹, inv_mem hg, rfl⟩
  · exact ⟨x⁻¹ * g⁻¹, mul_mem (inv_mem hxst) (inv_mem hg), by rw [mul_smul]⟩

omit [Fintype F] in
theorem exists_mem_stab_of_mem_lamAt (h : PUHyp M T L) {q : ℕ}
    {γ γ' δ μ : Vtx (puAmalgam h.le)} (hμ : μ ∈ lamAt h q a γ γ' δ) :
    ∃ y ∈ stab _ γ, μ = y • δ := by
  obtain ⟨g, hg1, -, hμ⟩ := hμ
  obtain ⟨y, hy, hyμ⟩ := exists_mem_stab_of_mem_lam hμ
  refine ⟨g⁻¹ * y * g, ?_, ?_⟩
  · have hγ : γ = g⁻¹ • baseA (puAmalgam h.le) := by rw [← hg1, inv_smul_smul]
    rw [hγ, stab_smul]
    exact ⟨y, hy, by simp⟩
  · rw [mul_smul, mul_smul, ← hyμ, inv_smul_smul]

theorem exists_smul_base_of_isCritical (h : PUHyp M T L) {γ γ' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ γ γ') :
    ∃ g : (puAmalgam h.le).Universal, g • γ = baseA _ ∧ g • geo _ γ γ' 1 = baseB _ := by
  have hb0 := h.critDist_pos
  have hd : (puAmalgam h.le).treeGraph.dist γ γ' = critDist (puAmalgam h.le) := hc.2.1
  have hadj : (puAmalgam h.le).treeGraph.Adj γ (geo _ γ γ' 1) := adj_geo_one _ (by omega)
  obtain ⟨g, hg1, hg2⟩ := exists_smul_base_edge _ hc.1 hadj
  refine ⟨g⁻¹, ?_, ?_⟩
  · rw [hg1, inv_smul_smul]
  · rw [hg2, inv_smul_smul]

end Transport

section Steps

omit [Finite G] [Fintype F] in
theorem relIndex_qv_zm_smul {hTM : T ≤ M} (g : (puAmalgam hTM).Universal)
    (x y : Vtx (puAmalgam hTM)) :
    (Qv _ (g • x)).relIndex (ZM _ (g • y)) = (Qv _ x).relIndex (ZM _ y) := by
  rw [qv_smul, zm_smul, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

theorem relIndex_bSub_zm_smul (h : PUHyp M T L) (g : (puAmalgam h.le).Universal)
    (x y : Vtx (puAmalgam h.le)) :
    (S5.bSub h.le L (g • x)).relIndex (ZM _ (g • y)) = (S5.bSub h.le L x).relIndex (ZM _ y) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  rw [bSub_smul h.le hLn, zm_smul,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

omit [Fintype F] in
theorem lamStep_geo (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4) {q : ℕ}
    {γ γ' μ : Vtx (puAmalgam h.le)} (hs : IsLamStep h q a γ γ' μ) :
    (puAmalgam h.le).treeGraph.dist γ μ = 2 ∧ geo _ μ (geo _ γ γ' 2) 2 = γ := by
  obtain ⟨hc, hμ, hμc⟩ := hs
  have hd : (puAmalgam h.le).treeGraph.dist γ γ' = 4 := hc.2.1.trans hb4
  have hdγ2 : (puAmalgam h.le).treeGraph.dist γ (geo _ γ γ' 2) = 2 := dist_geo _ (by omega)
  obtain ⟨y, hy, rfl⟩ := exists_mem_stab_of_mem_lamAt h hμ
  have hyγ : y • γ = γ := (mem_stab _).1 hy
  have h1 : (puAmalgam h.le).treeGraph.dist γ (y • geo _ γ γ' 2) = 2 := by
    have := dist_smul _ y γ (geo _ γ γ' 2)
    rw [hyγ] at this
    rw [this, hdγ2]
  have h2 : (puAmalgam h.le).treeGraph.dist (y • geo _ γ γ' 2) (geo _ γ γ' 2) = 4 :=
    hμc.2.1.trans hb4
  refine ⟨h1, ?_⟩
  symm
  apply eq_geo_of_dist _ (by rw [SimpleGraph.dist_comm]; exact h1)
  rw [SimpleGraph.dist_comm, h1, hdγ2, h2]

theorem not_uSub_le_bSub_of_isCritical (h58 : S58) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ γ') :
    ¬ S5.uSub h.le L (geo _ γ γ' 2) ≤ S5.bSub h.le L γ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, hg1, hg2⟩ := exists_smul_base_of_isCritical h hc
  have hc' : IsCritical _ (baseA (puAmalgam h.le)) (g • γ') := by
    rw [← hg1]
    exact (isCritical_smul _ g _ _).2 hc
  have hαβ : geo _ (baseA (puAmalgam h.le)) (g • γ') 1 = baseB _ := by
    rw [← hg1, geo_smul, hg2]
  have h3 := (h58 G M T L h hmin hb k F _ _ a hd (g • γ') hc' hαβ).2.2
  intro hle
  have e : (S5.bSub h.le L (baseA _)).relIndex
      (S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) (g • γ') 2)) = 1 := by
    rw [Subgroup.relIndex_eq_one, ← hg1, geo_smul, uSub_smul h.le hLn, bSub_smul h.le hLn,
      map_conj_le_map_conj_iff]
    exact hle
  rw [e] at h3
  have := Nat.one_lt_two_pow (show k ≠ 0 by have := hd.1; omega)
  omega

omit [Fintype F] in
theorem mem_lamAllAt_of_mem_lamAt (h : PUHyp M T L) {q : ℕ} {γ γ' μ : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ γ γ') (hμ : μ ∈ lamAt h q a γ γ' (geo _ γ γ' 2))
    (hB : ¬ S5.uSub h.le L (geo _ γ γ' 2) ≤ S5.bSub h.le L γ) : μ ∈ lamAllAt h q a γ γ' := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hb2 := two_le_critDist _ h.hyp20 h.critDist_pos
  have hd : (puAmalgam h.le).treeGraph.dist γ γ' = critDist (puAmalgam h.le) := hc.2.1
  obtain ⟨g, h1, h2, h3⟩ := hμ
  have hadj : (puAmalgam h.le).treeGraph.Adj (geo _ γ γ' 1) (geo _ γ γ' 2) :=
    adj_geo _ (i := 1) (by omega)
  refine ⟨g, h1, h2, g • geo _ γ γ' 2, ?_, ?_, h3⟩
  · rw [← h2]
    exact (adj_smul _ g _ _).2 hadj
  · rw [← h1, uSub_smul h.le hLn, bSub_smul h.le hLn, map_conj_le_map_conj_iff]
    exact hB

omit [Fintype F] in
theorem mem_lamAllAtSel_of_mem_lamAtSel (h : PUHyp M T L) {q : ℕ}
    {S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop}
    {γ γ' μ : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ γ')
    (hμ : μ ∈ lamAtSel h q a S γ γ' (geo _ γ γ' 2))
    (hB : ¬ S5.uSub h.le L (geo _ γ γ' 2) ≤ S5.bSub h.le L γ) : μ ∈ lamAllAtSel h q a S γ γ' := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hb2 := two_le_critDist _ h.hyp20 h.critDist_pos
  have hd : (puAmalgam h.le).treeGraph.dist γ γ' = critDist (puAmalgam h.le) := hc.2.1
  obtain ⟨g, h1, h2, h3⟩ := hμ
  have hadj : (puAmalgam h.le).treeGraph.Adj (geo _ γ γ' 1) (geo _ γ γ' 2) :=
    adj_geo _ (i := 1) (by omega)
  refine ⟨g, h1, h2, g • geo _ γ γ' 2, ?_, ?_, h3⟩
  · rw [← h2]
    exact (adj_smul _ g _ _).2 hadj
  · rw [← h1, uSub_smul h.le hLn, bSub_smul h.le hLn, map_conj_le_map_conj_iff]
    exact hB

@[expose] def ChainInvSel (h : PUHyp M T L) (q : ℕ) (a : ↥M →* ↥(StatedSp 2 F))
    (S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop)
    (x y z w : Vtx (puAmalgam h.le)) : Prop :=
  IsCritical _ z x ∧ geo _ z x 2 = y ∧ IsCritical _ w y ∧ geo _ w y 2 = z ∧
    w ∈ lamAllAtSel h q a S z x

theorem chain_extend_sel (h58 : S58) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) (hd : S5.IsSp4Data M T L k F a)
    {S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop}
    (hch : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      geo _ (baseA _) α' 1 = baseB _ →
      ∀ δ' : Vtx (puAmalgam h.le), IsCritical _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ' →
        geo _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ' 2 = α' →
        baseA _ ∈ lamAllAtSel h (2 ^ k) a S (geo _ (baseA (puAmalgam h.le)) α' 2) δ' →
        ∃ μ ∈ lamSel h (2 ^ k) a S α' (geo _ (baseA (puAmalgam h.le)) α' 2),
          IsCritical _ μ (geo _ (baseA (puAmalgam h.le)) α' 2))
    {x y z w : Vtx (puAmalgam h.le)} (hinv : ChainInvSel h (2 ^ k) a S x y z w) :
    ∃ v, IsLamStepSel h (2 ^ k) a S w y v ∧ ChainInvSel h (2 ^ k) a S y z w v := by
  obtain ⟨hzx, hzxy, hwy, hwyz, hw⟩ := hinv
  obtain ⟨g, hg1, hg2⟩ := exists_smul_base_of_isCritical h hwy
  have hcb : IsCritical _ (baseA (puAmalgam h.le)) (g • y) := by
    rw [← hg1]
    exact (isCritical_smul _ g _ _).2 hwy
  have hαβ : geo _ (baseA (puAmalgam h.le)) (g • y) 1 = baseB _ := by
    rw [← hg1, geo_smul, hg2]
  have hgeo2 : geo _ (baseA (puAmalgam h.le)) (g • y) 2 = g • z := by
    rw [← hg1, geo_smul, hwyz]
  have hc' : IsCritical _ (geo _ (baseA (puAmalgam h.le)) (g • y) 2) (g • x) := by
    rw [hgeo2]
    exact (isCritical_smul _ g _ _).2 hzx
  have hgeo' : geo _ (geo _ (baseA (puAmalgam h.le)) (g • y) 2) (g • x) 2 = g • y := by
    rw [hgeo2, geo_smul, hzxy]
  have hmem : baseA _ ∈ lamAllAtSel h (2 ^ k) a S (geo _ (baseA (puAmalgam h.le)) (g • y) 2)
      (g • x) := by
    rw [hgeo2, ← hg1]
    exact lamAllAtSel_smul g hw
  obtain ⟨μ, hμ, hμc⟩ := hch (g • y) hcb hαβ (g • x) hc' hgeo' hmem
  have hμS : g⁻¹ • μ ∈ lamAtSel h (2 ^ k) a S w y (geo _ w y 2) := by
    refine ⟨g, hg1, hg2, ?_⟩
    rw [smul_inv_smul, hwyz, ← hgeo2]
    exact hμ
  have hs : IsLamStepSel h (2 ^ k) a S w y (g⁻¹ • μ) := by
    refine ⟨hwy, hμS, ?_⟩
    rw [hwyz]
    have := (isCritical_smul _ g⁻¹ _ _).2 hμc
    rwa [hgeo2, inv_smul_smul] at this
  have hgv := (lamStep_geo h hb4 (isLamStepSel_subset hs)).2
  rw [hwyz] at hgv
  refine ⟨g⁻¹ • μ, hs, hwy, hwyz, ?_, hgv, ?_⟩
  · have := hs.2.2
    rwa [hwyz] at this
  · exact mem_lamAllAtSel_of_mem_lamAtSel h hwy hμS
      (not_uSub_le_bSub_of_isCritical h58 h hmin (by omega) hd hwy)

end Steps

section Frame

omit [Fintype F] in
theorem isChain512Sel_frame (h : PUHyp M T L) {q : ℕ}
    {S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop}
    {u₃ u₂ u₁ w v₁ v₂ : Vtx (puAmalgam h.le)}
    (ha : IsLamStepSel h q a S u₁ u₃ w) (hb : geo _ u₁ u₃ 2 = u₂)
    (hc : IsLamStepSel h q a S w u₂ v₁) (hd : IsLamStepSel h q a S v₁ u₁ v₂)
    (he : geo _ w u₂ 2 = u₁) :
    ∃ g : (puAmalgam h.le).Universal, g • w = baseA _ ∧
      IsChain512Sel h q a S (g • u₂) (g • u₃) (g • v₁) (g • v₂) := by
  obtain ⟨hc1, ⟨g, hg1, hg2, hg3⟩, hc3⟩ := hc
  rw [he] at hg3 hc3
  refine ⟨g, hg1, ?_⟩
  have hgeo2 : geo _ (baseA (puAmalgam h.le)) (g • u₂) 2 = g • u₁ := by
    rw [← hg1, geo_smul, he]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hg1, geo_smul, hg2]
  · rw [hgeo2, ← hg1]
    exact isLamStepSel_smul g ha
  · rw [hgeo2, geo_smul, hb]
  · rw [← hg1]
    exact (isCritical_smul _ g _ _).2 hc1
  · rw [hgeo2]
    exact hg3
  · rw [hgeo2]
    exact (isCritical_smul _ g _ _).2 hc3
  · rw [hgeo2]
    exact isLamStepSel_smul g hd

omit [Fintype F] in
theorem two_gen_sel (h : PUHyp M T L)
    {S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop}
    (h2 : ∀ α' ν μ₁ μ₂ : Vtx (puAmalgam h.le), IsChain512Sel h (2 ^ k) a S α' ν μ₁ μ₂ →
      (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k)
    {u₃ u₂ u₁ w v₁ v₂ : Vtx (puAmalgam h.le)}
    (ha : IsLamStepSel h (2 ^ k) a S u₁ u₃ w) (hb : geo _ u₁ u₃ 2 = u₂)
    (hc : IsLamStepSel h (2 ^ k) a S w u₂ v₁) (hd' : IsLamStepSel h (2 ^ k) a S v₁ u₁ v₂)
    (he : geo _ w u₂ 2 = u₁) : (Qv _ u₁).relIndex (ZM _ v₁) = 2 ^ k := by
  obtain ⟨g, hg1, hch⟩ := isChain512Sel_frame h ha hb hc hd' he
  have := h2 _ _ _ _ hch
  have hgeo2 : geo _ (baseA (puAmalgam h.le)) (g • u₂) 2 = g • u₁ := by
    rw [← hg1, geo_smul, he]
  rwa [hgeo2, relIndex_qv_zm_smul] at this

omit [Fintype F] in
theorem three_gen_sel (h : PUHyp M T L)
    {S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop}
    (h3 : ∀ α' ν μ₁ μ₂ : Vtx (puAmalgam h.le), IsChain512Sel h (2 ^ k) a S α' ν μ₁ μ₂ →
      (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k →
      (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k →
      (S5.bSub h.le L (baseA _)).relIndex (ZM _ μ₁) = 2 ^ k)
    {u₃ u₂ u₁ w v₁ v₂ : Vtx (puAmalgam h.le)}
    (ha : IsLamStepSel h (2 ^ k) a S u₁ u₃ w) (hb : geo _ u₁ u₃ 2 = u₂)
    (hc : IsLamStepSel h (2 ^ k) a S w u₂ v₁) (hd' : IsLamStepSel h (2 ^ k) a S v₁ u₁ v₂)
    (he : geo _ w u₂ 2 = u₁) (h2a : (Qv _ u₂).relIndex (ZM _ w) = 2 ^ k)
    (h2b : (Qv _ u₁).relIndex (ZM _ v₁) = 2 ^ k) :
    (S5.bSub h.le L w).relIndex (ZM _ v₁) = 2 ^ k := by
  obtain ⟨g, hg1, hch⟩ := isChain512Sel_frame h ha hb hc hd' he
  have hgeo2 : geo _ (baseA (puAmalgam h.le)) (g • u₂) 2 = g • u₁ := by
    rw [← hg1, geo_smul, he]
  have := h3 _ _ _ _ hch
    (by rw [← hg1, relIndex_qv_zm_smul]; exact h2a)
    (by rw [hgeo2, relIndex_qv_zm_smul]; exact h2b)
  rwa [← hg1, relIndex_bSub_zm_smul h] at this

end Frame

theorem s512b4_sel (h58 : S58) (hn : S512Nat) (h310m : S310m)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a)
    {S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop}
    (h2 : ∀ α' ν μ₁ μ₂ : Vtx (puAmalgam h.le), IsChain512Sel h (2 ^ k) a S α' ν μ₁ μ₂ →
      (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k)
    (h3 : ∀ α' ν μ₁ μ₂ : Vtx (puAmalgam h.le), IsChain512Sel h (2 ^ k) a S α' ν μ₁ μ₂ →
      (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k →
      (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k →
      (S5.bSub h.le L (baseA _)).relIndex (ZM _ μ₁) = 2 ^ k)
    (h58S : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      geo _ (baseA _) α' 1 = baseB _ →
      ∃ μ ∈ lamAllSel h (2 ^ k) a S α', IsCritical _ μ (geo _ α' (baseA (puAmalgam h.le)) 2))
    (hch : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      geo _ (baseA _) α' 1 = baseB _ →
      ∀ δ' : Vtx (puAmalgam h.le), IsCritical _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ' →
        geo _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ' 2 = α' →
        baseA _ ∈ lamAllAtSel h (2 ^ k) a S (geo _ (baseA (puAmalgam h.le)) α' 2) δ' →
        ∃ μ ∈ lamSel h (2 ^ k) a S α' (geo _ (baseA (puAmalgam h.le)) α' 2),
          IsCritical _ μ (geo _ (baseA (puAmalgam h.le)) α' 2)) : False := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  obtain ⟨α₀', hc₀, hαβ₀⟩ := exists_isCritical_geo _ hyp hb0 (isMVtx_baseA (puAmalgam h.le))
    (adj_baseA_baseB _)
  obtain ⟨μ₀, hμ₀, hμ₀c⟩ := h58S α₀' hc₀ hαβ₀
  have hd₀ : (puAmalgam h.le).treeGraph.dist (baseA _) α₀' = 4 := hc₀.2.1.trans hb4
  have hm₀ : geo _ α₀' (baseA (puAmalgam h.le)) 2 = geo _ (baseA (puAmalgam h.le)) α₀' 2 := by
    have := geo_symm _ (show 2 ≤ (puAmalgam h.le).treeGraph.dist (baseA _) α₀' by omega)
    rwa [hd₀] at this
  rw [hm₀] at hμ₀c
  have hinv₀ : ChainInvSel h (2 ^ k) a S α₀' (geo _ (baseA (puAmalgam h.le)) α₀' 2) (baseA _)
      μ₀ := by
    refine ⟨hc₀, rfl, hμ₀c, ?_, 1, one_smul _ _, by rw [one_smul, hαβ₀], by simpa using hμ₀⟩
    obtain ⟨-, hdμ⟩ := lamAll_facts h (lamAllSel_subset hμ₀)
    have hdm : (puAmalgam h.le).treeGraph.dist (baseA _)
        (geo _ (baseA (puAmalgam h.le)) α₀' 2) = 2 := dist_geo _ (by omega)
    have h4 : (puAmalgam h.le).treeGraph.dist μ₀ (geo _ (baseA (puAmalgam h.le)) α₀' 2) = 4 :=
      hμ₀c.2.1.trans hb4
    have hdμ2 : (puAmalgam h.le).treeGraph.dist (baseA _) μ₀ = 2 := by
      have e1 : (puAmalgam h.le).treeGraph.dist μ₀ (baseA _) =
          (puAmalgam h.le).treeGraph.dist (baseA _) μ₀ := SimpleGraph.dist_comm
      have := dist_triangle _ μ₀ (baseA (puAmalgam h.le)) (geo _ (baseA (puAmalgam h.le)) α₀' 2)
      omega
    symm
    apply eq_geo_of_dist _ (by rw [SimpleGraph.dist_comm]; exact hdμ2)
    rw [SimpleGraph.dist_comm, hdμ2, hdm, h4]
  obtain ⟨c₁, hs₀, hinv₁⟩ := chain_extend_sel h58 h hmin hb4 hd hch hinv₀
  obtain ⟨c₂, hs₁, hinv₂⟩ := chain_extend_sel h58 h hmin hb4 hd hch hinv₁
  obtain ⟨c₃, hs₂, hinv₃⟩ := chain_extend_sel h58 h hmin hb4 hd hch hinv₂
  obtain ⟨c₄, hs₃, hinv₄⟩ := chain_extend_sel h58 h hmin hb4 hd hch hinv₃
  obtain ⟨c₅, hs₄, hinv₅⟩ := chain_extend_sel h58 h hmin hb4 hd hch hinv₄
  have t1 := two_gen_sel h h2 hs₀ hinv₁.2.1 hs₁ hs₂ hinv₁.2.2.2.1
  have t2 := two_gen_sel h h2 hs₁ hinv₂.2.1 hs₂ hs₃ hinv₂.2.2.2.1
  have t3 := two_gen_sel h h2 hs₂ hinv₃.2.1 hs₃ hs₄ hinv₃.2.2.2.1
  have r2 := three_gen_sel h h3 hs₁ hinv₂.2.1 hs₂ hs₃ hinv₂.2.2.2.1 t1 t2
  have r3 := three_gen_sel h h3 hs₂ hinv₃.2.1 hs₃ hs₄ hinv₃.2.2.2.1 t2 t3
  obtain ⟨g, hg1, hch2'⟩ := isChain512Sel_frame h hs₁ hinv₂.2.1 hs₂ hs₃ hinv₂.2.2.2.1
  have hch2 := isChain512Sel_subset hch2'
  have hgeo2 : geo _ (baseA (puAmalgam h.le)) (g • μ₀) 2 = g • c₁ := by
    rw [← hg1, geo_smul, hinv₂.2.2.2.1]
  obtain ⟨F', _, _, a', hF', ha', hnat, hcomm⟩ := hn G M T L h hmin hb4 k F _ _ a hd _ _ _ _ hch2
    (by rw [← hg1, relIndex_qv_zm_smul]; exact t1)
    (by rw [hgeo2, relIndex_qv_zm_smul]; exact t2)
    (by rw [← hg1, relIndex_bSub_zm_smul h]; exact r2)
    (by rw [relIndex_bSub_zm_smul h]; exact r3)
  have hc24 : IsCritical _ c₂ c₄ := ms22_iii _ hyp hb0 hC hinv₄.2.2.1
  have hcrit : IsCritical _ (baseA (puAmalgam h.le)) (g • c₄) := by
    rw [← hg1]
    exact (isCritical_smul _ g _ _).2 hc24
  have hg24 : geo _ c₂ c₄ 2 = c₃ := by
    have hd24 : (puAmalgam h.le).treeGraph.dist c₄ c₂ = 4 := hinv₄.2.2.1.2.1.trans hb4
    have := geo_symm _ (show 2 ≤ (puAmalgam h.le).treeGraph.dist c₄ c₂ by omega)
    rw [hd24] at this
    rw [this]
    exact hinv₄.2.2.2.1
  have hgeo4 : geo _ (baseA (puAmalgam h.le)) (g • c₄) 2 = g • c₃ := by
    rw [← hg1, geo_smul, hg24]
  have hfull : IsSp4Full M T L := S5.isSp4Full_iff.2 ⟨k, F, _, _, a, hd⟩
  rw [← hgeo4] at hnat hcomm
  rcases h310m G M T L h hmin hfull hb4 (g • c₄) hcrit k F' _ _ a' hF' ha' hnat hcomm with
    hi | hi | hi
  · rw [hgeo4, ← hg1, relIndex_bSub_zm_smul h, r2] at hi
    exact lt_irrefl _ hi
  · rw [hgeo4, relIndex_bSub_zm_smul h, r3] at hi
    exact lt_irrefl _ hi
  ·
    have hmem := lamAtSel_subset hs₃.2.1
    rw [hinv₄.2.1] at hmem
    obtain ⟨y, hy, hyc⟩ := exists_mem_stab_of_mem_lamAt h hmem
    apply hi (g * y * g⁻¹)
    · rw [hgeo4, stab_smul]
      exact ⟨y, hy, by simp⟩
    · rw [← hg1, mul_smul, mul_smul, inv_smul_smul, ← hyc]

end S5B

end CFSG.Quasithin.MS93
