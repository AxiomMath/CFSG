module

public import CFSG.Quasithin.MS93.S512ZOne
public import CFSG.Quasithin.MS93.S512ZStmt
public import CFSG.Quasithin.MS93.S512TThree
public import CFSG.Quasithin.MS93.S512TTwo
public import CFSG.Quasithin.MS93.S512NBase

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

namespace S512Z

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem relIndex_bSub_le_relIndex_centralizer_at (h32 : S32) (h : PUHyp M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {u δ : Vtx (puAmalgam h.le)} (hu : IsMVtx _ u)
    (hδM : IsMVtx _ δ) (hd : (puAmalgam h.le).treeGraph.dist u δ = 2) :
    (S5.bSub h.le L u).relIndex (S5.uSub h.le L δ) ≤
      (Subgroup.centralizer (Qv _ u : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L δ) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hu
  have hδ' : δ = g • (g⁻¹ • δ) := by rw [smul_inv_smul]
  rw [hδ']
  have hδ₁M : IsMVtx _ (g⁻¹ • δ) := (isMVtx_smul _ g⁻¹ _).2 hδM
  have hd₁ : (puAmalgam h.le).treeGraph.dist (baseA _) (g⁻¹ • δ) = 2 := by
    have := dist_smul _ g⁻¹ (g • baseA (puAmalgam h.le)) δ
    rw [inv_smul_smul] at this
    rw [this, hd]
  have h1 := relIndex_bSub_le_relIndex_centralizer h32 h hb hδ₁M hd₁
  rw [S5B.bSub_smul h.le hLn, S5B.uSub_smul h.le hLn, qv_smul, PU.centralizer_map_mulEquiv,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact h1

theorem le_relIndex_bSub_of_isCritical (h58 : S5B.S58) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ γ') :
    2 ^ k ≤ (S5.bSub h.le L γ).relIndex (S5.uSub h.le L (geo _ γ γ' 2)) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, hg1, hg2⟩ := S5B.exists_smul_base_of_isCritical h hc
  have hc' : IsCritical _ (baseA (puAmalgam h.le)) (g • γ') := by
    rw [← hg1]
    exact (isCritical_smul _ g _ _).2 hc
  have hαβ : geo _ (baseA (puAmalgam h.le)) (g • γ') 1 = baseB _ := by
    rw [← hg1, geo_smul, hg2]
  have h3 := (h58 G M T L h hmin hb k F _ _ a hd (g • γ') hc' hαβ).2.2
  rw [← hg1, geo_smul, S5B.uSub_smul h.le hLn, S5B.bSub_smul h.le hLn,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at h3
  exact h3

theorem relIndex_centralizer_le_of_le (h : PUHyp M T L) {u : Vtx (puAmalgam h.le)}
    (hu : IsMVtx _ u) {K K' : Subgroup (puAmalgam h.le).Universal} (hKK : K ≤ K') :
    (Subgroup.centralizer (K : Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L u) ≤
      (Subgroup.centralizer (K' : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L u) := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hu
  have hadj : (puAmalgam h.le).treeGraph.Adj (g • baseA (puAmalgam h.le))
      (g • baseB (puAmalgam h.le)) := (adj_smul _ g _ _).2 (adj_baseA_baseB _)
  have hη : ¬ IsMVtx _ (g • baseB (puAmalgam h.le)) := by
    rw [isMVtx_smul]
    exact not_isMVtx_baseB _
  have : Finite ↥(Qv (puAmalgam h.le) (g • baseB (puAmalgam h.le))) :=
    finite_qv _ h.hyp20 hη
  have hUs : S5.uSub h.le L (g • baseA (puAmalgam h.le)) ≤ Qv _ (g • baseB (puAmalgam h.le)) :=
    (uSub_le_zm' h _).trans ((zm_le_qv_self _ hu h.critDist_pos).trans
      (qv_le_qv _ h.hyp20 hu hadj))
  have : Finite ↥(S5.uSub h.le L (g • baseA (puAmalgam h.le))) :=
    Finite.of_injective (Subgroup.inclusion hUs) (Subgroup.inclusion_injective hUs)
  exact Subgroup.relIndex_le_of_le_left (Subgroup.centralizer_le hKK)
    (by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)


theorem false_of_not_large (h32 : S32) (h58 : S5B.S58) (hn : S5B.S512Nat) (h310m : S310m)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a) {α' ν μ₁ μ₂ : Vtx (puAmalgam h.le)}
    (hch : S5B.IsChain512 h (2 ^ k) a α' ν μ₁ μ₂)
    (hsm1 : ¬ Large h k (baseA _) (geo _ (baseA (puAmalgam h.le)) α' 2))
    (hsm2 : ¬ Large h k (geo _ (baseA (puAmalgam h.le)) α' 2) (baseA _)) : False := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hk : 1 < 2 ^ k := Nat.one_lt_two_pow (by have := hd.1; omega)
  have hkk : 2 ^ k < (2 ^ k) ^ 2 := by nlinarith
  obtain ⟨hc, -, hcμ, hmid, ⟨y, hy, hμy⟩, hc₂', hc₂, hmid₂', hmid₂, ⟨y', hy', hμ₂y⟩⟩ :=
    S512N.chain_geo h hb4 hch
  set δ := geo _ (baseA (puAmalgam h.le)) α' 2 with hδ
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hδM : IsMVtx _ δ := isMVtx_geo_two _ hyp hb0 hc
  have hμ₁M : IsMVtx _ μ₁ := hcμ.1
  have hμ₂M : IsMVtx _ μ₂ := hc₂'.1
  have hd4 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb4
  have hdδ : (puAmalgam h.le).treeGraph.dist (baseA _) δ = 2 := dist_geo _ (by omega)
  have hdδα' : (puAmalgam h.le).treeGraph.dist δ α' = 2 := by
    rw [dist_geo_right _ (by omega), hd4]
  have hyα : y • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hy
  have hy'μ : y' • μ₁ = μ₁ := (mem_stab _).1 hy'
  have hdμ₁ : (puAmalgam h.le).treeGraph.dist (baseA _) μ₁ = 2 := by
    have := dist_smul _ y (baseA (puAmalgam h.le)) δ
    rw [hyα] at this
    rw [hμy, this, hdδ]
  have hdμ₁μ₂ : (puAmalgam h.le).treeGraph.dist μ₁ μ₂ = 2 := by
    have := dist_smul _ y' μ₁ (baseA (puAmalgam h.le))
    rw [hy'μ] at this
    rw [hμ₂y, this, tdist_comm, hdμ₁]
  have hsmμ₁α : ¬ Large h k μ₁ (baseA _) := by
    have := large_smul h y δ (baseA (puAmalgam h.le)) (k := k)
    rw [hyα, ← hμy] at this
    rw [this]
    exact hsm2
  have hsmαμ₁ : ¬ Large h k (baseA _) μ₁ := by
    have := large_smul h y (baseA (puAmalgam h.le)) δ (k := k)
    rw [hyα, ← hμy] at this
    rw [this]
    exact hsm1
  have hsmμ₂μ₁ : ¬ Large h k μ₂ μ₁ := by
    have := large_smul h y' (baseA (puAmalgam h.le)) μ₁ (k := k)
    rw [hy'μ, ← hμ₂y] at this
    rw [this]
    exact hsmαμ₁
  have H1 : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k := by
    refine le_antisymm ?_ (S512T.le_relIndex_qv_zm h hb4 hd hc)
    by_contra hbad
    push Not at hbad
    have h1 := (S512T.bad_indices h hb4 hd hc hbad).1
    have h2 := relIndex_centralizer_le_of_le h hα (L := L)
      (zm_le_qv_of_dist_lt _ hα' (by rw [tdist_comm, hdδα']; omega) : ZM _ α' ≤ Qv _ δ)
    have h3 := not_lt.1 hsm1
    omega
  have H2 : (Qv _ δ).relIndex (ZM _ μ₁) = 2 ^ k := by
    refine le_antisymm ?_ (S512T.le_relIndex_qv_zm h hb4 hd hcμ)
    by_contra hbad
    push Not at hbad
    have h1 := (S512T.bad_indices h hb4 hd hcμ hbad).1
    have h2 := relIndex_centralizer_le_of_le h hμ₁M (L := L)
      (zm_le_qv_of_dist_lt _ hδM (by rw [tdist_comm, hdδ]; omega) :
        ZM _ δ ≤ Qv _ (baseA (puAmalgam h.le)))
    have h3 := not_lt.1 hsmμ₁α
    omega
  have H3 : (S5.bSub h.le L (baseA _)).relIndex (ZM _ μ₁) = 2 ^ k := by
    rw [S512T.relIndex_bSub_zm_eq h hb4 hcμ hmid]
    refine le_antisymm ((relIndex_bSub_le_relIndex_centralizer h32 h hb hμ₁M hdμ₁).trans
      (not_lt.1 hsmμ₁α)) ?_
    have := le_relIndex_bSub_of_isCritical h58 h hmin hb hd hc₂
    rwa [hmid₂] at this
  have H4 : (S5.bSub h.le L μ₁).relIndex (ZM _ μ₂) = 2 ^ k := by
    rw [S512T.relIndex_bSub_zm_eq h hb4 hc₂' hmid₂']
    refine le_antisymm ((relIndex_bSub_le_relIndex_centralizer_at h32 h hb hμ₁M hμ₂M
      hdμ₁μ₂).trans (not_lt.1 hsmμ₂μ₁)) ?_
    have hcρ : IsCritical _ μ₁ (y' • δ) := by
      have := (isCritical_smul _ y' μ₁ δ).2 hcμ
      rwa [hy'μ] at this
    have hgρ : geo _ μ₁ (y' • δ) 2 = μ₂ := by
      have := geo_smul _ y' μ₁ δ 2
      rw [hy'μ, hmid, ← hμ₂y] at this
      exact this
    have := le_relIndex_bSub_of_isCritical h58 h hmin hb hd hcρ
    rwa [hgρ] at this
  obtain ⟨F', _, _, a', hF', ha', hnat, hcomm⟩ :=
    hn G M T L h hmin hb4 k F _ _ a hd α' ν μ₁ μ₂ hch H1 H2 H3 H4
  have hfull : IsSp4Full M T L := S5.isSp4Full_iff.2 ⟨k, F, _, _, a, hd⟩
  rw [← hmid₂] at hnat hcomm
  rcases h310m G M T L h hmin hfull hb4 μ₂ hc₂ k F' _ _ a' hF' ha' hnat hcomm with hi | hi | hi
  · rw [hmid₂, H3] at hi
    exact lt_irrefl _ hi
  · rw [hmid₂, H4] at hi
    exact lt_irrefl _ hi
  · exact hi y' (by rw [hmid₂]; exact hy') hμ₂y.symm


omit [Fintype F] in
theorem exists_stab_mid (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4) {q : ℕ}
    {α' ν : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _)
    (hc' : IsCritical _ (geo _ (baseA (puAmalgam h.le)) α' 2) ν)
    (hgeo : geo _ (geo _ (baseA (puAmalgam h.le)) α' 2) ν 2 = α')
    (hmem : baseA _ ∈ S5B.lamAt h q a (geo _ (baseA (puAmalgam h.le)) α' 2) ν
      (geo _ (geo _ (baseA (puAmalgam h.le)) α' 2) ν 2)) :
    ∃ y₀ ∈ stab _ (geo _ (baseA (puAmalgam h.le)) α' 2), y₀ • α' = baseA _ ∧
      y₀ • geo _ (geo _ (baseA (puAmalgam h.le)) α' 2) ν 1 = baseB _ := by
  have hb0 := h.critDist_pos
  have hd4 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb4
  set δ := geo _ (baseA (puAmalgam h.le)) α' 2 with hδ
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ] at this
  have hdδ : (puAmalgam h.le).treeGraph.dist (baseA _) δ = 2 := dist_geo _ (by omega)
  have hd' : (puAmalgam h.le).treeGraph.dist δ ν = 4 := hc'.2.1.trans hb4
  have hδε : (puAmalgam h.le).treeGraph.Adj δ (geo _ δ ν 1) := adj_geo_one _ (by omega)
  have hεα' : (puAmalgam h.le).treeGraph.Adj (geo _ δ ν 1) α' := by
    have := adj_geo _ (u := δ) (w := ν) (i := 1) (by omega)
    rwa [hgeo] at this
  obtain ⟨y₀, hy₀, hy₀α⟩ := S5B.exists_mem_stab_of_mem_lamAt h hmem
  rw [hgeo] at hy₀α
  have hy₀δ : y₀ • δ = δ := (mem_stab _).1 hy₀
  refine ⟨y₀, hy₀, hy₀α.symm, ?_⟩
  have h1 : (puAmalgam h.le).treeGraph.Adj (baseA _) (y₀ • geo _ δ ν 1) := by
    rw [hy₀α]
    exact (adj_smul _ y₀ _ _).2 hεα'.symm
  have h2 : (puAmalgam h.le).treeGraph.Adj (y₀ • geo _ δ ν 1) δ := by
    have := (adj_smul _ y₀ _ _).2 hδε.symm
    rwa [hy₀δ] at this
  rw [eq_geo_one _ h1 (by rw [dist_eq_one_of_adj _ h2, hdδ]),
    eq_geo_one _ (adj_baseA_baseB (puAmalgam h.le)) (by rw [dist_eq_one_of_adj _ hβδ, hdδ])]

omit [Fintype F] in
theorem jOff_mid_eq (h : PUHyp M T L) {q : ℕ} {δ ε α' : Vtx (puAmalgam h.le)}
    {y₀ : (puAmalgam h.le).Universal} (hy₀ : y₀ ∈ stab _ δ) (hy₀α : y₀ • α' = baseA _)
    (hy₀ε : y₀ • ε = baseB _)
    (hJ : S5.jOff h.le L q δ (baseB _) = S5.jOff h.le L q (baseA _) (baseB _)) :
    S5.jOff h.le L q α' ε = S5.jOff h.le L q δ ε := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have e1 := S5B.jOff_smul h.le hLn q y₀ α' ε
  have e2 := S5B.jOff_smul h.le hLn q y₀ δ ε
  rw [hy₀α, hy₀ε] at e1
  rw [(mem_stab _).1 hy₀, hy₀ε] at e2
  rw [e1, e2] at hJ
  exact (Subgroup.map_injective (MulAut.conj y₀).injective hJ).symm


theorem oneCF_holds (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h58 : S5B.S58)
    (hn : S5B.S512Nat) (h310m : S310m) : OneCF := by
  intro G _ _ M T L h hmin hb4 k F _ _ a hd α' ν μ₁ μ₂ hchS μ hμ
  have hch := S5B.isChain512Sel_subset hchS
  obtain ⟨hαβ, hs0, hgeo, hc, -, -, -⟩ := hchS
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hc' := hs0.1
  set δ := geo _ (baseA (puAmalgam h.le)) α' 2 with hδ
  by_cases h56 : ∃ l, S5.Case56 h (2 ^ k) a δ l
  swap
  · push Not at h56
    exact S5B.s512One_case55 h32 hX2 h52 h54 h hmin hb4 hd hc hαβ hc' hgeo
      (S5B.lamAllAtSel_subset (S5B.mem_lamAllAtSel_of_mem_lamAtSel h hc' hs0.2.1
        (S5B.not_uSub_le_bSub_of_isCritical h58 h hmin hb hd hc'))) h56 hμ
  obtain ⟨l, hl⟩ := h56
  by_cases hL : Large h k (baseA _) δ ∨ Large h k δ (baseA _)
  swap
  · exact (false_of_not_large h32 h58 hn h310m h hmin hb4 hd hch (not_or.1 hL).1
      (not_or.1 hL).2).elim
  have hd' : (puAmalgam h.le).treeGraph.dist δ ν = 4 := hc'.2.1.trans hb4
  have hεα' : (puAmalgam h.le).treeGraph.Adj (geo _ δ ν 1) α' := by
    have := adj_geo _ (u := δ) (w := ν) (i := 1) (by omega)
    rwa [hgeo] at this
  obtain ⟨y₀, hy₀, hy₀α, hy₀ε⟩ :=
    exists_stab_mid h hb4 hc hαβ hc' hgeo (S5B.lamAtSel_subset hs0.2.1)
  have hJmid := jOff_mid_eq h hy₀ hy₀α hy₀ε hl.1
  have hy₀δ : y₀ • δ = δ := (mem_stab _).1 hy₀
  have e1 := large_smul h y₀ δ α' (k := k)
  rw [hy₀δ, hy₀α] at e1
  have e2 := large_smul h y₀ α' δ (k := k)
  rw [hy₀δ, hy₀α] at e2
  have hLout : Large h k δ α' ∨ Large h k α' δ := hL.symm.imp e1.1 e2.1
  obtain ⟨g₀, hg₀δ, hg₀ε, g', x', hg', hx', hconc, hν⟩ := hs0.2.1
  rw [hgeo] at hconc hν
  have hβδ₀ : (puAmalgam h.le).treeGraph.Adj (baseB _) (g₀ • α') := by
    rw [← hg₀ε]
    exact (adj_smul _ g₀ _ _).2 hεα'
  rcases hconc with ⟨hno, -⟩ | ⟨l₀, hl₀, hc56, hopp⟩
  · exact absurd (case56_smul_of_jOff_eq h hg₀δ hg₀ε hJmid hl) (hno l)
  exact one56_of_large h32 hX2 h52 h54 h hmin hb4 hd hc hαβ hl hc' hgeo hg₀δ hg₀ε hβδ₀
    hg' hx' hl₀ hc56 hν hJmid (fun _ => Or.inr hopp) hL hLout hμ

end S512Z

end CFSG.Quasithin.MS93
