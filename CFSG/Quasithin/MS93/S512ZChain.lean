module

public import CFSG.Quasithin.MS93.S5B512Fin
public import CFSG.Quasithin.MS93.S512ZOne
public import CFSG.Quasithin.MS93.S5B512One

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

namespace S512Z

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

@[expose] def GoodInv (h : PUHyp M T L) (k : ℕ) (x y z w : Vtx (puAmalgam h.le)) : Prop :=
  S5.jOff h.le L (2 ^ k) w (geo _ w y 1) ≠ S5.jOff h.le L (2 ^ k) z (geo _ w y 1) ∨
    ((Large h k w z ∨ Large h k z w) ∧
      S5.jOff h.le L (2 ^ k) z (geo _ z x 1) = S5.jOff h.le L (2 ^ k) y (geo _ z x 1) ∧
      (Large h k z y ∨ Large h k y z))

theorem goodInv_smul (h : PUHyp M T L) (g : (puAmalgam h.le).Universal)
    (x y z w : Vtx (puAmalgam h.le)) :
    GoodInv h k (g • x) (g • y) (g • z) (g • w) ↔ GoodInv h k x y z w := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hinj := Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  simp only [GoodInv, geo_smul, S5B.jOff_smul h.le hLn, large_smul, ne_eq, hinj.eq_iff]

omit [Fintype F] in
theorem goodInv_step (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4) {q : ℕ}
    {x y z w v : Vtx (puAmalgam h.le)} (hwy : IsCritical _ w y) (hwyz : geo _ w y 2 = z)
    (hvz : IsCritical _ v z) (hv : v ∈ S5B.lamAt h q a w y z) (hgood : GoodInv h k x y z w) :
    GoodInv h k y z w v := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨y₁, hy₁, rfl⟩ := S5B.exists_mem_stab_of_mem_lamAt h hv
  have hy₁w : y₁ • w = w := (mem_stab _).1 hy₁
  unfold GoodInv at hgood ⊢
  set η := geo _ w y 1 with hη
  have hdwy : (puAmalgam h.le).treeGraph.dist w y = 4 := hwy.2.1.trans hb4
  have hwη : (puAmalgam h.le).treeGraph.Adj w η := adj_geo_one _ (by omega)
  have hηz : (puAmalgam h.le).treeGraph.Adj η z := by
    have := adj_geo _ (u := w) (w := y) (i := 1) (by omega)
    rwa [hwyz] at this
  have hdwz : (puAmalgam h.le).treeGraph.dist w z = 2 := by
    rw [← hwyz]
    exact dist_geo _ (by omega)
  have hdvz : (puAmalgam h.le).treeGraph.dist (y₁ • z) z = 4 := hvz.2.1.trans hb4
  have hvη : (puAmalgam h.le).treeGraph.Adj (y₁ • z) (y₁ • η) := (adj_smul _ y₁ _ _).2 hηz.symm
  have hηw : (puAmalgam h.le).treeGraph.Adj (y₁ • η) w := by
    have := (adj_smul _ y₁ _ _).2 hwη.symm
    rwa [hy₁w] at this
  have hd3 : (puAmalgam h.le).treeGraph.dist (y₁ • η) z = 3 := by
    have t1 := dist_triangle _ (y₁ • z) (y₁ • η) z
    have t2 := dist_triangle _ (y₁ • η) w z
    rw [dist_eq_one_of_adj _ hvη] at t1
    rw [dist_eq_one_of_adj _ hηw, hdwz] at t2
    omega
  have hgeo1 : y₁ • η = geo _ (y₁ • z) z 1 := eq_geo_one _ hvη (by rw [hd3, hdvz])
  have l1 := large_smul h y₁ z w (k := k)
  have l2 := large_smul h y₁ w z (k := k)
  rw [hy₁w] at l1 l2
  by_cases hJ : S5.jOff h.le L (2 ^ k) w η = S5.jOff h.le L (2 ^ k) z η
  · rcases hgood with hne | ⟨hL, -, -⟩
    · exact absurd hJ hne
    · refine Or.inr ⟨?_, hJ, hL⟩
      rcases hL with hL | hL
      · exact Or.inr (l2.2 hL)
      · exact Or.inl (l1.2 hL)
  · left
    have j1 := S5B.jOff_smul h.le hLn (2 ^ k) y₁ z η
    have j2 := S5B.jOff_smul h.le hLn (2 ^ k) y₁ w η
    rw [hy₁w] at j2
    rw [← hgeo1, j1, j2]
    intro he
    exact hJ (Subgroup.map_injective (MulAut.conj y₁).injective he).symm

omit [Fintype F] in
theorem case56_of_mem_lamSel (h : PUHyp M T L) {q : ℕ}
    {S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop}
    {α'' δ δ₀ : Vtx (puAmalgam h.le)} {g₀ : (puAmalgam h.le).Universal}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    (hdδ : (puAmalgam h.le).treeGraph.dist (baseA _) δ = 2)
    (hβδ₀ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ₀) (hg₀δ : g₀ • δ = baseA _)
    (hmem : g₀ • baseA (puAmalgam h.le) ∈ S5B.lamSel h q a S α'' δ₀)
    {l : Submodule F (MSP.V4 F)} (hl : S5.Case56 h q a δ l) : S5.Case56 h q a δ₀ l := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨y, hy, hyeq⟩ := S5B.exists_mem_stab_of_mem_lamSel hmem
  have hyα : y • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hy
  have hd2 : (puAmalgam h.le).treeGraph.dist (g₀ • baseA (puAmalgam h.le)) (baseA _) = 2 := by
    have := dist_smul _ g₀ (baseA (puAmalgam h.le)) δ
    rw [hg₀δ, hdδ] at this
    exact this
  have e1 : y • baseB (puAmalgam h.le) = geo _ (g₀ • baseA (puAmalgam h.le)) (baseA _) 1 := by
    refine eq_geo_one _ ?_ ?_
    · rw [hyeq]
      exact (adj_smul _ y _ _).2 hβδ₀.symm
    · have := dist_smul _ y (baseB (puAmalgam h.le)) (baseA _)
      rw [hyα, dist_eq_one_of_adj _ (adj_baseA_baseB _).symm] at this
      rw [this, hd2]
  have e2 : g₀ • baseB (puAmalgam h.le) = geo _ (g₀ • baseA (puAmalgam h.le)) (baseA _) 1 := by
    refine eq_geo_one _ ((adj_smul _ g₀ _ _).2 (adj_baseA_baseB _)) ?_
    have := dist_smul _ g₀ (baseB (puAmalgam h.le)) δ
    rw [hg₀δ, dist_eq_one_of_adj _ hβδ] at this
    rw [this, hd2]
  have hyβ : y • baseB (puAmalgam h.le) = g₀ • baseB _ := e1.trans e2.symm
  refine ⟨?_, hl.2⟩
  have j1 := S5B.jOff_smul h.le hLn q y δ₀ (baseB _)
  have j2 := S5B.jOff_smul h.le hLn q y (baseA _) (baseB _)
  have j3 := S5B.jOff_smul h.le hLn q g₀ (baseA _) (baseB _)
  have j4 := S5B.jOff_smul h.le hLn q g₀ δ (baseB _)
  rw [← hyeq, hyβ] at j1
  rw [hyα, hyβ] at j2
  rw [hg₀δ] at j4
  refine Subgroup.map_injective (f := (MulAut.conj y).toMonoidHom) (MulAut.conj y).injective ?_
  rw [← j1, ← j2, j3, j4, hl.1]

theorem one_frame (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {δ' : Vtx (puAmalgam h.le)}
    (hc' : IsCritical _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ')
    (hgeo : geo _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ' 2 = α')
    (hmem : baseA _ ∈ S5B.lamAllAtSel h (2 ^ k) a (S5.Opp56 h (2 ^ k) a)
      (geo _ (baseA (puAmalgam h.le)) α' 2) δ')
    (hgood : GoodInv h k δ' α' (geo _ (baseA (puAmalgam h.le)) α' 2) (baseA _))
    {μ : Vtx (puAmalgam h.le)}
    (hμ : μ ∈ S5.lam h (2 ^ k) a α' (geo _ (baseA (puAmalgam h.le)) α' 2)) :
    S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) := by
  have hb0 := h.critDist_pos
  have hd4 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb4
  set δ := geo _ (baseA (puAmalgam h.le)) α' 2 with hδ
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ] at this
  have hdδ : (puAmalgam h.le).treeGraph.dist (baseA _) δ = 2 := dist_geo _ (by omega)
  by_cases h56 : ∃ l, S5.Case56 h (2 ^ k) a δ l
  swap
  · push Not at h56
    exact S5B.s512One_case55 h32 hX2 h52 h54 h hmin hb4 hd hc hαβ hc' hgeo
      (S5B.lamAllAtSel_subset hmem) h56 hμ
  obtain ⟨l, hl⟩ := h56
  obtain ⟨hLin, hJ, hLout⟩ : (Large h k (baseA _) δ ∨ Large h k δ (baseA _)) ∧
      S5.jOff h.le L (2 ^ k) δ (geo _ δ δ' 1) = S5.jOff h.le L (2 ^ k) α' (geo _ δ δ' 1) ∧
      (Large h k δ α' ∨ Large h k α' δ) := by
    rcases hgood with hne | hgood
    · exact absurd (by rw [hαβ]; exact hl.1.symm) hne
    · exact hgood
  obtain ⟨g₀, hg₀δ, hg₀ε, δ₀, hβδ₀, -, hmem₀⟩ := hmem
  have hl₀' := case56_of_mem_lamSel h hβδ hdδ hβδ₀ hg₀δ hmem₀ hl
  obtain ⟨g', x', hg', hx', hconc, hν⟩ := hmem₀
  rcases hconc with ⟨hno, -⟩ | ⟨l₀, hl₀, hc56, hopp⟩
  · exact absurd hl₀' (hno l)
  exact one56_of_large h32 hX2 h52 h54 h hmin hb4 hd hc hαβ hl hc' hgeo hg₀δ hg₀ε hβδ₀ hg' hx'
    hl₀ hc56 hν hJ.symm (fun _ => Or.inr hopp) hLin hLout hμ

theorem chain_extend_good (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h55 : S55)
    (h58 : S5B.S58) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) (hd : S5.IsSp4Data M T L k F a)
    (h56S : S5B.Prod56 h k a (S5.Opp56 h (2 ^ k) a)) {x y z w : Vtx (puAmalgam h.le)}
    (hinv : S5B.ChainInvSel h (2 ^ k) a (S5.Opp56 h (2 ^ k) a) x y z w)
    (hgood : GoodInv h k x y z w) :
    ∃ v, S5B.IsLamStepSel h (2 ^ k) a (S5.Opp56 h (2 ^ k) a) w y v ∧
      S5B.ChainInvSel h (2 ^ k) a (S5.Opp56 h (2 ^ k) a) y z w v ∧ GoodInv h k y z w v := by
  have hb0 := h.critDist_pos
  obtain ⟨hzx, hzxy, hwy, hwyz, hw⟩ := hinv
  obtain ⟨g, hg1, hg2⟩ := S5B.exists_smul_base_of_isCritical h hwy
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
  have hmem : baseA _ ∈ S5B.lamAllAtSel h (2 ^ k) a (S5.Opp56 h (2 ^ k) a)
      (geo _ (baseA (puAmalgam h.le)) (g • y) 2) (g • x) := by
    rw [hgeo2, ← hg1]
    exact S5B.lamAllAtSel_smul g hw
  have hgood' : GoodInv h k (g • x) (g • y) (geo _ (baseA (puAmalgam h.le)) (g • y) 2)
      (baseA _) := by
    rw [hgeo2, ← hg1]
    exact (goodInv_smul h g x y z w).2 hgood
  obtain ⟨μ, hμ, hμc⟩ := S5B.s512chain_sel h32 h55 h58 h hmin hb4 hd h56S hcb hαβ
    fun μ hμ => one_frame h32 hX2 h52 h54 h hmin hb4 hd hcb hαβ hc' hgeo' hmem hgood'
      (S5B.lamSel_subset hμ)
  have hμS : g⁻¹ • μ ∈ S5B.lamAtSel h (2 ^ k) a (S5.Opp56 h (2 ^ k) a) w y (geo _ w y 2) := by
    refine ⟨g, hg1, hg2, ?_⟩
    rw [smul_inv_smul, hwyz, ← hgeo2]
    exact hμ
  have hs : S5B.IsLamStepSel h (2 ^ k) a (S5.Opp56 h (2 ^ k) a) w y (g⁻¹ • μ) := by
    refine ⟨hwy, hμS, ?_⟩
    rw [hwyz]
    have := (isCritical_smul _ g⁻¹ _ _).2 hμc
    rwa [hgeo2, inv_smul_smul] at this
  have hgv := (S5B.lamStep_geo h hb4 (S5B.isLamStepSel_subset hs)).2
  rw [hwyz] at hgv
  have hvz : IsCritical _ (g⁻¹ • μ) z := by
    have := hs.2.2
    rwa [hwyz] at this
  have hvl : g⁻¹ • μ ∈ S5B.lamAt h (2 ^ k) a w y z := by
    have := S5B.lamAtSel_subset hμS
    rwa [hwyz] at this
  refine ⟨g⁻¹ • μ, hs, ⟨hwy, hwyz, hvz, hgv, ?_⟩, goodInv_step h hb4 hwy hwyz hvz hvl hgood⟩
  exact S5B.mem_lamAllAtSel_of_mem_lamAtSel h hwy hμS
    (S5B.not_uSub_le_bSub_of_isCritical h58 h hmin (by omega) hd hwy)

theorem exists_step57 (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h55 : S55)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a)
    {S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop}
    (h56S : S5B.Prod56 h k a S) {δ'' : Vtx (puAmalgam h.le)}
    (hβδ'' : (puAmalgam h.le).treeGraph.Adj (baseB _) δ'')
    (hlt : 2 ^ k < (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L δ''))
    {w y : Vtx (puAmalgam h.le)} (hwy : IsCritical _ w y) :
    ∃ v, IsCritical _ v (geo _ w y 2) ∧ geo _ v (geo _ w y 2) 2 = w ∧
      v ∈ S5B.lamAllAtSel h (2 ^ k) a S w y ∧ Large h k v w := by
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  obtain ⟨g, hg1, hg2⟩ := S5B.exists_smul_base_of_isCritical h hwy
  have hcb : IsCritical _ (baseA (puAmalgam h.le)) (g • y) := by
    rw [← hg1]
    exact (isCritical_smul _ g _ _).2 hwy
  have hαβ : geo _ (baseA (puAmalgam h.le)) (g • y) 1 = baseB _ := by
    rw [← hg1, geo_smul, hg2]
  have hgeo2 : geo _ (baseA (puAmalgam h.le)) (g • y) 2 = g • geo _ w y 2 := by
    rw [← hg1, geo_smul]
  have hd4 : (puAmalgam h.le).treeGraph.dist (baseA _) (g • y) = 4 := hcb.2.1.trans hb4
  have hgα : geo _ (g • y) (baseA (puAmalgam h.le)) 2 =
      geo _ (baseA (puAmalgam h.le)) (g • y) 2 := by
    have := geo_symm _ (show 2 ≤ (puAmalgam h.le).treeGraph.dist (baseA _) (g • y) by omega)
    rwa [hd4] at this
  have hδ''B : ¬ S5.uSub h.le L δ'' ≤ S5.bSub h.le L (baseA _) := by
    intro hle
    rw [Subgroup.relIndex_eq_one.2 hle] at hlt
    exact absurd hlt (not_lt.2 Nat.one_le_two_pow)
  obtain ⟨μ, hμ, hZμ⟩ : ∃ μ ∈ S5B.lamSel h (2 ^ k) a S (g • y) δ'',
      ¬ ZM _ μ ≤ Qv _ (geo _ (g • y) (baseA (puAmalgam h.le)) 2) := by
    by_contra hno
    push Not at hno
    exact absurd (S5B.s57_sel h32 hX2 h52 h54 h55 h hmin hb hd h56S hcb hαβ hβδ'' hno)
      (not_le.2 hlt)
  rw [hgα] at hZμ
  have hμall : μ ∈ S5B.lamAllSel h (2 ^ k) a S (g • y) := ⟨δ'', hβδ'', hδ''B, hμ⟩
  obtain ⟨hμM, -⟩ := S5B.lamAll_facts h (S5B.lamAllSel_subset hμall)
  obtain ⟨y', hy', rfl⟩ := S5B.exists_mem_stab_of_mem_lamSel hμ
  have hy'α : y' • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hy'
  have hdm : (puAmalgam h.le).treeGraph.dist (baseA _)
      (geo _ (baseA (puAmalgam h.le)) (g • y) 2) = 2 := dist_geo _ (by omega)
  have hdδ''2 : (puAmalgam h.le).treeGraph.dist (baseA _) δ'' ≤ 2 := by
    have := dist_triangle _ (baseA (puAmalgam h.le)) (baseB _) δ''
    rwa [dist_eq_one_of_adj _ (adj_baseA_baseB _), dist_eq_one_of_adj _ hβδ''] at this
  have hdμα : (puAmalgam h.le).treeGraph.dist (baseA _) (y' • δ'') =
      (puAmalgam h.le).treeGraph.dist (baseA _) δ'' := by
    have := dist_smul _ y' (baseA (puAmalgam h.le)) δ''
    rwa [hy'α] at this
  have hge : 4 ≤ (puAmalgam h.le).treeGraph.dist (y' • δ'')
      (geo _ (baseA (puAmalgam h.le)) (g • y) 2) := by
    by_contra hlt'
    exact hZμ (zm_le_qv_of_dist_lt _ hμM (by omega))
  have htri := dist_triangle _ (y' • δ'') (baseA (puAmalgam h.le))
    (geo _ (baseA (puAmalgam h.le)) (g • y) 2)
  have e1 : (puAmalgam h.le).treeGraph.dist (y' • δ'') (baseA _) =
      (puAmalgam h.le).treeGraph.dist (baseA _) (y' • δ'') := SimpleGraph.dist_comm
  have hd4' : (puAmalgam h.le).treeGraph.dist (y' • δ'')
      (geo _ (baseA (puAmalgam h.le)) (g • y) 2) = 4 := by omega
  have hdμ2 : (puAmalgam h.le).treeGraph.dist (baseA _) (y' • δ'') = 2 := by omega
  have hcμ : IsCritical _ (y' • δ'') (geo _ (baseA (puAmalgam h.le)) (g • y) 2) :=
    ⟨hμM, by omega, hZμ⟩
  have hgμ : geo _ (y' • δ'') (geo _ (baseA (puAmalgam h.le)) (g • y) 2) 2 = baseA _ := by
    symm
    apply eq_geo_of_dist _ (by rw [SimpleGraph.dist_comm]; exact hdμ2)
    rw [SimpleGraph.dist_comm, hdμ2, hdm, hd4']
  have hlg : Large h k (y' • δ'') (baseA _) := by
    have hδ''M : IsMVtx _ δ'' := (isMVtx_iff_of_adj _ hβδ''.symm).2 (not_isMVtx_baseB _)
    have h1 := large_of_lt_relIndex_bSub h32 h hb hδ''M (by omega) hlt
    have h2 := (large_smul h y' δ'' (baseA _)).2 h1
    rwa [hy'α] at h2
  refine ⟨g⁻¹ • (y' • δ''), ?_, ?_, ⟨g, hg1, hg2, by rw [smul_inv_smul]; exact hμall⟩, ?_⟩
  · have := (isCritical_smul _ g⁻¹ _ _).2 hcμ
    rwa [hgeo2, inv_smul_smul] at this
  · have := geo_smul _ g⁻¹ (y' • δ'') (geo _ (baseA (puAmalgam h.le)) (g • y) 2) 2
    rw [hgμ, hgeo2, inv_smul_smul, ← hg1, inv_smul_smul] at this
    exact this
  · have := (large_smul h g⁻¹ (y' • δ'') (baseA _)).2 hlg
    rwa [← hg1, inv_smul_smul] at this

theorem exists_start (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h55 : S55)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a)
    {S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop}
    (h56S : S5B.Prod56 h k a S) {δ'' : Vtx (puAmalgam h.le)}
    (hβδ'' : (puAmalgam h.le).treeGraph.Adj (baseB _) δ'')
    (hlt : 2 ^ k < (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L δ'')) :
    ∃ x y z w, S5B.ChainInvSel h (2 ^ k) a S x y z w ∧ GoodInv h k x y z w := by
  obtain ⟨α₀', hc₀, -⟩ := exists_isCritical_geo _ h.hyp20 h.critDist_pos
    (isMVtx_baseA (puAmalgam h.le)) (adj_baseA_baseB _)
  obtain ⟨μ₀, hcμ₀, hgμ₀, hμ₀, hLμ₀⟩ :=
    exists_step57 h32 hX2 h52 h54 h55 h hmin hb4 hd h56S hβδ'' hlt hc₀
  by_cases hJ : S5.jOff h.le L (2 ^ k) μ₀ (geo _ μ₀ (geo _ (baseA (puAmalgam h.le)) α₀' 2) 1) =
      S5.jOff h.le L (2 ^ k) (baseA _) (geo _ μ₀ (geo _ (baseA (puAmalgam h.le)) α₀' 2) 1)
  · obtain ⟨v₁, hcv₁, hgv₁, hv₁, hLv₁⟩ :=
      exists_step57 h32 hX2 h52 h54 h55 h hmin hb4 hd h56S hβδ'' hlt hcμ₀
    rw [hgμ₀] at hcv₁ hgv₁
    exact ⟨_, _, _, _, ⟨hcμ₀, hgμ₀, hcv₁, hgv₁, hv₁⟩, Or.inr ⟨Or.inl hLv₁, hJ, Or.inl hLμ₀⟩⟩
  · exact ⟨_, _, _, _, ⟨hc₀, rfl, hcμ₀, hgμ₀, hμ₀⟩, Or.inl hJ⟩

theorem exists_lamSel_crit_of_hP (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h55 : S55)
    (h58 : S5B.S58) (h : PUHyp M T L) (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a)
    {S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop}
    (h56S : S5B.Prod56 h k a S)
    (hidx : ∀ δ, (puAmalgam h.le).treeGraph.Adj (baseB _) δ →
      (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L δ) ≤ 2 ^ k)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) :
    ∃ μ ∈ S5B.lamSel h (2 ^ k) a S α' (geo _ (baseA (puAmalgam h.le)) α' 2),
      IsCritical _ μ (geo _ (baseA (puAmalgam h.le)) α' 2) := by
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hd4 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb4
  have hgα : geo _ α' (baseA (puAmalgam h.le)) 2 = geo _ (baseA (puAmalgam h.le)) α' 2 := by
    have := geo_symm _ (show 2 ≤ (puAmalgam h.le).treeGraph.dist (baseA _) α' by omega)
    rwa [hd4] at this
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) (geo _ (baseA (puAmalgam h.le)) α' 2) := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ] at this
  have hdm : (puAmalgam h.le).treeGraph.dist (baseA _)
      (geo _ (baseA (puAmalgam h.le)) α' 2) = 2 := dist_geo _ (by omega)
  by_contra hno
  push Not at hno
  have hlam : ∀ μ ∈ S5B.lamSel h (2 ^ k) a S α' (geo _ (baseA (puAmalgam h.le)) α' 2),
      ZM _ μ ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2) := by
    intro μ hμ
    rw [hgα]
    by_contra hZ
    obtain ⟨y, hy, rfl⟩ := S5B.exists_mem_stab_of_mem_lamSel hμ
    have hyα : y • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hy
    have hμM : IsMVtx _ (y • geo _ (baseA (puAmalgam h.le)) α' 2) :=
      (isMVtx_smul _ y _).2 (isMVtx_geo_two _ h.hyp20 hb0 hc)
    have hdμ : (puAmalgam h.le).treeGraph.dist (baseA _)
        (y • geo _ (baseA (puAmalgam h.le)) α' 2) = 2 := by
      have := dist_smul _ y (baseA (puAmalgam h.le)) (geo _ (baseA (puAmalgam h.le)) α' 2)
      rw [hyα] at this
      rw [this, hdm]
    have htri := dist_triangle _ (y • geo _ (baseA (puAmalgam h.le)) α' 2) (baseA _)
      (geo _ (baseA (puAmalgam h.le)) α' 2)
    have e1 : (puAmalgam h.le).treeGraph.dist (y • geo _ (baseA (puAmalgam h.le)) α' 2)
        (baseA _) = 2 := by
      rw [SimpleGraph.dist_comm]
      exact hdμ
    have hge : critDist (puAmalgam h.le) ≤ (puAmalgam h.le).treeGraph.dist
        (y • geo _ (baseA (puAmalgam h.le)) α' 2) (geo _ (baseA (puAmalgam h.le)) α' 2) := by
      by_contra hlt
      exact hZ (zm_le_qv_of_dist_lt _ hμM (by omega))
    exact hno _ hμ ⟨hμM, by omega, hZ⟩
  obtain ⟨μ, hμ, hdμ, hZμ, hcard, hidx', hXU, hR⟩ :=
    S5B.s58_mu_sel h32 hX2 h52 h55 h hmin hb hd h56S hc hαβ hβδ
      (S5B.not_uSub_le_bSub_of_isCritical h58 h hmin hb hd hc) hlam
  obtain ⟨z, hz, u, hu, huQ, hzu⟩ := S5B.s58_zu h hb hd hc hZμ hcard hidx' hXU
  exact S5B.s58_contra h hb hd
    (fun γ ε ρ hγ hγε hερ => S5B.relIndex_bSub_uSub_le h hidx hγ hγε hερ) hc hμ hdμ hZμ hR hz hu
    huQ hzu

theorem false_of_chain (hn : S5B.S512Nat) (h310m : S310m) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) (hd : S5.IsSp4Data M T L k F a)
    {S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop}
    (h2 : ∀ α' ν μ₁ μ₂ : Vtx (puAmalgam h.le), S5B.IsChain512Sel h (2 ^ k) a S α' ν μ₁ μ₂ →
      (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k)
    (h3 : ∀ α' ν μ₁ μ₂ : Vtx (puAmalgam h.le), S5B.IsChain512Sel h (2 ^ k) a S α' ν μ₁ μ₂ →
      (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k →
      (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k →
      (S5.bSub h.le L (baseA _)).relIndex (ZM _ μ₁) = 2 ^ k)
    (P : Vtx (puAmalgam h.le) → Vtx (puAmalgam h.le) → Vtx (puAmalgam h.le) →
      Vtx (puAmalgam h.le) → Prop)
    (hext : ∀ x y z w, S5B.ChainInvSel h (2 ^ k) a S x y z w → P x y z w →
      ∃ v, S5B.IsLamStepSel h (2 ^ k) a S w y v ∧ S5B.ChainInvSel h (2 ^ k) a S y z w v ∧
        P y z w v)
    (hstart : ∃ x y z w, S5B.ChainInvSel h (2 ^ k) a S x y z w ∧ P x y z w) : False := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  obtain ⟨x, y, z, w, hinv₀, hP₀⟩ := hstart
  obtain ⟨c₁, hs₀, hinv₁, hP₁⟩ := hext _ _ _ _ hinv₀ hP₀
  obtain ⟨c₂, hs₁, hinv₂, hP₂⟩ := hext _ _ _ _ hinv₁ hP₁
  obtain ⟨c₃, hs₂, hinv₃, hP₃⟩ := hext _ _ _ _ hinv₂ hP₂
  obtain ⟨c₄, hs₃, hinv₄, hP₄⟩ := hext _ _ _ _ hinv₃ hP₃
  obtain ⟨c₅, hs₄, hinv₅, -⟩ := hext _ _ _ _ hinv₄ hP₄
  have t1 := S5B.two_gen_sel h h2 hs₀ hinv₁.2.1 hs₁ hs₂ hinv₁.2.2.2.1
  have t2 := S5B.two_gen_sel h h2 hs₁ hinv₂.2.1 hs₂ hs₃ hinv₂.2.2.2.1
  have t3 := S5B.two_gen_sel h h2 hs₂ hinv₃.2.1 hs₃ hs₄ hinv₃.2.2.2.1
  have r2 := S5B.three_gen_sel h h3 hs₁ hinv₂.2.1 hs₂ hs₃ hinv₂.2.2.2.1 t1 t2
  have r3 := S5B.three_gen_sel h h3 hs₂ hinv₃.2.1 hs₃ hs₄ hinv₃.2.2.2.1 t2 t3
  obtain ⟨g, hg1, hch2'⟩ := S5B.isChain512Sel_frame h hs₁ hinv₂.2.1 hs₂ hs₃ hinv₂.2.2.2.1
  have hch2 := S5B.isChain512Sel_subset hch2'
  have hgeo2 : geo _ (baseA (puAmalgam h.le)) (g • w) 2 = g • c₁ := by
    rw [← hg1, geo_smul, hinv₂.2.2.2.1]
  obtain ⟨F', _, _, a', hF', ha', hnat, hcomm⟩ := hn G M T L h hmin hb4 k F _ _ a hd _ _ _ _ hch2
    (by rw [← hg1, S5B.relIndex_qv_zm_smul]; exact t1)
    (by rw [hgeo2, S5B.relIndex_qv_zm_smul]; exact t2)
    (by rw [← hg1, S5B.relIndex_bSub_zm_smul h]; exact r2)
    (by rw [S5B.relIndex_bSub_zm_smul h]; exact r3)
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
  · rw [hgeo4, ← hg1, S5B.relIndex_bSub_zm_smul h, r2] at hi
    exact lt_irrefl _ hi
  · rw [hgeo4, S5B.relIndex_bSub_zm_smul h, r3] at hi
    exact lt_irrefl _ hi
  ·
    have hmem := S5B.lamAtSel_subset hs₃.2.1
    rw [hinv₄.2.1] at hmem
    obtain ⟨y, hy, hyc⟩ := S5B.exists_mem_stab_of_mem_lamAt h hmem
    apply hi (g * y * g⁻¹)
    · rw [hgeo4, stab_smul]
      exact ⟨y, hy, by simp⟩
    · rw [← hg1, mul_smul, mul_smul, inv_smul_smul, ← hyc]

theorem s512b4_of (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h55 : S55)
    (h56f : S5.S56f) (h2 : S5B.S512TwoF) (h3 : S5B.S512ThreeF)
    (hn : S5B.S512Nat) (h310m : S310m) : S5B.S512b4 := by
  have h58 := S5B.s58_of h32 hX2 h52 h54 h55 (S5B.s56_of_s56f h56f)
  intro G _ _ M T L h hmin hb4 k F _ _ a hd
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have h56S := S5B.prod56_opp (h := h) h56f hmin hb hd
  have h2' := h2 G M T L h hmin hb4 k F _ _ a hd
  have h3' := h3 G M T L h hmin hb4 k F _ _ a hd
  by_cases hidx : ∀ δ, (puAmalgam h.le).treeGraph.Adj (baseB _) δ →
      (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L δ) ≤ 2 ^ k
  · exact S5B.s512b4_sel h58 hn h310m h hmin hb4 hd h2' h3'
      (fun α' hc hαβ => S5B.s58_first_sel h32 hX2 h52 h54 h55 h hmin hb hd h56S hc hαβ)
      (fun α' hc hαβ _ _ _ _ =>
        exists_lamSel_crit_of_hP h32 hX2 h52 h55 h58 h hmin hb4 hd h56S hidx hc hαβ)
  · push Not at hidx
    obtain ⟨δ'', hβδ'', hlt⟩ := hidx
    exact false_of_chain hn h310m h hmin hb4 hd h2' h3' (GoodInv h k)
      (fun _ _ _ _ hinv hgood =>
        chain_extend_good h32 hX2 h52 h54 h55 h58 h hmin hb4 hd h56S hinv hgood)
      (exists_start h32 hX2 h52 h54 h55 h hmin hb4 hd h56S hβδ'' hlt)

theorem s512_of (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h55 : S55)
    (h56f : S5.S56f) (h511 : S5B.S511) (h2 : S5B.S512TwoF)
    (h3 : S5B.S512ThreeF) (hn : S5B.S512Nat) (h310m : S310m) : S512 :=
  S5B.s512_of_parts h511 (s512b4_of h32 hX2 h52 h54 h55 h56f h2 h3 hn h310m)

end S512Z

end CFSG.Quasithin.MS93
