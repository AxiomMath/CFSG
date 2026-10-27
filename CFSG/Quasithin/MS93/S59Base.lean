module

public import CFSG.Quasithin.MS93.S5B58A

public noncomputable section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

namespace S59

section Defs

variable {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M) (L : Subgroup G)

@[expose] def tZero (γ : Vtx (puAmalgam hTM)) : Subgroup (puAmalgam hTM).Universal :=
  Qv _ (baseA (puAmalgam hTM)) ⊓ Subgroup.centralizer
    ((S5.uSub hTM L γ ⊓ S5.bSub hTM L (baseA _) : Subgroup _) : Set (puAmalgam hTM).Universal)

@[expose] def hSub (γ : Vtx (puAmalgam hTM)) : Subgroup (puAmalgam hTM).Universal :=
  ⁅S5.uSub hTM L γ, tZero hTM L γ⁆

end Defs

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section Lift

theorem lift_baseA (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {m u : (puAmalgam h.le).Universal} (hm : m ∈ stab _ (baseA (puAmalgam h.le)))
    (hu : u ∈ S5.uSub h.le L (baseA (puAmalgam h.le)))
    (hc : m * u * m⁻¹ * u⁻¹ ∈ Subgroup.centralizer
      (puTrans h.le L (baseA (puAmalgam h.le)) : Set (puAmalgam h.le).Universal)) :
    m * u * m⁻¹ = u := by
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  rw [puAmalgam.stab_baseA] at hm
  rw [S5B.uSub_baseA h] at hu
  rw [S5B.puTrans_L_baseA h] at hc
  obtain ⟨m₀, -, rfl⟩ := hm
  obtain ⟨u₀, hu₀, rfl⟩ := hu
  have hu₀' : (u₀ : G) ∈ Uq M T L := Subgroup.mem_subgroupOf.1 hu₀
  have hcL : (m₀ : G) * u₀ * (m₀ : G)⁻¹ * (u₀ : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hlA : (puAmalgam h.le).ofA ⟨l, h.L_le hl⟩ ∈ imM h.le L :=
      ⟨⟨l, h.L_le hl⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hc _ hlA
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul] at h1
    have h2 := congrArg Subtype.val ((puAmalgam h.le).ofA_injective h1)
    simpa using h2
  have h3 := hlift m₀ m₀.2 u₀ hu₀' hcL
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (by simpa using h3)

theorem lift_vtx (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {m u : (puAmalgam h.le).Universal}
    (hm : m ∈ stab _ δ) (hu : u ∈ S5.uSub h.le L δ)
    (hc : ⁅m, u⁆ ∈ Subgroup.centralizer (puTrans h.le L δ : Set (puAmalgam h.le).Universal)) :
    ⁅m, u⁆ = 1 := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  rw [mem_stab_smul] at hm
  rw [S5B.uSub_smul h.le hLn, mem_map_conj] at hu
  rw [puTrans_smul h.le hLn, PU.centralizer_map_mulEquiv, mem_map_conj] at hc
  have e : g⁻¹ * ⁅m, u⁆ * g =
      (g⁻¹ * m * g) * (g⁻¹ * u * g) * (g⁻¹ * m * g)⁻¹ * (g⁻¹ * u * g)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e] at hc
  have h1 := lift_baseA h hd hm hu hc
  calc ⁅m, u⁆ = g * ((g⁻¹ * m * g) * (g⁻¹ * u * g) * (g⁻¹ * m * g)⁻¹) * g⁻¹ * u⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = 1 := by rw [h1]; group

theorem commutator_eq_bot_of_le (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ δ)
    (hc : ⁅S5.uSub h.le L δ, E⁆ ≤
      Subgroup.centralizer (puTrans h.le L δ : Set (puAmalgam h.le).Universal)) :
    ⁅S5.uSub h.le L δ, E⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro u hu e he
  rw [Subgroup.mem_bot]
  have h1 : ⁅e, u⁆ = 1 := lift_vtx h hd hδ (hE he) hu (by
    rw [← commutatorElement_inv]
    exact inv_mem (hc (Subgroup.commutator_mem_commutator hu he)))
  rw [← commutatorElement_inv, h1, inv_one]

theorem stab_le_normalizer_uSub (h : PUHyp M T L) (δ : Vtx (puAmalgam h.le)) :
    stab _ δ ≤ Subgroup.normalizer (S5.uSub h.le L δ : Set (puAmalgam h.le).Universal) :=
  le_normalizer_commutator (stab_le_normalizer_zm _ _)
    (stab_le_normalizer_puTrans h.le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer) _)

theorem stab_le_normalizer_bSub (h : PUHyp M T L) (δ : Vtx (puAmalgam h.le)) :
    stab _ δ ≤ Subgroup.normalizer (S5.bSub h.le L δ : Set (puAmalgam h.le).Universal) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  rw [← S5B.bSub_smul h.le hLn, (mem_stab _).1 hg]

end Lift

section Cent

variable {Γ : Type*} [Group Γ]

theorem mem_centralizer_of_le {x : Γ} {Y : Subgroup Γ}
    (hY : Y ≤ Subgroup.centralizer ({x} : Set Γ)) : x ∈ Subgroup.centralizer (Y : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.1 (hY hy) x rfl).symm

theorem centralizer_sup (A B : Subgroup Γ) :
    Subgroup.centralizer ((A ⊔ B : Subgroup Γ) : Set Γ) =
      Subgroup.centralizer (A : Set Γ) ⊓ Subgroup.centralizer (B : Set Γ) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left))
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_right))
  · rintro x ⟨hA, hB⟩
    refine mem_centralizer_of_le (sup_le ?_ ?_)
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact (Subgroup.mem_centralizer_iff.1 hA y hy).symm
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact (Subgroup.mem_centralizer_iff.1 hB y hy).symm

end Cent

section Normal

theorem tZero_eq (h : PUHyp M T L) (γ : Vtx (puAmalgam h.le)) :
    tZero h.le L γ = Qv _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer
      ((S5.uSub h.le L γ ⊓ S5.bSub h.le L (baseA _) ⊔ ZM _ (baseA (puAmalgam h.le)) :
        Subgroup _) : Set (puAmalgam h.le).Universal) := by
  have hQZ : Qv _ (baseA (puAmalgam h.le)) ≤
      Subgroup.centralizer (ZM _ (baseA (puAmalgam h.le)) : Set _) :=
    Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ h.hyp20 (isMVtx_baseA _))
  rw [tZero, centralizer_sup]
  apply le_antisymm
  · exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hQZ))
  · exact le_inf inf_le_left (inf_le_right.trans inf_le_left)

theorem le_normalizer_tZero (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {ε γ : Vtx (puAmalgam h.le)} (hαε : (puAmalgam h.le).treeGraph.Adj (baseA _) ε)
    (hεγ : (puAmalgam h.le).treeGraph.Adj ε γ) :
    stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (tZero h.le L γ : Set (puAmalgam h.le).Universal) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hα := isMVtx_baseA (puAmalgam h.le)
  set Y := S5.uSub h.le L γ ⊓ S5.bSub h.le L (baseA _) ⊔ ZM _ (baseA (puAmalgam h.le)) with hYdef
  have hLY : puTrans h.le L (baseA _) ≤ Subgroup.normalizer (Y : Set _) := by
    refine le_normalizer_sup_of_commutator_le
      ((puTrans_le_stab h.le L _).trans (stab_le_normalizer_zm _ _)) ?_
    rw [Subgroup.commutator_le]
    intro v hv l hl
    exact Subgroup.mem_sup_right (S5B.commutator_mem_zm_of_mem_bSub h hb hα hv.2 hl)
  have hTY : Qv _ ε ≤ Subgroup.normalizer (Y : Set _) := by
    have h1 : Qv _ ε ≤ stab _ (baseA (puAmalgam h.le)) :=
      qv_le_stab_of_isMVtx _ h.hyp20 hα hαε
    have h2 : Qv _ ε ≤ stab _ γ := qv_le_stab_of_adj _ hεγ
    exact le_normalizer_sup (le_normalizer_inf (h2.trans (stab_le_normalizer_uSub h γ))
      (h1.trans (stab_le_normalizer_bSub h _))) (h1.trans (stab_le_normalizer_zm _ _))
  have hY : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer (Y : Set _) := by
    intro g hg
    obtain ⟨l, hl, t, ht, rfl⟩ := S5B.exists_puTrans_mul h hαε hg
    exact mul_mem (hLY hl) (hTY ht)
  rw [tZero_eq h γ, ← hYdef]
  exact le_normalizer_inf (stab_le_normalizer_qv _ _) (le_normalizer_centralizer hY)

theorem tZero_smul_eq (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {ε γ : Vtx (puAmalgam h.le)} (hαε : (puAmalgam h.le).treeGraph.Adj (baseA _) ε)
    (hεγ : (puAmalgam h.le).treeGraph.Adj ε γ) {g : (puAmalgam h.le).Universal}
    (hg : g ∈ stab _ (baseA (puAmalgam h.le))) : tZero h.le L (g • γ) = tZero h.le L γ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hgα : g • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hg
  have e1 : tZero h.le L (g • γ) = (tZero h.le L γ).map (MulAut.conj g).toMonoidHom := by
    rw [tZero, tZero, Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      ← PU.centralizer_map_mulEquiv, Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      ← S5B.uSub_smul h.le hLn, ← qv_smul, ← S5B.bSub_smul h.le hLn, hgα]
  rw [e1]
  exact map_conj_eq_of_mem_normalizer (le_normalizer_tZero h hb hαε hεγ hg)

end Normal

section Mem

omit [Finite G] in
theorem tZero_le_qv (hTM : T ≤ M) (γ : Vtx (puAmalgam hTM)) :
    tZero hTM L γ ≤ Qv _ (baseA (puAmalgam hTM)) := inf_le_left

omit [Finite G] in
theorem tZero_le_centralizer (hTM : T ≤ M) (γ : Vtx (puAmalgam hTM)) :
    tZero hTM L γ ≤ Subgroup.centralizer
      ((S5.uSub hTM L γ ⊓ S5.bSub hTM L (baseA _) : Subgroup _) : Set _) := inf_le_right

theorem zm_le_tZero (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {ε γ ν : Vtx (puAmalgam h.le)} (hαε : (puAmalgam h.le).treeGraph.Adj (baseA _) ε)
    (hεγ : (puAmalgam h.le).treeGraph.Adj ε γ) (hν : IsMVtx _ ν)
    (hν1 : 1 ≤ (puAmalgam h.le).treeGraph.dist (baseA _) ν)
    (hν2 : (puAmalgam h.le).treeGraph.dist (baseA _) ν + 2 ≤ critDist (puAmalgam h.le)) :
    ZM _ ν ≤ tZero h.le L γ := by
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαε' : (puAmalgam h.le).treeGraph.Adj (baseA _) (geo _ (baseA (puAmalgam h.le)) ν 1) :=
    adj_geo_one _ hν1
  have hε'ν : (puAmalgam h.le).treeGraph.dist (geo _ (baseA (puAmalgam h.le)) ν 1) ν =
      (puAmalgam h.le).treeGraph.dist (baseA _) ν - 1 := dist_geo_right _ hν1
  have hle := S5B.uSub_inf_bSub_le_qv h hb (ν := ν) hα hαε hαε' hεγ (by omega) (by omega)
  refine le_inf (zm_le_qv_of_dist_lt _ hν (by rw [SimpleGraph.dist_comm]; omega)) ?_
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ h.hyp20 hν hz) v (hle hv)

theorem xm_inf_le_tZero (h : PUHyp M T L) {γ σ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hγσ : (puAmalgam h.le).treeGraph.dist γ σ < critDist (puAmalgam h.le)) :
    XM _ σ ⊓ Qv _ (baseA (puAmalgam h.le)) ≤ tZero h.le L γ := by
  refine le_inf inf_le_right ?_
  rintro x ⟨hx, -⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvQ : v ∈ Qv _ σ := zm_le_qv_of_dist_lt _ hγ hγσ (S5B.uSub_le_zm h.le γ hv.1)
  exact Subgroup.mem_centralizer_iff.1 (xm_le_centralizer _ σ hx) v hvQ

end Mem

section Comm

theorem commutator_zm_tZero (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {ε γ : Vtx (puAmalgam h.le)} (hαε : (puAmalgam h.le).treeGraph.Adj (baseA _) ε)
    (hεγ : (puAmalgam h.le).treeGraph.Adj ε γ) :
    ⁅ZM _ γ, tZero h.le L γ⁆ = hSub h.le L γ := by
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hγ : IsMVtx _ γ := by
    have h1 := isMVtx_iff_of_adj _ hαε
    have h2 := isMVtx_iff_of_adj _ hεγ
    tauto
  have hTn := le_normalizer_tZero h hb (L := L) hαε hεγ
  have hεα : Qv _ ε ≤ stab _ (baseA (puAmalgam h.le)) := qv_le_stab_of_isMVtx _ h.hyp20 hα hαε
  have hdγ : (puAmalgam h.le).treeGraph.dist γ (baseA _) < critDist (puAmalgam h.le) := by
    have t := dist_triangle _ γ ε (baseA (puAmalgam h.le))
    rw [dist_eq_one_of_adj _ hεγ.symm, dist_eq_one_of_adj _ hαε.symm] at t
    omega
  apply le_antisymm
  · rw [S5B.zm_eq_zh_sup_uSub h hγ hεγ.symm]
    refine S5B.commutator_sup_le_of_le ?_ ?_ ?_ le_rfl
    · exact le_normalizer_commutator
        (((zh_le_qv _ ε).trans (qv_le_stab_of_adj _ hεγ)).trans (stab_le_normalizer_uSub h γ))
        (((zh_le_qv _ ε).trans hεα).trans hTn)
    · exact le_normalizer_commutator
        (((S5B.uSub_le_zm h.le γ).trans ((zm_le_qv_self _ hγ h.critDist_pos).trans
          (qv_le_stab _ _))).trans (stab_le_normalizer_uSub h γ))
        (((S5B.uSub_le_zm h.le γ).trans ((zm_le_qv_of_dist_lt _ hγ hdγ).trans
          (qv_le_stab _ _))).trans hTn)
    · have hc : tZero h.le L γ ≤ Subgroup.centralizer (ZH _ ε : Set _) :=
        (tZero_le_qv h.le γ).trans ((qv_le_qv _ h.hyp20 hα hαε).trans
          (Subgroup.le_centralizer_iff.1 (zh_le_centralizer _ ε)))
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer.2 hc]
      exact bot_le
  · exact Subgroup.commutator_mono (S5B.uSub_le_zm h.le γ) le_rfl

end Comm

end S59

end CFSG.Quasithin.MS93
