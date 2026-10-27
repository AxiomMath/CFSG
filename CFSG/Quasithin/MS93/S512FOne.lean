module

public import CFSG.Quasithin.MS93.S512ZOneC
public import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Card
public import CFSG.Quasithin.MS93.MSPLeviQ
public import CFSG.Quasithin.MS93.S510Path
public import CFSG.Quasithin.MS93.S512TBad
public import CFSG.Quasithin.MS93.S512TStmt
public import CFSG.Quasithin.MS93.S5A56L
public import CFSG.Quasithin.MS93.S5B56R
public import CFSG.Quasithin.Vol2.Ch11SecBFacts
public import CFSG.Quasithin.Vol2.Ch11SecCFacts
public import CFSG.Quasithin.Vol2.Ch11SecCFacts2
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.KGNatSL2
public import CFSG.Quasithin.Vol2.KGNatSemi
public import CFSG.Quasithin.Vol2.KGNatSp4Flag

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

namespace S512F

open S5B S512Z

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

private theorem le_of_le_sup_stabCenter (h : PUHyp M T L) {α' ε : Vtx (puAmalgam h.le)}
    (hα' : IsMVtx _ α') (hεα' : (puAmalgam h.le).treeGraph.Adj ε α')
    {R R₁ K : Subgroup (puAmalgam h.le).Universal} (hRst : R ≤ stab _ α') (hRX : R ≤ XM _ α')
    (hR1 : R₁ ≤ R ⊔ stabCenter _ α') (hR₁X : R₁ ≤ XM _ α') (hRK : R ≤ K)
    (hεK : ZH _ ε ≤ K) : R₁ ≤ K := by
  intro r₁ hr₁
  have h1 := hR1 hr₁
  have hZn : stabCenter _ α' ≤ Subgroup.normalizer (R : Set (puAmalgam h.le).Universal) :=
    (stabCenter_le_inf α').trans (inf_le_right.trans ((Subgroup.centralizer_le hRst).trans
      (Subgroup.centralizer_le_normalizer _)))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZn] at h1
  obtain ⟨r, hr, z, hz, rfl⟩ := h1
  have hzX : z ∈ XM _ α' := by
    have e : z = r⁻¹ * (r * z) := by group
    rw [e]
    exact mul_mem (inv_mem (hRX hr)) (hR₁X hr₁)
  exact mul_mem (hRK hr) (hεK (stabCenter_inf_xm_le_zh h hα' hεα'.symm ⟨hz, hzX⟩))

omit [Fintype F] in
private theorem xm_facts (h : PUHyp M T L) (hXU : Xq M = Uq M T L ⊔ Zq M L)
    (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G)) (l : Submodule F (MSP.V4 F)) :
    XM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer
        (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _) ≤
      S5.uSub h.le L (baseA _) ⊔ XM _ (baseA (puAmalgam h.le)) ⊓ stabCenter _ (baseA _) ∧
    XM _ (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal) ≤
      ZM _ (baseA (puAmalgam h.le)) :=
  ⟨inf_le_left.trans (S5B.xm_eq_uSub_sup h hXU hZc).le,
    inf_le_left.trans (S5B.xm_eq_zm h hXU hZc).le⟩

private theorem commutator_uSub_le_zm_baseA (h54 : S54)
    (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G))
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) (hXU : Xq M = Uq M T L ⊔ Zq M L)
    {δ : Vtx (puAmalgam h.le)} (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    {l : Submodule F (MSP.V4 F)} (hl : S5.Case56 h (2 ^ k) a δ l)
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ (baseA (puAmalgam h.le)))
    {A : Subgroup (puAmalgam h.le).Universal} (hAQ : A ≤ Qv _ (baseA (puAmalgam h.le))) :
    ⁅S5.uSub h.le L (y • δ) ⊓ Qv _ δ, A⁆ ≤ ZM _ (baseA (puAmalgam h.le)) := by
  have hyα : y • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hy
  obtain ⟨hXZ, hXQ⟩ := xm_facts (k := k) (a := a) h hXU hZc l
  have hcomm := commutator_zm_qv_le_baseA h hmin hb hd h54 hβδ hl hXZ
  intro r hr
  have h1 : r ∈ ⁅ZM _ (y • δ), Qv _ (baseA (puAmalgam h.le))⁆ :=
    Subgroup.commutator_mono (inf_le_left.trans (uSub_le_zm h.le _)) hAQ hr
  have e1 : ZM _ (y • δ) = (ZM _ δ).map (MulAut.conj y).toMonoidHom := zm_smul _ _ _
  have e2 : Qv _ (baseA (puAmalgam h.le)) =
      (Qv _ (baseA (puAmalgam h.le))).map (MulAut.conj y).toMonoidHom := by
    rw [← qv_smul, hyα]
  rw [e1, e2, ← Subgroup.map_commutator, mem_map_conj] at h1
  have h3 := hXQ (hcomm h1)
  have h4 := (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_zm _ _ hy) _).1 h3
  have e3 : y * (y⁻¹ * r * y) * y⁻¹ = r := by group
  rw [e3] at h4
  exact h4

private theorem commutator_eq_bot_of_le_stabCenter (h : PUHyp M T L)
    (hd : S5.IsSp4Data M T L k F a) {δ : Vtx (puAmalgam h.le)} (hδM : IsMVtx _ δ)
    (hdδ : (puAmalgam h.le).treeGraph.dist (baseA _) δ = 2)
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ (baseA (puAmalgam h.le)))
    {A : Subgroup (puAmalgam h.le).Universal} (hAQ : A ≤ Qv _ (baseA (puAmalgam h.le)))
    (hZα : ⁅S5.uSub h.le L (y • δ) ⊓ Qv _ δ, A⁆ ≤ stabCenter _ (baseA (puAmalgam h.le)))
    (hZδ : ⁅S5.uSub h.le L (y • δ) ⊓ Qv _ δ, A⁆ ≤ stabCenter _ δ) :
    ⁅S5.uSub h.le L (y • δ) ⊓ Qv _ δ, A⁆ = ⊥ := by
  have hyα : y • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hy
  have hμM : IsMVtx _ (y • δ) := (isMVtx_smul _ y _).2 hδM
  have hdμ : (puAmalgam h.le).treeGraph.dist (baseA _) (y • δ) = 2 := by
    have := dist_smul _ y (baseA (puAmalgam h.le)) δ
    rw [hyα] at this
    rw [this, hdδ]
  have hQαμ : Qv _ (baseA (puAmalgam h.le)) ≤ stab _ (y • δ) :=
    qv_le_stab_of_dist_le_two _ h.hyp20 (isMVtx_baseA _) hdμ.le
  have hZμ : ⁅S5.uSub h.le L (y • δ) ⊓ Qv _ δ, A⁆ ≤ stabCenter _ (y • δ) := by
    intro r hr
    rw [S510.stabCenter_smul, mem_map_conj]
    have hc1 : y⁻¹ * r * y = r := by
      have := S5C56.mul_comm_of_mem_stabCenter (hZα hr) hy
      calc y⁻¹ * r * y = y⁻¹ * (r * y) := by group
        _ = y⁻¹ * (y * r) := by rw [this]
        _ = r := by group
    rw [hc1]
    exact hZδ hr
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro u hu a' ha'
  have hc1 : ⁅u, a'⁆ ∈ ⁅S5.uSub h.le L (y • δ) ⊓ Qv _ δ, A⁆ :=
    Subgroup.commutator_mem_commutator hu ha'
  have hmem1 : a' * u * a'⁻¹ * u⁻¹ ∈ Subgroup.centralizer
      (puTrans h.le L (y • δ) : Set (puAmalgam h.le).Universal) := by
    have e : a' * u * a'⁻¹ * u⁻¹ = ⁅u, a'⁆⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    refine inv_mem (Subgroup.mem_centralizer_iff.2 fun x hx => ?_)
    exact S510.commute_of_mem_stabCenter (hZμ hc1) (puTrans_le_stab h.le L _ hx)
  have h1 := lift_at h hd hμM (hQαμ (hAQ ha')) hu.1 hmem1
  have h2 : u * a' = a' * u := by
    calc u * a' = (a' * u * a'⁻¹) * a' := by rw [h1]
      _ = a' * u := by group
  rw [Subgroup.mem_bot, commutatorElement_def, h2]
  group

private theorem commutator_zm_zm_le_of_frame (h54 : S54)
    (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G))
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) (hXU : Xq M = Uq M T L ⊔ Zq M L)
    {δ ε α' : Vtx (puAmalgam h.le)} {g₀ : (puAmalgam h.le).Universal}
    (hg₀δ : g₀ • δ = baseA _) (hg₀ε : g₀ • ε = baseB _)
    (hεα' : (puAmalgam h.le).treeGraph.Adj ε α')
    (hdδ : (puAmalgam h.le).treeGraph.dist (baseA _) δ = 2) {l₀ : Submodule F (MSP.V4 F)}
    (hlm : S5.Case56 h (2 ^ k) a (g₀ • α') l₀) :
    ⁅ZM _ (baseA (puAmalgam h.le)), ZM _ α'⁆ ≤ ZM _ δ := by
  have hβm : (puAmalgam h.le).treeGraph.Adj (baseB _) (g₀ • α') := by
    have := (adj_smul _ g₀ _ _).2 hεα'
    rwa [hg₀ε] at this
  obtain ⟨hXZm, hXQm⟩ := xm_facts (k := k) (a := a) h hXU hZc l₀
  have hcm := commutator_zm_qv_le_baseA h hmin hb hd h54 hβm hlm hXZm
  have hdgα : (puAmalgam h.le).treeGraph.dist (g₀ • baseA (puAmalgam h.le)) (baseA _) = 2 := by
    have := dist_smul _ g₀ (baseA (puAmalgam h.le)) δ
    rw [hg₀δ] at this
    rw [this, hdδ]
  have hZgαQ : ZM _ (g₀ • baseA (puAmalgam h.le)) ≤ Qv _ (baseA (puAmalgam h.le)) :=
    zm_le_qv_of_dist_lt _ ((isMVtx_smul _ g₀ _).2 (isMVtx_baseA _)) (by omega)
  intro r hr
  have h1 : g₀ * r * g₀⁻¹ ∈ ⁅ZM _ (g₀ • baseA (puAmalgam h.le)), ZM _ (g₀ • α')⁆ := by
    rw [zm_smul, zm_smul, ← Subgroup.map_commutator]
    exact conj_mem_map_conj hr
  have h2 := (Subgroup.commutator_mono hZgαQ le_rfl) h1
  rw [Subgroup.commutator_comm] at h2
  have h3 := hXQm (hcm h2)
  rw [← hg₀δ, zm_smul, mem_map_conj] at h3
  have e : g₀⁻¹ * (g₀ * r * g₀⁻¹) * g₀ = r := by group
  rwa [e] at h3

private theorem zm_inf_le_stabCenter_of_frame (h : PUHyp M T L)
    (hd : S5.IsSp4Data M T L k F a) {δ δ' α' δ₀ : Vtx (puAmalgam h.le)}
    {g₀ g' x' : (puAmalgam h.le).Universal} {l₀ : Submodule F (MSP.V4 F)}
    (hg₀δ : g₀ • δ = baseA _)
    (hg' : g' ∈ stab _ (baseA (puAmalgam h.le))) (hx' : x' ∈ puTrans h.le L (baseA _))
    (hl₀ : S5.Case56 h (2 ^ k) a δ₀ l₀) (hc56 : S5.Concl56 h (2 ^ k) a (g₀ • δ') l₀ g' x')
    (hν : g₀ • baseA (puAmalgam h.le) = g'⁻¹ • δ₀ ∨
      g₀ • baseA (puAmalgam h.le) = x'⁻¹ • (g'⁻¹ • δ₀))
    (hZm : ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (g₀ • α') ≤
      Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l₀) : Set (puAmalgam h.le).Universal))
    (hZδ₀ : ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ δ₀ ≤
      Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l₀) : Set (puAmalgam h.le).Universal))
    (hidxo : g₀ • baseA (puAmalgam h.le) = x'⁻¹ • (g'⁻¹ • δ₀) →
      (Qv _ δ').relIndex (ZM _ δ) = 2 ^ k ∨ S5.Opp56 h (2 ^ k) a l₀ g' x') :
    ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ δ ⊓ ZM _ α' ≤ stabCenter _ δ := by
  have hcen : ZM _ (g₀ • baseA (puAmalgam h.le)) ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓
      ZM _ (g₀ • α') ≤ stabCenter _ (baseA (puAmalgam h.le)) := by
    rcases hν with hν | hν
    · rw [hν]
      exact S5C56.c56g_two h hd hl₀.2.1 hZm hZδ₀ hg' hc56
    · rw [hν]
      rcases hidxo hν with hidx | hopp
      · have hidxb : (Qv _ (g₀ • δ')).relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k := by
          rw [qv_smul, ← hg₀δ, zm_smul,
            Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g₀).injective]
          exact hidx
        exact S5C56.c56x_two h hd hl₀.2.1 hZm hZδ₀ hg' hx' hc56 hidxb
      · exact S5C56.c56x_two_of_opp h hd hl₀.2.1 hZm hZδ₀ hg' hx' hopp
  intro r hr
  have h1 : g₀ * r * g₀⁻¹ ∈ ZM _ (g₀ • baseA (puAmalgam h.le)) ⊓
      ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (g₀ • α') := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [zm_smul]
      exact conj_mem_map_conj hr.1.1
    · rw [← hg₀δ, zm_smul]
      exact conj_mem_map_conj hr.1.2
    · rw [zm_smul]
      exact conj_mem_map_conj hr.2
  have hδg : δ = g₀⁻¹ • baseA (puAmalgam h.le) := by rw [← hg₀δ, inv_smul_smul]
  rw [hδg, S510.stabCenter_smul, mem_map_conj, inv_inv]
  exact hcen h1

theorem false_of_data (h54 : S54) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    {δ' : Vtx (puAmalgam h.le)} (hc' : IsCritical _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ')
    (hgeo : geo _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ' 2 = α')
    {g₀ g' x' : (puAmalgam h.le).Universal} {δ₀ : Vtx (puAmalgam h.le)}
    {l₀ : Submodule F (MSP.V4 F)}
    (hg₀δ : g₀ • geo _ (baseA (puAmalgam h.le)) α' 2 = baseA _)
    (hg₀ε : g₀ • geo _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ' 1 = baseB _)
    (hβδ₀ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ₀)
    (hg' : g' ∈ stab _ (baseA (puAmalgam h.le))) (hx' : x' ∈ puTrans h.le L (baseA _))
    (hl₀ : S5.Case56 h (2 ^ k) a δ₀ l₀) (hc56 : S5.Concl56 h (2 ^ k) a (g₀ • δ') l₀ g' x')
    (hν : g₀ • baseA (puAmalgam h.le) = g'⁻¹ • δ₀ ∨
      g₀ • baseA (puAmalgam h.le) = x'⁻¹ • (g'⁻¹ • δ₀))
    (hJmid : S5.jOff h.le L (2 ^ k) α' (geo _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ' 1) =
      S5.jOff h.le L (2 ^ k) (geo _ (baseA (puAmalgam h.le)) α' 2)
        (geo _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ' 1))
    (hidxo : g₀ • baseA (puAmalgam h.le) = x'⁻¹ • (g'⁻¹ • δ₀) →
      (Qv _ δ').relIndex (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)) = 2 ^ k ∨
        S5.Opp56 h (2 ^ k) a l₀ g' x')
    (hLin : Large h k (baseA _) (geo _ (baseA (puAmalgam h.le)) α' 2) ∨
      Large h k (geo _ (baseA (puAmalgam h.le)) α' 2) (baseA _))
    (hLout : Large h k (geo _ (baseA (puAmalgam h.le)) α' 2) α' ∨
      Large h k α' (geo _ (baseA (puAmalgam h.le)) α' 2))
    {μ : Vtx (puAmalgam h.le)}
    (hμ : μ ∈ S5.lam h (2 ^ k) a α' (geo _ (baseA (puAmalgam h.le)) α' 2))
    (hidx : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k)
    (hXU : Xq M = Uq M T L ⊔ Zq M L)
    (hcard : Nat.card ↥⁅S5.uSub h.le L μ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2),
      critA _ (baseA (puAmalgam h.le)) α'⁆ = 2 ^ k)
    (hR1 : ⁅S5.uSub h.le L μ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2),
        critA _ (baseA (puAmalgam h.le)) α'⁆ ≤
      critR _ (baseA (puAmalgam h.le)) α' ⊔ stabCenter _ α') : False := by
  have hZc := S5Q2.UC.zq_le_centralizer_of_relIndex_eq h hd hc hidx
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hα : IsMVtx _ (baseA (puAmalgam h.le)) := isMVtx_baseA _
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hd4 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb4
  set δ := geo _ (baseA (puAmalgam h.le)) α' 2 with hδ
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ] at this
  have hδM : IsMVtx _ δ := isMVtx_geo_two _ hyp hb0 hc
  have hdδ : (puAmalgam h.le).treeGraph.dist (baseA _) δ = 2 := dist_geo _ (by omega)
  have hdδα' : (puAmalgam h.le).treeGraph.dist δ α' = 2 := by
    rw [dist_geo_right _ (by omega), hd4]
  have hd' : (puAmalgam h.le).treeGraph.dist δ δ' = 4 := hc'.2.1.trans hb4
  set ε := geo _ δ δ' 1 with hε
  have hδε : (puAmalgam h.le).treeGraph.Adj δ ε := adj_geo_one _ (by omega)
  have hεα' : (puAmalgam h.le).treeGraph.Adj ε α' := by
    have := adj_geo _ (u := δ) (w := δ') (i := 1) (by omega)
    rwa [hgeo] at this
  have hsymm := large_symm hZc h54 h hmin hb hd hXU hβδ hl
  have hLαδ : Large h k (baseA _) δ := hLin.elim id hsymm.2
  have hLδα : Large h k δ (baseA _) := hsymm.1 hLαδ
  have hlm := case56_smul_of_jOff_eq h hg₀δ hg₀ε hJmid hl₀
  have hβm : (puAmalgam h.le).treeGraph.Adj (baseB _) (g₀ • α') := by
    have := (adj_smul _ g₀ _ _).2 hεα'
    rwa [hg₀ε] at this
  have hLm : Large h k (baseA _) (g₀ • α') := by
    rcases hLout with h1 | h1
    · rw [← hg₀δ]
      exact (large_smul h g₀ δ α').2 h1
    · have h2 : Large h k (g₀ • α') (baseA _) := by
        rw [← hg₀δ]
        exact (large_smul h g₀ α' δ).2 h1
      exact (large_symm hZc h54 h hmin hb hd hXU hβm hlm).2 h2
  have hZm := zz56_of_large hZc h hd hXU hβm hlm hLm
  have hZδ₀ : ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ δ₀ ≤
      Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l₀) : Set (puAmalgam h.le).Universal) := by
    obtain ⟨y, hy, hyν⟩ : ∃ y ∈ stab _ (baseA (puAmalgam h.le)),
        y • (g₀ • baseA (puAmalgam h.le)) = δ₀ := by
      rcases hν with hν | hν
      · exact ⟨g', hg', by rw [hν, smul_inv_smul]⟩
      · exact ⟨g' * x', mul_mem hg' (puTrans_le_stab h.le L _ hx'),
          by rw [hν, mul_smul, smul_inv_smul, smul_inv_smul]⟩
    have hL0 : Large h k (baseA _) δ₀ := by
      have h1 : Large h k (g₀ • δ) (g₀ • baseA (puAmalgam h.le)) :=
        (large_smul h g₀ δ (baseA _)).2 hLδα
      rw [hg₀δ] at h1
      have h2 := (large_smul h y (baseA _) (g₀ • baseA (puAmalgam h.le))).2 h1
      rwa [(mem_stab _).1 hy, hyν] at h2
    exact zz56_of_large hZc h hd hXU hβδ₀ hl₀ hL0
  obtain ⟨y, hy, rfl⟩ := exists_mem_stab_of_mem_lam (id hμ)
  have hyα : y • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hy
  have hdμ : (puAmalgam h.le).treeGraph.dist (baseA _) (y • δ) = 2 := by
    have := dist_smul _ y (baseA (puAmalgam h.le)) δ
    rw [hyα] at this
    rw [this, hdδ]
  set Y := S5.uSub h.le L (y • δ) ⊓ Qv _ δ with hY
  set A := critA _ (baseA (puAmalgam h.le)) α' with hA
  set R := critR _ (baseA (puAmalgam h.le)) α' with hR
  have hAQ : A ≤ Qv _ (baseA (puAmalgam h.le)) := inf_le_right
  have hAX : A ≤ XM _ α' := inf_le_left
  have hQαμ : Qv _ (baseA (puAmalgam h.le)) ≤ stab _ (y • δ) :=
    qv_le_stab_of_dist_le_two _ hyp hα hdμ.le
  have hQδα' : Qv _ δ ≤ stab _ α' := qv_le_stab_of_dist_le_two _ hyp hδM hdδα'.le
  have hR₁X : ⁅Y, A⁆ ≤ XM _ α' := by
    refine (Subgroup.commutator_mono le_rfl hAX).trans ?_
    rw [Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer
      ((inf_le_right.trans hQδα').trans (stab_le_normalizer_xm _ _))
  have hR₁Zμ : ⁅Y, A⁆ ≤ ZM _ (y • δ) :=
    (Subgroup.commutator_mono (inf_le_left.trans (uSub_le_zm h.le _)) le_rfl).trans
      (commutator_le_left_of_le_normalizer ((hAQ.trans hQαμ).trans (stab_le_normalizer_zm _ _)))
  have hRZ' : R ≤ ZM _ α' := by
    rw [hR, critR, Subgroup.commutator_comm]
    refine commutator_le_left_of_le_normalizer ?_
    exact ((zm_le_qv_of_dist_lt _ hα (by omega)).trans hQδα').trans (stab_le_normalizer_zm _ _)
  have hRZδ : R ≤ ZM _ δ :=
    commutator_zm_zm_le_of_frame h54 hZc h hmin hb hd hXU hg₀δ hg₀ε hεα' hdδ hlm
  have hR₁Zδα' : ⁅Y, A⁆ ≤ ZM _ δ ⊓ ZM _ α' :=
    le_of_le_sup_stabCenter h hα' hεα'
      (hRZ'.trans ((zm_le_qv_self _ hα' hb0).trans (qv_le_stab _ _)))
      (hRZ'.trans (zm_le_xm _ hyp hb0 hα')) hR1 hR₁X (le_inf hRZδ hRZ')
      (le_inf (zh_le_zm _ hδε) (zh_le_zm _ hεα'.symm))
  have hR₁Zα : ⁅Y, A⁆ ≤ ZM _ (baseA (puAmalgam h.le)) :=
    commutator_uSub_le_zm_baseA h54 hZc h hmin hb hd hXU hβδ hl hy hAQ
  have hR₁ZGα : ⁅Y, A⁆ ≤ stabCenter _ (baseA (puAmalgam h.le)) := fun r hr =>
    S5C56.zm_inf_le_stabCenter_of_mem_lam h hd
      (fun l' hl' => zz56_of_large hZc h hd hXU hβδ hl' hLαδ) ⟨l, hl⟩ hidx hμ
      ⟨⟨hR₁Zμ hr, hR₁Zα hr⟩, (hR₁Zδα' hr).1⟩
  have hR₁ZG : ⁅Y, A⁆ ≤ stabCenter _ δ := fun r hr =>
    zm_inf_le_stabCenter_of_frame h hd hg₀δ hg' hx' hl₀ hc56 hν hZm hZδ₀ hidxo
      ⟨⟨hR₁Zα hr, (hR₁Zδα' hr).1⟩, (hR₁Zδα' hr).2⟩
  have hbot : ⁅Y, A⁆ = ⊥ :=
    commutator_eq_bot_of_le_stabCenter h hd hδM hdδ hy hAQ hR₁ZGα hR₁ZG
  rw [hbot, Subgroup.card_bot] at hcard
  exact absurd hcard (Nat.one_lt_two_pow (by have := hd.1; omega)).ne

theorem commutator_zm_qv_le_xm (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    {l : Submodule F (MSP.V4 F)} (hc56 : S5.Case56 h (2 ^ k) a δ l) :
    ⁅ZM _ δ, Qv _ (baseA (puAmalgam h.le))⁆ ≤ XM _ (baseA (puAmalgam h.le)) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨hJδ, hl, -, hJl⟩ := hc56
  set J := S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) with hJ
  have hα : IsMVtx _ (baseA (puAmalgam h.le)) := isMVtx_baseA _
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hδ : IsMVtx _ δ := by
    have := isMVtx_iff_of_adj _ hβδ
    have hβ := not_isMVtx_baseB (puAmalgam h.le)
    tauto
  have hQJ : Qv _ (baseA (puAmalgam h.le)) ≤ J :=
    qv_le_jOff h (Nat.one_le_two_pow) hα hαβ
  have hJT : J ≤ Qv _ (baseB (puAmalgam h.le)) := jOff_le_qv h.le L _ _ _
  obtain ⟨g, hg, hgα⟩ := exists_mem_stab_smul _ hαβ.symm hβδ
  have hgβ : g • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 hg
  have hJg : J.map (MulAut.conj g).toMonoidHom = J := by
    have := jOff_smul h.le hLn (2 ^ k) g (baseA (puAmalgam h.le)) (baseB _)
    rw [hgα, hgβ, hJδ] at this
    exact this.symm
  have hquadδ : ⁅S5.uSub h.le L δ, J⁆ ≤ Subgroup.centralizer (J : Set _) := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom)
      (commutator_uSub_le_centralizer_baseA h hd hl hJl)
    rw [Subgroup.map_commutator, ← PU.centralizer_map_mulEquiv, ← uSub_smul h.le hLn, hgα,
      hJg] at h1
    exact h1
  have hZδ := zm_eq_zh_sup_uSub h hδ hβδ.symm
  have hδst : Qv _ (baseB (puAmalgam h.le)) ≤ stab _ δ := qv_le_stab_of_adj _ hβδ
  have hUδT : S5.uSub h.le L δ ≤ Qv _ (baseB (puAmalgam h.le)) :=
    (commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L δ).trans
      (stab_le_normalizer_zm _ _))).trans ((zm_le_qv_self _ hδ hb0).trans
        (qv_le_qv _ hyp hδ hβδ.symm))
  have hZβc : ZH _ (baseB (puAmalgam h.le)) ≤
      Subgroup.centralizer (Qv _ (baseB (puAmalgam h.le)) : Set _) :=
    (PU.omegaOneCenterOf_le_centerOf _).trans inf_le_right
  have hZJ : ⁅ZM _ δ, J⁆ ≤ ⁅S5.uSub h.le L δ, J⁆ := by
    rw [Subgroup.commutator_le]
    intro z hz j hj
    rw [hZδ] at hz
    have hn : ZH _ (baseB (puAmalgam h.le)) ≤
        Subgroup.normalizer (S5.uSub h.le L δ : Set (puAmalgam h.le).Universal) :=
      ((PU.omegaOneCenterOf_le _).trans hδst).trans
        (le_normalizer_commutator (stab_le_normalizer_zm _ _)
          (stab_le_normalizer_puTrans h.le hLn δ))
    have hz' : z ∈ ((ZH _ (baseB (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) *
        (S5.uSub h.le L δ : Set (puAmalgam h.le).Universal)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn]
      exact hz
    obtain ⟨z₀, hz₀, u, hu, rfl⟩ := hz'
    have hc₀ : ∀ t ∈ Qv _ (baseB (puAmalgam h.le)), z₀ * t = t * z₀ := fun t ht =>
      (Subgroup.mem_centralizer_iff.1 (hZβc hz₀) t ht).symm
    have e : ⁅z₀ * u, j⁆ = ⁅u, j⁆ := by
      simp only [commutatorElement_def]
      have h1 := hc₀ (u * j * u⁻¹) (mul_mem (mul_mem (hUδT hu) (hJT hj)) (inv_mem (hUδT hu)))
      calc z₀ * u * j * (z₀ * u)⁻¹ * j⁻¹ = z₀ * (u * j * u⁻¹) * z₀⁻¹ * j⁻¹ := by group
        _ = u * j * u⁻¹ * j⁻¹ := by rw [h1]; group
    rw [e]
    exact Subgroup.commutator_mem_commutator hu hj
  have hdα : (puAmalgam h.le).treeGraph.dist δ (baseA _) < critDist (puAmalgam h.le) := by
    have := dist_triangle _ δ (baseB (puAmalgam h.le)) (baseA _)
    rw [dist_eq_one_of_adj _ hβδ.symm, dist_eq_one_of_adj _ hαβ.symm] at this
    omega
  have hZQ : ZM _ δ ≤ Qv _ (baseA (puAmalgam h.le)) := zm_le_qv_of_dist_lt _ hδ hdα
  have hcomm : ⁅ZM _ δ, Qv _ (baseA (puAmalgam h.le))⁆ ≤ Subgroup.centralizer (J : Set _) :=
    (Subgroup.commutator_mono le_rfl hQJ).trans (hZJ.trans hquadδ)
  have hcommZ : ⁅ZM _ δ, Qv _ (baseA (puAmalgam h.le))⁆ ≤ ZM _ δ :=
    commutator_le_left_of_le_normalizer ((qv_le_qv _ hyp hα hαβ).trans
      (hδst.trans (stab_le_normalizer_zm _ _)))
  intro x hx
  refine Subgroup.subset_closure ⟨⟨hZQ (hcommZ hx), ?_⟩, ?_⟩
  · exact Subgroup.centralizer_le hQJ (hcomm hx)
  · exact (isElemAbelian_zm _ hyp hb0 hδ).2 x (hcommZ hx)

theorem commutator_zm_smul_qv_le_xm (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    {l : Submodule F (MSP.V4 F)} (hc56 : S5.Case56 h (2 ^ k) a δ l)
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ (baseA (puAmalgam h.le))) :
    ⁅ZM _ (y • δ), Qv _ (baseA (puAmalgam h.le))⁆ ≤ XM _ (baseA (puAmalgam h.le)) := by
  have hyα : y • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hy
  have e1 : ZM _ (y • δ) = (ZM _ δ).map (MulAut.conj y).toMonoidHom := zm_smul _ _ _
  have e2 : Qv _ (baseA (puAmalgam h.le)) =
      (Qv _ (baseA (puAmalgam h.le))).map (MulAut.conj y).toMonoidHom := by
    rw [← qv_smul, hyα]
  have e3 : XM _ (baseA (puAmalgam h.le)) =
      (XM _ (baseA (puAmalgam h.le))).map (MulAut.conj y).toMonoidHom := by
    rw [← xm_smul, hyα]
  intro r hr
  rw [e1, e2, ← Subgroup.map_commutator] at hr
  rw [e3]
  exact Subgroup.map_mono (commutator_zm_qv_le_xm h hb hd hβδ hc56) hr

theorem commutator_le_xm (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a) {α' ν μ₁ μ₂ : Vtx (puAmalgam h.le)}
    (hchS : S5B.IsChain512Sel h (2 ^ k) a (S5.Opp56 h (2 ^ k) a) α' ν μ₁ μ₂)
    {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    (hL : Large h k (baseA _) (geo _ (baseA (puAmalgam h.le)) α' 2) ∨
      Large h k (geo _ (baseA (puAmalgam h.le)) α' 2) (baseA _))
    {μ : Vtx (puAmalgam h.le)}
    (hμ : μ ∈ S5.lam h (2 ^ k) a α' (geo _ (baseA (puAmalgam h.le)) α' 2)) :
    ⁅S5.uSub h.le L μ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2),
      S5.zHat _ (baseA (puAmalgam h.le)) α'⁆ ≤ XM _ (baseA (puAmalgam h.le)) := by
  obtain ⟨hαβ, hs0, hgeo, hc, -, -, -⟩ := hchS
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hd4 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb4
  have hgδ : geo _ α' (baseA (puAmalgam h.le)) 2 = geo _ (baseA (puAmalgam h.le)) α' 2 := by
    have := geo_symm _ (show 2 ≤ (puAmalgam h.le).treeGraph.dist (baseA _) α' by omega)
    rwa [hd4] at this
  have hdδ : (puAmalgam h.le).treeGraph.dist (baseA _) (geo _ (baseA (puAmalgam h.le)) α' 2) =
      2 := dist_geo _ (by omega)
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) (geo _ (baseA (puAmalgam h.le)) α' 2) := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ] at this
  obtain ⟨y, hy, hyμ⟩ := exists_mem_stab_of_mem_lam hμ
  have hδM := isMVtx_geo_two _ hyp hb0 hc
  have hμM : IsMVtx _ μ := hyμ ▸ (isMVtx_smul _ y _).2 hδM
  have hdμ : (puAmalgam h.le).treeGraph.dist (baseA _) μ = 2 := by
    have := dist_smul _ y (baseA (puAmalgam h.le)) (geo _ (baseA (puAmalgam h.le)) α' 2)
    rw [(mem_stab _).1 hy, ← hyμ] at this
    rw [this, hdδ]
  obtain ⟨-, -, -, hRX, hXX, hQQ⟩ := crit_facts h hc
  obtain ⟨hZQ, hZR⟩ := zm_le_centralizer_critR h hb hc hμM hdμ
  set Y := S5.uSub h.le L μ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) with hY
  have hYZ : Y ≤ ZM _ μ := inf_le_left.trans (uSub_le_zm h.le μ)
  have hZμX : ⁅ZM _ μ, Qv _ (baseA (puAmalgam h.le))⁆ ≤ XM _ (baseA (puAmalgam h.le)) := by
    rw [hyμ]
    exact commutator_zm_smul_qv_le_xm h hb hd hβδ hl hy
  have hAX : ⁅critA (puAmalgam h.le) (baseA _) α', Y⁆ ≤ XM _ (baseA (puAmalgam h.le)) := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono hYZ inf_le_right).trans hZμX
  by_contra hne
  have hY3 : ¬ ⁅ZM (puAmalgam h.le) α', Y⁆ ≤
      ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ ⊔
        ⁅critA (puAmalgam h.le) (baseA _) α', Y⁆ := by
    intro hle
    apply hne
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono inf_le_left le_rfl).trans (hle.trans (sup_le hXX hAX))
  have hYZ' : ¬ ⁅Y, S5.zHat _ (baseA (puAmalgam h.le)) α'⁆ ≤
      critR _ (baseA (puAmalgam h.le)) α' := fun hle => hne (hle.trans hRX)
  have hYT : Y ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 1) := by
    refine inf_le_right.trans ?_
    rw [← hgδ]
    exact hQQ
  obtain ⟨hidx, hXU, hD⟩ := s33ii2_of' hX2 h hd (h32 G M T L h).2.1 hc hYT (hYZ.trans hZR)
    ((hYZ.trans hZQ).trans (qv_le_centralizer_xm _ _)) hY3 hYZ'
  have hAYY : ⁅⁅critA (puAmalgam h.le) (baseA _) α', Y⁆, Y⁆ = ⊥ := by
    have h52iii := (h52 G M T L h hmin hb k F _ _ a hd α' hc).2.2.2
    have hle : Y ≤ Vv _ (baseA (puAmalgam h.le)) ⊓ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2) :=
      le_inf (hYZ.trans (zm_le_vv_of_dist hμM hdμ.le)) (by rw [hgδ]; exact inf_le_right)
    refine le_bot_iff.1 ?_
    rw [← h52iii]
    exact Subgroup.commutator_mono (Subgroup.commutator_mono le_rfl hle) hle
  obtain ⟨hcard, hR1⟩ := hD hAYY
  have hc' := hs0.1
  set δ := geo _ (baseA (puAmalgam h.le)) α' 2 with hδ
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
  exact false_of_data h54 h hmin hb4 hd hc hαβ hl hc' hgeo hg₀δ hg₀ε hβδ₀ hg' hx' hl₀ hc56 hν
    hJmid (fun _ => Or.inr hopp) hL hLout hμ hidx hXU hcard hR1

end S512F

end CFSG.Quasithin.MS93
