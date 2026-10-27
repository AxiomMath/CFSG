module

public import CFSG.Quasithin.MS93.S512RCent
public import CFSG.Quasithin.MS93.S5Q2OddC
public import CFSG.Quasithin.MS93.S5Q2EvenZ
public import CFSG.Quasithin.MS93.S512TBad
public import CFSG.Quasithin.MS93.S512TStmt
public import CFSG.Quasithin.MS93.S512TThree
public import CFSG.Quasithin.MS93.S512TTwo

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S512R

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem le_centralizer_L_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (h32 : ⁅Xq M, L⁆ ≤ Uq M T L) {R : Subgroup G} (hRX : R ≤ Xq M)
    (hRn : M ≤ Subgroup.normalizer (R : Set G)) (hRc : Nat.card R < (2 ^ k) ^ 4) :
    R ≤ Subgroup.centralizer (L : Set G) := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hclaim : ∀ u : ↥(Uq M T L), (u : G) ∈ R → c.vec u = 0 := by
    by_contra hne
    push Not at hne
    obtain ⟨u₀, hu₀R, hu₀⟩ := hne
    let S : AddSubgroup (MSP.V4 F) :=
      { carrier := {w | ∃ u : ↥(Uq M T L), (u : G) ∈ R ∧ c.vec u = w}
        add_mem' := by
          rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
          exact ⟨u * u', R.mul_mem hu hu', c.vec_mul u u'⟩
        zero_mem' := ⟨1, R.one_mem, by simp [MSP.NatCoord.vec]⟩
        neg_mem' := by
          rintro _ ⟨u, hu, rfl⟩
          exact ⟨u⁻¹, R.inv_mem hu, c.vec_inv u⟩ }
    have hinv : ∀ g : MSP.Sp4 F, ∀ v ∈ S, MSP.mat g *ᵥ v ∈ S := by
      rintro g _ ⟨u, huR, rfl⟩
      obtain ⟨m, rfl⟩ := hd.2.2.1 g
      have hu' : (m : G) * u * (m : G)⁻¹ ∈ Uq M T L :=
        (Subgroup.mem_normalizer_iff.1 (hUn m.2) u).1 u.2
      exact ⟨⟨_, hu'⟩, (Subgroup.mem_normalizer_iff.1 (hRn m.2) u).1 huR, c.vec_conj m u hu'⟩
    have htop := S512T.eq_top_of_invariant hinv ⟨u₀, hu₀R, rfl⟩ hu₀
    have hsurj : Function.Surjective
        (fun u : {u : ↥(Uq M T L) // (u : G) ∈ R} => c.vec u.1) := by
      intro w
      have hw : w ∈ S := by rw [htop]; exact AddSubgroup.mem_top w
      obtain ⟨u, hu, rfl⟩ := hw
      exact ⟨⟨u, hu⟩, rfl⟩
    have hinj : Function.Injective
        (fun u : {u : ↥(Uq M T L) // (u : G) ∈ R} => (⟨u.1, u.2⟩ : ↥R)) := by
      intro x y hxy
      simp only [Subtype.mk.injEq] at hxy
      exact Subtype.ext (Subtype.ext hxy)
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    have h2 := Nat.card_le_card_of_injective _ hinj
    rw [MSP.card_V4, hFq] at h1
    omega
  have hW : R ⊓ Uq M T L ≤ Subgroup.centralizer (L : Set G) := by
    rintro x ⟨hxR, hxU⟩
    exact ((c.vec_eq_zero_iff ⟨x, hxU⟩).1 (hclaim ⟨x, hxU⟩ hxR)).2
  have hRL : ⁅R, L⁆ ≤ R ⊓ Uq M T L :=
    le_inf (commutator_le_left_of_le_normalizer (h.L_le.trans hRn))
      ((Subgroup.commutator_mono hRX le_rfl).trans h32)
  have hRL2 : ⁅R ⊓ Uq M T L, L⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxy : y * x = x * y := Subgroup.mem_centralizer_iff.1 (hW hx) y hy
    rw [commutatorElement_def, ← hxy, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hRL3 := S5B.commutator_le_of_perfect (U := (⊥ : Subgroup G)) h.perfect
    (Subgroup.le_normalizer_of_normal) (Subgroup.le_normalizer_of_normal) hRL hRL2
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact le_bot_iff.1 hRL3

theorem puTrans_le_centralizer_of_normal (h32 : S32) (h : PUHyp M T L)
    (hd : S5.IsSp4Data M T L k F a) {R : Subgroup (puAmalgam h.le).Universal}
    (hRX : R ≤ XM _ (baseA (puAmalgam h.le)))
    (hRn : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer (R : Set _))
    (hRc : Nat.card R < (2 ^ k) ^ 4) :
    puTrans h.le L (baseA _) ≤ Subgroup.centralizer (R : Set (puAmalgam h.le).Universal) := by
  rw [S5B.xm_baseA_eq h] at hRX
  obtain ⟨R₀, hR₀X, hR₀M, rfl⟩ := S5B.exists_eq_imM h.le hRX
  have hRn₀ : M ≤ Subgroup.normalizer (R₀ : Set G) := by
    rw [puAmalgam.stab_baseA] at hRn
    exact S512T.le_normalizer_of_imM h.le le_rfl hR₀M hRn
  rw [S5B.card_imM h.le hR₀M] at hRc
  have key := le_centralizer_L_M h hd (h32 G M T L h).2.1 hR₀X hRn₀ hRc
  rw [S5B.puTrans_L_baseA h, S512T.imM_le_centralizer_iff h.le h.L_le hR₀M]
  exact Subgroup.le_centralizer_iff.1 key

theorem le_stabCenter_of_not_case56 (h32 : S32) (h54 : S54) (hq55 : S5Q2.Q2Cent55)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a) {μ γ : Vtx (puAmalgam h.le)} (hcμ : IsCritical _ μ γ)
    (hmid : geo _ μ γ 2 = baseA _) (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ)
    (h56 : ∀ l, ¬ S5.Case56 h (2 ^ k) a γ l) {R : Subgroup (puAmalgam h.le).Universal}
    (hRX : R ≤ XM _ (baseA (puAmalgam h.le)))
    (hRL : puTrans h.le L (baseA _) ≤ Subgroup.centralizer (R : Set (puAmalgam h.le).Universal))
    (hRZ : R ≤ ZM _ γ) : R ≤ stabCenter _ (baseA (puAmalgam h.le)) := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hRC : R ≤ XM _ (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) :=
    le_inf hRX fun r hr => Subgroup.mem_centralizer_iff.2 fun w hw =>
      (Subgroup.mem_centralizer_iff.1 (hRL hw) r hr).symm
  have hcase1 : Zq M L ≤ Subgroup.centralizer (M : Set G) →
      R ≤ stabCenter _ (baseA (puAmalgam h.le)) := fun hZc =>
    hRC.trans (S5Q2.xm_inf_centralizer_le_stabCenter h hZc (isMVtx_baseA _))
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by have := hd.1; omega
    by_cases hXU : Xq M = Uq M T L ⊔ Zq M L
    · by_cases hC : Zq M L ≤ Subgroup.centralizer (M : Set G)
      · exact hcase1 hC
      · have hyp := h.hyp20
        have hb0 := h.critDist_pos
        obtain ⟨-, -, -, hd4, -, -, -, -, hdμα, -, -, -⟩ := S512T.pair_facts h hb4 hcμ
        rw [hmid] at hdμα
        have hc' : IsCritical _ γ μ := ms22_iii _ hyp hb0 h.centHyp hcμ
        have h2 : geo _ γ μ 2 = baseA _ := by
          have := geo_symm _ (show 2 ≤ (puAmalgam h.le).treeGraph.dist μ γ by omega)
          rw [hd4, hmid] at this
          exact this
        have hdβμ : (puAmalgam h.le).treeGraph.dist (baseB _) μ = 3 := by
          have t1 := dist_triangle _ γ (baseB (puAmalgam h.le)) μ
          have t2 := dist_triangle _ (baseB (puAmalgam h.le)) (baseA _) μ
          have hdαμ : (puAmalgam h.le).treeGraph.dist (baseA _) μ = 2 := by
            rw [SimpleGraph.dist_comm]
            exact hdμα
          rw [dist_eq_one_of_adj _ hβγ.symm, SimpleGraph.dist_comm (u := γ), hd4] at t1
          rw [dist_eq_one_of_adj _ (adj_baseA_baseB _).symm, hdαμ] at t2
          omega
        have h1 : geo _ γ μ 1 = baseB _ := by
          symm
          refine eq_geo_of_dist _ (dist_eq_one_of_adj _ hβγ.symm) ?_
          rw [dist_eq_one_of_adj _ hβγ.symm, hdβμ, SimpleGraph.dist_comm, hd4]
        have hcase : ∀ l, ¬ S5.Case56 h 2 a γ l := by simpa using h56
        intro r hr
        exact S5Q2.UC.cX_inf_zm_le_stabCenter_of_not_case56 h hq55 h54 hmin hb hd hXU hC hc' h1
          h2 hcase ⟨hRC hr, hRZ hr⟩
    · exact hcase1 (S5Q2.X52.zq_le_centralizer_of_ne h hd (h32 G M T L h).2.1 hXU)
  · exact hcase1 (S5Q2.zq_le_centralizer_of_two_le h hd hk)

theorem commutator_zm_le_stabCenter_of_gen_e (h32 : S32) (h52 : S52)
    (hZ : S5Q2.Q2EvenZ) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {γ : Vtx (puAmalgam h.le)} (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ)
    {l : Submodule F (MSP.V4 F)} (hl : S5.Case56 h (2 ^ k) a γ l)
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ (baseA (puAmalgam h.le)))
    (hgen : ∀ E : Subgroup (puAmalgam h.le).Universal, E ≤ S5.vPre h.le a (MSP.qLine l) →
      IsPGroup 2 E → (2 ^ k) ^ 2 < (Qv _ (baseA (puAmalgam h.le))).relIndex E →
      S5.rconj y E ⊔ E ⊔ Qv _ (baseA (puAmalgam h.le)) = stab _ (baseA _)) :
    ⁅ZM _ (y⁻¹ • γ), ZM _ γ⁆ ≤ stabCenter _ (baseA (puAmalgam h.le)) := by
  have hyp := h.hyp20
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have key := commutator_zm_le_dSub_of_gen h32 h52 h hmin hb hd hβγ hl hy hgen
  have hdist := dist_triangle _ (baseA (puAmalgam h.le)) (baseB _) γ
  rw [dist_eq_one_of_adj _ hαβ, dist_eq_one_of_adj _ hβγ] at hdist
  have hdμ : (puAmalgam h.le).treeGraph.dist (baseA _) (y⁻¹ • γ) ≤ 2 := by
    have := dist_smul _ y⁻¹ (baseA (puAmalgam h.le)) γ
    rw [(mem_stab _).1 (inv_mem hy)] at this
    rw [this]
    exact hdist
  have hγM : IsMVtx _ γ := (isMVtx_iff_of_adj _ hβγ.symm).2 (not_isMVtx_baseB _)
  have hZμ : ZM _ (y⁻¹ • γ) ≤ Qv _ (baseA (puAmalgam h.le)) :=
    zm_le_qv_of_dist_lt _ ((isMVtx_smul _ _ _).2 hγM) (by rw [tdist_comm]; omega)
  have hJ : ⁅ZM _ (y⁻¹ • γ), ZM _ γ⁆ ≤ Subgroup.centralizer
      (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _) := by
    refine (Subgroup.commutator_mono hZμ le_rfl).trans ?_
    rw [Subgroup.commutator_comm]
    exact S5C56.commutator_zm_qv_le_centralizer_jOff h hd hl.2.1 hl.2.2.2 hβγ hl.1
  have hRZ : ⁅ZM _ (y⁻¹ • γ), ZM _ γ⁆ ≤ ZM _ γ := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer (hZμ.trans ((qv_le_qv _ hyp hα hαβ).trans
      ((qv_le_stab_of_adj _ hβγ).trans (stab_le_normalizer_zm _ _))))
  intro r hr
  have hrL : r ∈ Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) :=
    Subgroup.mem_centralizer_iff.2 fun w hw => (key hr).1.2 w hw
  exact S5Q2.UC.cX_inf_centralizer_inf_zm_le_stabCenter h hZ h32 hmin hb hd hβγ hl
    ⟨⟨⟨(key hr).2, hrL⟩, hJ hr⟩, hRZ hr⟩

theorem cent56F_holds_e (h32 : S32) (h52 : S52) (hZ : S5Q2.Q2EvenZ) : Cent56F := by
  intro G _ _ M T L h hmin hb k F _ _ a hd α' hc hαβ l hl g hg x hx hc56 hopp μ hμ
  have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
  have hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) (geo _ (baseA (puAmalgam h.le)) α' 2) := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by have := hc.2.1; omega)
    rwa [hαβ] at this
  rcases hμ with rfl | rfl
  · exact commutator_zm_le_stabCenter_of_gen_e h32 h52 hZ h hmin hb hd hβγ hl hg
      (gen_g h hg hc56)
  · have key := commutator_zm_le_stabCenter_of_gen_e h32 h52 hZ h hmin hb hd hβγ hl
      (mul_mem hg hxst) (gen_gx h hg hxst hopp)
    rwa [mul_inv_rev, mul_smul] at key

theorem s512TwoF_holds_e (h32 : S32) (h52 : S52) (h54 : S54) (hZ : S5Q2.Q2EvenZ)
    (hq55 : S5Q2.Q2Cent55) (hcore : S512T.Core) (hA2 : S512T.TwoAlt2) : S5B.S512TwoF := by
  intro G _ _ M T L h hmin hb4 k F _ _ a hd α' ν μ₁ μ₂ hchS
  have hch := S5B.isChain512Sel_subset hchS
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨hc, hαβ, hcμ, ⟨y, hy, hμy⟩, hdμ, hmid, hβγ⟩ := S512T.chain_geo h hb4 hch
  refine le_antisymm ?_ (S512T.le_relIndex_qv_zm h hb4 hd hcμ)
  by_contra hbad
  push Not at hbad
  by_cases h56 : ∃ l, S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l
  · obtain ⟨g, x, hg, hx, hconc, hμeq⟩ := hchS.2.2.2.2.1
    obtain ⟨l, hl, hc56, hopp⟩ : ∃ l,
        S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l ∧
        S5.Concl56 h (2 ^ k) a α' l g x ∧ S5.Opp56 h (2 ^ k) a l g x := by
      rcases hconc with ⟨hno, -⟩ | ⟨l, hl, hc, ho⟩
      · obtain ⟨l, hl⟩ := h56
        exact absurd hl (hno l)
      · exact ⟨l, hl, hc, ho⟩
    have hcent' := cent56F_holds_e h32 h52 hZ G M T L h hmin hb k F _ _ a hd α' hc hαβ l hl g hg
      x hx hc56 hopp μ₁ hμeq
    exact hcore G M T L h hmin hb4 k F _ _ a hd α' hc hαβ l hl μ₁ ⟨y, hy, hμy⟩ hcμ hbad hcent'
  push Not at h56
  obtain ⟨hμM, hγM, -, -, hμρ, hρα, -, -, -, hαγ, -, -⟩ := S512T.pair_facts h hb4 hcμ
  rw [hmid] at hρα hαγ
  obtain ⟨hEε, -, -, -⟩ := S512T.zm_facts h hb4 hcμ
  obtain ⟨hrel, hEQ⟩ := S512T.bad_indices h hb4 hd hcμ hbad
  have hα'M : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hd4 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb4
  have hγα' : (puAmalgam h.le).treeGraph.dist α' (geo _ (baseA (puAmalgam h.le)) α' 2) = 2 := by
    rw [SimpleGraph.dist_comm, dist_geo_right _ (by omega), hd4]
  have hZγ : ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
      Subgroup.centralizer (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) : Set _) :=
    zm_le_centralizer_qv _ hyp hγM
  have hZ'γ : ZM _ α' ≤ Subgroup.centralizer
      (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) : Set (puAmalgam h.le).Universal) :=
    (zm_le_qv_of_dist_lt _ hα'M (by omega)).trans (Subgroup.le_centralizer_iff.1 hZγ)
  set R := ⁅S5.uSub h.le L μ₁, ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)⁆ with hR
  have hRZ : R ≤ ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) :=
    (S512T.commutator_uSub_zm_le h hb4 hcμ).trans inf_le_left
  have hquad : R ≤ Subgroup.centralizer
      (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) : Set (puAmalgam h.le).Universal) := by
    have hab := (isElemAbelian_zm _ hyp hb0 hγM).1
    refine hRZ.trans fun z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := hab.is_comm.comm ⟨w, hw⟩ ⟨z, hz⟩
    simpa using congrArg Subtype.val this
  have hRX : R ≤ XM _ (baseA (puAmalgam h.le)) := by
    have hV1 : S5.uSub h.le L μ₁ ≤ Vv _ (baseA (puAmalgam h.le)) :=
      (S5B.uSub_le_zm h.le μ₁).trans (S5B.zm_le_vv_of_dist hμM hdμ.le)
    have hV2 : ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤ Vv _ (baseA (puAmalgam h.le)) :=
      S5B.zm_le_vv_of_dist hγM hαγ.le
    exact (Subgroup.commutator_mono hV1 hV2).trans
      (h52 G M T L h hmin hb k F _ _ a hd α' hc).2.2.1
  have hNc : R ≤ Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) : Set _) :=
    hRX.trans (Subgroup.le_centralizer_iff.1 (qv_le_centralizer_xm _ _))
  have hEN : ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤ Qv _ (baseA (puAmalgam h.le)) :=
    zm_le_qv_of_dist_lt _ hγM (by rw [SimpleGraph.dist_comm, hαγ]; omega)
  have hQαρ : Qv _ (baseA (puAmalgam h.le)) ≤
      Qv _ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) :=
    qv_le_qv _ hyp (isMVtx_baseA _) hρα.symm
  have hNs : Qv _ (baseA (puAmalgam h.le)) ≤ stab _ μ₁ :=
    hQαρ.trans (qv_le_stab_of_adj _ hμρ.symm)
  have bad := S512T.bad_vertex h54 h hmin hb hd hμM hμρ hEε hrel hquad hEQ hNs hEN hNc
  have hQR : R ≤ stabCenter _ (baseA (puAmalgam h.le)) →
      Qv _ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ≤
        Subgroup.centralizer (R : Set (puAmalgam h.le).Universal) := by
    intro hRc t ht
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (S510.commute_of_mem_stabCenter (hRc hr) (qv_le_stab_of_adj _ hρα ht)).symm
  have hcase : R ≤ stabCenter _ (baseA (puAmalgam h.le)) → False := by
    intro hRc
    obtain ⟨-, hJα, l₀, hl₀, hT₀, hJ₀⟩ := bad.2.2.1 (hQR hRc)
    refine h56 l₀ ⟨?_, hl₀, hT₀, hJ₀⟩
    rw [S512T.jOff_eq_qv_of_point h hJα hγM hβγ.symm, hJα]
  have hnorm : ⁅S5.uSub h.le L μ₁, Qv _ (baseA (puAmalgam h.le))⁆ ≤ R → False := by
    intro hNR
    have hReq : ⁅S5.uSub h.le L μ₁, Qv _ (baseA (puAmalgam h.le))⁆ = R :=
      le_antisymm hNR (Subgroup.commutator_mono le_rfl hEN)
    obtain ⟨ρ, hαρ, hρμ, -, hst, -⟩ := S510.lam55_facts h hc hβγ h56 hch.2.2.2.2.1
    have hρe := S512T.eq_geo_one_of_adj h hb4 hcμ hmid hαρ hρμ
    subst hρe
    have hRn : stab _ (baseA (puAmalgam h.le)) ≤
        Subgroup.normalizer (R : Set (puAmalgam h.le).Universal) := by
      rw [← hst]
      refine sup_le ?_ ?_
      · rw [← hReq]
        refine le_normalizer_commutator_of ?_
          ((qv_le_stab_of_adj _ hρα).trans (stab_le_normalizer_qv _ _))
        exact (qv_le_stab_of_adj _ hμρ.symm).trans (le_normalizer_commutator_of
          (stab_le_normalizer_zm _ _) (stab_le_normalizer_puTrans h.le hLn _))
      · exact (hZ'γ.trans (Subgroup.centralizer_le hRZ)).trans
          (Subgroup.centralizer_le_normalizer _)
    exact hcase (le_stabCenter_of_not_case56 h32 h54 hq55 h hmin hb4 hd hcμ hmid hβγ h56 hRX
      (puTrans_le_centralizer_of_normal h32 h hd hRX hRn bad.1) hRZ)
  obtain ⟨g, x, hg, hx, hconc, hμeq⟩ := hch.2.2.2.2.1
  have hc55 : S5.Concl55 h (2 ^ k) α' (geo _ (baseA (puAmalgam h.le)) α' 2) g x := by
    rcases hconc with ⟨-, h1⟩ | ⟨l, hl, -⟩
    · exact h1
    · exact absurd hl (h56 l)
  rcases h54 G M T L h hmin hb k F _ _ a hd with ⟨hcard, hline, hJ2⟩ | ⟨-, -, p₀, hp₀, hTq⟩
  ·
    by_cases hL : puTrans h.le L (baseA _) ≤
        S5.jOff h.le L (2 ^ k) μ₁ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ⊔
          S5.zHat _ (baseA _) α'
    ·
      have hTN : Qv _ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ≤
          Subgroup.normalizer (Qv _ (baseA (puAmalgam h.le)) : Set _) :=
        (qv_le_stab_of_adj _ hρα).trans (stab_le_normalizer_qv _ _)
      have hJR := bad.2.1 hTN hcard hline hJ2
      have hZR : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤
          Subgroup.centralizer (R : Set (puAmalgam h.le).Universal) :=
        (inf_le_left.trans hZ'γ).trans (Subgroup.centralizer_le hRZ)
      exact hcase (le_stabCenter_of_not_case56 h32 h54 hq55 h hmin hb4 hd hcμ hmid hβγ h56 hRX
        (hL.trans (sup_le hJR hZR)) hRZ)
    ·
      have halt : ¬ puTrans h.le L (baseA _) ≤
          (S5.jOff h.le L (2 ^ k) (g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2)
              (g⁻¹ • baseB (puAmalgam h.le)) ⊔ S5.zHat _ (baseA _) α') ⊓
            (S5.rconj x (S5.jOff h.le L (2 ^ k) (g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2)
              (g⁻¹ • baseB (puAmalgam h.le))) ⊔ S5.zHat _ (baseA _) α') :=
        fun h1 => hL (S512T.le_sup_of_alt1 h hb4 hch hg hx hμeq h1)
      by_cases hXU : Xq M = Uq M T L ⊔ Zq M L
      ·
        exfalso
        have hX := S512T.xm_eq_uSub_sup_of_xq h hXU
        obtain ⟨-, -, hc3⟩ := hc55
        tauto
      · by_cases hQ : (Qv _ μ₁).relIndex (Qv _ (baseA (puAmalgam h.le))) ≤ (2 ^ k) ^ 2
        · exact hnorm (bad.2.2.2.1 hQαρ hQ)
        · push Not at hQ
          exact hA2 G M T L h hmin hb4 k F _ _ a hd α' ν μ₁ μ₂ hch hbad hQ h56 hline hXU g hg
            x hx hc55 hμeq hL
  ·
    exact hnorm (bad.2.2.2.1 hQαρ (bad.2.2.2.2 hQαρ p₀ hp₀ hTq))

end S512R

end CFSG.Quasithin.MS93
