module

public import CFSG.Quasithin.MS93.S512GOff
public import CFSG.Quasithin.MS93.S512LOff
public import CFSG.Quasithin.MS93.S5Q2Hat

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512G

theorem relIndex_le_of_forall_exists {Γ : Type*} [Group Γ] {F Z V : Subgroup Γ} [Finite Z]
    (hZV : Z ≤ V) (hV : ∀ x ∈ V, ∃ z ∈ Z, z⁻¹ * x ∈ F) : F.relIndex V ≤ F.relIndex Z := by
  unfold Subgroup.relIndex Subgroup.index
  let f : ↥Z ⧸ F.subgroupOf Z → ↥V ⧸ F.subgroupOf V :=
    Quotient.map' (Subgroup.inclusion hZV) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      rw [Subgroup.mem_subgroupOf] at hab ⊢
      simpa using hab)
  refine Nat.card_le_card_of_surjective f ?_
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨z, hz, hzx⟩ := hV x x.2
    refine ⟨QuotientGroup.mk ⟨z, hz⟩, ?_⟩
    change QuotientGroup.mk (Subgroup.inclusion hZV ⟨z, hz⟩) = (QuotientGroup.mk x : ↥V ⧸ _)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hzx

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem commutator_vv_le_xm (h52 : S52) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    ⁅Vv (puAmalgam h.le) δ, Vv (puAmalgam h.le) δ⁆ ≤ XM _ δ := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  have key := (h52 G M T L h hmin hb k F _ _ a hd α' hc).2.2.1
  change ⁅Vi (puAmalgam h.le) (g • baseA _) 2, Vi (puAmalgam h.le) (g • baseA _) 2⁆ ≤
    XM _ (g • baseA (puAmalgam h.le))
  rw [vi_smul, xm_smul, ← Subgroup.map_commutator]
  exact Subgroup.map_mono key

theorem secHyp_nclStab (h32 : S32) (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hdαδ : (puAmalgam h.le).treeGraph.dist (baseA _) δ = 2)
    (hVX : ⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆ ≤
      XM _ (baseA (puAmalgam h.le)))
    (hZB : ¬ ZM _ δ ≤ S5.bSub h.le L (baseA _)) :
    S512N.SecHyp h (S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ δ)) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hVv : S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ δ) ≤ Vv _ (baseA (puAmalgam h.le)) :=
    S512N.nclStab_le_vv h hδ hdαδ.le
  have hXB : XM _ (baseA (puAmalgam h.le)) ⊓ Vv _ (baseA (puAmalgam h.le)) ≤
      S5.bSub h.le L (baseA _) := by
    intro x hx
    refine Subgroup.subset_closure ⟨hx.2, fun y hy => ?_⟩
    exact S5B.uSub_le_zm h.le _ (S5C56.commutator_xm_puTrans_le_uSub h32 h
      (Subgroup.commutator_mem_commutator hx.1 hy))
  have hcomm : ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ δ),
      S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ δ)⁆ ≤ S5.bSub h.le L (baseA _) :=
    (le_inf ((Subgroup.commutator_mono hVv hVv).trans hVX)
      ((Subgroup.commutator_mono hVv hVv).trans (Subgroup.commutator_le.2 fun x hx y hy => by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)))).trans hXB
  refine ⟨hb, hVv, S310.stab_le_normalizer_nclStab _ _ _, hcomm, ?_, ?_⟩
  · intro v hv
    refine S512N.sq_mem_of_iSup (K := fun g : ↥(stab (puAmalgam h.le) (baseA _)) =>
      (ZM _ δ).map (MulAut.conj (g : (puAmalgam h.le).Universal)).toMonoidHom) ?_ hcomm v hv
    rintro g _ ⟨z, hz, rfl⟩
    have hz2 : z ^ 2 = 1 := (isElemAbelian_zm _ hyp hb0 hδ).2 z hz
    rw [← map_pow, hz2, map_one]
  · intro hle
    exact hZB ((S512N.le_nclStab _ _ _).trans hle)

theorem isElemAbelian_two_of_le {Γ : Type*} [Group Γ] {E E' : Subgroup Γ} (hEE' : E ≤ E')
    (hE' : CFSG.Open.IsElemAbelian 2 E') : CFSG.Open.IsElemAbelian 2 E := by
  refine ⟨IsMulCommutative.of_comm fun x y => ?_, fun x hx => hE'.2 x (hEE' hx)⟩
  apply Subtype.ext
  have hxy := congrArg Subtype.val ((isMulCommutative_iff.mp hE'.1) ⟨x, hEE' x.2⟩ ⟨y, hEE' y.2⟩)
  exact hxy

theorem false_of_frame (h14 : MS14AS) (hSQ : SQTKQuot)
    (hT : S32.TypeFacts) (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h55 : S55)
    (h56 : S56) (hq2 : S5B.Q2Cent) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) (hd : S5.IsSp4Data M T L k F a)
    {α' μ δ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _)
    (hbad : 2 ^ k < (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))))
    (hμ : μ ∈ S5.lam h (2 ^ k) a α' (geo _ (baseA (puAmalgam h.le)) α' 2))
    (hcμ : IsCritical _ μ (geo _ (baseA (puAmalgam h.le)) α' 2))
    (hJne : S5.jOff h.le L (2 ^ k) (geo _ (baseA (puAmalgam h.le)) α' 2) (baseB _) ≠
      S5.jOff h.le L (2 ^ k) (baseA _) (baseB _))
    (hQ : (2 ^ k) ^ 2 < (Qv _ (baseA (puAmalgam h.le))).relIndex
      (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)))
    (hQJ : Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
      S5.jOff h.le L (2 ^ k) (baseA _) (baseB _))
    (hline : ∃ l : Submodule F (MSP.V4 F), MSP.IsLine l ∧
      Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.stab l) ∧
      S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l))
    (hc' : IsCritical _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ')
    (hgeo : geo _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ' 2 = α')
    (hmem : baseA _ ∈ S5B.lamAllAt h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) δ') :
    False := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hq1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hd4 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb4
  have hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) (geo _ (baseA (puAmalgam h.le)) α' 2) := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ] at this
  have hγM : IsMVtx _ (geo _ (baseA (puAmalgam h.le)) α' 2) :=
    (isMVtx_iff_of_adj _ hβγ.symm).2 (not_isMVtx_baseB _)
  have hαγ : (puAmalgam h.le).treeGraph.dist (baseA _) (geo _ (baseA (puAmalgam h.le)) α' 2) =
      2 := dist_geo _ (by omega)
  have hα'M : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hγα' : (puAmalgam h.le).treeGraph.dist α' (geo _ (baseA (puAmalgam h.le)) α' 2) = 2 := by
    rw [SimpleGraph.dist_comm, dist_geo_right _ (by omega), hd4]
  have h56' : ∀ l, ¬ S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l :=
    fun l hl => hJne hl.1
  obtain ⟨hcard, -, hJ2⟩ : Nat.card (S5.offSet h.le L (2 ^ k) (baseA _) (baseB _)) = 1 ∧
      (∃ l : Submodule F (MSP.V4 F), MSP.IsLine l ∧
        Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.stab l) ∧
        S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l)) ∧
      (2 ^ k) ^ 2 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex
        (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)) := by
    rcases h54 G M T L h hmin hb k F _ _ a hd with h4a | ⟨-, hJT, p₀, hp₀, hTq⟩
    · exact h4a
    · exfalso
      obtain ⟨l, hl, -, hJl⟩ := hline
      have hFq : 1 < Nat.card F := by
        rw [Nat.card_eq_fintype_card, hd.2.1]
        exact Nat.one_lt_two_pow (by have := hd.1; omega)
      refine S512T.not_qPoint_le_qLine hFq hp₀ hl ?_
      rw [← hTq, ← hJT]
      rintro _ ⟨m, hm, rfl⟩
      obtain ⟨m', hm', hmm⟩ := hJl hm
      rw [← (puAmalgam h.le).ofA_injective hmm]
      exact hm'
  have hlamAt : μ ∈ S5B.lamAt h (2 ^ k) a (baseA _) α' (geo _ (baseA (puAmalgam h.le)) α' 2) :=
    ⟨1, one_smul _ _, by rw [one_smul, hαβ], by simpa using hμ⟩
  obtain ⟨hdμ, hmid⟩ := S5B.lamStep_geo h hb4 ⟨hc, hlamAt, hcμ⟩
  obtain ⟨t, ht, hμt⟩ := S5B.exists_mem_stab_of_mem_lam hμ
  obtain ⟨hμM, -, -, -, hμρ, hρα, -, -, -, -, -, -⟩ := S512T.pair_facts h hb4 hcμ
  rw [hmid] at hρα
  obtain ⟨ν, hαν, hνμ, -, -, -, halt⟩ := S510.lam55_facts h hc hβγ h56' hμ
  have hνe : ν = geo _ μ (geo _ (baseA (puAmalgam h.le)) α' 2) 1 :=
    S512T.eq_geo_one_of_adj h hb4 hcμ hmid hαν hνμ
  subst hνe
  have hL1 : puTrans h.le L (baseA _) ≤
      S5.jOff h.le L (2 ^ k) μ (geo _ μ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ⊔
        S5.zHat _ (baseA _) α' := by
    rcases halt with h1 | ⟨-, hidx, -⟩
    · exact h1
    · exfalso
      have hQγ : Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
          S5.jOff h.le L (2 ^ k) (geo _ (baseA (puAmalgam h.le)) α' 2) (baseB _) ⊓
            S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) :=
        le_inf (S5B.qv_le_jOff h hq1 hγM hβγ.symm) hQJ
      have hfin : Finite ↥(Qv (puAmalgam h.le) (baseB _)) :=
        finite_qv _ hyp (not_isMVtx_baseB _)
      have hJfin : Finite ↥(S5.jOff h.le L (2 ^ k) (geo _ (baseA (puAmalgam h.le)) α' 2)
          (baseB _) ⊓ S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)) :=
        Finite.of_injective _ (Subgroup.inclusion_injective
          (inf_le_left.trans (S5B.jOff_le_qv h.le L _ _ _)))
      have := Subgroup.relIndex_le_of_le_right (H := Qv _ (baseA (puAmalgam h.le))) hQγ
        (by exact Subgroup.index_ne_zero_of_finite)
      omega
  have hZ'γ : ZM _ α' ≤ Subgroup.centralizer
      (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) : Set (puAmalgam h.le).Universal) :=
    (zm_le_qv_of_dist_lt _ hα'M (by omega)).trans
      (Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hγM))
  have hq : (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ) = 2 ^ k := by
    refine le_antisymm ?_ (S512T.le_relIndex_qv_zm h hb4 hd hcμ)
    by_contra hbad₂
    push Not at hbad₂
    obtain ⟨hEε, -, -, -⟩ := S512T.zm_facts h hb4 hcμ
    obtain ⟨hrel, hEQ⟩ := S512T.bad_indices h hb4 hd hcμ hbad₂
    set R := ⁅S5.uSub h.le L μ, ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)⁆ with hR
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
      have hV1 : S5.uSub h.le L μ ≤ Vv _ (baseA (puAmalgam h.le)) :=
        (S5B.uSub_le_zm h.le μ).trans (S5B.zm_le_vv_of_dist hμM hdμ.le)
      have hV2 : ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤ Vv _ (baseA (puAmalgam h.le)) :=
        S5B.zm_le_vv_of_dist hγM hαγ.le
      exact (Subgroup.commutator_mono hV1 hV2).trans
        (h52 G M T L h hmin hb k F _ _ a hd α' hc).2.2.1
    have hNc : R ≤ Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) : Set _) :=
      hRX.trans (Subgroup.le_centralizer_iff.1 (qv_le_centralizer_xm _ _))
    have hEN : ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤ Qv _ (baseA (puAmalgam h.le)) :=
      zm_le_qv_of_dist_lt _ hγM (by rw [SimpleGraph.dist_comm, hαγ]; omega)
    have hQαρ : Qv _ (baseA (puAmalgam h.le)) ≤
        Qv _ (geo _ μ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) :=
      qv_le_qv _ hyp hα hρα.symm
    have hNs : Qv _ (baseA (puAmalgam h.le)) ≤ stab _ μ :=
      hQαρ.trans (qv_le_stab_of_adj _ hμρ.symm)
    have bad := S512T.bad_vertex h54 h hmin hb hd hμM hμρ hEε hrel hquad hEQ hNs hEN hNc
    have hTN : Qv _ (geo _ μ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ≤
        Subgroup.normalizer (Qv _ (baseA (puAmalgam h.le)) : Set _) :=
      (qv_le_stab_of_adj _ hρα).trans (stab_le_normalizer_qv _ _)
    have hJR := bad.2.1 hTN hcard hline hJ2
    have hZR : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤
        Subgroup.centralizer (R : Set (puAmalgam h.le).Universal) :=
      (inf_le_left.trans hZ'γ).trans (Subgroup.centralizer_le hRZ)
    have hRc := S512T.le_stabCenter_of_le_centralizer hq2 h hmin hb hd hRX
      (hL1.trans (sup_le hJR hZR))
    have hQR : Qv _ (geo _ μ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ≤
        Subgroup.centralizer (R : Set (puAmalgam h.le).Universal) := by
      intro r hr
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact (S510.commute_of_mem_stabCenter (hRc hs) (qv_le_stab_of_adj _ hρα hr)).symm
    obtain ⟨-, hJα, l₀, hl₀, hT₀, hJ₀⟩ := bad.2.2.1 hQR
    refine h56' l₀ ⟨?_, hl₀, hT₀, hJ₀⟩
    rw [S512T.jOff_eq_qv_of_point h hJα hγM hβγ.symm, hJα]
  have hn : puTrans h.le L (baseA _) ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) :=
    hL1.trans (sup_le (S512T.jOff_le_normalizer_y h54 h hmin hb4 hd hcμ hmid hαν hνμ hq)
      (S5B.s512One_case55 h32 hX2 h52 h54 h hmin hb4 hd hc hαβ hc' hgeo hmem h56' hμ))
  have hYZ : S5.uSub h.le L μ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤ ZM _ μ :=
    inf_le_left.trans (S5B.uSub_le_zm h.le μ)
  have hYB : S5.uSub h.le L μ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
      S5.bSub h.le L (baseA _) :=
    S5B.le_bSub_of_xm h hb (h32 G M T L h).2.1 hα hdμ (hYZ.trans (zm_le_xm _ hyp hb0 hμM))
      (hYZ.trans (S5B.zm_le_vv_of_dist hμM hdμ.le)) hn
  have hBμ : (S5.bSub h.le L (baseA _)).relIndex (ZM _ μ) ≤ 2 ^ k := by
    rw [S512T.relIndex_bSub_zm_eq h hb4 hcμ hmid]
    have hq' := hq
    rw [← S512T.relIndex_qv_uSub_eq h hb4 hcμ] at hq'
    rw [← hq', ← Subgroup.inf_relIndex_right (S5.bSub h.le L (baseA _)),
      ← Subgroup.inf_relIndex_right (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2))]
    refine Subgroup.relIndex_le_of_le_left (fun x hx => ⟨hYB ⟨hx.2, hx.1⟩, hx.2⟩) ?_
    rw [Subgroup.inf_relIndex_right, hq']
    positivity
  have hBγ : (S5.bSub h.le L (baseA _)).relIndex (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ≤
      2 ^ k := by
    have e := S5B.relIndex_bSub_zm_smul h t (baseA (puAmalgam h.le))
      (geo _ (baseA (puAmalgam h.le)) α' 2)
    rw [(mem_stab _).1 ht, ← hμt] at e
    rw [← e]
    exact hBμ
  set V := S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2))
    with hVdef
  have hZμV : ZM _ μ ≤ V := by
    rw [hμt]
    exact S512R.zm_smul_le_nclStab h ht _
  have hVQ : V ≤ Qv _ (baseA (puAmalgam h.le)) := S310.nclStab_le_qv h hγM hαγ hb
  have hrel : (Subgroup.centralizer (V : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2)) ≤ 2 ^ k := by
    have := S512N.finite_zm h hγM
    have hY := S512N.inf_bSub_sup_le_centralizer_nclStab h hb hα hγM hαγ
    calc (Subgroup.centralizer (V : Set (puAmalgam h.le).Universal)).relIndex
          (S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2))
        ≤ (Subgroup.centralizer (V : Set (puAmalgam h.le).Universal)).relIndex
          (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)) :=
          Subgroup.relIndex_le_of_le_right (S5B.uSub_le_zm h.le _)
            Subgroup.FiniteIndex.index_ne_zero
      _ ≤ (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ⊓ S5.bSub h.le L (baseA _)).relIndex
          (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)) :=
          Subgroup.relIndex_le_of_le_left (le_sup_left.trans hY)
            Subgroup.FiniteIndex.index_ne_zero
      _ = (S5.bSub h.le L (baseA _)).relIndex (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)) :=
          Subgroup.inf_relIndex_left _ _
      _ ≤ 2 ^ k := hBγ
  have hV2 : IsPGroup 2 V :=
    (isPGroup_qv _ hyp (not_isMVtx_baseB _)).to_le
      (hVQ.trans (qv_le_qv _ hyp hα (adj_baseA_baseB _)))
  have hVst : V ≤ stab _ (geo _ (baseA (puAmalgam h.le)) α' 2) :=
    hVQ.trans (qv_le_stab_of_dist_le_two _ hyp hα hαγ.le)
  have hmul : ∀ x ∈ V, ∃ z ∈ ZM _ μ, z⁻¹ * x ∈ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) :=
    fun x hx => S310.exists_mem_mul_qv h hd hγM hVst hV2 hZμV hcμ.2.2 hrel
      (S512T.le_relIndex_qv_zm h hb4 hd hcμ) hx
  have hcγμ : IsCritical _ (geo _ (baseA (puAmalgam h.le)) α' 2) μ :=
    ms22_iii _ hyp hb0 h.centHyp hcμ
  have hmid' : geo _ (geo _ (baseA (puAmalgam h.le)) α' 2) μ 2 = baseA _ := by
    obtain ⟨-, -, -, hd4', -⟩ := S512T.pair_facts h hb4 hcμ
    have := geo_symm _ (show 2 ≤ (puAmalgam h.le).treeGraph.dist μ
      (geo _ (baseA (puAmalgam h.le)) α' 2) by omega)
    rw [hd4', hmid] at this
    exact this
  have hV := secHyp_nclStab h32 h hb hγM hαγ (commutator_vv_le_xm h52 h hmin hb hd hc hα)
    (S512L.zm_not_le_bSub h hb hcγμ hmid')
  obtain ⟨-, -, hEs, hRX', -, -⟩ := S5B.crit_facts h hc
  have hEe : CFSG.Open.IsElemAbelian 2 (S5.zHat _ (baseA (puAmalgam h.le)) α') :=
    isElemAbelian_two_of_le inf_le_left (isElemAbelian_zm _ hyp hb0 hα'M)
  have hΛ : (2 ^ k) ^ 2 ≤ (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) := by
    rw [S512T.relIndex_qv_zm_eq h hb4 hc, (S512T.bad_indices h hb4 hd hc hbad).1]
  have hγε : (puAmalgam h.le).treeGraph.Adj (geo _ (baseA (puAmalgam h.le)) α' 2)
      (geo _ α' (baseA (puAmalgam h.le)) 1) := by
    have e := geo_symm _ (show 3 ≤ (puAmalgam h.le).treeGraph.dist (baseA (puAmalgam h.le)) α'
      by omega)
    rw [hd4, show 4 - 3 = 1 from rfl] at e
    rw [e]
    exact adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 2) (by omega)
  have hYQ : V ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤ Qv _ (geo _ α' (baseA _) 1) :=
    inf_le_right.trans (qv_le_qv _ hyp hγM hγε)
  have hYR : V ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
      Subgroup.centralizer (critR _ (baseA (puAmalgam h.le)) α' : Set _) :=
    (inf_le_left.trans hVQ).trans
      ((qv_le_centralizer_xm _ _).trans (Subgroup.centralizer_le hRX'))
  have hcomm := S512R.commutator_zHat_le_critR_at h hd hc hΛ hYQ hYR
  have hRB : critR _ (baseA (puAmalgam h.le)) α' ≤ S5.bSub h.le L (baseA _) :=
    (commutator_le_left_of_le_normalizer ((S5B.crit_facts h hc).1.trans
      (stab_le_normalizer_zm _ _))).trans (S512T.zm_le_bSub h hα)
  have hEW : (S36E.fixSec V (V ⊓ S5.bSub h.le L (baseA _)) (S5.zHat _ (baseA _) α')
      (hV.le_stab.trans hV.le_normalizer_inf)).relIndex V ≤ 2 ^ k := by
    have := S512N.finite_zm h hμM
    have hNV : ∀ x ∈ V, ∃ z ∈ ZM _ μ, z⁻¹ * x ∈ S36E.fixSec V (V ⊓ S5.bSub h.le L (baseA _))
        (S5.zHat _ (baseA _) α') (hV.le_stab.trans hV.le_normalizer_inf) := by
      intro x hx
      obtain ⟨z, hz, hzx⟩ := hmul x hx
      have hzxV : z⁻¹ * x ∈ V := mul_mem (inv_mem (hZμV hz)) hx
      refine ⟨z, hz, S36E.mem_fixSec.2 ⟨hzxV, fun e he => ?_⟩⟩
      have hev : e ∈ stab _ (baseA (puAmalgam h.le)) := hEs he
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hV.vn hev) _).1 hzxV) (inv_mem hzxV)
      · have h1 : ⁅z⁻¹ * x, e⁆ ∈ critR _ (baseA (puAmalgam h.le)) α' :=
          hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_inf.2 ⟨hzxV, hzx⟩) he)
        have e2 : e * (z⁻¹ * x) * e⁻¹ * (z⁻¹ * x)⁻¹ = ⁅z⁻¹ * x, e⁆⁻¹ := by
          rw [commutatorElement_inv, commutatorElement_def]
        rw [e2]
        exact hRB (inv_mem h1)
    have hZN : ZM _ μ ⊓ S5.bSub h.le L (baseA _) ≤ S36E.fixSec V (V ⊓ S5.bSub h.le L (baseA _))
        (S5.zHat _ (baseA _) α') (hV.le_stab.trans hV.le_normalizer_inf) := by
      intro z hz
      obtain ⟨hz₁, hz₂⟩ := Subgroup.mem_inf.1 hz
      refine S36E.mem_fixSec.2 ⟨hZμV hz₁, fun e he => ?_⟩
      have hev : e ∈ stab _ (baseA (puAmalgam h.le)) := hEs he
      refine Subgroup.mem_inf.2 ⟨mul_mem ((Subgroup.mem_normalizer_iff.1 (hV.vn hev) _).1
        (hZμV hz₁)) (inv_mem (hZμV hz₁)), mul_mem ?_ (inv_mem hz₂)⟩
      exact (Subgroup.mem_normalizer_iff.1 (S310.stab_le_normalizer_bSub h _ hev) _).1 hz₂
    calc _ ≤ (S36E.fixSec V (V ⊓ S5.bSub h.le L (baseA _)) (S5.zHat _ (baseA _) α')
          (hV.le_stab.trans hV.le_normalizer_inf)).relIndex (ZM _ μ) :=
          relIndex_le_of_forall_exists hZμV hNV
      _ ≤ (ZM _ μ ⊓ S5.bSub h.le L (baseA _)).relIndex (ZM _ μ) :=
          Subgroup.relIndex_le_of_le_left hZN Subgroup.FiniteIndex.index_ne_zero
      _ = (S5.bSub h.le L (baseA _)).relIndex (ZM _ μ) := Subgroup.inf_relIndex_left _ _
      _ ≤ 2 ^ k := hBμ
  by_cases hbig : 2 ^ k < (Qv _ (baseA (puAmalgam h.le))).relIndex (S5.zHat _ (baseA _) α')
  · exact absurd (S512N.relIndex_qv_le_of_offender h14 hSQ hT hd hV hEs hEe hEW) (not_le.2 hbig)
  push Not at hbig
  obtain ⟨t₁, t₂, t₃, htr, htn⟩ : ∃ t₁ t₂ t₃ : (puAmalgam h.le).Universal,
      S5.IsHatTriple _ (baseA _) α' t₁ t₂ t₃ ∧
        t₃ ∉ Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α' := by
    by_contra hno
    push Not at hno
    have hZeq : S5.zHat _ (baseA (puAmalgam h.le)) α' = ZM _ α' :=
      le_antisymm inf_le_left (le_inf le_rfl (le_iInf fun t => le_iInf fun ht =>
        le_iInf fun hn => absurd (hno t.1 t.2.1 t.2.2 ht) hn))
    rw [hZeq, (S512T.bad_indices h hb4 hd hc hbad).2] at hbig
    have hk : 1 < 2 ^ k := Nat.one_lt_two_pow (by have := hd.1; omega)
    nlinarith
  obtain ⟨rfl, -, -, -⟩ := S33.of_isHatTriple h hd hc htr
  exact false_of_even_offender h14 hSQ hT hd hV hEs hEe (by simpa using hEW)
    (S5.hatEven_holds G M T L h hmin hb 1 F _ _ a hd α' hc t₁ t₂ t₃ htr htn)
    (S59.zHat_not_le_qv_baseA h55 h56 h hmin hb hd hc)

end S512G

end CFSG.Quasithin.MS93
