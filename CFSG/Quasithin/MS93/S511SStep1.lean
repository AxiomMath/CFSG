module

public import CFSG.Quasithin.MS93.S511SSt1
public import CFSG.Quasithin.MS93.S511SV
public import CFSG.Quasithin.MS93.S511SVec

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

namespace S511S

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem finite_zm (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ) : Finite ↥(ZM _ μ) := by
  have := (isPGroup_vv h hb hμ).2
  exact Finite.of_injective _ (Subgroup.inclusion_injective (S38E.zm_le_vv (α := μ) _ hμ (by simp)))

theorem false_of_le_bSub (h59 : S5B.S59) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {ζ : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) ζ)
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ (baseA (puAmalgam h.le)))
    {Y : Subgroup (puAmalgam h.le).Universal}
    (hYB : Y ≤ S5.bSub h.le L (baseA (puAmalgam h.le)))
    (hidx : Y.relIndex (ZM _ (y⁻¹ • geo _ (baseA (puAmalgam h.le)) ζ 2)) ≤ 2 ^ k) : False := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hyα : y⁻¹ • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 (inv_mem hy)
  have hc' : IsCritical _ (baseA (puAmalgam h.le)) (y⁻¹ • ζ) := by
    have := (isCritical_smul _ y⁻¹ _ _).2 hc
    rwa [hyα] at this
  have hgeo : geo _ (baseA (puAmalgam h.le)) (y⁻¹ • ζ) 2 =
      y⁻¹ • geo _ (baseA (puAmalgam h.le)) ζ 2 := by
    conv_lhs => rw [← hyα]
    rw [geo_smul]
  have key := S510.s59_gp h59 h hmin hb hd hc'
  rw [hgeo] at key
  set μ := y⁻¹ • geo _ (baseA (puAmalgam h.le)) ζ 2 with hμdef
  have hμ : IsMVtx _ μ := by
    rw [hμdef, isMVtx_smul]
    exact isMVtx_geo_two _ hyp hb0 hc
  have : Finite ↥(ZM _ μ) := finite_zm h (by omega) hμ
  have hUZ : S5.uSub h.le L μ ≤ ZM _ μ := S5B.uSub_le_zm h.le _
  have h1 : (S5.bSub h.le L (baseA (puAmalgam h.le))).relIndex (S5.uSub h.le L μ) ≤
      (S5.bSub h.le L (baseA (puAmalgam h.le))).relIndex (ZM _ μ) :=
    Subgroup.relIndex_le_of_le_right hUZ
      (by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
  have h2 : (S5.bSub h.le L (baseA (puAmalgam h.le))).relIndex (ZM _ μ) ≤ Y.relIndex (ZM _ μ) :=
    Subgroup.relIndex_le_of_le_left hYB
      (by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
  omega

theorem commutator_sup_zm_le (h : PUHyp M T L) (hb : 4 < critDist (puAmalgam h.le))
    {ζ : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) ζ)
    {B : Subgroup (puAmalgam h.le).Universal} (hBV : B ≤ Vv _ (baseA (puAmalgam h.le)))
    (hBQ : B ≤ Qv _ ζ) :
    ⁅ZM _ (baseA (puAmalgam h.le)) ⊔ B, ZM _ ζ⁆ ≤ ZM _ (baseA (puAmalgam h.le)) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hζ : IsMVtx _ ζ := hc.isMVtx_right _ hyp
  have hZV : ZM _ (baseA (puAmalgam h.le)) ≤ Vv _ (baseA (puAmalgam h.le)) :=
    S38E.zm_le_vv _ hα (by simp)
  have hn : ZM _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer (B : Set _) :=
    (hZV.trans ((vv_le_centralizer_self h hb hα).trans (Subgroup.centralizer_le hBV))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hBc : B ≤ Subgroup.centralizer (ZM _ ζ : Set (puAmalgam h.le).Universal) :=
    hBQ.trans (Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hζ))
  exact (commutator_sup_le_left hn hBc).trans (commutator_le_left_of_le_normalizer
    ((zm_le_stab_of_isCritical _ hyp hb0 hc).trans (stab_le_normalizer_zm _ _)))

theorem step1_core (h : PUHyp M T L) (hb : 4 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a)
    (hJα : ∀ (δ : Vtx (puAmalgam h.le)) (l : Submodule F (MSP.V4 F)),
      (puAmalgam h.le).treeGraph.Adj (baseB _) δ → S5.Case56 h (2 ^ k) a δ l →
      ZM _ δ ⊓ XM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer
        (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _) ≤
      ZM _ (baseA (puAmalgam h.le)))
    {ζ : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) ζ)
    (hαβ : geo _ (baseA (puAmalgam h.le)) ζ 1 = baseB _) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) ζ 2) l)
    (hAZ : Vv _ (baseA (puAmalgam h.le)) ⊓ Qv _ (geo _ ζ (baseA (puAmalgam h.le)) 2) ≤
      ZM _ (baseA (puAmalgam h.le)) ⊔ (Vv _ (baseA (puAmalgam h.le)) ⊓
        Qv _ (geo _ ζ (baseA (puAmalgam h.le)) 2) ⊓ Qv _ ζ))
    {y w : (puAmalgam h.le).Universal} (hy : y ∈ stab _ (baseA (puAmalgam h.le)))
    (hw : w ∈ stab _ (baseA (puAmalgam h.le)))
    (hgen : puTrans h.le L (baseA (puAmalgam h.le)) ≤
      S5.rconj y (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)) ⊔
        S5.zHat _ (baseA (puAmalgam h.le)) ζ ⊔ S5.rconj w (S5.zHat _ (baseA (puAmalgam h.le)) ζ))
    (hwY : (ZM _ (y⁻¹ • geo _ (baseA (puAmalgam h.le)) ζ 2) ⊓
        Qv _ (geo _ ζ (baseA (puAmalgam h.le)) 2)).map (MulAut.conj w).toMonoidHom ≤
      Vv _ (baseA (puAmalgam h.le)) ⊓ Qv _ (geo _ ζ (baseA (puAmalgam h.le)) 2)) :
    ZM _ (y⁻¹ • geo _ (baseA (puAmalgam h.le)) ζ 2) ⊓
        Qv _ (geo _ ζ (baseA (puAmalgam h.le)) 2) ≤ S5.bSub h.le L (baseA (puAmalgam h.le)) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _) ζ = critDist (puAmalgam h.le) := hc.2.1
  set δ := geo _ (baseA (puAmalgam h.le)) ζ 2 with hδ
  set ζ₂ := geo _ ζ (baseA (puAmalgam h.le)) 2 with hζ₂
  set J := S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) with hJdef
  set V := Vv _ (baseA (puAmalgam h.le)) with hV
  set A := V ⊓ Qv _ ζ₂ with hA
  set Y := ZM _ (y⁻¹ • δ) ⊓ Qv _ ζ₂ with hY
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB (puAmalgam h.le)) δ := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := ζ) (i := 1) (by omega)
    rwa [hαβ] at this
  have hδM : IsMVtx _ δ := isMVtx_geo_two _ hyp hb0 hc
  have hμM : IsMVtx _ (y⁻¹ • δ) := (isMVtx_smul _ _ _).2 hδM
  have hdαμ : (puAmalgam h.le).treeGraph.dist (baseA _) (y⁻¹ • δ) = 2 := by
    have := dist_smul _ y⁻¹ (baseA (puAmalgam h.le)) δ
    rw [(mem_stab _).1 (inv_mem hy), dist_geo _ (by omega)] at this
    exact this
  have hYV : Y ≤ V := inf_le_left.trans (S38E.zm_le_vv _ hμM hdαμ.le)
  have hYA : Y ≤ A := le_inf hYV inf_le_right
  have hAZζ : ⁅A, ZM _ ζ⁆ ≤ ZM _ (baseA (puAmalgam h.le)) :=
    (Subgroup.commutator_mono hAZ le_rfl).trans
      (commutator_sup_zm_le h hb hc (inf_le_left.trans inf_le_left) inf_le_right)
  have hZhat : S5.zHat _ (baseA (puAmalgam h.le)) ζ ≤ ZM _ ζ := inf_le_left
  have hJst : J ≤ stab _ (baseA (puAmalgam h.le)) :=
    (S5B.jOff_le_qv h.le L _ _ _).trans (qv_le_stab_of_adj _ (adj_baseA_baseB _).symm)
  have hK₂ : S5.zHat _ (baseA (puAmalgam h.le)) ζ ≤ stab _ (baseA (puAmalgam h.le)) :=
    hZhat.trans (zm_le_stab_of_isCritical _ hyp hb0 hc)
  have hY₁ : ⁅Y, S5.rconj y J⁆ ≤ ZM _ (baseA (puAmalgam h.le)) := by
    have h1 := commutator_zm_jOff_le_zm_baseA h (by omega) hd hβδ hl (hJα _ _ hβδ hl)
    have h2 := Subgroup.map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) h1
    rw [Subgroup.map_commutator, ← zm_smul, ← zm_smul, (mem_stab _).1 (inv_mem hy)] at h2
    refine (Subgroup.commutator_mono inf_le_left le_rfl).trans ?_
    rw [S5B.rconj_eq_map]
    exact h2
  have hY₂ : ⁅Y, S5.zHat _ (baseA (puAmalgam h.le)) ζ⁆ ≤ ZM _ (baseA (puAmalgam h.le)) :=
    (Subgroup.commutator_mono hYA hZhat).trans hAZζ
  have hY₃ : ⁅Y, S5.rconj w (S5.zHat _ (baseA (puAmalgam h.le)) ζ)⁆ ≤
      ZM _ (baseA (puAmalgam h.le)) := by
    rw [← map_conj_le_map_conj_iff w, Subgroup.map_commutator, S5B.rconj_eq_map,
      map_conj_map_conj_inv, ← zm_smul, (mem_stab _).1 hw]
    exact (Subgroup.commutator_mono hwY hZhat).trans hAZζ
  have hcomm := commutator_le_zm_of_le_sup (S5.rconj_le_stab h hJst hy) hK₂
    (S5.rconj_le_stab h hK₂ hw) hY₁ hY₂ hY₃ hgen
  intro v hv
  exact Subgroup.subset_closure
    ⟨hYV hv, fun t ht => hcomm (Subgroup.commutator_mem_commutator hv ht)⟩

theorem uSub_inf_centralizer_eq_gp (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) {E E' : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ ρ) (hE' : E' ≤ stab _ ρ)
    (heq : ⁅S5.uSub h.le L ρ, E⁆ = ⁅S5.uSub h.le L ρ, E'⁆) :
    S5.uSub h.le L ρ ⊓ Subgroup.centralizer (E : Set _) =
      S5.uSub h.le L ρ ⊓ Subgroup.centralizer (E' : Set _) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hρ
  have hst : ∀ {K : Subgroup (puAmalgam h.le).Universal}, K ≤ stab _ (g • baseA _) →
      K.map (MulAut.conj g⁻¹).toMonoidHom ≤ stab _ (baseA (puAmalgam h.le)) := by
    intro K hK
    rw [stab_smul] at hK
    have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hK
    rwa [map_conj_inv_map_conj] at this
  have hrw : ∀ K : Subgroup (puAmalgam h.le).Universal,
      K = (K.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    fun K => (map_conj_map_conj_inv K g).symm
  rw [hrw E, hrw E', S5B.uSub_smul h.le hLn, ← Subgroup.map_commutator,
    ← Subgroup.map_commutator] at heq
  have heq₀ := Subgroup.map_injective (MulAut.conj g).injective heq
  have key := uSub_inf_centralizer_eq_baseA h hd (hst hE) (hst hE') heq₀
  have h1 := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) key
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← PU.centralizer_map_mulEquiv,
    ← PU.centralizer_map_mulEquiv, map_conj_map_conj_inv, map_conj_map_conj_inv,
    ← S5B.uSub_smul h.le hLn] at h1
  exact h1

theorem zm_inf_centralizer_zm_eq (h : PUHyp M T L) {μ ν : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ μ ν) :
    ZM _ μ ⊓ Subgroup.centralizer (ZM _ ν : Set (puAmalgam h.le).Universal) = ZM _ μ ⊓ Qv _ ν := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hc' := ms22_iii _ hyp hb0 hC hc
  have hν : IsMVtx _ ν := hc'.1
  apply le_antisymm
  · intro z ⟨hzZ, hzC⟩
    refine ⟨hzZ, ?_⟩
    have hadj := adj_geo_one_of_isCritical _ hb0 hc'
    rw [← hC ν _ hν hadj]
    exact ⟨zm_le_qv_geo_one _ hyp hb0 hc' hzZ, hzC⟩
  · exact inf_le_inf_left _ (Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv _ hyp hν))

theorem step1_both (h32 : S32) (h53 : S53) (h54 : S54) (h59 : S5B.S59) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    (hJα : ∀ (δ : Vtx (puAmalgam h.le)) (l : Submodule F (MSP.V4 F)),
      (puAmalgam h.le).treeGraph.Adj (baseB _) δ → S5.Case56 h (2 ^ k) a δ l →
      ZM _ δ ⊓ XM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer
        (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _) ≤
      ZM _ (baseA (puAmalgam h.le)))
    {ζ : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) ζ)
    (hαβ : geo _ (baseA (puAmalgam h.le)) ζ 1 = baseB _) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) ζ 2) l)
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hx : x ∈ puTrans h.le L (baseA _)) (hconc : S5.Concl56 h (2 ^ k) a ζ l g x)
    (hV₁ : Vv _ (baseA (puAmalgam h.le)) ≤ ZM _ (g⁻¹ • geo _ (baseA (puAmalgam h.le)) ζ 2) ⊔
      (Vv _ (baseA (puAmalgam h.le)) ⊓ Qv _ (geo _ ζ (baseA (puAmalgam h.le)) 2)))
    (hV₂ : Vv _ (baseA (puAmalgam h.le)) ≤
      ZM _ (x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) ζ 2) ⊔
        (Vv _ (baseA (puAmalgam h.le)) ⊓ Qv _ (geo _ ζ (baseA (puAmalgam h.le)) 2)))
    (h₁ : ¬ ZM _ (g⁻¹ • geo _ (baseA (puAmalgam h.le)) ζ 2) ≤
      Qv _ (geo _ ζ (baseA (puAmalgam h.le)) 2))
    (h₂ : ¬ ZM _ (x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) ζ 2) ≤
      Qv _ (geo _ ζ (baseA (puAmalgam h.le)) 2)) :
    ZM _ (g⁻¹ • geo _ (baseA (puAmalgam h.le)) ζ 2) ⊓ Qv _ (geo _ ζ (baseA (puAmalgam h.le)) 2) ≤
      Qv _ (x • geo _ ζ (baseA (puAmalgam h.le)) 2) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _) ζ = critDist (puAmalgam h.le) := hc.2.1
  set δ := geo _ (baseA (puAmalgam h.le)) ζ 2 with hδ
  set ζ₂ := geo _ ζ (baseA (puAmalgam h.le)) 2 with hζ₂
  set V := Vv _ (baseA (puAmalgam h.le)) with hV
  set A := V ⊓ Qv _ ζ₂ with hA
  set μ₁ := g⁻¹ • δ with hμ₁
  set μ₂ := x⁻¹ • μ₁ with hμ₂
  have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
  have hδM : IsMVtx _ δ := isMVtx_geo_two _ hyp hb0 hc
  have hdist : ∀ y ∈ stab _ (baseA (puAmalgam h.le)),
      (puAmalgam h.le).treeGraph.dist (baseA _) (y • δ) = 2 := fun y hy => by
    have := dist_smul _ y (baseA (puAmalgam h.le)) δ
    rw [(mem_stab _).1 hy, dist_geo _ (by omega)] at this
    exact this
  have hμ₁M : IsMVtx _ μ₁ := (isMVtx_smul _ _ _).2 hδM
  have hμ₂M : IsMVtx _ μ₂ := (isMVtx_smul _ _ _).2 hμ₁M
  have hdαμ₁ : (puAmalgam h.le).treeGraph.dist (baseA _) μ₁ = 2 := hdist _ (inv_mem hg)
  have hdαμ₂ : (puAmalgam h.le).treeGraph.dist (baseA _) μ₂ = 2 := by
    rw [hμ₂, hμ₁, ← mul_smul]
    exact hdist _ (mul_mem (inv_mem hxst) (inv_mem hg))
  have hαζ₂ : (puAmalgam h.le).treeGraph.dist (baseA _) ζ₂ + 2 = critDist (puAmalgam h.le) := by
    rw [hζ₂, tdist_comm, dist_geo_right _ (by rw [tdist_comm]; omega), tdist_comm, hd2]
    omega
  have hc₁ : IsCritical _ μ₁ ζ₂ := isCritical_of_not_le h hμ₁M hdαμ₁ hαζ₂ h₁
  have hc₂ : IsCritical _ μ₂ ζ₂ := isCritical_of_not_le h hμ₂M hdαμ₂ hαζ₂ h₂
  have hζ₂M : IsMVtx _ ζ₂ := hc₁.isMVtx_right _ hyp
  have hZμ₁V : ZM _ μ₁ ≤ V := S38E.zm_le_vv _ hμ₁M hdαμ₁.le
  have hZμ₂V : ZM _ μ₂ ≤ V := S38E.zm_le_vv _ hμ₂M hdαμ₂.le
  have hAc : A ≤ Subgroup.centralizer (ZM _ ζ₂ : Set (puAmalgam h.le).Universal) :=
    inf_le_right.trans (Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hζ₂M))
  have hVab := vv_le_centralizer_self h hb hα
  have hRV : ∀ {μ : Vtx (puAmalgam h.le)}, ZM _ μ ≤ V → V ≤ ZM _ μ ⊔ A →
      ⁅ZM _ μ, ZM _ ζ₂⁆ = ⁅V, ZM _ ζ₂⁆ := by
    intro μ hZ hVle
    refine le_antisymm (Subgroup.commutator_mono hZ le_rfl) ?_
    have hn : ZM _ μ ≤ Subgroup.normalizer (A : Set (puAmalgam h.le).Universal) :=
      (hZ.trans (hVab.trans (Subgroup.centralizer_le inf_le_left))).trans
        (Subgroup.centralizer_le_normalizer _)
    exact (Subgroup.commutator_mono hVle le_rfl).trans (commutator_sup_le_left hn hAc)
  have hR₁ := hRV hZμ₁V hV₁
  have hR₂ := hRV hZμ₂V hV₂
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB (puAmalgam h.le)) δ := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := ζ) (i := 1) (by omega)
    rwa [hαβ] at this
  have hQJ : Qv _ (baseA (puAmalgam h.le)) ≤
      S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) :=
    S5B.qv_le_jOff h Nat.one_le_two_pow hα (adj_baseA_baseB _)
  have hZζ₂Q : ZM _ ζ₂ ≤ Qv _ (baseA (puAmalgam h.le)) :=
    zm_le_qv_of_dist_lt _ hζ₂M (by rw [tdist_comm]; omega)
  have hRpα : ⁅ZM _ μ₁, ZM _ ζ₂⁆ ≤ ZM _ (baseA (puAmalgam h.le)) := by
    have h1 := (Subgroup.commutator_mono le_rfl hQJ).trans
      (commutator_zm_jOff_le_zm_baseA h (by omega) hd hβδ hl (hJα _ _ hβδ hl))
    have h2 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h1
    rw [Subgroup.map_commutator, ← zm_smul, ← qv_smul, ← zm_smul,
      (mem_stab _).1 (inv_mem hg)] at h2
    exact (Subgroup.commutator_mono le_rfl hZζ₂Q).trans h2
  have hRp₁ : ⁅ZM _ μ₁, ZM _ ζ₂⁆ ≤ ZM _ μ₁ := commutator_le_left_of_le_normalizer
    ((zm_le_stab_of_isCritical _ hyp hb0 hc₁).trans (stab_le_normalizer_zm _ _))
  have hRp₂ : ⁅ZM _ μ₁, ZM _ ζ₂⁆ ≤ ZM _ μ₂ := by
    rw [hR₁, ← hR₂]
    exact commutator_le_left_of_le_normalizer
      ((zm_le_stab_of_isCritical _ hyp hb0 hc₂).trans (stab_le_normalizer_zm _ _))
  have hZZ := zz56 h53 h54 h59 h32 h hmin hb hd hc hαβ hl
  have hgx : g * x ∈ stab _ (baseA (puAmalgam h.le)) := mul_mem hg hxst
  have hRpc : ⁅ZM _ μ₁, ZM _ ζ₂⁆ ≤ stabCenter _ (baseA (puAmalgam h.le)) := by
    intro z hz
    have hz₁ := S5C56.zm_inf_zm_smul_le h hZZ (inv_mem hg) ⟨hRpα hz, hRp₁ hz⟩
    rw [inv_inv] at hz₁
    have hzμ₂ : z ∈ ZM _ ((g * x)⁻¹ • δ) := by
      rw [mul_inv_rev, mul_smul]
      exact hRp₂ hz
    have hz₂ := S5C56.zm_inf_zm_smul_le h hZZ (inv_mem hgx) ⟨hRpα hz, hzμ₂⟩
    rw [inv_inv] at hz₂
    exact hconc.2.1 ⟨⟨hRpα hz, hz₁⟩, hz₂⟩
  have hxn : x ∈ Subgroup.normalizer
      ((⁅ZM _ μ₁, ZM _ ζ₂⁆ : Subgroup (puAmalgam h.le).Universal) : Set _) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun r hr =>
      (S510.commute_of_mem_stabCenter (hRpc hr) hxst).symm)
  have hR3 : ⁅ZM _ μ₁, ZM _ (x • ζ₂)⁆ = ⁅ZM _ μ₁, ZM _ ζ₂⁆ := by
    have e1 : (⁅ZM _ μ₂, ZM _ ζ₂⁆).map (MulAut.conj x).toMonoidHom =
        ⁅ZM _ μ₁, ZM _ (x • ζ₂)⁆ := by
      rw [Subgroup.map_commutator, ← zm_smul, ← zm_smul, hμ₂, smul_inv_smul]
    rw [← e1, hR₂, ← hR₁]
    exact map_conj_eq_of_mem_normalizer hxn
  have hc₃ : IsCritical _ μ₁ (x • ζ₂) := by
    have := (isCritical_smul _ x μ₂ ζ₂).2 hc₂
    rwa [hμ₂, smul_inv_smul] at this
  have hst₁ : ZM _ ζ₂ ≤ stab _ μ₁ := zm_le_stab_of_isCritical _ hyp hb0 hc₁
  have hst₃ : ZM _ (x • ζ₂) ≤ stab _ μ₁ := zm_le_stab_of_isCritical _ hyp hb0 hc₃
  have hU : S5.uSub h.le L μ₁ ⊓ Subgroup.centralizer (ZM _ ζ₂ : Set _) =
      S5.uSub h.le L μ₁ ⊓ Subgroup.centralizer (ZM _ (x • ζ₂) : Set _) :=
    uSub_inf_centralizer_eq_gp h hd hμ₁M hst₁ hst₃ (by
      rw [← commutator_zm_eq_uSub h32 h53 h hmin (by omega) hd hμ₁M hst₁,
        ← commutator_zm_eq_uSub h32 h53 h hmin (by omega) hd hμ₁M hst₃, hR3])
  have hZ := zm_inf_centralizer_eq_of_uSub h32 h53 h hmin (by omega) hd hμ₁M hst₁ hst₃ hU
  rw [← zm_inf_centralizer_zm_eq h hc₁, hZ, zm_inf_centralizer_zm_eq h hc₃]
  exact inf_le_right

theorem step1_baseA (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h53 : S53) (h54 : S54)
    (h56f : S5.S56f) (hZ : S5Q2.Q2EvenZ) (h59 : S5B.S59) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    (h56all : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      geo _ (baseA _) α' 1 = baseB _ →
      ∃ l : Submodule F (MSP.V4 F), S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    {ζ : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) ζ)
    (hαβ : geo _ (baseA (puAmalgam h.le)) ζ 1 = baseB _) :
    (2 ^ k) ^ 2 < (Vv _ (baseA (puAmalgam h.le)) ⊓ Qv _ (geo _ ζ (baseA (puAmalgam h.le)) 2) ⊓
      Qv _ ζ).relIndex (Vv _ (baseA (puAmalgam h.le))) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _) ζ = critDist (puAmalgam h.le) := hc.2.1
  set δ := geo _ (baseA (puAmalgam h.le)) ζ 2 with hδ
  set ζ₂ := geo _ ζ (baseA (puAmalgam h.le)) 2 with hζ₂
  set V := Vv _ (baseA (puAmalgam h.le)) with hV
  set A := V ⊓ Qv _ ζ₂ with hA
  set B := A ⊓ Qv _ ζ with hB
  by_contra hcon
  push Not at hcon
  have hJα : ∀ (δ : Vtx (puAmalgam h.le)) (l : Submodule F (MSP.V4 F)),
      (puAmalgam h.le).treeGraph.Adj (baseB _) δ → S5.Case56 h (2 ^ k) a δ l →
      ZM _ δ ⊓ XM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer
        (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _) ≤
      ZM _ (baseA (puAmalgam h.le)) := fun _ _ hβδ hl =>
    zm_inf_xm_inf_centralizer_jOff_le_zm_e h32 h53 hZ h hmin hb2 hd hβδ hl
  obtain ⟨l, hl⟩ := h56all ζ hc hαβ
  obtain ⟨g, hg, x, hx, hconc⟩ :=
    h56f G M T L h hmin hb2 k F _ _ a hd ζ hc hαβ l hl.2.1 hl.2.2.1 hl.2.2.2
  have hconc' : S5.Concl56 h (2 ^ k) a ζ l g x := hconc.1.1
  have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
  have hgx : g * x ∈ stab _ (baseA (puAmalgam h.le)) := mul_mem hg hxst
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB (puAmalgam h.le)) δ := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := ζ) (i := 1) (by omega)
    rwa [hαβ] at this
  have hδM : IsMVtx _ δ := isMVtx_geo_two _ hyp hb0 hc
  have hdist : ∀ y ∈ stab _ (baseA (puAmalgam h.le)),
      (puAmalgam h.le).treeGraph.dist (baseA _) (y • δ) = 2 := fun y hy => by
    have := dist_smul _ y (baseA (puAmalgam h.le)) δ
    rw [(mem_stab _).1 hy, dist_geo _ (by omega)] at this
    exact this
  have hαζ₂ : (puAmalgam h.le).treeGraph.dist (baseA _) ζ₂ + 2 = critDist (puAmalgam h.le) := by
    rw [hζ₂, tdist_comm, dist_geo_right _ (by rw [tdist_comm]; omega), tdist_comm, hd2]
    omega
  have hμ₁M : IsMVtx _ (g⁻¹ • δ) := (isMVtx_smul _ _ _).2 hδM
  have hμ₂M : IsMVtx _ (x⁻¹ • g⁻¹ • δ) := (isMVtx_smul _ _ _).2 hμ₁M
  have hdαμ₁ : (puAmalgam h.le).treeGraph.dist (baseA _) (g⁻¹ • δ) = 2 := hdist _ (inv_mem hg)
  have hdαμ₂ : (puAmalgam h.le).treeGraph.dist (baseA _) (x⁻¹ • g⁻¹ • δ) = 2 := by
    rw [← mul_smul]
    exact hdist _ (mul_mem (inv_mem hxst) (inv_mem hg))
  have hZμ₁V : ZM _ (g⁻¹ • δ) ≤ V := S38E.zm_le_vv _ hμ₁M hdαμ₁.le
  have hZμ₂V : ZM _ (x⁻¹ • g⁻¹ • δ) ≤ V := S38E.zm_le_vv _ hμ₂M hdαμ₂.le
  have hVfin : Finite ↥V := (isPGroup_vv h hb2 hα).2
  have hne : ∀ (H K : Subgroup (puAmalgam h.le).Universal), K ≤ V → H.relIndex K ≠ 0 := by
    intro H K hK
    have : Finite ↥K := Finite.of_injective _ (Subgroup.inclusion_injective hK)
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have hZαV : ZM _ (baseA (puAmalgam h.le)) ≤ V := S38E.zm_le_vv _ hα (by simp)
  have hZαA : ZM _ (baseA (puAmalgam h.le)) ≤ A :=
    le_inf hZαV (zm_le_qv_of_dist_lt _ hα (by omega))
  have hq := S511.le_relIndex_zm h hd hc
  have hBZ : (Qv _ ζ).relIndex (ZM _ (baseA (puAmalgam h.le))) =
      B.relIndex (ZM _ (baseA (puAmalgam h.le))) := by
    rw [← Subgroup.inf_relIndex_right (Qv _ ζ), ← Subgroup.inf_relIndex_right B]
    congr 1
    exact le_antisymm (le_inf (le_inf (inf_le_right.trans hZαA) inf_le_left) inf_le_right)
      (inf_le_inf_right _ inf_le_right)
  have hQA : ∀ {μ : Vtx (puAmalgam h.le)}, ZM _ μ ≤ V →
      (Qv _ ζ₂).relIndex (ZM _ μ) = A.relIndex (ZM _ μ) := by
    intro μ hZ
    rw [← Subgroup.inf_relIndex_right (Qv _ ζ₂), ← Subgroup.inf_relIndex_right A]
    congr 1
    exact le_antisymm (le_inf (le_inf (inf_le_right.trans hZ) inf_le_left) inf_le_right)
      (inf_le_inf_right _ inf_le_right)
  have hAB : 2 ^ k ≤ B.relIndex A :=
    calc 2 ^ k ≤ (Qv _ ζ).relIndex (ZM _ (baseA (puAmalgam h.le))) := hq
      _ = B.relIndex (ZM _ (baseA (puAmalgam h.le))) := hBZ
      _ ≤ B.relIndex A := Subgroup.relIndex_le_of_le_right hZαA (hne _ _ inf_le_left)
  have hmul : B.relIndex A * A.relIndex V = B.relIndex V :=
    Subgroup.relIndex_mul_relIndex B A V inf_le_left inf_le_left
  have hqpos : 0 < 2 ^ k := by positivity
  have hVA : A.relIndex V ≤ 2 ^ k := by
    have h1 : 2 ^ k * A.relIndex V ≤ 2 ^ k * 2 ^ k :=
      (Nat.mul_le_mul_right _ hAB).trans (by rw [hmul, ← pow_two]; exact hcon)
    exact Nat.le_of_mul_le_mul_left h1 hqpos
  have hZμA : ∀ {μ : Vtx (puAmalgam h.le)}, ZM _ μ ≤ V →
      (Qv _ ζ₂).relIndex (ZM _ μ) ≤ 2 ^ k := fun hZ =>
    ((hQA hZ).trans_le (Subgroup.relIndex_le_of_le_right hZ (hne _ _ le_rfl))).trans hVA
  have hlow : ∀ {μ : Vtx (puAmalgam h.le)}, IsMVtx _ μ →
      (puAmalgam h.le).treeGraph.dist (baseA _) μ = 2 → ¬ ZM _ μ ≤ Qv _ ζ₂ →
      2 ^ k ≤ (Qv _ ζ₂).relIndex (ZM _ μ) := fun hμ hdμ hZ =>
    le_relIndex_zm_gp h hd (isCritical_of_not_le h hμ hdμ hαζ₂ hZ)
  have hVZ : ∀ {μ : Vtx (puAmalgam h.le)}, IsMVtx _ μ →
      (puAmalgam h.le).treeGraph.dist (baseA _) μ = 2 → ¬ ZM _ μ ≤ Qv _ ζ₂ →
      V ≤ ZM _ μ ⊔ A := by
    intro μ hμ hdμ hZ
    have hZV : ZM _ μ ≤ V := S38E.zm_le_vv _ hμ hdμ.le
    have hWV : ZM _ μ ⊔ A ≤ V := sup_le hZV inf_le_left
    have hmul' : A.relIndex (ZM _ μ ⊔ A) * (ZM _ μ ⊔ A).relIndex V = A.relIndex V :=
      Subgroup.relIndex_mul_relIndex A (ZM _ μ ⊔ A) V le_sup_right hWV
    have hAW : 2 ^ k ≤ A.relIndex (ZM _ μ ⊔ A) :=
      calc 2 ^ k ≤ (Qv _ ζ₂).relIndex (ZM _ μ) := hlow hμ hdμ hZ
        _ = A.relIndex (ZM _ μ) := hQA hZV
        _ ≤ A.relIndex (ZM _ μ ⊔ A) := Subgroup.relIndex_le_of_le_right le_sup_left (hne _ _ hWV)
    have h1 : 2 ^ k * (ZM _ μ ⊔ A).relIndex V ≤ 2 ^ k * 1 :=
      (Nat.mul_le_mul_right _ hAW).trans (by rw [hmul', mul_one]; exact hVA)
    have h2 := Nat.le_of_mul_le_mul_left h1 hqpos
    have h3 := hne (ZM _ μ ⊔ A) V le_rfl
    exact Subgroup.relIndex_eq_one.1 (by omega)
  have hAZ : ∀ {μ : Vtx (puAmalgam h.le)}, IsMVtx _ μ →
      (puAmalgam h.le).treeGraph.dist (baseA _) μ = 2 → ¬ ZM _ μ ≤ Qv _ ζ₂ →
      A ≤ ZM _ (baseA (puAmalgam h.le)) ⊔ B := by
    intro μ hμ hdμ hZ
    have hZV : ZM _ μ ≤ V := S38E.zm_le_vv _ hμ hdμ.le
    have hVA' : 2 ^ k ≤ A.relIndex V :=
      (hlow hμ hdμ hZ).trans ((hQA hZV).trans_le
        (Subgroup.relIndex_le_of_le_right hZV (hne _ _ le_rfl)))
    have hBA : B.relIndex A ≤ 2 ^ k := by
      have h1 : B.relIndex A * 2 ^ k ≤ 2 ^ k * 2 ^ k :=
        (Nat.mul_le_mul_left _ hVA').trans (by rw [hmul, ← pow_two]; exact hcon)
      exact Nat.le_of_mul_le_mul_right h1 hqpos
    have hWA : ZM _ (baseA (puAmalgam h.le)) ⊔ B ≤ A := sup_le hZαA inf_le_left
    have hmul' : B.relIndex (ZM _ (baseA (puAmalgam h.le)) ⊔ B) *
        (ZM _ (baseA (puAmalgam h.le)) ⊔ B).relIndex A = B.relIndex A :=
      Subgroup.relIndex_mul_relIndex B (ZM _ (baseA (puAmalgam h.le)) ⊔ B) A le_sup_right hWA
    have hBW : 2 ^ k ≤ B.relIndex (ZM _ (baseA (puAmalgam h.le)) ⊔ B) :=
      calc 2 ^ k ≤ (Qv _ ζ).relIndex (ZM _ (baseA (puAmalgam h.le))) := hq
        _ = B.relIndex (ZM _ (baseA (puAmalgam h.le))) := hBZ
        _ ≤ B.relIndex (ZM _ (baseA (puAmalgam h.le)) ⊔ B) :=
          Subgroup.relIndex_le_of_le_right le_sup_left (hne _ _ (hWA.trans inf_le_left))
    have h1 : 2 ^ k * (ZM _ (baseA (puAmalgam h.le)) ⊔ B).relIndex A ≤ 2 ^ k * 1 :=
      (Nat.mul_le_mul_right _ hBW).trans (by rw [hmul', mul_one]; exact hBA)
    have h2 := Nat.le_of_mul_le_mul_left h1 hqpos
    have h3 := hne (ZM _ (baseA (puAmalgam h.le)) ⊔ B) A inf_le_left
    exact Subgroup.relIndex_eq_one.1 (by omega)
  have hnb : ¬ (ZM _ (g⁻¹ • δ) ≤ Qv _ ζ₂ ∧ ZM _ (x⁻¹ • g⁻¹ • δ) ≤ Qv _ ζ₂) := by
    rintro ⟨hZ, hZx⟩
    have h1 := S5B.s57_case56 h32 hX2 h52 h54 h hmin hb2 hd hc hβδ hl hg hx hconc' hZ hZx
    have h2 : 2 ^ k < (S5.bSub h.le L (baseA (puAmalgam h.le))).relIndex (S5.uSub h.le L δ) :=
      h59 G M T L h hmin hb k F _ _ a hd ζ hc hαβ
    omega
  have hrel : ∀ {μ : Vtx (puAmalgam h.le)}, ZM _ μ ≤ V →
      (ZM _ μ ⊓ Qv _ ζ₂).relIndex (ZM _ μ) ≤ 2 ^ k := fun hZ => by
    rw [Subgroup.inf_relIndex_left]
    exact hZμA hZ
  by_cases h₂ : ZM _ (x⁻¹ • g⁻¹ • δ) ≤ Qv _ ζ₂
  ·
    have h₁ : ¬ ZM _ (g⁻¹ • δ) ≤ Qv _ ζ₂ := fun h₁ => hnb ⟨h₁, h₂⟩
    have hwY : (ZM _ (g⁻¹ • δ) ⊓ Qv _ ζ₂).map (MulAut.conj x⁻¹).toMonoidHom ≤ A := by
      have h1 : (ZM _ (g⁻¹ • δ)).map (MulAut.conj x⁻¹).toMonoidHom = ZM _ (x⁻¹ • g⁻¹ • δ) :=
        (zm_smul _ _ _).symm
      refine (Subgroup.map_mono inf_le_left).trans ?_
      rw [h1]
      exact le_inf hZμ₂V h₂
    have hYB := step1_core h hb hd hJα hc hαβ hl (hAZ hμ₁M hdαμ₁ h₁) hg (inv_mem hxst)
      hconc'.2.2.1 hwY
    exact false_of_le_bSub h59 h hmin hb hd hc hg hYB (hrel hZμ₁V)
  · by_cases h₁ : ZM _ (g⁻¹ • δ) ≤ Qv _ ζ₂
    ·
      have hμeq : x⁻¹ • g⁻¹ • δ = (g * x)⁻¹ • δ := by rw [mul_inv_rev, mul_smul]
      rw [hμeq] at h₂ hZμ₂V hdαμ₂ hμ₂M
      have hgen : puTrans h.le L (baseA (puAmalgam h.le)) ≤
          S5.rconj (g * x) (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)) ⊔
            S5.zHat _ (baseA (puAmalgam h.le)) ζ ⊔
              S5.rconj x (S5.zHat _ (baseA (puAmalgam h.le)) ζ) := by
        have h1 := Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hconc'.2.2.1
        rw [Subgroup.map_sup, Subgroup.map_sup, ← puTrans_smul h.le hLn,
          (mem_stab _).1 (inv_mem hxst), S5B.rconj_eq_map, S5B.rconj_eq_map, map_conj_map_conj,
          inv_inv, map_conj_inv_map_conj, ← mul_inv_rev] at h1
        rw [S5B.rconj_eq_map, S5B.rconj_eq_map, sup_right_comm]
        exact h1
      have hwY : (ZM _ ((g * x)⁻¹ • δ) ⊓ Qv _ ζ₂).map (MulAut.conj x).toMonoidHom ≤ A := by
        have h1 : (ZM _ ((g * x)⁻¹ • δ)).map (MulAut.conj x).toMonoidHom = ZM _ (g⁻¹ • δ) := by
          rw [← zm_smul, ← mul_smul, mul_inv_rev, mul_inv_cancel_left]
        refine (Subgroup.map_mono inf_le_left).trans ?_
        rw [h1]
        exact le_inf hZμ₁V h₁
      have hYB := step1_core h hb hd hJα hc hαβ hl (hAZ hμ₂M hdαμ₂ h₂) hgx hxst hgen hwY
      exact false_of_le_bSub h59 h hmin hb hd hc hgx hYB (hrel hZμ₂V)
    ·
      have hboth := step1_both h32 h53 h54 h59 h hmin hb hd hJα hc hαβ hl hg hx hconc'
        (hVZ hμ₁M hdαμ₁ h₁) (hVZ hμ₂M hdαμ₂ h₂) h₁ h₂
      have hwY : (ZM _ (g⁻¹ • δ) ⊓ Qv _ ζ₂).map (MulAut.conj x⁻¹).toMonoidHom ≤ A := by
        have h1 : (ZM _ (g⁻¹ • δ)).map (MulAut.conj x⁻¹).toMonoidHom = ZM _ (x⁻¹ • g⁻¹ • δ) :=
          (zm_smul _ _ _).symm
        have h2 := Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hboth
        rw [← qv_smul, inv_smul_smul] at h2
        refine le_inf ?_ h2
        refine (Subgroup.map_mono inf_le_left).trans ?_
        rw [h1]
        exact hZμ₂V
      have hYB := step1_core h hb hd hJα hc hαβ hl (hAZ hμ₁M hdαμ₁ h₁) hg (inv_mem hxst)
        hconc'.2.2.1 hwY
      exact false_of_le_bSub h59 h hmin hb hd hc hg hYB (hrel hZμ₁V)

end S511S

end CFSG.Quasithin.MS93
