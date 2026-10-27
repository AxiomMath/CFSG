module

public import CFSG.Quasithin.MS93.S310A
public import CFSG.Quasithin.MS93.S310Stmt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

@[expose] def S310mCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → IsSp4Full M T L → critDist (puAmalgam h.le) = 4 →
    ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
          (a : ↥(stab (puAmalgam h.le) (baseA _)) →* ↥(StatedSp 2 F)),
        Fintype.card F = 2 ^ k → Function.Surjective a →
        IsSumOfNaturalModulesVia (stab _ (baseA _))
          (S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)))
          (S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)) ⊓ S5.bSub h.le L (baseA _))
          a false 1 →
        ⁅⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)), puTrans h.le L (baseA _)⁆,
            ⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)), puTrans h.le L (baseA _)⁆⁆ ≤
          S5.dSub h.le L (baseA _) →
        (S5.bSub h.le L (baseA _)).relIndex (ZM _ (geo _ (baseA _) α' 2)) ≤ 2 ^ k →
        (S5.bSub h.le L (geo _ (baseA _) α' 2)).relIndex (ZM _ α') ≤ 2 ^ k →
        (∃ g ∈ stab _ (geo _ (baseA _) α' 2), g • baseA (puAmalgam h.le) = α') →
        ⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)), ZM _ α'⁆ ≤
          S5.bSub h.le L (baseA _)

namespace S310

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem stab_le_normalizer_bSub (h : PUHyp M T L) (δ : Vtx (puAmalgam h.le)) :
    stab _ δ ≤ Subgroup.normalizer (S5.bSub h.le L δ : Set (puAmalgam h.le).Universal) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  rw [← S5B.bSub_smul h.le hLn, (mem_stab _).1 hg]

theorem exists_setup (h : PUHyp M T L) {F : Type} [Field F]
    {a : ↥(stab (puAmalgam h.le) (baseA _)) →* ↥(StatedSp 2 F)} (ha : Function.Surjective a)
    {V B : Subgroup (puAmalgam h.le).Universal}
    (hnat : IsSumOfNaturalModulesVia (stab _ (baseA _)) V (V ⊓ B) a false 1) :
    ∃ βv : (puAmalgam h.le).Universal → MSP.V4 F,
      Setup (stab _ (baseA (puAmalgam h.le))) (puTrans h.le L (baseA _)) V (V ⊓ B) a βv := by
  classical
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨hAV, -, β, hβs, hβk, hβe⟩ := hnat
  let βv : (puAmalgam h.le).Universal → MSP.V4 F := fun x =>
    if hx : x ∈ V then Multiplicative.toAdd (β ⟨x, hx⟩) 0 else 0
  have hβv : ∀ x (hx : x ∈ V), βv x = Multiplicative.toAdd (β ⟨x, hx⟩) 0 := fun x hx => by
    simp [βv, hx]
  refine ⟨βv, puTrans_le_stab h.le L _, stab_le_normalizer_puTrans h.le hLn _, hAV, inf_le_left,
    fun x hx y hy => ?_, fun w => ?_, fun x hx => ?_, fun g x hx => ?_,
    exists_mem_puTrans_of_pow_three h ha⟩
  · rw [hβv x hx, hβv y hy, hβv _ (mul_mem hx hy)]
    rw [show (⟨x * y, mul_mem hx hy⟩ : ↥V) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul, toAdd_mul]
    rfl
  · obtain ⟨x, hx⟩ := hβs (Multiplicative.ofAdd fun _ => w)
    refine ⟨x, x.2, ?_⟩
    rw [hβv _ x.2, Subtype.coe_eta, hx]
    rfl
  · rw [hβv x hx]
    have hker : (⟨x, hx⟩ : ↥V) ∈ β.ker ↔ x ∈ V ⊓ B := by
      rw [hβk, Subgroup.mem_subgroupOf]
    rw [← hker, MonoidHom.mem_ker]
    constructor
    · intro h0
      apply Multiplicative.toAdd.injective
      funext i
      rw [Subsingleton.elim i 0]
      exact h0
    · intro h1
      rw [h1]
      rfl
  · have hgx : (g : (puAmalgam h.le).Universal) * x * (g : (puAmalgam h.le).Universal)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hAV g.2) x).1 hx
    rw [hβv x hx, hβv _ hgx]
    simpa only [moduleAct, Bool.false_eq_true, ↓reduceIte] using hβe g ⟨x, hx⟩ ⟨_, hgx⟩ rfl 0

theorem not_commutator_le_of_nat (h : PUHyp M T L) {F : Type} [Field F] [CharP F 2]
    {a : ↥(stab (puAmalgam h.le) (baseA _)) →* ↥(StatedSp 2 F)} (ha : Function.Surjective a)
    {V B : Subgroup (puAmalgam h.le).Universal}
    (hnat : IsSumOfNaturalModulesVia (stab _ (baseA _)) V (V ⊓ B) a false 1) :
    ¬ ⁅V, puTrans h.le L (baseA _)⁆ ≤ V ⊓ B := by
  intro hle
  obtain ⟨βv, hs⟩ := exists_setup h ha hnat
  obtain ⟨x, hx, hxe⟩ := hs.surj (MSP.e₁ F)
  have huv : MSP.form F (MSP.e₁ F) (MSP.f₁ F) = 1 := by rw [MSP.form_e₁]; simp
  have hab : (1 : F) * 1 = 1 := one_mul 1
  obtain ⟨l, hl, hal⟩ := hs.ord3 _ (MSP.transv_mul_transv_pow_three huv hab)
  have hmem := hle (Subgroup.commutator_mem_commutator hx hl)
  have h0 := (hs.ker _ hmem.1).2 hmem
  rw [hs.map_commutator l hx, hxe, hal, MSP.transv_mul_transv_mulVec_left huv hab, one_smul]
    at h0
  have := congrFun h0 (.inl 0)
  simp at this

end S310

theorem s310m_of (hcore : S310mCore) : S310m := by
  intro G _ _ M T L h hmin hfull hb α' hc k F _ _ a hF ha hnat hV₀
  have : CharP F 2 := S5B.charP_two_of_card hF
  by_contra hneg
  simp only [not_or, not_lt, not_forall, not_not] at hneg
  obtain ⟨h1, h2, g, hg, hga⟩ := hneg
  have hcore' := hcore G M T L h hmin hfull hb α' hc k F _ _ a hF ha hnat hV₀ h1 h2 ⟨g, hg, hga⟩
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hd : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hc' := ms22_iii _ hyp hb0 h.centHyp hc
  obtain ⟨y, hyZ, hyQ⟩ := Set.not_subset.1 hc'.2.2
  have hαδ : (puAmalgam h.le).treeGraph.Adj (baseA _) (geo _ (baseA (puAmalgam h.le)) α' 1) :=
    adj_geo_one _ (by omega)
  have hδ : ¬ IsMVtx _ (geo _ (baseA (puAmalgam h.le)) α' 1) :=
    (isMVtx_iff_of_adj _ hαδ).1 (isMVtx_baseA _)
  have hδα' : (puAmalgam h.le).treeGraph.dist (geo _ (baseA (puAmalgam h.le)) α' 1) α' = 3 := by
    rw [dist_geo_right _ (by omega), hd]
  have hyδ : y ∈ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 1) :=
    zm_le_qv_of_dist_lt _ hα' (by rw [SimpleGraph.dist_comm, hδα', hb]; norm_num) hyZ
  have hyst : y ∈ stab _ (baseA (puAmalgam h.le)) :=
    qv_le_stab_of_isMVtx _ hyp (isMVtx_baseA _) hαδ hyδ
  have hy2 : ∃ e : ℕ, y ^ 2 ^ e = 1 := by
    obtain ⟨e, he⟩ := isPGroup_qv _ hyp hδ ⟨y, hyδ⟩
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  set V := S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2))
    with hVdef
  set B := S5.bSub h.le L (baseA (puAmalgam h.le)) with hBdef
  have hAV : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer (V : Set _) := hnat.1
  have hAB : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer (B : Set _) :=
    S310.stab_le_normalizer_bSub h _
  have hVA : V ≤ stab _ (baseA (puAmalgam h.le)) := by
    refine iSup_le fun g' => ?_
    rw [← zm_smul]
    have hγ : IsMVtx _ (geo _ (baseA (puAmalgam h.le)) α' 2) := isMVtx_geo_two _ hyp hb0 hc
    refine (zm_le_qv_of_dist_lt _ ((isMVtx_smul _ _ _).2 hγ) ?_).trans (qv_le_stab _ _)
    have hgα : (g' : (puAmalgam h.le).Universal) • baseA (puAmalgam h.le) = baseA _ :=
      (mem_stab _).1 g'.2
    have hαγ : (puAmalgam h.le).treeGraph.dist (baseA _) (geo _ (baseA (puAmalgam h.le)) α' 2) =
        2 := dist_geo _ (by omega)
    calc (puAmalgam h.le).treeGraph.dist ((g' : (puAmalgam h.le).Universal) •
          geo _ (baseA (puAmalgam h.le)) α' 2) (baseA _) =
        (puAmalgam h.le).treeGraph.dist ((g' : (puAmalgam h.le).Universal) •
          geo _ (baseA (puAmalgam h.le)) α' 2) ((g' : (puAmalgam h.le).Universal) • baseA _) := by
          rw [hgα]
      _ = (puAmalgam h.le).treeGraph.dist (geo _ (baseA (puAmalgam h.le)) α' 2) (baseA _) :=
          dist_smul _ _ _ _
      _ < critDist (puAmalgam h.le) := by rw [SimpleGraph.dist_comm, hαγ, hb]; norm_num
  have hLA := puTrans_le_stab h.le L (baseA (puAmalgam h.le))
  have hVB : V ⊓ B ≤ stab _ (baseA (puAmalgam h.le)) := inf_le_left.trans hVA
  have hVBn : stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer ((V ⊓ B : Subgroup _) : Set _) :=
    S310.le_normalizer_inf hAV hAB
  have hyW : ∀ w ∈ V, y * w * y⁻¹ * w⁻¹ ∈ V ⊓ B := by
    intro w hw
    have hwV : y * w * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hAV hyst) w).1 hw
    rw [Subgroup.mem_inf]
    refine ⟨V.mul_mem hwV (V.inv_mem hw), ?_⟩
    have hc1 : ⁅w, y⁆ ∈ ⁅V, ZM _ α'⁆ := Subgroup.commutator_mem_commutator hw hyZ
    have := inv_mem (hcore' hc1)
    rwa [commutatorElement_inv, commutatorElement_def] at this
  have hcore2 := S310.commutator_le_of_two_elt_baseA h hVA hVB (hLA.trans hAV) (hLA.trans hVBn)
    hyst hy2 hyQ (hVBn hyst) hyW
  exact S310.not_commutator_le_of_nat h ha hnat hcore2

end CFSG.Quasithin.MS93
