module

public import CFSG.Quasithin.MS93.S4A431F
public import CFSG.Quasithin.MS93.S4AL1

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Group

variable {G : Type} [Group G]

theorem commutatorElement_mul_left_of_comm {a c y : G} (h : a * ⁅c, y⁆ = ⁅c, y⁆ * a) :
    ⁅a * c, y⁆ = ⁅c, y⁆ * ⁅a, y⁆ := by
  have h' : a * ⁅c, y⁆ * a⁻¹ = ⁅c, y⁆ := by rw [h, mul_inv_cancel_right]
  calc ⁅a * c, y⁆ = (a * ⁅c, y⁆ * a⁻¹) * ⁅a, y⁆ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅c, y⁆ * ⁅a, y⁆ := by rw [h']

theorem commutatorElement_mem_of_normalizer {V : Subgroup G} {v y : G} (hv : v ∈ V)
    (hy : y ∈ Subgroup.normalizer (V : Set G)) : ⁅v, y⁆ ∈ V := by
  have h1 : y * v⁻¹ * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hy v⁻¹).mp (V.inv_mem hv)
  have e : ⁅v, y⁆ = v * (y * v⁻¹ * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact V.mul_mem hv h1

theorem commutator_mem_of_forall_not_mem {V A B D : Subgroup G} {y : G}
    (hV : ⁅V, V⁆ = ⊥) (hy : y ∈ Subgroup.normalizer (V : Set G)) (hAV : A ≤ V)
    (hAB : ¬ A ≤ B) (h : ∀ a ∈ A, a ∉ B → ⁅a, y⁆ ∈ D) : ∀ a ∈ A, ⁅a, y⁆ ∈ D := by
  intro a ha
  by_cases haB : a ∈ B
  · obtain ⟨c, hc, hcB⟩ := Set.not_subset.mp hAB
    have hac : a * c ∉ B := fun h' => hcB (by
      have := B.mul_mem (B.inv_mem haB) h'
      simpa using this)
    have hcomm : a * ⁅c, y⁆ = ⁅c, y⁆ * a := by
      have := Subgroup.commutator_mem_commutator (hAV ha)
        (commutatorElement_mem_of_normalizer (hAV hc) hy)
      rw [hV, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    have h1 := h _ (A.mul_mem ha hc) hac
    rw [commutatorElement_mul_left_of_comm hcomm] at h1
    have e : ⁅a, y⁆ = ⁅c, y⁆⁻¹ * (⁅c, y⁆ * ⁅a, y⁆) := by group
    rw [e]
    exact D.mul_mem (D.inv_mem (h c hc hcB)) h1
  · exact h a ha haB

theorem exists_not_mem_commutator_not_mem {V A B D : Subgroup G} {y : G} (hV : ⁅V, V⁆ = ⊥)
    (hy : y ∈ Subgroup.normalizer (V : Set G)) (hAV : A ≤ V) (hAB : ¬ A ≤ B) {a₀ : G}
    (ha₀ : a₀ ∈ A) (ha₀y : ⁅a₀, y⁆ ∉ D) : ∃ a ∈ A, a ∉ B ∧ ⁅a, y⁆ ∉ D := by
  by_contra hcon
  push Not at hcon
  exact ha₀y (commutator_mem_of_forall_not_mem hV hy hAV hAB hcon a₀ ha₀)

end Group

section Index

variable {G : Type} [Group G] {K V Z : Subgroup G} {F : Type} [Field F]
  {φ : ↥K →* ↥(StatedSL 3 F)}

theorem relIndex_eq_of_isSum (h : IsSumOfNaturalModulesVia K V Z φ false 1) :
    Z.relIndex V = Nat.card F ^ 3 := by
  have hker : (secHom h).ker = Z.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, secHom_apply, ofAdd_eq_one, secVec_eq_zero_iff,
      Subgroup.mem_subgroupOf]
  have hsurj : Function.Surjective (secHom h) := by
    intro y
    obtain ⟨v, hv⟩ := secVec_surjective h (Multiplicative.toAdd y)
    exact ⟨v, by rw [secHom_apply, hv]; rfl⟩
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj,
    Subgroup.card_top]
  change Nat.card (Fin 3 → F) = _
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]

end Index

section Nabla

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem mem_nablaSet_geo_two (hC : CentHyp (puAmalgam h.le)) (hb : 2 < critDist (puAmalgam h.le))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    α ∈ nablaSet h.le L (geo (puAmalgam h.le) α α' 2) := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hα := hc.1
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  set γ := geo (puAmalgam h.le) α α' 2 with hγdef
  have hγ : IsMVtx (puAmalgam h.le) γ := isMVtx_geo_two _ h20 hb0 hc
  have hαβ : (puAmalgam h.le).treeGraph.Adj α (geo (puAmalgam h.le) α α' 1) :=
    adj_geo_one_of_isCritical _ hb0 hc
  have hβγ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α α' 1) γ :=
    adj_geo _ (i := 1) (by omega)
  have hdαγ : (puAmalgam h.le).treeGraph.dist α γ = 2 := dist_geo _ (by omega)
  have hdγα : (puAmalgam h.le).treeGraph.dist γ α = 2 := by rw [tdist_comm]; exact hdαγ
  have hQβα : Qv (puAmalgam h.le) (geo (puAmalgam h.le) α α' 1) ≤ stab _ α :=
    qv_le_stab_of_adj _ hαβ.symm
  have hQβγ : Qv (puAmalgam h.le) (geo (puAmalgam h.le) α α' 1) ≤ stab _ γ :=
    qv_le_stab_of_adj _ hβγ
  have hZαQγ : ZM (puAmalgam h.le) α ≤ Qv _ γ := zm_le_qv_of_dist_lt _ hα (by omega)
  have hZγQα : ZM (puAmalgam h.le) γ ≤ Qv _ α :=
    zm_le_qv_of_dist_lt _ hγ (by rw [hdγα]; omega)
  refine ⟨hdγα, fun hle => ?_⟩
  rw [zv_of_isMVtx _ hα] at hle
  apply ms22_iv _ h20 hb0 hC hc
  rw [xm_eq_zm h hfull hγ, stab_eq_ltil_sup_qv_adj h hfull hγ hβγ.symm]
  have hN : stab (puAmalgam h.le) α ⊓ stab _ γ ≤ Subgroup.normalizer
      ((ZM (puAmalgam h.le) α ⊔ ZM (puAmalgam h.le) γ : Subgroup _) : Set _) :=
    (inf_le_inf (stab_le_normalizer_zm _ α) (stab_le_normalizer_zm _ γ)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  refine sup_le ?_ ((le_inf hQβα hQβγ).trans hN)
  rw [Subgroup.le_normalizer_iff_commutator_le_left]
  refine S4A.commutator_sup_le_of
    (((Subgroup.commutator_mono hle le_rfl).trans (commutator_bloc_le h hb hγ)).trans
      le_sup_right) ?_ ?_ ?_
  · exact (Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((ltil_le_stab h γ).trans (stab_le_normalizer_zm _ γ))).trans le_sup_right
  · exact (le_inf ((zm_le_qv_self _ hα hb0).trans (qv_le_stab _ α))
      (hZαQγ.trans (qv_le_stab _ γ))).trans hN
  · exact (le_inf (hZγQα.trans (qv_le_stab _ α)) ((zm_le_qv_self _ hγ hb0).trans
      (qv_le_stab _ γ))).trans hN

end Nabla

section Kind

variable {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M) (L : Subgroup G)

@[expose] def KindAt (F : Type) [Field F] (dual : Bool) (μ : Vtx (puAmalgam hTM)) : Prop :=
  ∃ ψ : ↥(stab (puAmalgam hTM) μ) →* ↥(StatedSL 3 F), Function.Surjective ψ ∧
    IsSumOfNaturalModulesVia (stab _ μ) (Uloc hTM L μ) ⊥ ψ false 1 ∧
    IsSumOfNaturalModulesVia (stab (puAmalgam hTM) μ)
      (⁅Vv (puAmalgam hTM) μ, stab (puAmalgam hTM) μ⁆ ⊔ ZM (puAmalgam hTM) μ)
      (⁅Vv (puAmalgam hTM) μ, Qv (puAmalgam hTM) μ⁆ ⊔ ZM (puAmalgam hTM) μ) ψ dual 1

end Kind

section KindSmul

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem kindAt_smul {F : Type} [Field F] {dual : Bool} {μ : Vtx (puAmalgam h.le)}
    (hk : KindAt h.le L F dual μ) (g : (puAmalgam h.le).Universal) :
    KindAt h.le L F dual (g • μ) := by
  obtain ⟨ψ, hψs, hU, hP⟩ := hk
  set e : (puAmalgam h.le).Universal →* (puAmalgam h.le).Universal :=
    (MulAut.conj g).toMonoidHom with he
  have hei : Function.Injective e := (MulAut.conj g).injective
  have hstab : stab (puAmalgam h.le) (g • μ) = (stab (puAmalgam h.le) μ).map e := stab_smul _ g μ
  have hUeq : Uloc h.le L (g • μ) = (Uloc h.le L μ).map e := uloc_smul h g μ
  have hPeq : ⁅Vv (puAmalgam h.le) (g • μ), stab (puAmalgam h.le) (g • μ)⁆ ⊔
      ZM (puAmalgam h.le) (g • μ) =
      (⁅Vv (puAmalgam h.le) μ, stab (puAmalgam h.le) μ⁆ ⊔ ZM (puAmalgam h.le) μ).map e := by
    rw [Subgroup.map_sup, Subgroup.map_commutator, ← hstab, he, ← zm_smul,
      show Vv (puAmalgam h.le) (g • μ) = Vi _ (g • μ) 2 from rfl, vi_smul]
  have hKeq : ⁅Vv (puAmalgam h.le) (g • μ), Qv (puAmalgam h.le) (g • μ)⁆ ⊔
      ZM (puAmalgam h.le) (g • μ) =
      (⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ⊔ ZM (puAmalgam h.le) μ).map e := by
    rw [Subgroup.map_sup, Subgroup.map_commutator, he, ← qv_smul, ← zm_smul,
      show Vv (puAmalgam h.le) (g • μ) = Vi _ (g • μ) 2 from rfl, vi_smul]
  have hU' := isSumOfNaturalModulesVia_map hU e hei
  have hP' := isSumOfNaturalModulesVia_map hP e hei
  rw [Subgroup.map_bot] at hU'
  set eK : ↥(stab (puAmalgam h.le) (g • μ)) ≃* ↥((stab (puAmalgam h.le) μ).map e) :=
    MulEquiv.subgroupCongr hstab
  have hnU : stab (puAmalgam h.le) (g • μ) ≤
      Subgroup.normalizer (Uloc h.le L (g • μ) : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) _
  have hnP : stab (puAmalgam h.le) (g • μ) ≤ Subgroup.normalizer
      ((⁅Vv (puAmalgam h.le) (g • μ), stab (puAmalgam h.le) (g • μ)⁆ ⊔
        ZM (puAmalgam h.le) (g • μ) : Subgroup _) : Set (puAmalgam h.le).Universal) :=
    (le_inf (le_normalizer_commutator (stab_le_normalizer_vv h _) Subgroup.le_normalizer)
      (stab_le_normalizer_zm _ _)).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hKP : ⁅Vv (puAmalgam h.le) (g • μ), Qv (puAmalgam h.le) (g • μ)⁆ ⊔
      ZM (puAmalgam h.le) (g • μ) ≤ ⁅Vv (puAmalgam h.le) (g • μ),
        stab (puAmalgam h.le) (g • μ)⁆ ⊔ ZM (puAmalgam h.le) (g • μ) :=
    sup_le_sup_right (Subgroup.commutator_mono le_rfl (qv_le_stab _ _)) _
  refine ⟨(ψ.comp ((stab (puAmalgam h.le) μ).equivMapOfInjective e hei).symm.toMonoidHom).comp
    eK.toMonoidHom, ?_, ?_, ?_⟩
  · rw [MonoidHom.coe_comp, MonoidHom.coe_comp]
    exact (hψs.comp (MulEquiv.surjective _)).comp (MulEquiv.surjective eK)
  · exact isSumOfNaturalModulesVia_of_equiv hU' eK (MulEquiv.subgroupCongr hUeq) hnU bot_le
      (fun v => by simp) (fun a u v huv => huv)
  · refine isSumOfNaturalModulesVia_of_equiv hP' eK (MulEquiv.subgroupCongr hPeq) hnP hKP
      (fun v => ?_) (fun a u v huv => huv)
    rw [← hKeq]
    rfl

theorem commutator_vv_qv_le_dloc_smul_iff (g : (puAmalgam h.le).Universal)
    (μ : Vtx (puAmalgam h.le)) :
    ⁅Vv (puAmalgam h.le) (g • μ), Qv (puAmalgam h.le) (g • μ)⁆ ≤ Dloc h.le L (g • μ) ↔
      ⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ≤ Dloc h.le L μ := by
  rw [show Vv (puAmalgam h.le) (g • μ) = Vi _ (g • μ) 2 from rfl, vi_smul, qv_smul,
    dloc_smul h, ← Subgroup.map_commutator,
    Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective]

end KindSmul

section Kind2

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem exists_kindAt (hb : 2 < critDist (puAmalgam h.le)) {μ : Vtx (puAmalgam h.le)}
    (hμ : IsMVtx _ μ) {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
    (hφ : IsSL3FullVia M T L φ)
    (hc : IsC1 h.le L (Fintype.card F) μ (Vv (puAmalgam h.le) μ) (ZM (puAmalgam h.le) μ)) :
    ∃ dual : Bool, KindAt h.le L F dual μ := by
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hμ
  obtain ⟨d, hd⟩ := exists_dual_of_isC1 h hfull hb hμ hφ hc hψs hψ
  exact ⟨d, ψ, hψs, hψ, hd⟩

theorem not_commutator_zm_qv_le_dloc (hb : 2 < critDist (puAmalgam h.le))
    {μ δ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hCH : ¬ ⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ≤ Dloc h.le L μ)
    (hiv : Vcirc h.le L μ ≤ conjCl (stab (puAmalgam h.le) μ) (ZM (puAmalgam h.le) δ))
    (hδ : ZM (puAmalgam h.le) δ ≤ stab (puAmalgam h.le) μ) :
    ¬ ⁅ZM (puAmalgam h.le) δ, Qv (puAmalgam h.le) μ⁆ ≤ Dloc h.le L μ := by
  intro hle
  apply hCH
  have hDn : stab (puAmalgam h.le) μ ≤
      Subgroup.normalizer (Dloc h.le L μ : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) μ
  refine commutator_vv_le_dloc h hfull hb hμ (stab_le_normalizer_qv _ μ) le_rfl ?_
  refine (Subgroup.commutator_mono hiv le_rfl).trans ?_
  exact commutator_conjCl_le hDn (stab_le_normalizer_qv _ μ) (hδ.trans hDn) hle

theorem relIndex_bloc_vv (hb : 2 < critDist (puAmalgam h.le)) {μ : Vtx (puAmalgam h.le)}
    (hμ : IsMVtx _ μ) {q : ℕ}
    (hc : IsC1 h.le L q μ (Vv (puAmalgam h.le) μ) (ZM (puAmalgam h.le) μ)) :
    (Bloc h.le L μ).relIndex (Vv (puAmalgam h.le) μ) = q ^ 3 := by
  obtain ⟨F', _, _, ψ', hcard', -, hnat, hPiB, hPB, -, -⟩ := isC1_normal h hfull hb hμ hc
  have hVs : Vv (puAmalgam h.le) μ ≤ stab _ μ := (vv_le_qv h hb hμ).trans (qv_le_stab _ μ)
  have hBn : stab (puAmalgam h.le) μ ≤
      Subgroup.normalizer (Bloc h.le L μ : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_of_smul (F := fun δ => Bloc h.le L δ) _ (fun g δ => bloc_smul h g δ) μ
  have hPV : ⁅Vv (puAmalgam h.le) μ, stab (puAmalgam h.le) μ⁆ ⊔ ZM (puAmalgam h.le) μ ≤
      Vv _ μ := sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (stab_le_normalizer_vv h μ)) (zm_le_vv h hμ)
  have h1 : (Bloc h.le L μ).relIndex (⁅Vv (puAmalgam h.le) μ, stab (puAmalgam h.le) μ⁆ ⊔
      ZM (puAmalgam h.le) μ) = ((⁅Vv (puAmalgam h.le) μ, stab (puAmalgam h.le) μ⁆ ⊔
        ZM (puAmalgam h.le) μ) ⊓ Bloc h.le L μ).relIndex (⁅Vv (puAmalgam h.le) μ,
          stab (puAmalgam h.le) μ⁆ ⊔ ZM (puAmalgam h.le) μ) := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
  rw [← hPB, relIndex_sup_of_le_normalizer ((hPV.trans hVs).trans hBn), h1, hPiB,
    relIndex_eq_of_isSum hnat, Nat.card_eq_fintype_card, hcard']

end Kind2

section Facts

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hH : Hyp40 h φ)
include h hH

theorem isC1_of_star (h431A : S431A) {α₀ α₀' μ : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α₀ α₀') (hμ : IsMVtx _ μ) :
    IsC1 h.le L (Fintype.card F) μ (Vv (puAmalgam h.le) μ) (ZM (puAmalgam h.le) μ) := by
  obtain ⟨μ', hsμ⟩ := exists_star_at _ hs hμ
  exact (h431A G M T L h F inferInstance inferInstance φ hH μ μ' hsμ).2.2.2.1

theorem vcirc_le_conjCl_of_star (h431A : S431A) {α₀ α₀' μ δ : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α₀ α₀') (hμ : IsMVtx _ μ) (hδ : δ ∈ nablaSet h.le L μ) :
    Vcirc h.le L μ ≤ conjCl (stab (puAmalgam h.le) μ) (ZM (puAmalgam h.le) δ) := by
  obtain ⟨μ', hsμ⟩ := exists_star_at _ hs hμ
  exact (h431A G M T L h F inferInstance inferInstance φ hH μ μ' hsμ).2.2.2.2.1 δ hδ

theorem commutator_zm_qv_eq_of_star (h431B : S431B) {α₀ α₀' μ δ : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α₀ α₀') (hμ : IsMVtx _ μ) (hδ : δ ∈ nablaSet h.le L μ) :
    ⁅ZM (puAmalgam h.le) δ, Qv (puAmalgam h.le) μ⁆ =
      Usup (puAmalgam h.le) δ (geo (puAmalgam h.le) μ δ 1) := by
  obtain ⟨μ', hsμ⟩ := exists_star_at _ hs hμ
  exact (h431B G M T L h F inferInstance inferInstance φ hH μ μ' hsμ).2.2 δ hδ

omit hH in
theorem zm_le_vv_of_mem_nablaSet {μ δ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hδ : δ ∈ nablaSet h.le L μ) :
    IsMVtx (puAmalgam h.le) δ ∧ ZM (puAmalgam h.le) δ ≤ Vv (puAmalgam h.le) μ := by
  have hδM : IsMVtx (puAmalgam h.le) δ := by
    have := (even_dist_iff (puAmalgam h.le) μ δ).mp (by rw [hδ.1]; decide)
    exact this.mp hμ
  refine ⟨hδM, ?_⟩
  rw [← zv_of_isMVtx _ hδM]
  exact zv_le_vv h hδ.1.le

theorem not_commutator_zm_qv_le_dloc_of_star (hfull : IsSL3Full M T L) (h431A : S431A)
    {α₀ α₀' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α₀ α₀')
    (hCH : ∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ →
      ¬ ⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ≤ Dloc h.le L μ)
    {μ δ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ) (hδ : δ ∈ nablaSet h.le L μ) :
    ¬ ⁅ZM (puAmalgam h.le) δ, Qv (puAmalgam h.le) μ⁆ ≤ Dloc h.le L μ :=
  not_commutator_zm_qv_le_dloc h hfull hH.2.1 hμ (hCH μ hμ)
    (vcirc_le_conjCl_of_star h hH h431A hs hμ hδ)
    ((zm_le_vv_of_mem_nablaSet h hμ hδ).2.trans ((vv_le_qv h hH.2.1 hμ).trans (qv_le_stab _ μ)))

end Facts

end CFSG.Quasithin.MS93.S4A
