module

public import CFSG.Quasithin.MS93.S46I464Loc

public section

namespace CFSG.Quasithin.MS93.S46.I464

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement

section Perp

variable {𝔾 : Type*} [Group 𝔾]

@[expose] def perpIn (W K : Subgroup 𝔾) : Subgroup 𝔾 :=
  Subgroup.closure {v | v ∈ W ∧ ∀ w ∈ W, ⁅v, w⁆ ∈ K}

theorem mem_perpIn_iff {W K : Subgroup 𝔾} (hK : W ≤ Subgroup.normalizer (K : Set 𝔾)) {v : 𝔾} :
    v ∈ perpIn W K ↔ v ∈ W ∧ ∀ w ∈ W, ⁅v, w⁆ ∈ K := by
  constructor
  · intro hv
    induction hv using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨Subgroup.one_mem _, fun w _ => by simp [commutatorElement_def]⟩
    | mul x y _ _ hx hy =>
      refine ⟨Subgroup.mul_mem _ hx.1 hy.1, fun w hw => ?_⟩
      have e : ⁅x * y, w⁆ = x * ⁅y, w⁆ * x⁻¹ * ⁅x, w⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hK hx.1) _).mp (hy.2 w hw)) (hx.2 w hw)
    | inv x _ hx =>
      refine ⟨Subgroup.inv_mem _ hx.1, fun w hw => ?_⟩
      have e : ⁅x⁻¹, w⁆ = x⁻¹ * (⁅x, w⁆)⁻¹ * x⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hK (Subgroup.inv_mem _ hx.1)) _).mp
        (K.inv_mem (hx.2 w hw))
  · exact fun hv => Subgroup.subset_closure hv

theorem perpIn_le (W K : Subgroup 𝔾) : perpIn W K ≤ W :=
  (Subgroup.closure_le _).mpr fun _ hv => hv.1

theorem le_normalizer_perpIn {H W K : Subgroup 𝔾} (hW : H ≤ Subgroup.normalizer (W : Set 𝔾))
    (hK : H ≤ Subgroup.normalizer (K : Set 𝔾)) (hWK : W ≤ Subgroup.normalizer (K : Set 𝔾)) :
    H ≤ Subgroup.normalizer (perpIn W K : Set 𝔾) := by
  have key : ∀ y ∈ H, ∀ v ∈ perpIn W K, y * v * y⁻¹ ∈ perpIn W K := by
    intro y hy v hv
    rw [mem_perpIn_iff hWK] at hv ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hW hy) v).mp hv.1, fun w hw => ?_⟩
    have hw' : y⁻¹ * w * y⁻¹⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hW (H.inv_mem hy)) w).mp hw
    have e : ⁅y * v * y⁻¹, w⁆ = y * ⁅v, y⁻¹ * w * y⁻¹⁻¹⁆ * y⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hK hy) _).mp (hv.2 _ hw')
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · exact key g hg v
  · intro hv
    have := key g⁻¹ (H.inv_mem hg) _ hv
    simpa [mul_assoc] using this

theorem commutator_self_le (W : Subgroup 𝔾) : ⁅W, W⁆ ≤ W :=
  Subgroup.commutator_le.mpr fun _ hx _ hy =>
    W.mul_mem (W.mul_mem (W.mul_mem hx hy) (W.inv_mem hx)) (W.inv_mem hy)

end Perp

section Crit

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hb4 : critDist (puAmalgam h.le) = 4)
include h hb4

theorem zm_le_qv_of_adj_adj {a b d : Vtx (puAmalgam h.le)} (ha : IsMVtx _ a)
    (hab : (puAmalgam h.le).treeGraph.Adj a b) (hbd : (puAmalgam h.le).treeGraph.Adj b d) :
    ZM (puAmalgam h.le) d ≤ Qv _ a :=
  zm_le_qv_of_dist_le_three hb4 (isMVtx_of_adj_adj h ha hab hbd)
    (by rw [tdist_comm]; have := dist_le_two_of_adj_adj h hab hbd; omega)

omit hb4 in
theorem zm_le_conjCl {a b d : Vtx (puAmalgam h.le)}
    (hab : (puAmalgam h.le).treeGraph.Adj a b) (hbd : (puAmalgam h.le).treeGraph.Adj b d) :
    ZM (puAmalgam h.le) a ≤ conjCl (stab (puAmalgam h.le) a) (ZM _ d) := by
  refine iSup₂_le fun ρ hρ => ?_
  obtain ⟨g, hg, rfl⟩ := exists_mem_stab_smul _ hab hρ
  rw [zh_smul]
  exact (Subgroup.map_mono (zh_le_zm _ hbd.symm)).trans
    (le_iSup₂_of_le (f := fun g (_ : g ∈ stab (puAmalgam h.le) a) =>
      (ZM (puAmalgam h.le) d).map (MulAut.conj g).toMonoidHom) g hg le_rfl)

theorem commutator_conjCl_le_of_ltil (hfull : IsSL3Full M T L) {a b d : Vtx (puAmalgam h.le)}
    (ha : IsMVtx _ a) (hab : (puAmalgam h.le).treeGraph.Adj a b)
    (hbd : (puAmalgam h.le).treeGraph.Adj b d) {K : Subgroup (puAmalgam h.le).Universal}
    (hK : stab (puAmalgam h.le) a ≤ Subgroup.normalizer (K : Set _))
    (hVL : ⁅conjCl (stab (puAmalgam h.le) a) (ZM _ d), Ltil h.le L a⁆ ≤
      perpIn (conjCl (stab (puAmalgam h.le) a) (ZM _ d)) K) :
    ⁅conjCl (stab (puAmalgam h.le) a) (ZM _ d), conjCl (stab (puAmalgam h.le) a) (ZM _ d)⁆ ≤
      K := by
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  set V := conjCl (stab (puAmalgam h.le) a) (ZM _ d) with hVdef
  have hZd : ZM (puAmalgam h.le) d ≤ stab _ a :=
    (zm_le_qv_of_adj_adj h hb4 ha hab hbd).trans (qv_le_stab _ a)
  have hVs : V ≤ stab _ a := conjCl_le_of_le hZd
  have hKV : V ≤ Subgroup.normalizer (K : Set _) := hVs.trans hK
  set Ut := perpIn V K with hUtdef
  have hUt : ∀ v, v ∈ Ut ↔ v ∈ V ∧ ∀ w ∈ V, ⁅v, w⁆ ∈ K := fun v => mem_perpIn_iff hKV
  have hUtV : Ut ≤ V := perpIn_le V K
  have hUtn : stab (puAmalgam h.le) a ≤ Subgroup.normalizer (Ut : Set _) :=
    le_normalizer_perpIn (le_normalizer_conjCl _ _) hK hKV
  have hZdV : ZM (puAmalgam h.le) d ≤ V := le_conjCl _ _
  have hWn : stab (puAmalgam h.le) a ≤
      Subgroup.normalizer ((ZM (puAmalgam h.le) d ⊔ Ut : Subgroup _) : Set _) := by
    rw [stab_eq_ltil_sup_qv_adj h hfull ha hab]
    refine sup_le ?_ ?_
    · refine le_normalizer_sup_of_commutator_le ((ltil_le_stab h a).trans hUtn) ?_
      exact ((Subgroup.commutator_mono hZdV le_rfl).trans hVL).trans le_sup_right
    · exact le_normalizer_sup ((qv_le_stab_of_adj _ hbd).trans (stab_le_normalizer_zm _ d))
        ((qv_le_stab_of_isMVtx _ h.hyp20 ha hab).trans hUtn)
  have hVW : V ≤ ZM (puAmalgam h.le) d ⊔ Ut := conjCl_le_of_le_normalizer le_sup_left hWn
  have hUtK : ∀ H : Subgroup (puAmalgam h.le).Universal, H ≤ V → ⁅Ut, H⁆ ≤ K := fun H hH =>
    Subgroup.commutator_le.mpr fun u hu w hw => ((hUt u).mp hu).2 w (hH hw)
  have hZdK : ⁅ZM (puAmalgam h.le) d, V⁆ ≤ K := by
    refine (Subgroup.commutator_mono le_rfl hVW).trans ?_
    rw [Subgroup.commutator_comm]
    refine S4A.commutator_sup_le_of ?_ (hUtK _ hZdV) (hZdV.trans hKV) (hUtV.trans hKV)
    have := (isElemAbelian_zm _ h.hyp20 hb0 (isMVtx_of_adj_adj h ha hab hbd)).1
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      (Subgroup.le_centralizer (ZM (puAmalgam h.le) d))]
    exact bot_le
  exact (Subgroup.commutator_mono hVW le_rfl).trans
    (S4A.commutator_sup_le_of hZdK (hUtK _ le_rfl) (hZdV.trans hKV) (hUtV.trans hKV))

end Crit

section SD

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (hb4 : critDist (puAmalgam h.le) = 4)
include h hφ hb4

theorem commutator_conjCl_eq_bot_of_offender (h14 : MS14AS) (hSQ : SQTKQuot)
    {a b d : Vtx (puAmalgam h.le)} (ha : IsMVtx _ a) (hab : (puAmalgam h.le).treeGraph.Adj a b)
    (hbd : (puAmalgam h.le).treeGraph.Adj b d)
    (hK : ⁅conjCl (stab (puAmalgam h.le) a) (ZM _ d), conjCl (stab (puAmalgam h.le) a) (ZM _ d)⁆
      ≤ Subgroup.centralizer (stab (puAmalgam h.le) a : Set _))
    (hK2 : ∀ k ∈ ⁅conjCl (stab (puAmalgam h.le) a) (ZM _ d),
      conjCl (stab (puAmalgam h.le) a) (ZM _ d)⁆, k ^ 2 = 1)
    {A Q' : Subgroup (puAmalgam h.le).Universal}
    (hAρ : ∃ ρ, (puAmalgam h.le).treeGraph.Adj a ρ ∧ A ≤ Qv _ ρ) (hAQ : ¬ A ≤ Qv _ a)
    (hA2 : ∀ x ∈ A, x ^ 2 ∈ Qv (puAmalgam h.le) a)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, ⁅x, y⁆ ∈ Qv (puAmalgam h.le) a)
    (hC₀A : ⁅conjCl (stab (puAmalgam h.le) a) (ZM _ d) ⊓ Q', A⁆ ≤ ZM _ a)
    (hidx : Q'.relIndex (conjCl (stab (puAmalgam h.le) a) (ZM _ d)) ≤
      (Qv (puAmalgam h.le) a).relIndex A) :
    ⁅conjCl (stab (puAmalgam h.le) a) (ZM _ d), conjCl (stab (puAmalgam h.le) a) (ZM _ d)⁆ =
      ⊥ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  obtain ⟨n, hF⟩ := hφ.1
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ ha
  have hsq := sqtkGroup_SL3 h hφ hSQ
  have hfinS : Finite ↥(stab (puAmalgam h.le) a) := finite_stab h ha
  set V := conjCl (stab (puAmalgam h.le) a) (ZM _ d) with hVdef
  have hZdQ := zm_le_qv_of_adj_adj h hb4 ha hab hbd
  have hVQ : V ≤ Qv _ a := conjCl_le_of_le_normalizer hZdQ (stab_le_normalizer_qv _ a)
  have hVs : V ≤ stab _ a := hVQ.trans (qv_le_stab _ a)
  have hfinV : Finite ↥V := Finite.of_injective _ (Subgroup.inclusion_injective hVs)
  have hVn : stab (puAmalgam h.le) a ≤ Subgroup.normalizer (V : Set _) :=
    le_normalizer_conjCl _ _
  by_contra hne
  set K' := ⁅V, V⁆ with hK'def
  have hK'V : K' ≤ V := commutator_self_le V
  have hK'cV : K' ≤ Subgroup.centralizer (V : Set _) := hK.trans (Subgroup.centralizer_le hVs)
  have hK'n : stab (puAmalgam h.le) a ≤ Subgroup.normalizer (K' : Set _) := by
    refine le_normalizer_of_map_conj_le fun g hg => ?_
    rw [hK'def, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hVn hg)]
  have hfinKQ : Finite ↥(K' ⊔ Qv (puAmalgam h.le) a) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (sup_le (hK'V.trans hVs)
      (qv_le_stab _ a)))
  have hLK : ⁅K', Ltil h.le L a⁆ ≤ ⊥ := by
    rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hK.trans (Subgroup.centralizer_le (ltil_le_stab h a))
  obtain ⟨K'', -, hK''K', hK''n, hidx2, hK'X⟩ :=
    exists_inv_index_two (X := stab (puAmalgam h.le) a) (L := Ltil h.le L a)
      (Q := Qv (puAmalgam h.le) a) (K₀ := ⊥) (K' := K')
      (fun k hk k' hk' => (Subgroup.mem_centralizer_iff.mp (hK'cV hk) k' (hK'V hk')).symm)
      hK2 (isPGroup_qv_of_isMVtx h ha) bot_le (fun hle => hne (le_bot_iff.mp hle))
      (stab_eq_ltil_sup_qv h hfull ha)
      (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge)
      hK'n (stab_le_normalizer_qv _ a) hLK
  have hK''V : V ≤ Subgroup.normalizer (K'' : Set _) := hVs.trans hK''n
  set Ut := perpIn V K'' with hUtdef
  have hUt : ∀ v, v ∈ Ut ↔ v ∈ V ∧ ∀ w ∈ V, ⁅v, w⁆ ∈ K'' := fun v => mem_perpIn_iff hK''V
  have hUtV : Ut ≤ V := perpIn_le V K''
  have hUtn : stab (puAmalgam h.le) a ≤ Subgroup.normalizer (Ut : Set _) :=
    le_normalizer_perpIn hVn hK''n hK''V
  have hZaV : ZM (puAmalgam h.le) a ≤ V := zm_le_conjCl h hab hbd
  have hZaUt : ZM (puAmalgam h.le) a ≤ Ut := by
    intro v hv
    rw [hUt]
    refine ⟨hZaV hv, fun w hw => ?_⟩
    have : ⁅v, w⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 ha hv) w (hVQ hw)).symm
    rw [this]
    exact Subgroup.one_mem _
  obtain ⟨ρ, haρ, hAρ'⟩ := hAρ
  have hAs : A ≤ stab (puAmalgam h.le) a := hAρ'.trans (qv_le_stab_of_adj _ haρ.symm)
  have hker := toSL3_eq_one_iff_mem_qv h hφ ha hψ
  have hZan : stab (puAmalgam h.le) a ≤
      Subgroup.normalizer ((ZM (puAmalgam h.le) a ⊔ Ut : Subgroup _) : Set _) :=
    le_normalizer_sup (stab_le_normalizer_zm _ a) hUtn
  have hVL := sd_group h14 hSQ hsq hF (X := stab (puAmalgam h.le) a) (V := V) (K' := K')
    (K'' := K'') (Ut := Ut) (Bh := ZM (puAmalgam h.le) a) (A := A) (Lg := Ltil h.le L a)
    (C₀ := (V ⊓ Q') ⊔ Ut)
    (toSL3 ψ) (toSL3_surjective hψs) (pow_two_pow_eq_one_of_toSL3_eq_one h hφ ha hψ)
    hVn hK'V hK'cV le_rfl hK''K' hK''n hidx2 hK'X hUt hZaV (stab_le_normalizer_zm _ a)
    (ltil_le_stab h a) (ltil_perfect h ha)
    ((Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((ltil_le_stab h a).trans (stab_le_normalizer_zm _ a))).trans hZaUt)
    hAs
    (fun x hx => by
      rw [← map_pow]
      exact (hker _).mpr (by simpa using hA2 x hx))
    (fun x y hx hy => by
      have h1 : toSL3 ψ ⁅x, y⁆ = 1 := (hker _).mpr (by
        have := hAc x hx y hy
        simpa [commutatorElement_def] using this)
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1)
    (by
      obtain ⟨x, hxA, hxQ⟩ := Set.not_subset.mp hAQ
      exact ⟨⟨x, hAs hxA⟩, hxA, fun h1 => hxQ ((hker _).mp h1)⟩)
    (sup_le (hZaUt.trans le_sup_right) le_sup_right) (sup_le (inf_le_left.trans le_rfl) hUtV)
    (S4A.commutator_sup_le_of (hC₀A.trans le_sup_left)
      ((Subgroup.le_normalizer_iff_commutator_le_left.mp (hAs.trans hUtn)).trans le_sup_right)
      ((inf_le_left.trans hVs).trans hZan) ((hUtV.trans hVs).trans hZan))
    (by
      have h1 : ((V ⊓ Q') ⊔ Ut).relIndex V ≤ (V ⊓ Q').relIndex V :=
        Subgroup.relIndex_le_of_le_left le_sup_left (by
          rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
      rw [Subgroup.inf_relIndex_left] at h1
      exact h1.trans (hidx.trans (card_natImage_eq_relIndex h hφ ha hψ hAs).ge))
  have hcrit := commutator_conjCl_le_of_ltil h hb4 hfull ha hab hbd hK''n hVL
  have : K'' = K' := le_antisymm hK''K' hcrit
  rw [this, Subgroup.relIndex_self] at hidx2
  omega

omit hφ hb4 in
theorem sq_mem_commutator_conjCl {a d : Vtx (puAmalgam h.le)} (hd : IsMVtx _ d)
    {v : (puAmalgam h.le).Universal} (hv : v ∈ conjCl (stab (puAmalgam h.le) a) (ZM _ d)) :
    v ^ 2 ∈ ⁅conjCl (stab (puAmalgam h.le) a) (ZM _ d),
      conjCl (stab (puAmalgam h.le) a) (ZM _ d)⁆ := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hVi : conjCl (stab (puAmalgam h.le) a) (ZM _ d) =
      ⨆ g : ↥(stab (puAmalgam h.le) a), (ZM (puAmalgam h.le) d).map
        (MulAut.conj (g : (puAmalgam h.le).Universal)).toMonoidHom := by
    rw [conjCl, iSup_subtype']
  rw [hVi] at hv ⊢
  refine sq_mem_commutator_of_iSup (fun g z hz => ?_) hv
  obtain ⟨y, hy, rfl⟩ := hz
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [conj_pow, (isElemAbelian_zm _ h20 hb0 hd).2 y hy, mul_one, mul_inv_cancel]

theorem commutator_conjCl_eq_bot_of_bad (h14 : MS14AS) (hSQ : SQTKQuot)
    (hC : CentHyp (puAmalgam h.le))
    (h461 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x → centerOf (Vv _ x) ≤ Bloc h.le L x)
    (h463 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
      ⁅Vv (puAmalgam h.le) x, Qv _ x⁆ ≤ centerOf (Vv _ x))
    {a b d : Vtx (puAmalgam h.le)} (ha : IsMVtx _ a) (hab : (puAmalgam h.le).treeGraph.Adj a b)
    (hbd : (puAmalgam h.le).treeGraph.Adj b d)
    (hbad : ¬ Usup (puAmalgam h.le) d b ≤ Bloc h.le L a) :
    ⁅conjCl (stab (puAmalgam h.le) a) (ZM _ d), conjCl (stab (puAmalgam h.le) a) (ZM _ d)⁆ =
      ⊥ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  obtain ⟨l, k, hcl, hgeol, hR, hk, hc, hgeo, -, hRe⟩ :=
    exists_special_raw h hφ hC hb4 h461 h463 ha hab hbd hbad
  have hRa := hRe.le.trans (critR_le_zm_left h hc)
  have hRa' : ⁅ZM (puAmalgam h.le) (k • d), Qv _ (geo (puAmalgam h.le) a (k • d) 2)⁆ ≤
      ZM _ a := by rw [hgeo]; exact hRa
  obtain ⟨hcen, hXm⟩ :=
    le_centralizer_stab_of_critical h hφ hC hb4 h461 h463 ha hab hbd hbad hc hRa'
  rw [hgeo] at hXm
  have hn := stab_le_normalizer_commutator h hφ hC hb4 h461 h463 ha hab hbd hbad hc hRa'
  have hVm := conjCl_not_le_qv h hC hb4 ha hab hbd hbad hfull hc hRa'
  rw [hgeo] at hVm
  have hd := isMVtx_of_adj_adj h ha hab hbd
  have hlM : IsMVtx _ l := hcl.1
  have hm : IsMVtx _ (k • a) := (isMVtx_smul _ k a).mpr ha
  have hXl : ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ ≤ ZM _ l := by
    rw [← hR, critR]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((zm_le_stab_of_isCritical _ h20 hb0 hcl).trans (stab_le_normalizer_zm _ l))
  have hZdQ := zm_le_qv_of_adj_adj h hb4 ha hab hbd
  have hVQ : conjCl (stab (puAmalgam h.le) a) (ZM _ d) ≤ Qv _ a :=
    conjCl_le_of_le_normalizer hZdQ (stab_le_normalizer_qv _ a)
  have hVs : conjCl (stab (puAmalgam h.le) a) (ZM _ d) ≤ stab _ a := hVQ.trans (qv_le_stab _ a)
  have hVQX : ⁅conjCl (stab (puAmalgam h.le) a) (ZM _ d), Qv _ a⁆ ≤
      ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ := by
    rw [conjCl, iSup_subtype']
    refine commutator_iSup_le_of (fun g => ?_) ?_
    · calc ⁅(ZM (puAmalgam h.le) d).map (MulAut.conj (g : (puAmalgam h.le).Universal)).toMonoidHom,
            Qv (puAmalgam h.le) a⁆ =
          ⁅(ZM (puAmalgam h.le) d).map (MulAut.conj (g : (puAmalgam h.le).Universal)).toMonoidHom,
            (Qv (puAmalgam h.le) a).map
              (MulAut.conj (g : (puAmalgam h.le).Universal)).toMonoidHom⁆ := by
            rw [map_conj_eq_of_mem_normalizer (stab_le_normalizer_qv _ a g.2)]
        _ = (⁅ZM (puAmalgam h.le) d, Qv _ a⁆).map
              (MulAut.conj (g : (puAmalgam h.le).Universal)).toMonoidHom :=
            (Subgroup.map_commutator _ _ _).symm
        _ ≤ ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ := (map_conj_eq_of_mem_normalizer (hn g.2)).le
    · rw [← iSup_subtype' (f := fun g (_ : g ∈ stab (puAmalgam h.le) a) =>
        (ZM (puAmalgam h.le) d).map (MulAut.conj g).toMonoidHom), ← conjCl]
      exact hVs.trans hn
  have hVV : ⁅conjCl (stab (puAmalgam h.le) a) (ZM _ d),
      conjCl (stab (puAmalgam h.le) a) (ZM _ d)⁆ ≤ ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ :=
    (Subgroup.commutator_mono le_rfl hVQ).trans hVQX
  have hXZd : ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ ≤ ZM _ d :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (((qv_le_qv _ h20 ha hab).trans (qv_le_stab_of_adj _ hbd)).trans
        (stab_le_normalizer_zm _ d))
  have hK2 : ∀ x ∈ ⁅conjCl (stab (puAmalgam h.le) a) (ZM _ d),
      conjCl (stab (puAmalgam h.le) a) (ZM _ d)⁆, x ^ 2 = 1 := fun x hx =>
    (isElemAbelian_zm _ h20 hb0 hd).2 x (hXZd (hVV hx))
  have hVl : ¬ conjCl (stab (puAmalgam h.le) a) (ZM _ d) ≤ Qv _ l := fun hle =>
    (ms22_iii _ h20 hb0 hC hcl).2.2 ((le_conjCl _ _).trans hle)
  have hkl : k⁻¹ • a = l := by rw [← hk, inv_smul_smul]
  have hQa : Qv (puAmalgam h.le) a = (Qv _ l).map (MulAut.conj k).toMonoidHom := by
    rw [← hk, qv_smul]
  have hQm : Qv (puAmalgam h.le) (k • a) = (Qv _ a).map (MulAut.conj k).toMonoidHom :=
    qv_smul _ k a
  have hZa : ZM (puAmalgam h.le) a = (ZM _ l).map (MulAut.conj k).toMonoidHom := by
    rw [← hk, zm_smul]
  have hQa' : Qv (puAmalgam h.le) a = (Qv _ (k • a)).map (MulAut.conj k⁻¹).toMonoidHom := by
    rw [← qv_smul, inv_smul_smul]
  have hZa' : ZM (puAmalgam h.le) a = (ZM _ (k • a)).map (MulAut.conj k⁻¹).toMonoidHom := by
    rw [← zm_smul, inv_smul_smul]
  have hZaQ := zm_le_qv_self _ ha hb0
  have hVQX' : ⁅Qv (puAmalgam h.le) a, conjCl (stab (puAmalgam h.le) a) (ZM _ d)⁆ ≤
      ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ := (Subgroup.commutator_comm _ _).le.trans hVQX
  by_cases hcmp : (Qv (puAmalgam h.le) (k • a)).relIndex
      (conjCl (stab (puAmalgam h.le) a) (ZM _ d)) ≤
      (Qv (puAmalgam h.le) l).relIndex (conjCl (stab (puAmalgam h.le) a) (ZM _ d))
  ·
    have hβ := adj_geo_one_of_isCritical _ hb0 hc
    have hmβ : (puAmalgam h.le).treeGraph.Adj (k • a) (geo (puAmalgam h.le) a (k • d) 1) := by
      have := (adj_geo_crit hb4 hc (i := 1) (by omega)).symm
      rwa [hgeo] at this
    refine commutator_conjCl_eq_bot_of_offender h hφ hb4 h14 hSQ ha hab hbd (hVV.trans hcen)
      hK2 (A := (conjCl (stab (puAmalgam h.le) a) (ZM _ d)).map (MulAut.conj k).toMonoidHom)
      (Q' := Qv _ (k • a)) ⟨_, hβ, ?_⟩ ?_ ?_ ?_ ?_ ?_
    · exact ((Subgroup.map_mono hVQ).trans hQm.ge).trans (qv_le_qv _ h20 hm hmβ)
    · intro hle
      apply hVl
      rw [map_conj_le_iff, hQa, map_conj_map_conj, inv_mul_cancel, map_conj_one] at hle
      exact hle
    · rintro _ ⟨v, hv, rfl⟩
      rw [← map_pow]
      exact hZaQ (hZa ▸ Subgroup.mem_map_of_mem _
        (hXl (hVV (sq_mem_commutator_conjCl h hd hv))))
    · rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
      rw [← map_commutatorElement]
      exact hZaQ (hZa ▸ Subgroup.mem_map_of_mem _
        (hXl (hVV (Subgroup.commutator_mem_commutator hv hw))))
    · calc ⁅conjCl (stab (puAmalgam h.le) a) (ZM _ d) ⊓ Qv _ (k • a),
            (conjCl (stab (puAmalgam h.le) a) (ZM _ d)).map (MulAut.conj k).toMonoidHom⁆ ≤
          ⁅(Qv (puAmalgam h.le) a).map (MulAut.conj k).toMonoidHom,
            (conjCl (stab (puAmalgam h.le) a) (ZM _ d)).map (MulAut.conj k).toMonoidHom⁆ :=
            Subgroup.commutator_mono (inf_le_right.trans hQm.le) le_rfl
        _ = (⁅Qv (puAmalgam h.le) a, conjCl (stab (puAmalgam h.le) a) (ZM _ d)⁆).map
              (MulAut.conj k).toMonoidHom := (Subgroup.map_commutator _ _ _).symm
        _ ≤ (ZM (puAmalgam h.le) l).map (MulAut.conj k).toMonoidHom :=
            Subgroup.map_mono (hVQX'.trans hXl)
        _ = ZM _ a := hZa.symm
    · rw [hQa, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj k).injective]
      exact hcmp
  ·
    have hla : (puAmalgam h.le).treeGraph.dist a l = 2 := by
      rw [tdist_comm, ← hgeol]
      exact dist_geo_crit hb4 hcl (by omega)
    have haρ : (puAmalgam h.le).treeGraph.Adj a (geo (puAmalgam h.le) a l 1) :=
      adj_geo_one _ (by omega)
    have hρl : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) a l 1) l := by
      have := adj_geo (puAmalgam h.le) (u := a) (w := l) (i := 1) (by omega)
      rwa [geo_of_le _ (by omega : (puAmalgam h.le).treeGraph.dist a l ≤ 1 + 1)] at this
    have hQl : Qv (puAmalgam h.le) l = (Qv _ a).map (MulAut.conj k⁻¹).toMonoidHom := by
      rw [← hkl, qv_smul]
    refine commutator_conjCl_eq_bot_of_offender h hφ hb4 h14 hSQ ha hab hbd (hVV.trans hcen)
      hK2 (A := (conjCl (stab (puAmalgam h.le) a) (ZM _ d)).map (MulAut.conj k⁻¹).toMonoidHom)
      (Q' := Qv _ l) ⟨_, haρ, ?_⟩ ?_ ?_ ?_ ?_ ?_
    · exact ((Subgroup.map_mono hVQ).trans hQl.ge).trans (qv_le_qv _ h20 hlM hρl.symm)
    · intro hle
      apply hVm
      rw [map_conj_le_iff, inv_inv, ← hQm] at hle
      exact hle
    · rintro _ ⟨v, hv, rfl⟩
      rw [← map_pow]
      exact hZaQ (hZa' ▸ Subgroup.mem_map_of_mem _
        (hXm (hVV (sq_mem_commutator_conjCl h hd hv))))
    · rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
      rw [← map_commutatorElement]
      exact hZaQ (hZa' ▸ Subgroup.mem_map_of_mem _
        (hXm (hVV (Subgroup.commutator_mem_commutator hv hw))))
    · calc ⁅conjCl (stab (puAmalgam h.le) a) (ZM _ d) ⊓ Qv _ l,
            (conjCl (stab (puAmalgam h.le) a) (ZM _ d)).map (MulAut.conj k⁻¹).toMonoidHom⁆ ≤
          ⁅(Qv (puAmalgam h.le) a).map (MulAut.conj k⁻¹).toMonoidHom,
            (conjCl (stab (puAmalgam h.le) a) (ZM _ d)).map (MulAut.conj k⁻¹).toMonoidHom⁆ :=
            Subgroup.commutator_mono (inf_le_right.trans hQl.le) le_rfl
        _ = (⁅Qv (puAmalgam h.le) a, conjCl (stab (puAmalgam h.le) a) (ZM _ d)⁆).map
              (MulAut.conj k⁻¹).toMonoidHom := (Subgroup.map_commutator _ _ _).symm
        _ ≤ (ZM (puAmalgam h.le) (k • a)).map (MulAut.conj k⁻¹).toMonoidHom :=
            Subgroup.map_mono (hVQX'.trans hXm)
        _ = ZM _ a := hZa'.symm
    · rw [hQa', Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj k⁻¹).injective]
      exact (not_le.mp hcmp).le

end SD

end CFSG.Quasithin.MS93.S46.I464
