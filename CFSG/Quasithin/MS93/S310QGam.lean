module

public import CFSG.Quasithin.MS93.S310QBase
public import CFSG.Quasithin.MS93.S310MV

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S310Q

section Group

variable {Γ : Type} [Group Γ]

theorem commutator_iSup_right_le {ι : Sort*} {Y N : Subgroup Γ} {K : ι → Subgroup Γ}
    (hn : ∀ i, K i ≤ Subgroup.normalizer (N : Set Γ)) (h : ∀ i, ⁅Y, K i⁆ ≤ N) :
    ⁅Y, ⨆ i, K i⁆ ≤ N := by
  let S : Subgroup Γ :=
    { carrier := {x | x ∈ Subgroup.normalizer (N : Set Γ) ∧ ∀ y ∈ Y, ⁅y, x⁆ ∈ N}
      one_mem' := ⟨one_mem _, fun y _ => by simp⟩
      mul_mem' := by
        rintro x₁ x₂ ⟨hx₁, h₁⟩ ⟨hx₂, h₂⟩
        refine ⟨mul_mem hx₁ hx₂, fun y hy => ?_⟩
        have e : ⁅y, x₁ * x₂⁆ = ⁅y, x₁⁆ * (x₁ * ⁅y, x₂⁆ * x₁⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem (h₁ y hy) ((Subgroup.mem_normalizer_iff.1 hx₁ _).1 (h₂ y hy))
      inv_mem' := by
        rintro x ⟨hx, h₁⟩
        refine ⟨inv_mem hx, fun y hy => ?_⟩
        have e : ⁅y, x⁻¹⁆ = x⁻¹ * ⁅y, x⁆⁻¹ * x := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hx) _).1 (inv_mem (h₁ y hy))
        simpa using this }
  have hS : (⨆ i, K i) ≤ S := iSup_le fun i x hx =>
    ⟨hn i hx, fun y hy => h i (Subgroup.commutator_mem_commutator hy hx)⟩
  rw [Subgroup.commutator_le]
  intro y hy x hx
  exact (hS hx).2 y hy

end Group

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section NclStab

variable (h : PUHyp M T L) {α δ γ : Vtx (puAmalgam h.le)}

include h in
theorem zm_le_nclStab : ZM _ α ≤ S5.nclStab _ γ (ZM _ α) := fun z hz =>
  Subgroup.mem_iSup_of_mem (⟨1, one_mem _⟩ : ↥(stab (puAmalgam h.le) γ)) ⟨z, hz, by simp⟩

theorem zm_smul_le_nclStab {g : (puAmalgam h.le).Universal} (hg : g ∈ stab _ γ) :
    ZM _ (g • α) ≤ S5.nclStab _ γ (ZM _ α) := by
  rw [zm_smul]
  exact le_iSup (fun y : ↥(stab (puAmalgam h.le) γ) =>
    (ZM _ α).map (MulAut.conj (y : (puAmalgam h.le).Universal)).toMonoidHom) ⟨g, hg⟩

theorem zm_le_nclStab_of_adj (hγδ : (puAmalgam h.le).treeGraph.Adj γ δ)
    (hδα : (puAmalgam h.le).treeGraph.Adj δ α) :
    ZM _ γ ≤ S5.nclStab _ γ (ZM _ α) := by
  refine iSup₂_le fun ρ hρ => ?_
  obtain ⟨t, ht, rfl⟩ := exists_mem_stab_smul _ hγδ hρ
  rw [zh_smul]
  refine le_trans ?_ (zm_smul_le_nclStab h ht)
  rw [zm_smul, map_conj_le_map_conj_iff]
  exact zh_le_zm _ hδα.symm

theorem nclStab_le_vv (hα : IsMVtx _ α) (hγα : (puAmalgam h.le).treeGraph.dist γ α = 2) :
    S5.nclStab _ γ (ZM _ α) ≤ Vv _ γ := by
  refine iSup_le fun g => ?_
  rw [← zm_smul]
  have hgM : IsMVtx _ ((g : (puAmalgam h.le).Universal) • α) := (isMVtx_smul _ _ _).2 hα
  have hd : (puAmalgam h.le).treeGraph.dist γ ((g : (puAmalgam h.le).Universal) • α) ≤ 2 := by
    have hgγ : (g : (puAmalgam h.le).Universal) • γ = γ := (mem_stab _).1 g.2
    have e := dist_smul (puAmalgam h.le) (g : (puAmalgam h.le).Universal) γ α
    rw [hgγ] at e
    rw [e, hγα]
  exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam h.le) |
    (puAmalgam h.le).treeGraph.dist γ ρ ≤ 2}) => Zv (puAmalgam h.le) ρ) _ hd
    (zv_of_isMVtx _ hgM).ge

end NclStab

section VoSub

theorem stab_le_normalizer_vv {A B C : Type} [Group A] [Group C] [Group B]
    (X : GoldAmalgam A C B) (ρ : Vtx X) :
    stab X ρ ≤ Subgroup.normalizer (Vv X ρ : Set X.Universal) :=
  stab_le_normalizer_of_smul X (fun g δ => vi_smul X g δ 2) ρ

theorem voSub_le_commutator_nclStab (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {α δ γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) (hα : IsMVtx _ α)
    (hγδ : (puAmalgam h.le).treeGraph.Adj γ δ) (hδα : (puAmalgam h.le).treeGraph.Adj δ α)
    (hγα : (puAmalgam h.le).treeGraph.dist γ α = 2)
    (hirr : ∀ X : Subgroup (puAmalgam h.le).Universal, X ≤ S5.voSub h.le L γ →
      stab _ γ ≤ Subgroup.normalizer (X : Set (puAmalgam h.le).Universal) →
      ¬ X ≤ S5.bSub h.le L γ → S5.voSub h.le L γ ≤ X ⊔ (S5.voSub h.le L γ ⊓ S5.bSub h.le L γ))
    (hZB : ¬ ZM _ α ≤ S5.bSub h.le L γ) :
    S5.voSub h.le L γ ≤ ⁅S5.nclStab _ γ (ZM _ α), puTrans h.le L γ⁆ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hperf := puTrans_perfect h hγ
  set Vγ := S5.nclStab _ γ (ZM _ α) with hVγdef
  set Lt := puTrans h.le L γ with hLtdef
  set X := ⁅Vγ, Lt⁆ with hXdef
  have hLt : Lt ≤ stab _ γ := puTrans_le_stab h.le L γ
  have hLtn : stab _ γ ≤ Subgroup.normalizer (Lt : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le hLn γ
  have hVγn : stab _ γ ≤ Subgroup.normalizer (Vγ : Set (puAmalgam h.le).Universal) :=
    S310.stab_le_normalizer_nclStab _ γ _
  have hXn : stab _ γ ≤ Subgroup.normalizer (X : Set (puAmalgam h.le).Universal) :=
    le_normalizer_commutator hVγn hLtn
  have hZn : stab _ γ ≤ Subgroup.normalizer (ZM _ γ : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_zm _ γ
  have hVγV : Vγ ≤ Vv _ γ := nclStab_le_vv h hα hγα
  have hVvQ : Vv _ γ ≤ stab _ γ := (S5B.vv_le_qv h hb hγ).trans (qv_le_stab _ _)
  have hVγst : Vγ ≤ stab _ γ := hVγV.trans hVvQ
  have hvoV : S5.voSub h.le L γ ≤ Vv _ γ :=
    Subgroup.le_normalizer_iff_commutator_le_left.1 (hLt.trans (stab_le_normalizer_vv _ γ))
  have hvost : S5.voSub h.le L γ ≤ stab _ γ := hvoV.trans hVvQ
  have hvon : stab _ γ ≤ Subgroup.normalizer (S5.voSub h.le L γ : Set (puAmalgam h.le).Universal) :=
    le_normalizer_commutator (stab_le_normalizer_vv _ γ) hLtn
  have hXvo : X ≤ S5.voSub h.le L γ := Subgroup.commutator_mono hVγV le_rfl
  have hXst : X ≤ stab _ γ := hXvo.trans hvost
  have hZγV : ZM _ γ ≤ Vγ := zm_le_nclStab_of_adj h hγδ hδα
  have hZst : ZM _ γ ≤ stab _ γ := (zm_le_qv_self _ hγ h.critDist_pos).trans (qv_le_stab _ _)
  have hBZ : ∀ x ∈ S5.bSub h.le L γ, ∀ l ∈ Lt, ⁅x, l⁆ ∈ ZM _ γ := fun x hx l hl =>
    S5B.commutator_mem_zm_of_mem_bSub h hb hγ hx hl
  have hXB : ¬ X ≤ S5.bSub h.le L γ := by
    intro hle
    have hXL : ⁅X, Lt⁆ ≤ ZM _ γ := by
      rw [Subgroup.commutator_le]
      intro x hx l hl
      exact hBZ x (hle hx) l hl
    have h1 : ⁅Vγ, Lt⁆ ≤ ZM _ γ :=
      S5B.commutator_le_of_perfect hperf (hVγst.trans hZn) (hLt.trans hZn) le_rfl hXL
    apply hZB
    intro z hz
    have hzV : z ∈ Vγ := zm_le_nclStab h hz
    exact Subgroup.subset_closure ⟨hVγV hzV, fun l hl =>
      h1 (Subgroup.commutator_mem_commutator hzV hl)⟩
  have hsup := hirr X hXvo hXn hXB
  have hXZn : stab _ γ ≤ Subgroup.normalizer ((X ⊔ ZM _ γ : Subgroup _) :
      Set (puAmalgam h.le).Universal) := le_normalizer_sup hXn hZn
  have h2 : ⁅S5.voSub h.le L γ, Lt⁆ ≤ X ⊔ ZM _ γ := by
    refine (Subgroup.commutator_mono hsup le_rfl).trans
      (S310.commutator_sup_left_le (hXst.trans hXZn)
        ((inf_le_left.trans hvost).trans hXZn) ?_ ?_)
    · exact (Subgroup.le_normalizer_iff_commutator_le_left.1 (hLt.trans hXn)).trans le_sup_left
    · rw [Subgroup.commutator_le]
      intro x hx l hl
      exact Subgroup.mem_sup_right (hBZ x hx.2 l hl)
  have hvoL : S5.voSub h.le L γ ≤ ⁅S5.voSub h.le L γ, Lt⁆ :=
    S5B.commutator_le_of_perfect hperf
      (hVvQ.trans (le_normalizer_commutator hvon hLtn))
      (hLt.trans (le_normalizer_commutator hvon hLtn)) le_rfl le_rfl
  have hUX : ⁅ZM _ γ, Lt⁆ ≤ X := Subgroup.commutator_mono hZγV le_rfl
  have h3 : ⁅S5.voSub h.le L γ, Lt⁆ ≤ X := by
    refine S5B.commutator_le_of_perfect hperf (hvost.trans hXn) (hLt.trans hXn) h2 ?_
    exact S310.commutator_sup_left_le (hXst.trans hXn) (hZst.trans hXn)
      (Subgroup.le_normalizer_iff_commutator_le_left.1 (hLt.trans hXn)) hUX
  exact hvoL.trans h3

theorem commutator_nclStab_le_dSub (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {α δ γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) (hα : IsMVtx _ α)
    (hγδ : (puAmalgam h.le).treeGraph.Adj γ δ) (hδα : (puAmalgam h.le).treeGraph.Adj δ α)
    (hγα : (puAmalgam h.le).treeGraph.dist γ α = 2)
    (hVoD : ⁅S5.voSub h.le L γ, S5.voSub h.le L γ⁆ ≤ S5.dSub h.le L γ)
    (hQ : ¬ Qv _ α ≤ Qv _ γ) :
    ⁅S5.nclStab _ γ (ZM _ α), S5.nclStab _ γ (ZM _ α)⁆ ≤ S5.dSub h.le L γ := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hperf := puTrans_perfect h hγ
  have hδ : ¬ IsMVtx _ δ := (isMVtx_iff_of_adj _ hγδ).1 hγ
  set Vγ := S5.nclStab _ γ (ZM _ α) with hVγdef
  set Lt := puTrans h.le L γ with hLtdef
  set D := S5.dSub h.le L γ with hDdef
  set Vo := S5.voSub h.le L γ with hVodef
  have hLt : Lt ≤ stab _ γ := puTrans_le_stab h.le L γ
  have hLtn : stab _ γ ≤ Subgroup.normalizer (Lt : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le hLn γ
  have hDn : stab _ γ ≤ Subgroup.normalizer (D : Set (puAmalgam h.le).Universal) :=
    le_normalizer_inf (stab_le_normalizer_qv _ γ) (le_normalizer_centralizer hLtn)
  have hQγδ : Qv _ γ ≤ Qv _ δ := qv_le_qv _ hyp hγ hγδ
  have hQδα : Qv _ δ ≤ stab _ α := qv_le_stab_of_adj _ hδα
  have hQδγ : Qv _ δ ≤ stab _ γ := qv_le_stab_of_adj _ hγδ.symm
  have hZαn : stab _ α ≤ Subgroup.normalizer (ZM _ α : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_zm _ α
  have hVvQ : Vv _ γ ≤ Qv _ γ := S5B.vv_le_qv h hb hγ
  have hVoV : Vo ≤ Vv _ γ :=
    Subgroup.le_normalizer_iff_commutator_le_left.1 (hLt.trans (stab_le_normalizer_vv _ γ))
  have hVoQ : Vo ≤ Qv _ γ := hVoV.trans hVvQ
  have hZαQ : ZM _ α ≤ Qv _ γ :=
    zm_le_qv_of_dist_lt _ hα (by rw [SimpleGraph.dist_comm, hγα]; omega)
  have hVγQ : Vγ ≤ Qv _ γ := S310.nclStab_le_qv h hα hγα hb
  have hVsup : Vγ ≤ Vo ⊔ ZM _ α := by
    refine iSup_le fun g => ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨l, hl, t, ht, hg⟩ := S310.exists_puTrans_mul_of_isMVtx h hγ hγδ g.2
    have hz' : t * z * t⁻¹ ∈ ZM _ α :=
      (Subgroup.mem_normalizer_iff.1 (hZαn (hQδα ht)) z).1 hz
    have hz'V : t * z * t⁻¹ ∈ Vv _ γ := nclStab_le_vv h hα hγα (zm_le_nclStab h hz')
    have hc' : ⁅l, t * z * t⁻¹⁆ ∈ Vo := by
      rw [hVodef, S5.voSub, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hl hz'V
    have e : (MulAut.conj (g : (puAmalgam h.le).Universal)).toMonoidHom z =
        ⁅l, t * z * t⁻¹⁆ * (t * z * t⁻¹) := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hc') (Subgroup.mem_sup_right hz')
  have hZab : ⁅ZM _ α, ZM _ α⁆ = ⊥ := by
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 ?_
    exact (zm_le_centralizer_qv _ hyp hα).trans
      (Subgroup.centralizer_le (zm_le_qv_self _ hα hb0))
  have hVoZ : Vo ≤ Subgroup.normalizer (ZM _ α : Set (puAmalgam h.le).Universal) :=
    hVoQ.trans (hQγδ.trans (hQδα.trans hZαn))
  have hN : ∀ K : Subgroup (puAmalgam h.le).Universal, K ≤ Qv _ γ →
      K ≤ Subgroup.normalizer (ZM _ α : Set (puAmalgam h.le).Universal) →
      K ≤ Subgroup.normalizer ((D ⊔ ZM _ α : Subgroup _) : Set (puAmalgam h.le).Universal) :=
    fun K hK hKZ => le_normalizer_sup (hK.trans ((qv_le_stab _ _).trans hDn)) hKZ
  have hV'DZ : ⁅Vγ, Vγ⁆ ≤ D ⊔ ZM _ α := by
    refine (Subgroup.commutator_mono hVsup hVsup).trans
      (S310.commutator_sup_sup_le (hN _ hVoQ hVoZ) (hN _ hZαQ (Subgroup.le_normalizer))
        (hVoD.trans le_sup_left) ?_ (by rw [hZab]; exact bot_le))
    rw [Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_left.1 hVoZ).trans le_sup_right
  obtain ⟨y, hyQα, hyQγ⟩ := Set.not_subset.1 hQ
  have hyδ : y ∈ Qv _ δ := qv_le_qv _ hyp hα hδα.symm hyQα
  have hyγ : y ∈ stab _ γ := hQδγ hyδ
  have hy2 : ∃ e : ℕ, y ^ 2 ^ e = 1 := by
    obtain ⟨e, he⟩ := isPGroup_qv _ hyp hδ ⟨y, hyδ⟩
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  have hyC : y ∈ Subgroup.centralizer (ZM _ α : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hα hz)) y hyQα).symm
  have hyD : y ∈ Subgroup.normalizer (D : Set (puAmalgam h.le).Universal) := hDn hyγ
  have hyW : ∀ w ∈ ⁅Vγ, Vγ⁆, y * w * y⁻¹ * w⁻¹ ∈ D := by
    intro w hw
    have hw' := hV'DZ hw
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left D (ZM _ α)
      (hZαQ.trans ((qv_le_stab _ _).trans hDn))] at hw'
    obtain ⟨d, hdD, z, hz, rfl⟩ := hw'
    have hyz : z * y⁻¹ = y⁻¹ * z :=
      (Commute.inv_right (Subgroup.mem_centralizer_iff.1 hyC z hz)).eq
    have e : y * (d * z) * y⁻¹ * (d * z)⁻¹ = y * d * y⁻¹ * d⁻¹ := by
      calc y * (d * z) * y⁻¹ * (d * z)⁻¹ = y * d * (z * y⁻¹) * z⁻¹ * d⁻¹ := by group
        _ = y * d * (y⁻¹ * z) * z⁻¹ * d⁻¹ := by rw [hyz]
        _ = y * d * y⁻¹ * d⁻¹ := by group
    rw [e]
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 hyD d).1 hdD) (inv_mem hdD)
  have hW : ⁅Vγ, Vγ⁆ ≤ stab _ γ :=
    (commutator_le_of_le hVγQ hVγQ).trans (qv_le_stab _ _)
  have hWn : Lt ≤ Subgroup.normalizer ((⁅Vγ, Vγ⁆ : Subgroup _) : Set (puAmalgam h.le).Universal) :=
    hLt.trans (le_normalizer_commutator (S310.stab_le_normalizer_nclStab _ γ _)
      (S310.stab_le_normalizer_nclStab _ γ _))
  have h1 := commutator_le_of_two_elt h hγ hW (inf_le_left.trans (qv_le_stab _ _)) hWn
    (hLt.trans hDn) hyγ hy2 hyQγ hyD hyW
  have hbot : Subgroup.normalizer ((⊥ : Subgroup (puAmalgam h.le).Universal) :
      Set (puAmalgam h.le).Universal) = ⊤ := Subgroup.normalizer_eq_top _
  have h2 : ⁅⁅Vγ, Vγ⁆, Lt⁆ ≤ ⊥ :=
    S5B.commutator_le_of_perfect hperf (by rw [hbot]; exact le_top) (by rw [hbot]; exact le_top)
      h1 (le_of_eq (Subgroup.commutator_eq_bot_iff_le_centralizer.2 inf_le_right))
  exact le_inf (commutator_le_of_le hVγQ hVγQ)
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (le_bot_iff.1 h2))

end VoSub

theorem commutator_inf_qv_le_dSub (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {α δ γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) (hα : IsMVtx _ α)
    (hγδ : (puAmalgam h.le).treeGraph.Adj γ δ) (hγα : (puAmalgam h.le).treeGraph.dist γ α = 2)
    (hQγ : ⁅Qv _ γ, puTrans h.le L γ⁆ = S5.voSub h.le L γ)
    (hvo : S5.voSub h.le L γ ≤ S5.nclStab _ γ (ZM _ α))
    (hVγD : ⁅S5.nclStab _ γ (ZM _ α), S5.nclStab _ γ (ZM _ α)⁆ ≤ S5.dSub h.le L γ)
    {P : Subgroup (puAmalgam h.le).Universal} (hPα : P ≤ Qv _ α)
    (hPn : Qv _ δ ≤ Subgroup.normalizer (P : Set (puAmalgam h.le).Universal)) :
    ⁅P ⊓ Qv _ γ, P ⊓ Qv _ γ⁆ ≤ S5.dSub h.le L γ := by
  have hyp := h.hyp20
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hperf := puTrans_perfect h hγ
  set Vγ := S5.nclStab _ γ (ZM _ α) with hVγdef
  set Lt := puTrans h.le L γ with hLtdef
  set D := S5.dSub h.le L γ with hDdef
  set Vo := S5.voSub h.le L γ with hVodef
  set Y := (P ⊓ Qv _ γ) ⊔ Vo with hYdef
  have hLt : Lt ≤ stab _ γ := puTrans_le_stab h.le L γ
  have hLtn : stab _ γ ≤ Subgroup.normalizer (Lt : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le hLn γ
  have hDn : stab _ γ ≤ Subgroup.normalizer (D : Set (puAmalgam h.le).Universal) :=
    le_normalizer_inf (stab_le_normalizer_qv _ γ) (le_normalizer_centralizer hLtn)
  have hvon : stab _ γ ≤ Subgroup.normalizer (Vo : Set (puAmalgam h.le).Universal) :=
    le_normalizer_commutator (stab_le_normalizer_vv _ γ) hLtn
  have hVoQ : Vo ≤ Qv _ γ :=
    (Subgroup.le_normalizer_iff_commutator_le_left.1 (hLt.trans (stab_le_normalizer_vv _ γ))).trans
      (S5B.vv_le_qv h hb hγ)
  have hYQ : Y ≤ Qv _ γ := sup_le inf_le_right hVoQ
  have hYst : Y ≤ stab _ γ := hYQ.trans (qv_le_stab _ _)
  have hQδγ : Qv _ δ ≤ stab _ γ := qv_le_stab_of_adj _ hγδ.symm
  have hYT : Qv _ δ ≤ Subgroup.normalizer (Y : Set (puAmalgam h.le).Universal) :=
    le_normalizer_sup (le_normalizer_inf hPn (hQδγ.trans (stab_le_normalizer_qv _ γ)))
      (hQδγ.trans hvon)
  have hYL : Lt ≤ Subgroup.normalizer (Y : Set (puAmalgam h.le).Universal) := by
    refine le_normalizer_of_map_conj_le fun l hl => ?_
    rw [hYdef, Subgroup.map_sup, map_conj_eq_of_mem_normalizer (hvon (hLt hl))]
    refine sup_le ?_ le_sup_right
    rintro _ ⟨y, hy, rfl⟩
    have hc : ⁅l, y⁆ ∈ Vo := by
      rw [← hQγ, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hl hy.2
    have e : (MulAut.conj l).toMonoidHom y = ⁅l, y⁆ * y := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hy)
  have hYn : stab _ γ ≤ Subgroup.normalizer (Y : Set (puAmalgam h.le).Universal) := by
    intro g hg
    obtain ⟨l, hl, t, ht, rfl⟩ := S310.exists_puTrans_mul_of_isMVtx h hγ hγδ hg
    exact mul_mem (hYL hl) (hYT ht)
  have hZαVγ : ZM _ α ≤ Vγ := zm_le_nclStab h
  have h1 : ⁅Y, ZM _ α⁆ ≤ D := by
    refine S310.commutator_sup_left_le ((inf_le_right.trans (qv_le_stab _ _)).trans hDn)
      ((hVoQ.trans (qv_le_stab _ _)).trans hDn) ?_
      ((Subgroup.commutator_mono hvo hZαVγ).trans hVγD)
    have : ⁅P ⊓ Qv _ γ, ZM _ α⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact inf_le_left.trans (hPα.trans
        (Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hα)))
    rw [this]
    exact bot_le
  have hVγQ : Vγ ≤ Qv _ γ := S310.nclStab_le_qv h hα hγα hb
  have h2 : ⁅Y, Vγ⁆ ≤ D := by
    refine commutator_iSup_right_le (fun g => ?_) (fun g => ?_)
    · exact (le_iSup (fun y : ↥(stab (puAmalgam h.le) γ) =>
        (ZM _ α).map (MulAut.conj (y : (puAmalgam h.le).Universal)).toMonoidHom) g).trans
        (hVγQ.trans ((qv_le_stab _ _).trans hDn))
    · have hYg : Y = Y.map (MulAut.conj (g : (puAmalgam h.le).Universal)).toMonoidHom :=
        (map_conj_eq_of_mem_normalizer (hYn g.2)).symm
      have hDg : D.map (MulAut.conj (g : (puAmalgam h.le).Universal)).toMonoidHom = D :=
        map_conj_eq_of_mem_normalizer (hDn g.2)
      rw [hYg, ← Subgroup.map_commutator, ← hDg]
      exact Subgroup.map_mono h1
  have h3 : ⁅Y, Vo⁆ ≤ D := (Subgroup.commutator_mono le_rfl hvo).trans h2
  have hYLt : ⁅Y, Lt⁆ ≤ Vo := (Subgroup.commutator_mono hYQ le_rfl).trans hQγ.le
  have h4 : ⁅⁅Y, Y⁆, Lt⁆ ≤ D := by
    have h3' : ⁅⁅Y, Lt⁆, Y⁆ ≤ D := by
      refine (Subgroup.commutator_mono hYLt le_rfl).trans ?_
      rw [Subgroup.commutator_comm Vo Y]
      exact h3
    refine S5B.commutator_commutator_le_of_rotate (hYst.trans hDn) (hYst.trans hDn)
      (hLt.trans hDn) h3' ?_
    rw [Subgroup.commutator_comm Lt Y]
    exact h3'
  have hbot : Subgroup.normalizer ((⊥ : Subgroup (puAmalgam h.le).Universal) :
      Set (puAmalgam h.le).Universal) = ⊤ := Subgroup.normalizer_eq_top _
  have h5 : ⁅⁅Y, Y⁆, Lt⁆ ≤ ⊥ :=
    S5B.commutator_le_of_perfect hperf (by rw [hbot]; exact le_top) (by rw [hbot]; exact le_top)
      h4 (le_of_eq (Subgroup.commutator_eq_bot_iff_le_centralizer.2 inf_le_right))
  have hY'D : ⁅Y, Y⁆ ≤ D := le_inf (commutator_le_of_le hYQ hYQ)
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (le_bot_iff.1 h5))
  exact (Subgroup.commutator_mono le_sup_left le_sup_left).trans hY'D

end S310Q

end CFSG.Quasithin.MS93
