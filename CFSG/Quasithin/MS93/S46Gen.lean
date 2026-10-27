module

public import CFSG.Quasithin.MS93.S4AVtx
public import CFSG.Quasithin.MS93.S46Base

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement
open CFSG.Quasithin.MS93.S4A

section Perfect

variable {G : Type} [Group G]

theorem commutator_le_of_perfect {L A B N : Subgroup G} (hL : ⁅L, L⁆ = L) (hAB : ⁅A, L⁆ ≤ B)
    (hBN : ⁅B, L⁆ ≤ N) (hLN : L ≤ Subgroup.normalizer (N : Set G))
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) : ⁅A, L⁆ ≤ N := by
  have h1 : ⁅⁅A, L⁆, L⁆ ≤ N := (Subgroup.commutator_mono hAB le_rfl).trans hBN
  have h3 := three_subgroups_le (N := N) (H₁ := L) (H₂ := L) (H₃ := A) hLN hLN hAN
    (show ⁅⁅L, A⁆, L⁆ ≤ N by rw [Subgroup.commutator_comm L A]; exact h1) h1
  rw [hL, Subgroup.commutator_comm] at h3
  exact h3

end Perfect

section NormalClosure

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem ltil_le_of_normal {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hδρ : (puAmalgam h.le).treeGraph.Adj δ ρ) {C K : Subgroup (puAmalgam h.le).Universal}
    (hCs : C ≤ stab _ δ) (hCn : stab _ δ ≤ Subgroup.normalizer (C : Set _)) (hKC : K ≤ C)
    (hKρ : K ≤ Qv _ ρ) (hKQ : ¬ K ≤ Qv _ δ) : Ltil h.le L δ ≤ C := by
  have hLs := ltil_le_stab h δ
  have hLn := stab_le_normalizer_ltil h δ
  set C' := C ⊓ Ltil h.le L δ with hC'
  have hC'n : Ltil h.le L δ ≤ Subgroup.normalizer (C' : Set _) :=
    (le_inf (hLs.trans hCn) Subgroup.le_normalizer).trans
      (Subgroup.inf_normalizer_le_normalizer_inf)
  rcases commutator_ltil_le_or h hδ (K := C') inf_le_right hC'n with hO | hle
  · exfalso
    apply hKQ
    have hCL : ⁅C, Ltil h.le L δ⁆ ≤ C' := le_inf
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hCn))
      (by rw [Subgroup.commutator_comm]
          exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hCs.trans hLn))
    have hQn : stab (puAmalgam h.le) δ ≤ Subgroup.normalizer (Qv _ δ : Set _) :=
      stab_le_normalizer_qv _ δ
    have h2 : ⁅⁅C, Ltil h.le L δ⁆, Ltil h.le L δ⁆ ≤ Qv _ δ :=
      ((Subgroup.commutator_mono hCL le_rfl).trans hO).trans (pCoreLtil_le_qv h hδ)
    have hperf := ltil_perfect h hδ
    have h3 : ⁅C, Ltil h.le L δ⁆ ≤ Qv _ δ := by
      have h4 := three_subgroups_le (N := Qv (puAmalgam h.le) δ) (H₁ := Ltil h.le L δ)
        (H₂ := Ltil h.le L δ) (H₃ := C) (hLs.trans hQn) (hLs.trans hQn) (hCs.trans hQn)
        (by rw [Subgroup.commutator_comm (Ltil h.le L δ) C]; exact h2) h2
      rw [hperf, Subgroup.commutator_comm] at h4
      exact h4
    exact le_qv_of_commutator_le h hfull hδ hδρ hKρ
      ((Subgroup.commutator_mono hKC le_rfl).trans h3)
  · exact hle.trans inf_le_left

theorem commutator_ltil_le_of_commutator_le {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hδρ : (puAmalgam h.le).treeGraph.Adj δ ρ) {A B K : Subgroup (puAmalgam h.le).Universal}
    (hA : stab _ δ ≤ Subgroup.normalizer (A : Set _))
    (hB : stab _ δ ≤ Subgroup.normalizer (B : Set _)) (hAK : ⁅A, K⁆ ≤ B)
    (hKρ : K ≤ Qv _ ρ) (hKQ : ¬ K ≤ Qv _ δ) : ⁅A, Ltil h.le L δ⁆ ≤ B := by
  have hKs : K ≤ stab (puAmalgam h.le) δ := hKρ.trans (qv_le_stab_of_adj _ hδρ.symm)
  let C : Subgroup (puAmalgam h.le).Universal :=
    { carrier := {g | g ∈ stab (puAmalgam h.le) δ ∧ ∀ a ∈ A, ⁅a, g⁆ ∈ B}
      mul_mem' := by
        rintro g k ⟨hg, hgA⟩ ⟨hk, hkA⟩
        refine ⟨Subgroup.mul_mem _ hg hk, fun a ha => ?_⟩
        have e : ⁅a, g * k⁆ = ⁅a, g⁆ * (g * ⁅a, k⁆ * g⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact B.mul_mem (hgA a ha) ((Subgroup.mem_normalizer_iff.mp (hB hg) _).mp (hkA a ha))
      one_mem' := ⟨Subgroup.one_mem _, fun a _ => by simp [commutatorElement_def]⟩
      inv_mem' := by
        rintro g ⟨hg, hgA⟩
        refine ⟨Subgroup.inv_mem _ hg, fun a ha => ?_⟩
        have e : ⁅a, g⁻¹⁆ = g⁻¹ * (⁅a, g⁆)⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hB (Subgroup.inv_mem _ hg)) _).mp
          (B.inv_mem (hgA a ha)) }
  have hCs : C ≤ stab (puAmalgam h.le) δ := fun g hg => hg.1
  have hCn : stab (puAmalgam h.le) δ ≤ Subgroup.normalizer (C : Set _) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have key : ∀ y ∈ stab (puAmalgam h.le) δ, ∀ g ∈ C, y * g * y⁻¹ ∈ C := by
      rintro y hy g ⟨hg, hgA⟩
      refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hg) (Subgroup.inv_mem _ hy),
        fun a ha => ?_⟩
      have ha' : y⁻¹ * a * y⁻¹⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (hA (Subgroup.inv_mem _ hy)) a).mp ha
      have e : ⁅a, y * g * y⁻¹⁆ = y * ⁅y⁻¹ * a * y⁻¹⁻¹, g⁆ * y⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hB hy) _).mp (hgA _ ha')
    constructor
    · exact key x hx g
    · intro hg
      have := key x⁻¹ (Subgroup.inv_mem _ hx) _ hg
      simpa [mul_assoc] using this
  have hKC : K ≤ C := fun k hk =>
    ⟨hKs hk, fun a ha => hAK (Subgroup.commutator_mem_commutator ha hk)⟩
  have hLC := ltil_le_of_normal h hfull hδ hδρ hCs hCn hKC hKρ hKQ
  rw [Subgroup.commutator_le]
  intro a ha l hl
  exact (hLC hl).2 a ha

end NormalClosure

section Gen

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

theorem exists_zv_le_vv_adj {α x : Vtx X} (hα : IsMVtx X α) (hx : X.treeGraph.dist α x ≤ 2) :
    ∃ ρ, X.treeGraph.Adj α ρ ∧ Zv X x ≤ Vv X ρ := by
  rcases (by omega : X.treeGraph.dist α x = 0 ∨ X.treeGraph.dist α x = 1 ∨
      X.treeGraph.dist α x = 2) with h0 | h1 | h2
  · have hxα : x = α := ((dist_eq_zero_iff X).mp h0).symm
    subst hxα
    obtain ⟨ρ, hρ⟩ := exists_adj X x
    exact ⟨ρ, hρ, by rw [zv_of_isMVtx X hα]; exact zm_le_vv_of_adj hρ.symm hα⟩
  · have hadj : X.treeGraph.Adj α x := SimpleGraph.dist_eq_one_iff_adj.mp h1
    refine ⟨x, hadj, le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : Vtx X |
      X.treeGraph.dist x μ ≤ 2}) => Zv X μ) x ?_ le_rfl⟩
    show X.treeGraph.dist x x ≤ 2
    rw [SimpleGraph.dist_self]
    omega
  · have hlt : 0 < X.treeGraph.dist α x := by omega
    set ρ := geo X α x 1
    have hαρ : X.treeGraph.Adj α ρ := adj_geo_one X hlt
    have hρx : X.treeGraph.Adj ρ x := by
      have := adj_geo X (u := α) (w := x) (i := 1) (by omega)
      rwa [geo_of_le X (by omega : X.treeGraph.dist α x ≤ 1 + 1)] at this
    have hxM : IsMVtx X x := by
      have h1 := (isMVtx_iff_of_adj X hαρ).mp hα
      have h2 := isMVtx_iff_of_adj X hρx
      tauto
    exact ⟨ρ, hαρ, by rw [zv_of_isMVtx X hxM]; exact zm_le_vv_of_adj hρx hxM⟩

theorem vv_eq_iSup_vv {α : Vtx X} (hα : IsMVtx X α) :
    Vv X α = ⨆ ρ ∈ X.treeGraph.neighborSet α, Vv X ρ := by
  apply le_antisymm
  · refine iSup₂_le fun x hx => ?_
    obtain ⟨ρ, hρ, hle⟩ := exists_zv_le_vv_adj hα hx
    exact hle.trans (le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ X.treeGraph.neighborSet α) => Vv X ρ)
      ρ hρ le_rfl)
  · refine iSup₂_le fun ρ hρ => ?_
    have hρH : ¬ IsMVtx X ρ := by have := isMVtx_iff_of_adj X hρ; tauto
    rw [vv_eq_iSup_of_not_isMVtx hρH]
    refine iSup₂_le fun δ hδ => ?_
    have hδM : IsMVtx X δ := by have := isMVtx_iff_of_adj X hδ; tauto
    have hd : X.treeGraph.dist α δ ≤ 2 := by
      have := dist_triangle X α ρ δ
      rw [dist_eq_one_of_adj X hρ, dist_eq_one_of_adj X hδ] at this
      omega
    have : Zv X δ ≤ Vv X α := le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : Vtx X |
      X.treeGraph.dist α μ ≤ 2}) => Zv X μ) δ hd le_rfl
    rwa [zv_of_isMVtx X hδM] at this

@[expose] def vvPerp (α : Vtx X) (K : Subgroup X.Universal) : Subgroup X.Universal :=
  Subgroup.closure {v | v ∈ Vv X α ∧ ∀ w ∈ Vv X α, ⁅v, w⁆ ∈ K}

theorem mem_vvPerp_iff {α : Vtx X} {K : Subgroup X.Universal}
    (hK : Vv X α ≤ Subgroup.normalizer (K : Set X.Universal)) {v : X.Universal} :
    v ∈ vvPerp α K ↔ v ∈ Vv X α ∧ ∀ w ∈ Vv X α, ⁅v, w⁆ ∈ K := by
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

theorem vvPerp_le (α : Vtx X) (K : Subgroup X.Universal) : vvPerp α K ≤ Vv X α :=
  (Subgroup.closure_le _).mpr fun _ hv => hv.1

end Gen

section CommCrit

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem commutator_vv_le_of_ltil (hb : 2 < critDist (puAmalgam h.le))
    {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) {K : Subgroup (puAmalgam h.le).Universal}
    (hK : stab _ α ≤ Subgroup.normalizer (K : Set _))
    (hVL : ⁅Vv (puAmalgam h.le) α, Ltil h.le L α⁆ ≤ vvPerp α K) :
    ⁅Vv (puAmalgam h.le) α, Vv (puAmalgam h.le) α⁆ ≤ K := by
  have h20 := h.hyp20
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α :=
    (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hKV : Vv (puAmalgam h.le) α ≤ Subgroup.normalizer (K : Set _) := hVs.trans hK
  set Ut := vvPerp (X := puAmalgam h.le) α K with hUt
  have hUtV : Ut ≤ Vv _ α := vvPerp_le α K
  have hUtn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (Ut : Set _) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ y ∈ stab (puAmalgam h.le) α, ∀ v ∈ Ut, y * v * y⁻¹ ∈ Ut := by
      intro y hy v hv
      rw [mem_vvPerp_iff hKV] at hv ⊢
      have hVn := stab_le_normalizer_vv h α
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hVn hy) v).mp hv.1, fun w hw => ?_⟩
      have hw' : y⁻¹ * w * y⁻¹⁻¹ ∈ Vv (puAmalgam h.le) α :=
        (Subgroup.mem_normalizer_iff.mp (hVn (Subgroup.inv_mem _ hy)) w).mp hw
      have e : ⁅y * v * y⁻¹, w⁆ = y * ⁅v, y⁻¹ * w * y⁻¹⁻¹⁆ * y⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hK hy) _).mp (hv.2 _ hw')
    intro v
    constructor
    · exact key g hg v
    · intro hv
      have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hv
      simpa [mul_assoc] using this
  have hZ : ∀ ρ₀ μ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj α ρ₀ →
      (puAmalgam h.le).treeGraph.Adj ρ₀ μ → ZM (puAmalgam h.le) μ ≤ Ut := by
    intro ρ₀ μ hαρ hρμ
    have hμM : IsMVtx (puAmalgam h.le) μ := by
      have h1 := (isMVtx_iff_of_adj _ hαρ).mp hα
      have h2 := isMVtx_iff_of_adj _ hρμ
      tauto
    have hZV : ZM (puAmalgam h.le) μ ≤ Vv _ α := by
      have hd : (puAmalgam h.le).treeGraph.dist α μ ≤ 2 := by
        have := dist_triangle _ α ρ₀ μ
        rw [dist_eq_one_of_adj _ hαρ, dist_eq_one_of_adj _ hρμ] at this
        omega
      have : Zv (puAmalgam h.le) μ ≤ Vv _ α := le_iSup₂_of_le (f := fun x (_ : x ∈
        {x : Vtx (puAmalgam h.le) | (puAmalgam h.le).treeGraph.dist α x ≤ 2}) =>
          Zv (puAmalgam h.le) x) μ hd le_rfl
      rwa [zv_of_isMVtx _ hμM] at this
    set W := ZM (puAmalgam h.le) μ ⊔ Ut with hW
    have hWn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (W : Set _) := by
      rw [stab_eq_ltil_sup_qv_adj h hfull hα hαρ]
      refine sup_le ?_ ?_
      · rw [Subgroup.le_normalizer_iff_commutator_le_left]
        refine S4A.commutator_sup_le_of ?_ ?_ ?_ ?_
        · exact ((Subgroup.commutator_mono hZV le_rfl).trans hVL).trans le_sup_right
        · exact (Subgroup.le_normalizer_iff_commutator_le_left.mp
            ((ltil_le_stab h α).trans hUtn)).trans le_sup_right
        · exact le_sup_left.trans Subgroup.le_normalizer
        · exact le_sup_right.trans Subgroup.le_normalizer
      · have hTμ : Qv (puAmalgam h.le) ρ₀ ≤ stab _ μ := qv_le_stab_of_adj _ hρμ
        have hTα : Qv (puAmalgam h.le) ρ₀ ≤ stab _ α := qv_le_stab_of_adj _ hαρ.symm
        exact (le_inf (hTμ.trans (stab_le_normalizer_zm _ μ)) (hTα.trans hUtn)).trans
          (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    have hρ : ∀ ρ ∈ (puAmalgam h.le).treeGraph.neighborSet α,
        ⁅ZM (puAmalgam h.le) μ, Vv _ ρ⁆ ≤ K := by
      intro ρ hρ
      obtain ⟨g, hg, hgρ⟩ := exists_mem_stab_smul _ hαρ hρ
      have hgμ : (puAmalgam h.le).treeGraph.Adj ρ (g • μ) := by
        rw [← hgρ]; exact (adj_smul _ g _ _).mpr hρμ
      have hle : ZM (puAmalgam h.le) μ ≤ Vv _ ρ ⊔ Ut := by
        have h1 : ZM (puAmalgam h.le) μ ≤ W.map (MulAut.conj g).toMonoidHom := by
          rw [map_conj_eq_of_mem_normalizer (hWn hg)]
          exact le_sup_left
        refine h1.trans ?_
        rw [hW, Subgroup.map_sup, ← zm_smul, map_conj_eq_of_mem_normalizer (hUtn hg)]
        have hgμM : IsMVtx (puAmalgam h.le) (g • μ) := (isMVtx_smul _ g μ).mpr hμM
        exact sup_le_sup_right (zm_le_vv_of_adj hgμ hgμM) _
      have hVρab := vv_le_centralizer_of_not_isMVtx h20 hb (ρ := ρ)
        (by have := isMVtx_iff_of_adj _ hρ; tauto)
      have hVρα : Vv (puAmalgam h.le) ρ ≤ Vv _ α := by
        rw [vv_eq_iSup_vv hα]
        exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ (puAmalgam h.le).treeGraph.neighborSet α) =>
          Vv (puAmalgam h.le) ρ) ρ hρ le_rfl
      refine (Subgroup.commutator_mono hle le_rfl).trans ?_
      refine S4A.commutator_sup_le_of ?_ ?_ ((hVρα.trans hKV)) (hUtV.trans hKV)
      · rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hVρab]
        exact bot_le
      · rw [Subgroup.commutator_le]
        intro u hu w hw
        exact ((mem_vvPerp_iff hKV).mp hu).2 w (hVρα hw)
    have hVρα' : ∀ ρ ∈ (puAmalgam h.le).treeGraph.neighborSet α,
        Vv (puAmalgam h.le) ρ ≤ Vv _ α := fun ρ hρ => by
      rw [vv_eq_iSup_vv hα]
      exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ (puAmalgam h.le).treeGraph.neighborSet α) =>
        Vv (puAmalgam h.le) ρ) ρ hρ le_rfl
    have hZVK : ⁅ZM (puAmalgam h.le) μ, Vv _ α⁆ ≤ K := by
      rw [vv_eq_iSup_vv hα, iSup_subtype', Subgroup.commutator_comm]
      refine commutator_iSup_le_of (fun ρ => ?_) ?_
      · rw [Subgroup.commutator_comm]; exact hρ ρ.1 ρ.2
      · exact iSup_le fun ρ => (hVρα' ρ.1 ρ.2).trans hKV
    intro z hz
    rw [mem_vvPerp_iff hKV]
    exact ⟨hZV hz, fun w hw => hZVK (Subgroup.commutator_mem_commutator hz hw)⟩
  have hVU : Vv (puAmalgam h.le) α ≤ Ut := by
    rw [vv_eq_iSup_vv hα]
    refine iSup₂_le fun ρ hρ => ?_
    have hρH : ¬ IsMVtx (puAmalgam h.le) ρ := by have := isMVtx_iff_of_adj _ hρ; tauto
    rw [vv_eq_iSup_of_not_isMVtx hρH]
    exact iSup₂_le fun μ hμ => hZ ρ μ hρ hμ
  rw [Subgroup.commutator_le]
  intro v hv w hw
  exact ((mem_vvPerp_iff hKV).mp (hVU hv)).2 w hw

end CommCrit

end CFSG.Quasithin.MS93.S46
