module

public import CFSG.Quasithin.MS93.S4AM
public import CFSG.Quasithin.MS93.Sec2Two

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Amalgam

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem usup_smul (g : X.Universal) (δ ρ : Vtx X) :
    Usup X (g • δ) (g • ρ) = (Usup X δ ρ).map (MulAut.conj g).toMonoidHom := by
  rw [Usup, Usup, zv_smul, qv_smul, Subgroup.map_commutator]

theorem conjCl_map_conj {G : Type*} [Group G] (g : G) (H K : Subgroup G) :
    (conjCl H K).map (MulAut.conj g).toMonoidHom =
      conjCl (H.map (MulAut.conj g).toMonoidHom) (K.map (MulAut.conj g).toMonoidHom) := by
  simp only [conjCl, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup₂_le fun h hh => le_iSup₂_of_le (g * h * g⁻¹) ⟨h, hh, rfl⟩ ?_
    rw [map_conj_map_conj, map_conj_map_conj]
    simp [mul_assoc]
  · refine iSup₂_le fun h hh => ?_
    obtain ⟨h', hh', rfl⟩ := hh
    refine le_iSup₂_of_le h' hh' ?_
    rw [map_conj_map_conj, map_conj_map_conj]
    simp [mul_assoc]

theorem isStraight_smul (g : X.Universal) (α α' : Vtx X) :
    IsStraight X (g • α) (g • α') ↔ IsStraight X α α' := by
  have key : ∀ (g : X.Universal) (α α' : Vtx X),
      IsStraight X α α' → IsStraight X (g • α) (g • α') := by
    intro g α α' h i hi hlt
    rw [dist_smul] at hlt
    obtain ⟨x, hx, hxe⟩ := h i hi hlt
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · rw [geo_smul, stab_smul]
      exact conj_mem_map_conj hx
    · rw [geo_smul, geo_smul, ← hxe, smul_smul, smul_smul]
      simp [mul_assoc]
  refine ⟨fun h => ?_, key g α α'⟩
  have := key g⁻¹ _ _ h
  simpa [smul_smul] using this

end Amalgam

section PUSmul

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

namespace S4A

theorem L_normal (h : PUHyp M T L) : (L.subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer

theorem Uq_normal (h : PUHyp M T L) : ((Uq M T L).subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Uq_le h.L_le)).2 (le_normalizer_Uq h.le_normalizer)

theorem Dq_normal (h : PUHyp M T L) : ((Dq M L).subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer Dq_le).2 (le_normalizer_Dq h.le_normalizer)

theorem Zq_normal (h : PUHyp M T L) : ((Zq M L).subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer Zq_le).2 (le_normalizer_Zq h.le_normalizer)

end S4A

variable (h : PUHyp M T L)
include h

theorem ltil_smul (g : (puAmalgam h.le).Universal) (δ : Vtx (puAmalgam h.le)) :
    Ltil h.le L (g • δ) = (Ltil h.le L δ).map (MulAut.conj g).toMonoidHom :=
  puTrans_smul h.le (S4A.L_normal h) g δ

theorem uloc_smul (g : (puAmalgam h.le).Universal) (δ : Vtx (puAmalgam h.le)) :
    Uloc h.le L (g • δ) = (Uloc h.le L δ).map (MulAut.conj g).toMonoidHom :=
  puTrans_smul h.le (S4A.Uq_normal h) g δ

theorem dloc_smul (g : (puAmalgam h.le).Universal) (δ : Vtx (puAmalgam h.le)) :
    Dloc h.le L (g • δ) = (Dloc h.le L δ).map (MulAut.conj g).toMonoidHom :=
  puTrans_smul h.le (S4A.Dq_normal h) g δ

theorem vcirc_smul (g : (puAmalgam h.le).Universal) (δ : Vtx (puAmalgam h.le)) :
    Vcirc h.le L (g • δ) = (Vcirc h.le L δ).map (MulAut.conj g).toMonoidHom := by
  rw [Vcirc, Vcirc, show Vv _ (g • δ) = (Vv _ δ).map _ from vi_smul _ g δ 2,
    show puTrans h.le L (g • δ) = _ from ltil_smul h g δ, Subgroup.map_commutator]

theorem hloc_smul (g : (puAmalgam h.le).Universal) (δ : Vtx (puAmalgam h.le)) :
    Hloc h.le L (g • δ) = (Hloc h.le L δ).map (MulAut.conj g).toMonoidHom := by
  rw [Hloc, Hloc, vcirc_smul h, qv_smul, Subgroup.map_commutator]

theorem bloc_smul (g : (puAmalgam h.le).Universal) (δ : Vtx (puAmalgam h.le)) :
    Bloc h.le L (g • δ) = (Bloc h.le L δ).map (MulAut.conj g).toMonoidHom := by
  rw [Bloc, Bloc, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hL := ltil_smul h g δ
  have hV : Vv (puAmalgam h.le) (g • δ) = (Vv _ δ).map (MulAut.conj g).toMonoidHom :=
    vi_smul (puAmalgam h.le) g δ 2
  have hZ := zv_smul (puAmalgam h.le) g δ
  simp only [Ltil] at hL
  constructor
  · rintro ⟨hxV, hxl⟩
    refine ⟨g⁻¹ * x * g, ⟨?_, fun l hl => ?_⟩, by group⟩
    · rw [hV, mem_map_conj] at hxV
      exact hxV
    · have hl' : g * l * g⁻¹ ∈ puTrans h.le L (g • δ) := by
        rw [hL]
        exact conj_mem_map_conj hl
      have := hxl _ hl'
      rw [hZ, mem_map_conj] at this
      have hrw : g⁻¹ * ⁅x, g * l * g⁻¹⁆ * g = ⁅g⁻¹ * x * g, l⁆ := by
        simp only [commutatorElement_def]
        group
      rwa [hrw] at this
  · rintro ⟨y, ⟨hyV, hyl⟩, rfl⟩
    refine ⟨?_, fun l hl => ?_⟩
    · rw [hV]
      exact conj_mem_map_conj hyV
    · rw [hL, mem_map_conj] at hl
      have := hyl _ hl
      rw [hZ]
      have hrw : ⁅g * y * g⁻¹, l⁆ = g * ⁅y, g⁻¹ * l * g⁆ * g⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [hrw]
      exact conj_mem_map_conj this

theorem mem_nablaSet_smul (g : (puAmalgam h.le).Universal) (δ μ : Vtx (puAmalgam h.le)) :
    g • μ ∈ nablaSet h.le L (g • δ) ↔ μ ∈ nablaSet h.le L δ := by
  simp only [nablaSet, Set.mem_ofPred_eq, dist_smul, zv_smul, bloc_smul h]
  rw [Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective]

end PUSmul

section Vloc

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem isMVtx_of_dist_le_two {α ρ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hd : (puAmalgam h.le).treeGraph.dist α ρ ≤ 2) :
    IsMVtx _ ρ ∨ (puAmalgam h.le).treeGraph.Adj α ρ := by
  by_cases hρ : IsMVtx _ ρ
  · exact Or.inl hρ
  · right
    have hodd : ¬ Even ((puAmalgam h.le).treeGraph.dist α ρ) := by
      rw [even_dist_iff]
      tauto
    have hne : (puAmalgam h.le).treeGraph.dist α ρ ≠ 0 := fun h0 => hodd (h0 ▸ ⟨0, rfl⟩)
    have hne2 : (puAmalgam h.le).treeGraph.dist α ρ ≠ 2 := fun h2 => hodd (h2 ▸ ⟨1, rfl⟩)
    have h1 : (puAmalgam h.le).treeGraph.dist α ρ = 1 := by omega
    rcases (dist_le_one_iff _).mp h1.le with h0 | hadj
    · subst h0
      exact absurd hα hρ
    · exact hadj

theorem vv_le_qv (hb : 2 < critDist (puAmalgam h.le)) {α : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) : Vv _ α ≤ Qv _ α := by
  refine iSup₂_le fun ρ hρ => ?_
  rcases isMVtx_of_dist_le_two h hα hρ with hρM | hadj
  · rw [zv_of_isMVtx _ hρM]
    have := zm_le_qv_of_dist_lt _ hρM (by rw [tdist_comm]; exact lt_of_le_of_lt hρ hb)
    exact this
  · have hρH : ¬ IsMVtx _ ρ := by
      rw [isMVtx_iff_of_adj _ hadj] at hα
      exact hα
    rw [zv_of_not_isMVtx _ hρH]
    exact (zh_le_zm _ hadj).trans (zm_le_qv_self _ hα h.critDist_pos)

theorem zm_le_vv {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) : ZM _ α ≤ Vv _ α := by
  have : Zv (puAmalgam h.le) α ≤ Vv _ α :=
    le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam h.le) |
      (puAmalgam h.le).treeGraph.dist α ρ ≤ 2}) => Zv (puAmalgam h.le) ρ) α
      (by simp) le_rfl
  rwa [zv_of_isMVtx _ hα] at this

theorem stab_le_normalizer_vv (δ : Vtx (puAmalgam h.le)) :
    stab _ δ ≤ Subgroup.normalizer (Vv (puAmalgam h.le) δ : Set (puAmalgam h.le).Universal) :=
  stab_le_normalizer_of_smul _ (fun g ρ => vi_smul _ g ρ 2) δ

theorem stab_le_normalizer_ltil (δ : Vtx (puAmalgam h.le)) :
    stab _ δ ≤ Subgroup.normalizer (Ltil h.le L δ : Set (puAmalgam h.le).Universal) :=
  stab_le_normalizer_puTrans h.le (S4A.L_normal h) δ

theorem ltil_le_stab (δ : Vtx (puAmalgam h.le)) : Ltil h.le L δ ≤ stab _ δ :=
  puTrans_le_stab h.le L δ

theorem mem_bloc_iff (hb : 2 < critDist (puAmalgam h.le)) {δ : Vtx (puAmalgam h.le)}
    (hδ : IsMVtx _ δ) {x : (puAmalgam h.le).Universal} :
    x ∈ Bloc h.le L δ ↔ x ∈ Vv _ δ ∧ ∀ l ∈ Ltil h.le L δ, ⁅x, l⁆ ∈ ZM _ δ := by
  have hZ : Zv (puAmalgam h.le) δ = ZM _ δ := zv_of_isMVtx _ hδ
  have hVs : Vv (puAmalgam h.le) δ ≤ stab _ δ := (vv_le_qv h hb hδ).trans (qv_le_stab _ δ)
  have hLs := ltil_le_stab h δ
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) δ
  constructor
  · intro hx
    rw [Bloc] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => rw [← hZ]; exact hy
    | one => exact ⟨Subgroup.one_mem _, fun l _ => by simp⟩
    | mul a b _ _ iha ihb =>
      refine ⟨Subgroup.mul_mem _ iha.1 ihb.1, fun l hl => ?_⟩
      have hrw : ⁅a * b, l⁆ = a * ⁅b, l⁆ * a⁻¹ * ⁅a, l⁆ := by
        simp only [commutatorElement_def]
        group
      rw [hrw]
      exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hZn (hVs iha.1)) _).mp
        (ihb.2 l hl)) (iha.2 l hl)
    | inv a _ iha =>
      refine ⟨Subgroup.inv_mem _ iha.1, fun l hl => ?_⟩
      have hrw : ⁅a⁻¹, l⁆ = a⁻¹ * (⁅a, l⁆)⁻¹ * a⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [hrw]
      exact (Subgroup.mem_normalizer_iff.mp (hZn (hVs (Subgroup.inv_mem _ iha.1))) _).mp
        (Subgroup.inv_mem _ (iha.2 l hl))
  · rintro ⟨hxV, hxl⟩
    exact Subgroup.subset_closure ⟨hxV, fun l hl => hZ ▸ hxl l hl⟩

theorem bloc_le_vv (δ : Vtx (puAmalgam h.le)) : Bloc h.le L δ ≤ Vv _ δ := by
  rw [Bloc, Subgroup.closure_le]
  exact fun x hx => hx.1

theorem commutator_bloc_le (hb : 2 < critDist (puAmalgam h.le)) {δ : Vtx (puAmalgam h.le)}
    (hδ : IsMVtx _ δ) : ⁅Bloc h.le L δ, Ltil h.le L δ⁆ ≤ ZM _ δ := by
  rw [Subgroup.commutator_le]
  intro x hx l hl
  exact ((mem_bloc_iff h hb hδ).mp hx).2 l hl

theorem zm_le_bloc (hb : 2 < critDist (puAmalgam h.le)) {δ : Vtx (puAmalgam h.le)}
    (hδ : IsMVtx _ δ) : ZM _ δ ≤ Bloc h.le L δ := by
  intro x hx
  refine (mem_bloc_iff h hb hδ).mpr ⟨zm_le_vv h hδ hx, fun l hl => ?_⟩
  have hn := stab_le_normalizer_zm (puAmalgam h.le) δ (ltil_le_stab h δ hl)
  have hl' : l * x⁻¹ * l⁻¹ ∈ ZM _ δ := (Subgroup.mem_normalizer_iff.mp hn _).mp (inv_mem hx)
  have hrw : ⁅x, l⁆ = x * (l * x⁻¹ * l⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [hrw]
  exact Subgroup.mul_mem _ hx hl'

end Vloc

section Transport41

variable {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M)

theorem puTrans_sup {N N' : Subgroup G} (hN : N ≤ M) (hN' : N' ≤ M)
    (α : Vtx (puAmalgam hTM)) :
    puTrans hTM (N ⊔ N') α = puTrans hTM N α ⊔ puTrans hTM N' α := by
  rw [puTrans, puTrans, puTrans, Subgroup.subgroupOf_sup hN hN']
  rcases α with q | q
  · simp only [transN, Subgroup.map_sup]
  · simp [transN]

noncomputable abbrev Zloc (L : Subgroup G) (δ : Vtx (puAmalgam hTM)) :
    Subgroup (puAmalgam hTM).Universal :=
  puTrans hTM (Zq M L) δ

end Transport41

section Vertex41

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem zloc_smul (g : (puAmalgam h.le).Universal) (δ : Vtx (puAmalgam h.le)) :
    Zloc h.le L (g • δ) = (Zloc h.le L δ).map (MulAut.conj g).toMonoidHom :=
  puTrans_smul h.le (S4A.Zq_normal h) g δ

variable (hfull : IsSL3Full M T L)
include hfull

theorem xm_eq_zm {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) : XM _ α = ZM _ α := by
  rw [h.xm_eq hα, zm_eq_puTrans h.le hα, (s41_holds G M T L h hfull).2.2.1]

theorem stab_eq_ltil_sup_qv {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    stab _ α = Ltil h.le L α ⊔ Qv _ α := by
  rw [← puTrans_self h.le hα, h.qv_eq hα, Ltil, ← puTrans_sup h.le h.L_le (pCoreOf_le' M)]
  rw [← (s41_holds G M T L h hfull).1]

theorem zm_eq_uloc_sup_zloc {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    ZM _ α = Uloc h.le L α ⊔ Zloc h.le L α := by
  have hX := hfull.1
  rw [zm_eq_puTrans h.le hα, Uloc, Zloc, ← puTrans_sup h.le (Uq_le h.L_le) Zq_le, sup_comm,
    ← hX, (s41_holds G M T L h hfull).2.2.1]

theorem uloc_inf_zloc (α : Vtx (puAmalgam h.le)) : Uloc h.le L α ⊓ Zloc h.le L α = ⊥ := by
  obtain ⟨-, hZU, -⟩ := hfull
  rw [Uloc, Zloc, ← puTrans_inf, inf_comm, hZU, puTrans, Subgroup.bot_subgroupOf, transN_bot]

theorem zloc_le_centralizer_stab {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    Zloc h.le L α ≤ Subgroup.centralizer (stab _ α : Set (puAmalgam h.le).Universal) := by
  have hZM := (s41_holds G M T L h hfull).2.1
  have h1 : Zq M L ⊓ Subgroup.centralizer (M : Set G) = Zq M L := inf_of_le_left hZM
  have h2 := puTrans_inf_centralizer (hTM := h.le) (Zq_le (M := M) (L := L)) le_rfl
    (le_normalizer_Zq h.le_normalizer) Subgroup.le_normalizer hα
  rw [h1, puTrans_self h.le hα] at h2
  rw [Zloc, h2]
  exact inf_le_right

theorem zloc_le_zm {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    Zloc h.le L α ≤ ZM _ α := by
  rw [zm_eq_uloc_sup_zloc h hfull hα]
  exact le_sup_right

theorem uloc_le_zm {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    Uloc h.le L α ≤ ZM _ α := by
  rw [zm_eq_uloc_sup_zloc h hfull hα]
  exact le_sup_left

end Vertex41

section Cent

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem centHyp_of_S32 (h32 : S32) (h : PUHyp M T L) : CentHyp (puAmalgam h.le) := by
  have hC := (h32 G M T L h).1
  refine centHyp_of_edge _ (isMVtx_baseA _) (adj_baseA_baseB _) ?_
  rw [puAmalgam.qv_baseB, puAmalgam.zm_baseA, puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup
    h.pCore_le, ← hC, imM_inf_centralizer h.le T (normalClosureIn_le M _)]

end Cent

end CFSG.Quasithin.MS93
