module

public import CFSG.Quasithin.MS93.S46I461
public import CFSG.Quasithin.MS93.ASIrr
public import CFSG.Quasithin.MS93.Sec2Three

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement

section CritGen'

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

theorem exists_zv_le_zm_of_dist {x ρ : Vtx X} (hx : IsMVtx X x)
    (hρ : X.treeGraph.dist x ρ ≤ 2) :
    ∃ μ, IsMVtx X μ ∧ X.treeGraph.dist x μ ≤ 2 ∧ Zv X ρ ≤ ZM X μ := by
  by_cases hρM : IsMVtx X ρ
  · exact ⟨ρ, hρM, hρ, (zv_of_isMVtx X hρM).le⟩
  · have hodd : ¬ Even (X.treeGraph.dist x ρ) := by rw [even_dist_iff]; tauto
    have h1 : X.treeGraph.dist x ρ = 1 := by
      rcases (by omega : X.treeGraph.dist x ρ = 0 ∨ X.treeGraph.dist x ρ = 1 ∨
          X.treeGraph.dist x ρ = 2) with e | e | e
      · exact absurd (by rw [e]; exact ⟨0, rfl⟩) hodd
      · exact e
      · exact absurd (by rw [e]; exact ⟨1, rfl⟩) hodd
    have hadj : X.treeGraph.Adj x ρ := SimpleGraph.dist_eq_one_iff_adj.mp h1
    refine ⟨x, hx, by simp, ?_⟩
    rw [zv_of_not_isMVtx X hρM]
    exact zh_le_zm X hadj

theorem commutator_vv_le_of_critR (h : Hyp20 X) (hb4 : critDist X = 4) {x : Vtx X}
    (hx : IsMVtx X x) {K : Subgroup X.Universal}
    (hK : Vv X x ≤ Subgroup.normalizer (K : Set X.Universal))
    (hcr : ∀ μ ν : Vtx X, IsCritical X μ ν → geo X μ ν 2 = x → critR X μ ν ≤ K) :
    ⁅Vv X x, Vv X x⁆ ≤ K := by
  have hV : Vv X x = ⨆ ρ : {ρ : Vtx X // X.treeGraph.dist x ρ ≤ 2}, Zv X ρ.1 := by
    rw [show Vv X x = Vi X x 2 from rfl]
    unfold Vi
    exact iSup_subtype'
  have key : ∀ ρ ρ' : Vtx X, X.treeGraph.dist x ρ ≤ 2 → X.treeGraph.dist x ρ' ≤ 2 →
      ⁅Zv X ρ, Zv X ρ'⁆ ≤ K := by
    intro ρ ρ' hρ hρ'
    obtain ⟨μ, hμ, hdμ, hle⟩ := exists_zv_le_zm_of_dist hx hρ
    obtain ⟨μ', hμ', hdμ', hle'⟩ := exists_zv_le_zm_of_dist hx hρ'
    refine (Subgroup.commutator_mono hle hle').trans ?_
    by_cases hQ : ZM X μ ≤ Qv X μ'
    · rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
        (hQ.trans (Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv X h hμ')))]
      exact bot_le
    · have htri := dist_triangle X μ x μ'
      rw [tdist_comm X μ x] at htri
      have hd4 : X.treeGraph.dist μ μ' = 4 := by
        by_contra hne
        exact hQ (zm_le_qv_of_dist_le_three hb4 hμ (by omega))
      have hc : IsCritical X μ μ' := ⟨hμ, by rw [hd4, hb4], hQ⟩
      have hgeo : x = geo X μ μ' 2 := by
        refine eq_geo_of_dist X (by rw [tdist_comm]; omega) ?_
        rw [tdist_comm X μ x]
        omega
      exact hcr μ μ' hc hgeo.symm
  have hKV : (⨆ ρ : {ρ : Vtx X // X.treeGraph.dist x ρ ≤ 2}, Zv X ρ.1) ≤
      Subgroup.normalizer (K : Set X.Universal) := hV ▸ hK
  rw [hV]
  refine commutator_iSup_le_of (fun ρ => ?_) hKV
  rw [Subgroup.commutator_comm]
  exact commutator_iSup_le_of (fun ρ' => key ρ'.1 ρ.1 ρ'.2 ρ.2) hKV

end CritGen'

section Gen23

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem gen23At_of {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) : Gen23At (puAmalgam h.le) α β := by
  intro x hxβ hxα
  set C := Subgroup.closure {y | ∃ k ∈ stab (puAmalgam h.le) α, k * x * k⁻¹ = y} with hCdef
  have hxs : x ∈ stab (puAmalgam h.le) α := qv_le_stab_of_adj _ hαβ.symm hxβ
  have hCs : C ≤ stab (puAmalgam h.le) α := by
    rw [hCdef, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hxs) (Subgroup.inv_mem _ hk)
  have hCn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (C : Set _) := by
    refine le_normalizer_of_map_conj_le fun g hg => ?_
    rw [hCdef, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine Subgroup.subset_closure ⟨g * k, Subgroup.mul_mem _ hg hk, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, _root_.mul_inv_rev]
    group
  have hxC : x ∈ C := Subgroup.subset_closure ⟨1, Subgroup.one_mem _, by group⟩
  have hLC := ltil_le_of_normal h hfull hα hαβ hCs hCn (Subgroup.zpowers_le.mpr hxC)
    (Subgroup.zpowers_le.mpr hxβ) (fun hle => hxα (hle (Subgroup.mem_zpowers x)))
  apply le_antisymm
  · rw [stab_eq_ltil_sup_qv_adj h hfull hα hαβ]
    exact sup_le_sup_right hLC _
  · exact sup_le hCs (qv_le_stab_of_adj _ hαβ.symm)

theorem centHyp_of_gen23 : CentHyp (puAmalgam h.le) := by
  obtain ⟨β, hβ⟩ := exists_adj (puAmalgam h.le) (baseA _)
  exact ms23_step1 _ h.hyp20 (isMVtx_baseA _) hβ (gen23At_of h hfull (isMVtx_baseA _) hβ)

omit hfull in
theorem not_qv_le_qv_of_adj {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) : ¬ Qv (puAmalgam h.le) β ≤ Qv _ α := by
  intro hle
  apply not_stab_le_normalizer_qv _ h.hyp20 hα hαβ
  rw [le_antisymm hle (qv_le_qv _ h.hyp20 hα hαβ)]
  exact stab_le_normalizer_qv _ α

theorem usup_eq_commutator_uloc {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    Usup (puAmalgam h.le) α β = ⁅Uloc h.le L α, Qv _ β⁆ := by
  rw [Usup, zv_of_isMVtx _ hα]
  exact commutator_zm_eq_uloc h hfull hα (qv_le_stab_of_adj _ hαβ.symm)

theorem usup_le_uloc {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) : Usup (puAmalgam h.le) α β ≤ Uloc h.le L α := by
  rw [usup_eq_commutator_uloc h hfull hα hαβ]
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp ((qv_le_stab_of_adj _ hαβ.symm).trans
    (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α))

end Gen23

theorem two_le_card_field {F : Type} [Field F] [Fintype F] : 2 ≤ Fintype.card F :=
  Fintype.one_lt_card

theorem card_field_lt_pow_three {F : Type} [Field F] [Fintype F] :
    Fintype.card F < Fintype.card F ^ 3 := by
  have hq2 := two_le_card_field (F := F)
  calc Fintype.card F = Fintype.card F ^ 1 := (pow_one _).symm
    _ < Fintype.card F ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)

section CardUsup

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem card_usup_eq_or {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    Nat.card ↥(Usup (puAmalgam h.le) α β) = Fintype.card F ∨
      Nat.card ↥(Usup (puAmalgam h.le) α β) = Fintype.card F ^ 2 := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  rw [usup_eq_commutator_uloc h hfull hα hαβ]
  obtain ⟨d, hd, hcard⟩ := card_commutator_uloc_le h hφ hα hαβ le_rfl
  rw [hcard]
  interval_cases d
  · exfalso
    have hbot : ⁅Uloc h.le L α, Qv (puAmalgam h.le) β⁆ = ⊥ := by
      rw [← Subgroup.card_eq_one, hcard, pow_zero]
    apply not_qv_le_qv_of_adj h hα hαβ
    intro x hx
    refine stab_inf_centralizer_uloc_le_qv h hφ hα ⟨qv_le_stab_of_adj _ hαβ.symm hx, ?_⟩
    exact Subgroup.le_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot) hx
  · exact Or.inl (pow_one _)
  · exact Or.inr rfl

omit hφ in
theorem card_usup_eq_card_usup {α β α₁ β₁ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) (hα₁ : IsMVtx _ α₁)
    (hα₁β₁ : (puAmalgam h.le).treeGraph.Adj α₁ β₁) :
    Nat.card ↥(Usup (puAmalgam h.le) α₁ β₁) = Nat.card ↥(Usup (puAmalgam h.le) α β) := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_of_isMVtx _ hα hαβ hα₁ hα₁β₁
  rw [usup_smul, Subgroup.card_map_of_injective (MulAut.conj g).injective]

omit hφ in
theorem finite_usup {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) : Finite ↥(Usup (puAmalgam h.le) α β) := by
  have := finite_stab h hα
  refine Finite.of_injective _ (Subgroup.inclusion_injective (?_ : Usup _ α β ≤ stab _ α))
  rw [Usup, zv_of_isMVtx _ hα]
  exact (Subgroup.le_normalizer_iff_commutator_le_left.mp ((qv_le_stab_of_adj _ hαβ.symm).trans
    (stab_le_normalizer_zm _ α))).trans ((zm_le_qv_self _ hα h.critDist_pos).trans
      (qv_le_stab _ α))

end CardUsup

section CardQ

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (hC : CentHyp (puAmalgam h.le))
  (hq : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Nat.card ↥(Usup (puAmalgam h.le) δ ρ) = Fintype.card F)
include h hφ hC hq

theorem critR_eq_usup {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    critR (puAmalgam h.le) α α' = Usup _ α (geo _ α α' 1) := by
  have hb0 := h.critDist_pos
  have hβ := adj_geo_one_of_isCritical _ hb0 hc
  have hle : critR (puAmalgam h.le) α α' ≤ Usup _ α (geo _ α α' 1) := by
    rw [critR, Usup, zv_of_isMVtx _ hc.1]
    exact Subgroup.commutator_mono le_rfl (zm_le_qv_geo_one _ h.hyp20 hb0 hc)
  have := finite_usup h hc.1 hβ
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hq α _ hc.1 hβ]
  rcases crit_type h hφ hC hc with ⟨-, hr⟩ | ⟨-, hr⟩ | ⟨-, hr, -⟩ <;> rw [hr]
  exact Nat.le_self_pow two_ne_zero _

theorem zc23_of {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    ∃ Z : Subgroup (puAmalgam h.le).Universal, Z ≤ XM _ α' ∧ ¬ Z ≤ Qv _ α ∧
      ∀ Y : Subgroup (puAmalgam h.le).Universal, Y ≤ Qv _ (geo _ α' α 1) →
        CFSG.Open.IsElemAbelian 2 (Y ⊔ XM _ α) →
          ⁅Y, Z⁆ ≤ ⁅XM _ α, XM _ α'⁆ ⊔ ⁅Y, XM _ α' ⊓ Qv _ α⁆ := by
  have hb0 := h.critDist_pos
  have h20 := h.hyp20
  have hc' := ms22_iii _ h20 hb0 hC hc
  refine ⟨ZM _ α', zm_le_xm _ h20 hb0 hc'.1, hc'.2.2, fun Y hY _ => le_sup_of_le_left ?_⟩
  calc ⁅Y, ZM (puAmalgam h.le) α'⁆ ≤ ⁅Qv _ (geo _ α' α 1), ZM _ α'⁆ :=
        Subgroup.commutator_mono hY le_rfl
    _ = Usup _ α' (geo _ α' α 1) := by
        rw [Usup, zv_of_isMVtx _ hc'.1, Subgroup.commutator_comm]
    _ = critR _ α' α := (critR_eq_usup h hφ hC hq hc').symm
    _ = ⁅ZM (puAmalgam h.le) α, ZM _ α'⁆ := by rw [critR, Subgroup.commutator_comm]
    _ ≤ ⁅XM (puAmalgam h.le) α, XM _ α'⁆ :=
        Subgroup.commutator_mono (zm_le_xm _ h20 hb0 hc.1) (zm_le_xm _ h20 hb0 hc'.1)

omit hC in
theorem usup_not_normal {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    ¬ stab _ α ≤ Subgroup.normalizer (Usup (puAmalgam h.le) α β : Set _) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  intro hn
  have hq2 := two_le_card_field (F := F)
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hα
  have hcard := hq α β hα hαβ
  rcases eq_or_eq_of_natural hψs statedSL3_transitive hψ bot_le (usup_le_uloc h hfull hα hαβ)
    hn with he | he
  · rw [he, Subgroup.card_bot] at hcard
    omega
  · rw [he, card_eq_of_natural hψ, Nat.card_eq_fintype_card] at hcard
    have := card_field_lt_pow_three (F := F)
    omega

theorem stab_geo_two_le_normalizer_usup (hb4 : critDist (puAmalgam h.le) = 4)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    stab _ (geo _ α α' 2) ≤
      Subgroup.normalizer (Usup (puAmalgam h.le) α (geo _ α α' 1) : Set _) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 := h.critDist_pos
  have hαβ := adj_geo_one_of_isCritical _ hb0 hc
  have hAT : Qv (puAmalgam h.le) (geo _ α α' 1) ≤
      Subgroup.normalizer (Usup (puAmalgam h.le) α (geo _ α α' 1) : Set _) := by
    refine le_normalizer_of_map_conj_le fun t ht => ?_
    rw [Usup, zv_of_isMVtx _ hc.1, Subgroup.map_commutator,
      map_conj_eq_of_mem_normalizer
        (stab_le_normalizer_zm _ α (qv_le_stab_of_adj _ hαβ.symm ht)),
      map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer ht)]
  have hAc : ∀ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α δ' →
      geo _ α δ' 1 = geo _ α α' 1 →
        Usup (puAmalgam h.le) α (geo _ α α' 1) ≤ ⁅XM _ α, XM _ δ'⁆ := by
    intro δ' hcδ hgeo
    rw [← hgeo, ← critR_eq_usup h hφ hC hq hcδ, critR]
    exact Subgroup.commutator_mono (zm_le_xm _ h.hyp20 hb0 hc.1)
      (zm_le_xm _ h.hyp20 hb0 (hcδ.isMVtx_right _ h.hyp20))
  obtain ⟨-, h23⟩ := ms23 _ h.hyp20 hc.1 hαβ (by omega) (gen23At_of h hfull hc.1 hαβ)
    (fun α₁ hc₁ _ => zc23_of h hφ hC hq hc₁) hAT (usup_not_normal h hφ hq hc.1 hαβ) hAc
  exact h23 α' hc rfl

theorem usup_le_dloc (hb4 : critDist (puAmalgam h.le) = 4)
    (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
      Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    Usup (puAmalgam h.le) α (geo _ α α' 1) ≤ Dloc h.le L (geo _ α α' 2) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 := h.critDist_pos
  have hαβ := adj_geo_one_of_isCritical _ hb0 hc
  have hγ : IsMVtx _ (geo (puAmalgam h.le) α α' 2) := isMVtx_geo_two' hb4 hc
  have hβγ := adj_geo_crit hb4 hc (i := 1) (by norm_num)
  set U := Usup (puAmalgam h.le) α (geo _ α α' 1) with hUdef
  have hUZ : U ≤ ZM _ (geo (puAmalgam h.le) α α' 2) :=
    (h464 α _ hc.1 hαβ).trans (zh_le_zm _ hβγ.symm)
  have hUQ : U ≤ Qv _ (geo (puAmalgam h.le) α α' 2) := hUZ.trans (zm_le_qv_self _ hγ hb0)
  have hn := stab_geo_two_le_normalizer_usup h hφ hC hq hb4 hc
  have hUn := stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) (geo (puAmalgam h.le) α α' 2)
  have hYn : stab _ (geo (puAmalgam h.le) α α' 2) ≤
      Subgroup.normalizer ((U ⊓ Uloc h.le L (geo _ α α' 2) : Subgroup _) : Set _) :=
    (le_inf hn hUn).trans Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hγ
  have hLs := ltil_le_stab h (geo (puAmalgam h.le) α α' 2)
  have hcomm : ⁅U, Ltil h.le L (geo _ α α' 2)⁆ ≤ U ⊓ Uloc h.le L (geo _ α α' 2) := by
    refine le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hn)) ?_
    refine (Subgroup.commutator_mono hUZ le_rfl).trans ?_
    rw [commutator_zm_eq_uloc h hfull hγ hLs]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hUn)
  rcases eq_or_eq_of_natural hψs statedSL3_transitive hψ bot_le inf_le_right hYn with hY | hY
  · exact le_dloc_of_commutator_le h hγ hUQ ((hcomm.trans hY.le).trans bot_le)
  · exfalso
    have := finite_usup h hc.1 hαβ
    have h1 := Subgroup.card_le_of_le (inf_le_left : U ⊓ Uloc h.le L (geo _ α α' 2) ≤ U)
    rw [hY, card_eq_of_natural hψ, hq α _ hc.1 hαβ, Nat.card_eq_fintype_card] at h1
    have := card_field_lt_pow_three (F := F)
    omega

theorem commutator_vv_le_dloc_of_card (hb4 : critDist (puAmalgam h.le) = 4)
    (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
      Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
    {x : Vtx (puAmalgam h.le)} (hx : IsMVtx _ x) :
    ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ Dloc h.le L x := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  refine commutator_vv_le_of_critR h.hyp20 hb4 hx (((vv_le_qv h hb hx).trans (qv_le_stab _ x)).trans
    (stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) x)) fun μ ν hc hgeo => ?_
  rw [critR_eq_usup h hφ hC hq hc, ← hgeo]
  exact usup_le_dloc h hφ hC hq hb4 h464 hc

theorem commutator_vv_inf_qv_critGen_le_zm (hb4 : critDist (puAmalgam h.le) = 4)
    {x y : Vtx (puAmalgam h.le)} (hy : IsMVtx _ y)
    (hd : (puAmalgam h.le).treeGraph.dist x y = 2) :
    ⁅Vv (puAmalgam h.le) x ⊓ Qv _ y, critGen _ x y⁆ ≤ ZM _ x := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 := h.critDist_pos
  have h20 := h.hyp20
  set β := geo (puAmalgam h.le) x y 1
  have hxβ : (puAmalgam h.le).treeGraph.Adj x β := adj_geo_one _ (by omega)
  have hβy : (puAmalgam h.le).treeGraph.Adj β y := by
    have := adj_geo (puAmalgam h.le) (u := x) (w := y) (i := 1) (by omega)
    rwa [geo_of_le _ (by omega : (puAmalgam h.le).treeGraph.dist x y ≤ 1 + 1)] at this
  have hWs : critGen (puAmalgam h.le) x y ≤ stab _ x :=
    (critGen_le_vv hb4 x y).trans ((vv_le_qv h hb hy).trans
      ((qv_le_qv _ h20 hy hβy.symm).trans (qv_le_stab_of_adj _ hxβ.symm)))
  rw [Subgroup.commutator_comm, critGen, iSup_subtype']
  refine commutator_iSup_le_of (fun δ => ?_) ?_
  · obtain ⟨δ, hc, hgeo⟩ := δ
    have hc' := ms22_iii _ h20 hb0 hC hc
    have hyε : (puAmalgam h.le).treeGraph.Adj y (geo _ δ x 1) := by
      rw [geo_rev_one hb4 hc, ← hgeo]
      exact adj_geo_crit hb4 hc (i := 2) (by norm_num)
    rw [Subgroup.commutator_comm]
    calc ⁅Vv (puAmalgam h.le) x ⊓ Qv _ y, ZM _ δ⁆ ≤ ⁅Qv _ (geo (puAmalgam h.le) δ x 1), ZM _ δ⁆ :=
          Subgroup.commutator_mono (inf_le_right.trans (qv_le_qv _ h20 hy hyε)) le_rfl
      _ = Usup _ δ (geo (puAmalgam h.le) δ x 1) := by
          rw [Usup, zv_of_isMVtx _ hc'.1, Subgroup.commutator_comm]
      _ = critR _ δ x := (critR_eq_usup h hφ hC hq hc').symm
      _ = ⁅ZM (puAmalgam h.le) x, ZM _ δ⁆ := by rw [critR, Subgroup.commutator_comm]
      _ ≤ ZM _ x := Subgroup.le_normalizer_iff_commutator_le_left.mp
          ((zm_le_stab_of_isCritical _ h20 hb0 hc).trans (stab_le_normalizer_zm _ x))
  · rw [← iSup_subtype' (f := fun δ (_ : δ ∈ {δ : Vtx (puAmalgam h.le) |
      IsCritical (puAmalgam h.le) x δ ∧ geo (puAmalgam h.le) x δ 2 = y}) =>
        ZM (puAmalgam h.le) δ), ← critGen]
    exact hWs.trans (stab_le_normalizer_zm _ x)

end CardQ

section Offender

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hC : CentHyp (puAmalgam h.le))
include h hC

omit hC in
private theorem stab_le_normalizer_bloc₀ (δ : Vtx (puAmalgam h.le)) :
    stab _ δ ≤ Subgroup.normalizer (Bloc h.le L δ : Set _) :=
  le_normalizer_of_map_conj_le fun g hg => by rw [← bloc_smul h g δ, (mem_stab _).mp hg]

theorem exists_offender_bloc (h43 : S43) (hmin : PUMin M T L) (hfull : IsSL3Full M T L)
    (hb4 : critDist (puAmalgam h.le) = 4)
    (h463 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x → ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ ZM _ x)
    (hcomm : ∀ x y : Vtx (puAmalgam h.le), IsMVtx _ x → IsMVtx _ y →
      (puAmalgam h.le).treeGraph.dist x y = 2 →
        ⁅Vv (puAmalgam h.le) x ⊓ Qv _ y, critGen _ x y⁆ ≤ Bloc h.le L x)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    (∃ As, IsOffenderOn (puAmalgam h.le) α (Bloc h.le L α) As) ∨
      (∃ As, IsOffenderOn (puAmalgam h.le) (geo _ α α' 2) (Bloc h.le L (geo _ α α' 2)) As) := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  set γ := geo (puAmalgam h.le) α α' 2 with hγdef
  set β := geo (puAmalgam h.le) α α' 1 with hβdef
  have hγ : IsMVtx _ γ := isMVtx_geo_two' hb4 hc
  have hd : (puAmalgam h.le).treeGraph.dist α γ = 2 := dist_geo_crit hb4 hc (by omega)
  have hd' : (puAmalgam h.le).treeGraph.dist γ α = 2 := by rw [tdist_comm]; exact hd
  have hαβ : (puAmalgam h.le).treeGraph.Adj α β := adj_geo_one_of_isCritical _ hb0 hc
  have hβγ : (puAmalgam h.le).treeGraph.Adj β γ := adj_geo_crit hb4 hc (i := 1) (by omega)
  have hVαγ : ¬ Vv (puAmalgam h.le) α ≤ Qv _ γ := by
    have := h43 G M T L h hmin hb hfull α α' hc
    rwa [geo_rev_two hb4 hc] at this
  have hW₂ : ¬ critGen (puAmalgam h.le) γ α ≤ Qv _ γ := fun hle =>
    hVαγ ((vv_le_critGen_sup h20 hC hb4 hc.1 hd').trans (sup_le hle le_rfl))
  obtain ⟨μ, hcμ, hgeoμ⟩ : ∃ μ, IsCritical (puAmalgam h.le) γ μ ∧
      geo (puAmalgam h.le) γ μ 2 = α := by
    by_contra hno
    apply hW₂
    refine iSup₂_le fun δ hδ => (hno ⟨δ, hδ⟩).elim
  have hVγα : ¬ Vv (puAmalgam h.le) γ ≤ Qv _ α := by
    have := h43 G M T L h hmin hb hfull γ μ hcμ
    rwa [geo_rev_two hb4 hcμ, hgeoμ] at this
  have hW₁ : ¬ critGen (puAmalgam h.le) α γ ≤ Qv _ α := fun hle =>
    hVγα ((vv_le_critGen_sup h20 hC hb4 hγ hd).trans (sup_le hle le_rfl))
  have hZγα : ZM (puAmalgam h.le) γ ≤ Qv _ α := zm_le_qv_of_dist_le_three hb4 hγ (by omega)
  have hZαγ : ZM (puAmalgam h.le) α ≤ Qv _ γ := zm_le_qv_of_dist_le_three hb4 hc.1 (by omega)
  have hsqγ : ∀ a ∈ Vv (puAmalgam h.le) γ, a ^ 2 ∈ Qv _ α := fun a ha =>
    hZγα (h463 γ hγ (sq_mem_commutator_vv h hb0 ha))
  have hcomγ : ∀ a ∈ Vv (puAmalgam h.le) γ, ∀ b ∈ Vv (puAmalgam h.le) γ, ⁅a, b⁆ ∈ Qv _ α :=
    fun a ha b hb' => hZγα (h463 γ hγ (Subgroup.commutator_mem_commutator ha hb'))
  have hsqα : ∀ a ∈ Vv (puAmalgam h.le) α, a ^ 2 ∈ Qv _ γ := fun a ha =>
    hZαγ (h463 α hc.1 (sq_mem_commutator_vv h hb0 ha))
  have hcomα : ∀ a ∈ Vv (puAmalgam h.le) α, ∀ b ∈ Vv (puAmalgam h.le) α, ⁅a, b⁆ ∈ Qv _ γ :=
    fun a ha b hb' => hZαγ (h463 α hc.1 (Subgroup.commutator_mem_commutator ha hb'))
  have hfinα := finite_stab h hc.1
  have hfinγ := finite_stab h hγ
  have hβs : Qv (puAmalgam h.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  have hβs' : Qv (puAmalgam h.le) β ≤ stab _ γ := qv_le_stab_of_adj _ hβγ
  have hVγβ : Vv (puAmalgam h.le) γ ≤ Qv _ β :=
    (vv_le_qv h hb hγ).trans (qv_le_qv _ h20 hγ hβγ.symm)
  have hVαβ : Vv (puAmalgam h.le) α ≤ Qv _ β :=
    (vv_le_qv h hb hc.1).trans (qv_le_qv _ h20 hc.1 hαβ)
  have hVαs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hc.1).trans (qv_le_stab _ α)
  have hVγs : Vv (puAmalgam h.le) γ ≤ stab _ γ := (vv_le_qv h hb hγ).trans (qv_le_stab _ γ)
  have hfinVα : Finite ↥(Vv (puAmalgam h.le) α) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hVαs)
  have hfinVγ : Finite ↥(Vv (puAmalgam h.le) γ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hVγs)
  have hb1 : (Qv (puAmalgam h.le) α).relIndex (Vv _ γ) ≤
      (Qv (puAmalgam h.le) α).relIndex (critGen _ α γ) :=
    relIndex_le_of_le_sup (S := stab _ α) (hVγβ.trans hβs)
      (((critGen_le_vv hb4 α γ).trans hVγβ).trans hβs) (qv_le_stab _ α)
      (stab_le_normalizer_qv _ α) (vv_le_critGen_sup h20 hC hb4 hγ hd)
  have ha1 : (Qv (puAmalgam h.le) γ).relIndex (Vv _ α) ≤
      (Qv (puAmalgam h.le) γ).relIndex (critGen _ γ α) :=
    relIndex_le_of_le_sup (S := stab _ γ) (hVαβ.trans hβs')
      (((critGen_le_vv hb4 γ α).trans hVαβ).trans hβs') (qv_le_stab _ γ)
      (stab_le_normalizer_qv _ γ) (vv_le_critGen_sup h20 hC hb4 hc.1 hd')
  by_cases hab : (Qv (puAmalgam h.le) γ).relIndex (Vv _ α) ≤
      (Qv (puAmalgam h.le) α).relIndex (Vv _ γ)
  · left
    have hWs : critGen (puAmalgam h.le) α γ ≤ stab _ α :=
      ((critGen_le_vv hb4 α γ).trans hVγβ).trans hβs
    have hBn := stab_le_normalizer_bloc₀ h (L := L) α
    refine ⟨critGen _ α γ, ⟨β, hαβ, (critGen_le_vv hb4 α γ).trans hVγβ⟩, hW₁,
      fun a ha => hsqγ a (critGen_le_vv hb4 α γ ha),
      fun a ha b hb' => hcomγ a (critGen_le_vv hb4 α γ ha) b (critGen_le_vv hb4 α γ hb'),
      (Vv _ α ⊓ Qv _ γ) ⊔ Bloc h.le L α, le_sup_right, sup_le inf_le_left (bloc_le_vv h α),
      S4A.commutator_sup_le_of (hcomm α γ hc.1 hγ hd)
        (Subgroup.le_normalizer_iff_commutator_le_left.mp (hWs.trans hBn))
        (inf_le_left.trans (hVαs.trans hBn)) ((bloc_le_vv h α).trans (hVαs.trans hBn)), ?_⟩
    refine (Subgroup.relIndex_le_of_le_left le_sup_left (by
      rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)).trans ?_
    rw [Subgroup.inf_relIndex_left]
    exact hab.trans hb1
  · right
    have hWs : critGen (puAmalgam h.le) γ α ≤ stab _ γ :=
      ((critGen_le_vv hb4 γ α).trans hVαβ).trans hβs'
    have hBn := stab_le_normalizer_bloc₀ h (L := L) γ
    refine ⟨critGen _ γ α, ⟨β, hβγ.symm, (critGen_le_vv hb4 γ α).trans hVαβ⟩, hW₂,
      fun a ha => hsqα a (critGen_le_vv hb4 γ α ha),
      fun a ha b hb' => hcomα a (critGen_le_vv hb4 γ α ha) b (critGen_le_vv hb4 γ α hb'),
      (Vv _ γ ⊓ Qv _ α) ⊔ Bloc h.le L γ, le_sup_right, sup_le inf_le_left (bloc_le_vv h γ),
      S4A.commutator_sup_le_of (hcomm γ α hγ hc.1 hd')
        (Subgroup.le_normalizer_iff_commutator_le_left.mp (hWs.trans hBn))
        (inf_le_left.trans (hVγs.trans hBn)) ((bloc_le_vv h γ).trans (hVγs.trans hBn)), ?_⟩
    refine (Subgroup.relIndex_le_of_le_left le_sup_left (by
      rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)).trans ?_
    rw [Subgroup.inf_relIndex_left]
    exact (le_of_lt (not_le.mp hab)).trans ha1

end Offender

section I465

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem uloc_inf_dloc_eq_bot (x : Vtx (puAmalgam h.le)) : Uloc h.le L x ⊓ Dloc h.le L x = ⊥ := by
  have hUD : Uq M T L ⊓ Dq M L = ⊥ := by
    rw [h.Uq_inf_Dq, ← h.Uq_inf_Zq, inf_comm]
    exact hφ.2.2.2.1
  rw [Uloc, Dloc, ← puTrans_inf, hUD, puTrans, Subgroup.bot_subgroupOf, transN_bot]

theorem card_usup_eq_sq (h43 : S43) (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (h462 : ∀ (x : Vtx (puAmalgam h.le)) (As : Subgroup (puAmalgam h.le).Universal),
      IsMVtx _ x → IsOffenderOn (puAmalgam h.le) x (Bloc h.le L x) As →
        ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ Uloc h.le L x)
    (h463 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x → ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ ZM _ x)
    (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
      Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
    {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    Nat.card ↥(Usup (puAmalgam h.le) α β) = Fintype.card F ^ 2 := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hC := centHyp_of_gen23 h hfull
  rcases card_usup_eq_or h hφ hα hαβ with hq1 | hq2
  · exfalso
    have hq : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
        Nat.card ↥(Usup (puAmalgam h.le) δ ρ) = Fintype.card F := fun δ ρ hδ hδρ =>
      (card_usup_eq_card_usup h hα hαβ hδ hδρ).trans hq1
    have hb : 2 < critDist (puAmalgam h.le) := by omega
    obtain ⟨α', hc⟩ := exists_isCritical_of_isMVtx _ h.hyp20 hα
    have hcomm : ∀ x y : Vtx (puAmalgam h.le), IsMVtx _ x → IsMVtx _ y →
        (puAmalgam h.le).treeGraph.dist x y = 2 →
          ⁅Vv (puAmalgam h.le) x ⊓ Qv _ y, critGen _ x y⁆ ≤ Bloc h.le L x :=
      fun x y hx hy hd => (commutator_vv_inf_qv_critGen_le_zm h hφ hC hq hb4 hy hd).trans
        (zm_le_bloc h hb hx)
    have key : ∀ (x : Vtx (puAmalgam h.le)) (As : Subgroup (puAmalgam h.le).Universal),
        IsMVtx _ x → IsOffenderOn (puAmalgam h.le) x (Bloc h.le L x) As → False := by
      intro x As hx hA
      apply commutator_vv_ne_bot h hC h43 hmin hfull hb4 hx
      rw [eq_bot_iff, ← uloc_inf_dloc_eq_bot h hφ x]
      exact le_inf (h462 x As hx hA) (commutator_vv_le_dloc_of_card h hφ hC hq hb4 h464 hx)
    rcases exists_offender_bloc h hC h43 hmin hfull hb4 h463 hcomm hc with ⟨As, hA⟩ | ⟨As, hA⟩
    · exact key α As hα hA
    · exact key _ As (isMVtx_geo_two' hb4 hc) hA
  · exact hq2

theorem card_uloc_inf_centralizer_qv
    (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
      Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
    {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
    (hsq : Nat.card ↥(Usup (puAmalgam h.le) α β) = Fintype.card F ^ 2) :
    Nat.card ↥(Uloc h.le L α ⊓ Subgroup.centralizer (Qv (puAmalgam h.le) β : Set _)) =
      Fintype.card F ^ 2 := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hα
  have hTs : Qv (puAmalgam h.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  have hq2 := two_le_card_field (F := F)
  have hU := card_eq_of_natural hψ
  rw [Nat.card_eq_fintype_card (α := F)] at hU
  have hfinS := finite_stab h hα
  have hfinU : Finite ↥(Uloc h.le L α) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (puTrans_le_stab h.le _ α))
  set C := Uloc h.le L α ⊓ Subgroup.centralizer (Qv (puAmalgam h.le) β : Set _) with hCdef
  have hCU : C ≤ Uloc h.le L α := inf_le_left
  have hfinC : Finite ↥C := Finite.of_injective _ (Subgroup.inclusion_injective hCU)
  have hCcard : Nat.card ↥C =
      Fintype.card F ^ Module.finrank F (fixN (natImage ψ (Qv (puAmalgam h.le) β))) := by
    rw [hCdef, card_inf_centralizer_eq hψ hTs, card_fixN, Nat.card_eq_fintype_card]
  have hle : Usup (puAmalgam h.le) α β ≤ C :=
    le_inf (usup_le_uloc h hfull hα hαβ) ((h464 α β hα hαβ).trans (zh_le_centralizer _ β))
  have h1 : Fintype.card F ^ 2 ≤ Nat.card ↥C := hsq ▸ Subgroup.card_le_of_le hle
  have hne : C ≠ Uloc h.le L α := by
    intro he
    have hbot : Usup (puAmalgam h.le) α β = ⊥ := by
      rw [usup_eq_commutator_uloc h hfull hα hαβ, Subgroup.commutator_eq_bot_iff_le_centralizer,
        ← he]
      exact inf_le_right
    rw [hbot, Subgroup.card_bot] at hsq
    nlinarith
  have h2 : Nat.card ↥C < Fintype.card F ^ 3 := by
    rw [← hU]
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hCU) fun heq => hne ?_
    exact Subgroup.eq_of_le_of_card_ge hCU heq.ge
  rw [hCcard] at h1 h2 ⊢
  have hf2 := (Nat.pow_le_pow_iff_right (by omega)).mp h1
  have hf3 := (Nat.pow_lt_pow_iff_right (by omega)).mp h2
  rw [show Module.finrank F (fixN (natImage ψ (Qv (puAmalgam h.le) β))) = 2 by omega]

omit h hφ in
theorem relIndex_sup_of_le_of_comm {𝔾 : Type*} [Group 𝔾] {A B H K : Subgroup 𝔾}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hH : H ≤ A) (hK : K ≤ A)
    (hKB : K ≤ B) : B.relIndex (H ⊔ K) = B.relIndex H := by
  have hn : (B.subgroupOf A).Normal := ⟨fun n hn g => by
    have e : g * n * g⁻¹ = n := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcomm g g.2 n n.2, mul_inv_cancel_right]
    rw [e]
    exact hn⟩
  rw [← Subgroup.relIndex_subgroupOf (sup_le hH hK), ← Subgroup.relIndex_subgroupOf hH,
    Subgroup.subgroupOf_sup hH hK,
    ← Subgroup.relIndex_sup_right (H := H.subgroupOf A ⊔ K.subgroupOf A) (K := B.subgroupOf A),
    ← Subgroup.relIndex_sup_right (H := H.subgroupOf A) (K := B.subgroupOf A)]
  congr 1
  rw [sup_assoc, sup_eq_right.mpr (show K.subgroupOf A ≤ B.subgroupOf A from fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hKB (Subgroup.mem_subgroupOf.mp hx)))]

theorem relIndex_zh_zm
    (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
      Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
    {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
    (hsq : Nat.card ↥(Usup (puAmalgam h.le) α β) = Fintype.card F ^ 2) :
    (ZH (puAmalgam h.le) β).relIndex (ZM _ α) = Fintype.card F := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hα
  have hZab : ∀ a ∈ ZM (puAmalgam h.le) α, ∀ b ∈ ZM (puAmalgam h.le) α, a * b = b * a := by
    intro a ha b hb'
    have := (isElemAbelian_zm _ h20 hb0 hα).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb'⟩
    simpa using congrArg Subtype.val this
  have hZ2 : ∀ a ∈ ZM (puAmalgam h.le) α, a ^ 2 = 1 := (isElemAbelian_zm _ h20 hb0 hα).2
  have hZQ : ZM (puAmalgam h.le) α ≤ Qv _ β :=
    (zm_le_qv_self _ hα hb0).trans (qv_le_qv _ h20 hα hαβ)
  have hTs : Qv (puAmalgam h.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  have hmem : ∀ z ∈ ZM (puAmalgam h.le) α,
      z ∈ Subgroup.centralizer (Qv (puAmalgam h.le) β : Set _) → z ∈ ZH _ β := by
    intro z hz hzc
    exact Subgroup.subset_closure ⟨⟨hZQ hz, hzc⟩, hZ2 z hz⟩
  have hZloc : Zloc h.le L α ≤ ZH (puAmalgam h.le) β := fun z hz =>
    hmem z (zloc_le_zm h hfull hα hz)
      (Subgroup.centralizer_le hTs (zloc_le_centralizer_stab h hfull hα hz))
  have h1 : (ZH (puAmalgam h.le) β).relIndex (ZM _ α) =
      (ZH (puAmalgam h.le) β).relIndex (Uloc h.le L α) := by
    conv_lhs => rw [zm_eq_uloc_sup_zloc h hfull hα]
    exact relIndex_sup_of_le_of_comm hZab (uloc_le_zm h hfull hα) (zloc_le_zm h hfull hα) hZloc
  have h2 : ZH (puAmalgam h.le) β ⊓ Uloc h.le L α =
      Uloc h.le L α ⊓ Subgroup.centralizer (Qv (puAmalgam h.le) β : Set _) := by
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans (zh_le_centralizer _ β))
    · exact le_inf (fun z hz => hmem z (uloc_le_zm h hfull hα hz.1) hz.2) inf_le_left
  have h3 := Subgroup.relIndex_mul_card (H := ZH (puAmalgam h.le) β) (K := Uloc h.le L α)
  rw [h2, card_uloc_inf_centralizer_qv h hφ h464 hα hαβ hsq, card_eq_of_natural hψ,
    Nat.card_eq_fintype_card] at h3
  rw [h1]
  have hq0 : 0 < Fintype.card F ^ 2 := by positivity
  exact Nat.eq_of_mul_eq_mul_right hq0 (h3.trans (by ring))

omit hφ in
theorem commutator_vv_qv_le_zm (hb : 2 < critDist (puAmalgam h.le))
    (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
      Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
    {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    ⁅Vv (puAmalgam h.le) α, Qv _ α⁆ ≤ ZM _ α := by
  have h20 := h.hyp20
  have hV : Vv (puAmalgam h.le) α =
      ⨆ ρ : {ρ : Vtx (puAmalgam h.le) // (puAmalgam h.le).treeGraph.dist α ρ ≤ 2},
        Zv (puAmalgam h.le) ρ.1 := by
    rw [show Vv (puAmalgam h.le) α = Vi (puAmalgam h.le) α 2 from rfl]
    unfold Vi
    exact iSup_subtype'
  rw [hV]
  refine commutator_iSup_le_of (fun ρ => ?_) ?_
  · obtain ⟨μ, hμ, hdμ, hle⟩ := exists_zv_le_zm_of_dist hα ρ.2
    refine (Subgroup.commutator_mono hle le_rfl).trans ?_
    by_cases hμα : μ = α
    · rw [hμα, commutator_zm_qv _ h20 hα]
      exact bot_le
    · have hd2 : (puAmalgam h.le).treeGraph.dist α μ = 2 := by
        have hev : Even ((puAmalgam h.le).treeGraph.dist α μ) := by
          rw [even_dist_iff]; tauto
        have h0 : (puAmalgam h.le).treeGraph.dist α μ ≠ 0 := fun h0 =>
          hμα ((dist_eq_zero_iff _).mp h0).symm
        rcases (by omega : (puAmalgam h.le).treeGraph.dist α μ = 1 ∨
            (puAmalgam h.le).treeGraph.dist α μ = 2) with e | e
        · exact absurd (by rw [e] at hev; exact hev) (by decide)
        · exact e
      set β := geo (puAmalgam h.le) α μ 1
      have hαβ : (puAmalgam h.le).treeGraph.Adj α β := adj_geo_one _ (by omega)
      have hβμ : (puAmalgam h.le).treeGraph.Adj β μ := by
        have := adj_geo (puAmalgam h.le) (u := α) (w := μ) (i := 1) (by omega)
        rwa [geo_of_le _ (by omega : (puAmalgam h.le).treeGraph.dist α μ ≤ 1 + 1)] at this
      calc ⁅ZM (puAmalgam h.le) μ, Qv _ α⁆ ≤ ⁅ZM (puAmalgam h.le) μ, Qv _ β⁆ :=
            Subgroup.commutator_mono le_rfl (qv_le_qv _ h20 hα hαβ)
        _ = Usup _ μ β := by rw [Usup, zv_of_isMVtx _ hμ]
        _ ≤ ZH _ β := h464 μ β hμ hβμ.symm
        _ ≤ ZM _ α := zh_le_zm _ hαβ
  · rw [← hV]
    exact (vv_le_qv h hb hα).trans ((qv_le_stab _ α).trans (stab_le_normalizer_zm _ α))

end I465

theorem i465_of (h43 : S43) (h462 : I462) (h463 : I463) (h464 : I464) : I465 := by
  intro G _ _ M T L F _ _ φ c α β hα hαβ
  have hb : 2 < critDist (puAmalgam c.pu.le) := by rw [c.b4]; norm_num
  have h462' := fun x As hx hA => h462 G M T L F φ c x As hx hA
  have h463' := fun x hx => (h463 G M T L F φ c x hx).2
  have h464' := fun δ ρ hδ hδρ => h464 G M T L F φ c δ ρ hδ hδρ
  have hsq := card_usup_eq_sq c.pu c.via h43 c.min c.b4 h462' h463' h464' hα hαβ
  exact ⟨hsq, relIndex_zh_zm c.pu c.via h464' hα hαβ hsq, commutator_vv_qv_le_zm c.pu hb h464' hα⟩

end CFSG.Quasithin.MS93.S46
