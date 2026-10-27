module

public import CFSG.Quasithin.MS93.S38G2Step

public section

namespace CFSG.Quasithin.MS93.S38G

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93 SimpleGraph
open scoped commutatorElement

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}
  {Lt Ut Wt : Vtx X → Subgroup X.Universal}

namespace G2Hyp

variable (hG : G2Hyp X Lt Ut Wt)
include hG

theorem stab_le_normalizer_wt {γ : Vtx X} (hγ : IsMVtx X γ) :
    stab X γ ≤ Subgroup.normalizer (Wt γ : Set X.Universal) := by
  rw [hG.wt_eq γ hγ]
  exact le_normalizer_inf' (hG.ut_nor γ hγ) (le_normalizer_centralizer' (hG.lt_nor γ hγ))

theorem zm_right_le_qv_two {α α' : Vtx X} (hc : IsCritical X α α') :
    ZM X α' ≤ Qv X (geo X α α' 2) :=
  hG.zm_le_qv (hc.isMVtx_right X hG.h20) (by rw [tdist_comm]; rw [hG.dist_two_right hc]; omega)

theorem qv_two_le_centralizer_r {α α' : Vtx X} (hc : IsCritical X α α') :
    Qv X (geo X α α' 2) ≤
      Subgroup.centralizer ((⁅ZM X α, ZM X α'⁆ : Subgroup X.Universal) : Set X.Universal) := by
  obtain ⟨δ, hcδ, -, -, -⟩ := hG.exists_crit_back hc
  set μ := geo X α α' 2
  have h7 := (hG.commutator_vv_qv hcδ).2
  have hα : ZM X α ≤ Vv X μ :=
    S38E.zm_le_vv X hc.1 (by rw [tdist_comm]; rw [hG.dist_two hc])
  have hα' : ZM X α' ≤ Vv X μ :=
    S38E.zm_le_vv X (hc.isMVtx_right X hG.h20) (by rw [hG.dist_two_right hc])
  have hR : ⁅ZM X α, ZM X α'⁆ ≤ ⁅Vv X μ, Vv X μ⁆ := Subgroup.commutator_mono hα hα'
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  rw [eq_bot_iff, ← h7]
  exact Subgroup.commutator_mono hR le_rfl

theorem qv_two_le_sup {α α' : Vtx X} (hc : IsCritical X α α') :
    Qv X (geo X α α' 2) ≤ ZM X α' ⊔ Qv X α := by
  intro y hy
  refine hG.off_fix α α' hc y (qv_le_qv X hG.h20 (hG.isMVtx_two hc) (hG.adj_one_two hc).symm hy)
    fun r hr => ?_
  have : ⁅r, y⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (hG.qv_two_le_centralizer_r hc hy) r hr)
  rw [this]
  exact Subgroup.one_mem _

theorem qv_one_le_normalizer_r {α α' : Vtx X} (hc : IsCritical X α α') :
    Qv X (geo X α α' 1) ≤
      Subgroup.normalizer ((⁅ZM X α, ZM X α'⁆ : Subgroup X.Universal) : Set X.Universal) := by
  set β := geo X α α' 1
  set μ := geo X α α' 2
  have hμ := hG.isMVtx_two hc
  have hTα : Qv X β ≤ stab X α := qv_le_stab_of_isMVtx X hG.h20 hc.1 (hG.adj_one hc)
  have hTμ : Qv X β ≤ stab X μ := qv_le_stab_of_isMVtx X hG.h20 hμ (hG.adj_one_two hc).symm
  have heq : ZM X α' ⊔ Qv X α = Qv X μ ⊔ Qv X α :=
    le_antisymm (sup_le_sup_right (hG.zm_right_le_qv_two hc) _)
      (sup_le (hG.qv_two_le_sup hc) le_sup_right)
  have hZn : ZM X α' ≤ Subgroup.normalizer (ZM X α : Set X.Universal) :=
    (zm_le_stab_of_isCritical X hG.h20 hG.critDist_pos hc).trans (stab_le_normalizer_zm X α)
  have hR : ⁅ZM X α, ZM X α'⁆ = ⁅ZM X α, Qv X μ ⊔ Qv X α⁆ := by
    rw [← heq, commutator_sup_eq_of_le_centralizer hZn (qv_le_centralizer_xm X α |>.trans ?_)]
    rw [hG.xm_eq α hc.1]
  rw [hR]
  exact S38E.le_normalizer_commutator' (hTα.trans (stab_le_normalizer_zm X α))
    (le_normalizer_sup (hTμ.trans (stab_le_normalizer_qv X μ))
      (hTα.trans (stab_le_normalizer_qv X α)))

theorem r_le_zm_two {α α' : Vtx X} (hc : IsCritical X α α') :
    ⁅ZM X α, ZM X α'⁆ ≤ ZM X (geo X α α' 2) := by
  set μ := geo X α α' 2
  rw [← hG.xm_eq μ (hG.isMVtx_two hc)]
  intro r hr
  have hrZ := hG.commutator_zm_le_left hc hr
  have hrμ : r ∈ Qv X μ := hG.zm_le_qv hc.1 (by rw [hG.dist_two hc]; omega) hrZ
  refine Subgroup.subset_closure ⟨⟨hrμ, ?_⟩, ?_⟩
  · change r ∈ Subgroup.centralizer (Qv X μ : Set X.Universal)
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (hG.qv_two_le_centralizer_r hc hq) r hr).symm
  · exact (isElemAbelian_zm X hG.h20 hG.critDist_pos hc.1).2 r hrZ

theorem commutator_r_qv_le {α α' : Vtx X} (hc : IsCritical X α α') :
    ⁅(⁅ZM X α, ZM X α'⁆ : Subgroup X.Universal), Qv X (geo X α α' 1)⁆ ≤ Wt α := by
  obtain ⟨δ, hcδ, hδ1, hδ2, -⟩ := hG.exists_crit_back hc
  set β := geo X α α' 1 with hβdef
  set μ := geo X α α' 2 with hμdef
  set R : Subgroup X.Universal := ⁅ZM X α, ZM X α'⁆ with hRdef
  have hμ := hG.isMVtx_two hc
  have hβ : ¬ IsMVtx X β := hG.not_isMVtx_one hc
  have hTα : Qv X β ≤ stab X α := qv_le_stab_of_isMVtx X hG.h20 hc.1 (hG.adj_one hc)
  have hTμ : Qv X β ≤ stab X μ := qv_le_stab_of_isMVtx X hG.h20 hμ (hG.adj_one_two hc).symm
  have hRn := hG.qv_one_le_normalizer_r hc
  have hRU : R ≤ Ut α := hG.r_le α α' hc
  have hWR : Wt α ≤ R := hG.w_le_r α α' hc
  have hWn : Qv X β ≤ Subgroup.normalizer (Wt α : Set X.Universal) :=
    hTα.trans (hG.stab_le_normalizer_wt hc.1)
  have hRT : R ≤ Qv X β := (hG.commutator_zm_le_left hc).trans
    (hG.zm_le_qv hc.1 (by rw [dist_eq_one_of_adj X (hG.adj_one hc)]; omega))
  have hCR : ⁅R, Qv X β⁆ ≤ R := commutator_le_self_of hRn
  by_contra hne
  set Y₀ := ⁅R, Qv X β⁆ ⊔ Wt α with hY₀def
  have hY₀R : Y₀ ≤ R := sup_le hCR hWR
  have : Finite ↥(Qv X β) := hG.qv_finite_h hβ
  have hT2 : IsPGroup 2 ↥(Qv X β) := isPGroup_qv X hG.h20 hβ
  have hY₀n : Qv X β ≤ Subgroup.normalizer (Y₀ : Set X.Universal) :=
    le_normalizer_sup (S38E.le_normalizer_commutator' hRn Subgroup.le_normalizer) hWn
  obtain ⟨x, hx, hxW⟩ := exists_mem_botLayer hT2 le_sup_right (hY₀R.trans hRT) hWn hY₀n
    fun h => hne (le_sup_left.trans h)
  obtain ⟨hxY, -, -, -, hxt⟩ := hx
  have hCn : ⁅R, Qv X β⁆ ≤ Subgroup.normalizer (Wt α : Set X.Universal) :=
    (hCR.trans hRT).trans hWn
  obtain ⟨y, hy, w, hw, rfl⟩ := exists_mul_of_mem_sup hCn hxY
  have hyW : y ∉ Wt α := fun h => hxW (Subgroup.mul_mem _ h hw)
  have hyR : y ∈ R := hCR hy
  have hyt : ∀ t ∈ Qv X β, ⁅y, t⁆ ∈ Wt α := by
    intro t ht
    have e : ⁅y, t⁆ = (y * w) * ⁅w⁻¹, t⁆ * (y * w)⁻¹ * ⁅y * w, t⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have h1 : ⁅w⁻¹, t⁆ ∈ Wt α := by
      have e2 : ⁅w⁻¹, t⁆ = w⁻¹ * (t * w * t⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e2]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hw)
        ((Subgroup.mem_normalizer_iff.mp (hWn ht) w).mp hw)
    have hywn : y * w ∈ Subgroup.normalizer (Wt α : Set X.Universal) :=
      hWn (hRT (hY₀R hxY))
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hywn _).mp h1) (hxt t ht)
  have hyL := hG.a_cent α α' hc y (hRU hyR) hyt
  have hyU : y ∈ Ut μ := by
    have h1 : ⁅R, Qv X β⁆ ≤ ⁅ZM X μ, stab X μ⁆ :=
      Subgroup.commutator_mono (hG.r_le_zm_two hc) hTμ
    exact hG.zm_comm μ hμ (h1 hy)
  have hyWμ : y ∈ Wt μ := by
    rw [hG.wt_eq μ hμ]
    exact ⟨hyU, hyL⟩
  have hyLα : y ∈ Subgroup.centralizer (Lt α : Set X.Universal) := by
    have h1 := hG.a_cent μ δ hcδ y hyU (by
      intro t ht
      rw [hδ1] at ht
      have e : ⁅y, t⁆ = y * (t * y⁻¹ * t⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem _ hyWμ ((Subgroup.mem_normalizer_iff.mp
        (hTμ.trans (hG.stab_le_normalizer_wt hμ) ht) _).mp (Subgroup.inv_mem _ hyWμ)))
    rwa [hδ2] at h1
  apply hyW
  rw [hG.wt_eq α hc.1]
  exact ⟨hRU hyR, hyLα⟩

theorem qv_le_zm_sup {α α' : Vtx X} (hc : IsCritical X α α') :
    Qv X (geo X α α' 1) ≤ ZM X α' ⊔ Qv X α := by
  intro t ht
  refine hG.off_fix α α' hc t ht fun r hr => ?_
  exact hG.commutator_r_qv_le hc (Subgroup.commutator_mem_commutator hr ht)

theorem qv_le_centralizer_r {α α' : Vtx X} (hc : IsCritical X α α') :
    Qv X (geo X α α' 1) ≤
      Subgroup.centralizer ((⁅ZM X α, ZM X α'⁆ : Subgroup X.Universal) : Set X.Universal) := by
  refine (hG.qv_le_zm_sup hc).trans (sup_le ?_ ?_)
  · intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' := hG.commutator_zm_le_right hc hr
    exact congrArg Subtype.val ((isElemAbelian_zm X hG.h20 hG.critDist_pos
      (hc.isMVtx_right X hG.h20)).1.1.1 ⟨r, hr'⟩ ⟨z, hz⟩)
  · intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv X hG.h20 hc.1
      (hG.commutator_zm_le_left hc hr)) q hq).symm

theorem mem_r_iff {α α' : Vtx X} (hc : IsCritical X α α') (u : X.Universal) :
    (u ∈ Ut α ∧ ∀ t ∈ Qv X (geo X α α' 1), ⁅u, t⁆ ∈ Wt α) ↔ u ∈ ⁅ZM X α, ZM X α'⁆ := by
  constructor
  · rintro ⟨hu, hut⟩
    exact hG.r_eq α α' hc u hu fun z hz =>
      hut z (zm_le_qv_geo_one X hG.h20 hG.critDist_pos hc hz)
  · intro hu
    refine ⟨hG.r_le α α' hc hu, fun t ht => ?_⟩
    have : ⁅u, t⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp (hG.qv_le_centralizer_r hc ht) u hu)
    rw [this]
    exact Subgroup.one_mem _

theorem stab_le_normalizer_r {α α' : Vtx X} (hc : IsCritical X α α') :
    stab X (geo X α α' 2) ≤
      Subgroup.normalizer ((⁅ZM X α, ZM X α'⁆ : Subgroup X.Universal) : Set X.Universal) :=
  le_normalizer_of_conj fun g hg u hu =>
    (hG.mem_r_iff hc _).mp (hG.a_nor α α' hc g hg u ((hG.mem_r_iff hc u).mpr hu).1
      ((hG.mem_r_iff hc u).mpr hu).2)

theorem lt_le_centralizer_r {α α' : Vtx X} (hc : IsCritical X α α') :
    Lt (geo X α α' 2) ≤
      Subgroup.centralizer ((⁅ZM X α, ZM X α'⁆ : Subgroup X.Universal) : Set X.Universal) := by
  rw [← Subgroup.le_centralizer_iff]
  intro u hu
  exact hG.a_cent α α' hc u ((hG.mem_r_iff hc u).mpr hu).1 ((hG.mem_r_iff hc u).mpr hu).2

theorem stab_le_centralizer_r {α α' : Vtx X} (hc : IsCritical X α α') :
    stab X (geo X α α' 2) ≤
      Subgroup.centralizer ((⁅ZM X α, ZM X α'⁆ : Subgroup X.Universal) : Set X.Universal) := by
  rw [hG.lt_sup _ _ (hG.isMVtx_two hc) (hG.adj_one_two hc).symm]
  exact sup_le (hG.lt_le_centralizer_r hc) (hG.qv_le_centralizer_r hc)

theorem starNorm : S38E.StarNorm X := by
  intro δ δ' hc
  rw [hG.xm_eq δ hc.1, hG.xm_eq δ' (hc.isMVtx_right X hG.h20)]
  exact hG.stab_le_normalizer_r hc

end G2Hyp

end CFSG.Quasithin.MS93.S38G
