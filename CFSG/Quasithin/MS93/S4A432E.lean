module

public import CFSG.Quasithin.MS93.S4A432D
public import CFSG.Quasithin.MS93.S4A432N

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Dual

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L) {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
  (hH : Hyp40 h φ) (hC : CentHyp (puAmalgam h.le)) (h42 : S42) (h431A : S431A)
  (h431B : S431B) (hb : 4 < critDist (puAmalgam h.le)) {α₀ α₀' : Vtx (puAmalgam h.le)}
  (hs : Star (puAmalgam h.le) α₀ α₀')
  (hk : ∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ → KindAt h.le L F true μ)
  (hCH : ∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ →
    ¬ ⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ≤ Dloc h.le L μ)
include h hfull hH hC h42 h431A h431B hb hs hk hCH

theorem commutator_zm_qv_eq_usup_of_dual {μ ν δ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hμν : (puAmalgam h.le).treeGraph.Adj μ ν) (hνδ : (puAmalgam h.le).treeGraph.Adj ν δ)
    (hδ : δ ∈ nablaSet h.le L μ) :
    ⁅ZM (puAmalgam h.le) δ, Qv (puAmalgam h.le) μ⁆ = Usup (puAmalgam h.le) μ ν ∧
      Usup (puAmalgam h.le) δ ν = Usup (puAmalgam h.le) μ ν := by
  have h20 := h.hyp20
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  obtain ⟨hδM, hZδV⟩ := zm_le_vv_of_mem_nablaSet h hμ hδ
  have hZδB : ¬ ZM (puAmalgam h.le) δ ≤ Bloc h.le L μ := by
    have := hδ.2
    rwa [zv_of_isMVtx _ hδM] at this
  have hVs : Vv (puAmalgam h.le) μ ≤ stab _ μ := (vv_le_qv h hb2 hμ).trans (qv_le_stab _ μ)
  obtain ⟨hUμ, hUμq, -, -⟩ := concl433_edge h hfull h42 h431A h431B hH hC hs hμ hμν
  obtain ⟨hUδ, hUδq, -, -⟩ := concl433_edge h hfull h42 h431A h431B hH hC hs hδM hνδ.symm
  have hD := not_commutator_zm_qv_le_dloc_of_star h hH hfull h431A hs hCH hμ hδ
  obtain ⟨z, hz, y₀, hy₀, hzy₀⟩ : ∃ z ∈ ZM (puAmalgam h.le) δ, ∃ y₀ ∈ Qv (puAmalgam h.le) μ,
      ⁅z, y₀⁆ ∉ Dloc h.le L μ := by
    by_contra hall
    push Not at hall
    exact hD ((Subgroup.commutator_le).mpr hall)
  obtain ⟨x, hx, hxB, hxy₀⟩ := exists_not_mem_commutator_not_mem (vv_comm_eq_bot h hb hμ)
    (stab_le_normalizer_vv h μ (qv_le_stab _ μ hy₀)) hZδV hZδB hz hzy₀
  rcases commutator_le_zloc_or_eq_usup h hfull hb2 hμ (isC1_of_star h hH h431A hs hμ)
      (commutator_vv_qv_le_zm_of_star h hfull hH hC h42 h431A h431B hs hμ) (hk μ hμ) hμν hνδ
      hUμ hUμq hUδ hUδq hx hxB with hle | ⟨hNeq, hUeq⟩
  · exact absurd (zloc_le_dloc h μ (hle (Subgroup.subset_closure ⟨y₀, hy₀, rfl⟩))) hxy₀
  · refine ⟨le_antisymm ?_ ?_, hUeq⟩
    · rw [← hUeq, Usup, zv_of_isMVtx _ hδM]
      exact Subgroup.commutator_mono le_rfl (qv_le_qv _ h20 hμ hμν)
    · rw [← hNeq, Subgroup.closure_le]
      rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.commutator_mem_commutator hx hy

theorem mem_nablaSet_of_dual {μ ν δ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hμν : (puAmalgam h.le).treeGraph.Adj μ ν) (hνδ : (puAmalgam h.le).treeGraph.Adj ν δ)
    (hδ : δ ∈ nablaSet h.le L μ) : μ ∈ nablaSet h.le L δ := by
  classical
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  obtain ⟨hδM, -⟩ := zm_le_vv_of_mem_nablaSet h hμ hδ
  obtain ⟨hcomm, hUeq⟩ := commutator_zm_qv_eq_usup_of_dual h hfull hH hC h42 h431A h431B hb hs
    hk hCH hμ hμν hνδ hδ
  refine ⟨by rw [tdist_comm]; exact hδ.1, fun hle => ?_⟩
  rw [zv_of_isMVtx _ hμ] at hle
  have hcδ := isC1_of_star h hH h431A hs hδM
  obtain ⟨-, -, -, -, -, -, -, -, -, hBG, -⟩ := isC1_normal h hfull hb2 hδM hcδ
  have hVQδ := commutator_vv_qv_le_zm_of_star h hfull hH hC h42 h431A h431B hs hδM
  have hBG' : ⁅Bloc h.le L δ, stab (puAmalgam h.le) δ⁆ ≤ ZM (puAmalgam h.le) δ :=
    hBG.trans (sup_le hVQδ le_rfl)
  have hZcQ := zm_le_centralizer_qv _ h20 hδM
  have hUZδ : Usup (puAmalgam h.le) δ ν ≤ Uloc h.le L δ := by
    rw [usup_eq_commutator_uloc h hfull hδM hνδ.symm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_adj _ hνδ).trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) δ))
  have hQδν : Qv (puAmalgam h.le) δ ≤ Qv _ ν := qv_le_qv _ h20 hδM hνδ.symm
  have hQδs : Qv (puAmalgam h.le) δ ≤ stab _ μ := hQδν.trans (qv_le_stab_of_adj _ hμν.symm)
  have hx1 : ∀ x ∈ ZM (puAmalgam h.le) μ, ∀ y ∈ Qv (puAmalgam h.le) δ, ⁅x, y⁆ = 1 := by
    intro x hx
    set N := Subgroup.closure {r | ∃ y ∈ Qv (puAmalgam h.le) δ, ⁅x, y⁆ = r} with hNdef
    have hNU : N ≤ Usup (puAmalgam h.le) δ ν := by
      rw [hNdef, Subgroup.closure_le]
      rintro _ ⟨y, hy, rfl⟩
      rw [hUeq, Usup, zv_of_isMVtx _ hμ]
      exact Subgroup.commutator_mem_commutator hx (hQδν hy)
    have hNn : stab (puAmalgam h.le) δ ≤
        Subgroup.normalizer (N : Set (puAmalgam h.le).Universal) := by
      have key : ∀ g ∈ stab (puAmalgam h.le) δ, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
        intro g hg n hn
        induction hn using Subgroup.closure_induction with
        | mem n hn =>
          obtain ⟨y, hy, rfl⟩ := hn
          have hc : ⁅x⁻¹, g⁆ ∈ ZM (puAmalgam h.le) δ :=
            hBG' (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ (hle hx)) hg)
          have hy' : g * y * g⁻¹ ∈ Qv (puAmalgam h.le) δ :=
            (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_qv _ δ hg) y).mp hy
          have hcy : ⁅x⁻¹, g⁆ * (g * y * g⁻¹) = (g * y * g⁻¹) * ⁅x⁻¹, g⁆ :=
            (Subgroup.mem_centralizer_iff.mp (hZcQ hc) _ hy').symm
          have e : g * ⁅x, y⁆ * g⁻¹ = ⁅x, g * y * g⁻¹⁆ := by
            have e1 : g * ⁅x, y⁆ * g⁻¹ = ⁅x * ⁅x⁻¹, g⁆, g * y * g⁻¹⁆ := by
              simp only [commutatorElement_def]
              group
            rw [e1]
            simp only [commutatorElement_def] at hcy ⊢
            calc x * (x⁻¹ * g * x⁻¹⁻¹ * g⁻¹) * (g * y * g⁻¹) *
                  (x * (x⁻¹ * g * x⁻¹⁻¹ * g⁻¹))⁻¹ * (g * y * g⁻¹)⁻¹
                = x * ((x⁻¹ * g * x⁻¹⁻¹ * g⁻¹) * (g * y * g⁻¹)) *
                  (x⁻¹ * g * x⁻¹⁻¹ * g⁻¹)⁻¹ * x⁻¹ * (g * y * g⁻¹)⁻¹ := by group
              _ = x * ((g * y * g⁻¹) * (x⁻¹ * g * x⁻¹⁻¹ * g⁻¹)) *
                  (x⁻¹ * g * x⁻¹⁻¹ * g⁻¹)⁻¹ * x⁻¹ * (g * y * g⁻¹)⁻¹ := by rw [hcy]
              _ = x * (g * y * g⁻¹) * x⁻¹ * (g * y * g⁻¹)⁻¹ := by group
          rw [e]
          exact Subgroup.subset_closure ⟨_, hy', rfl⟩
        | one => simp
        | mul a b _ _ ha hb =>
          have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
          rw [this]
          exact N.mul_mem ha hb
        | inv a _ ha =>
          have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
          rw [this]
          exact N.inv_mem ha
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · exact key g hg n
      · intro hn
        have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hn
        simpa [mul_assoc] using this
    have hNZ : N ≤ Zloc h.le L δ := by
      by_contra hNZ
      have hUN := uloc_le_of_normal h hfull hH.2.2 hδM
        ((hNU.trans hUZδ).trans (uloc_le_zm h hfull hδM)) hNn hNZ
      have := finite_stab h hδM
      have hfinU : Finite ↥(Uloc h.le L δ) := Finite.of_injective _
        (Subgroup.inclusion_injective ((uloc_le_zm h hfull hδM).trans
          ((zm_le_qv_self _ hδM hb0).trans (qv_le_stab _ δ))))
      have hfinS : Finite ↥(Usup (puAmalgam h.le) δ ν) :=
        Finite.of_injective _ (Subgroup.inclusion_injective hUZδ)
      have h1 := Subgroup.card_le_of_le (hUN.trans hNU)
      obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hH.2.2 hδM
      obtain ⟨-, hUμq, -, -⟩ := concl433_edge h hfull h42 h431A h431B hH hC hs hμ hμν
      rw [card_eq_of_natural hψ, hUeq, hUμq, Nat.card_eq_fintype_card (α := F)] at h1
      have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
      have : Fintype.card F ^ 2 < Fintype.card F ^ 3 :=
        Nat.pow_lt_pow_right (by omega) (by norm_num)
      omega
    intro y hy
    have hmem : ⁅x, y⁆ ∈ Uloc h.le L δ ⊓ Zloc h.le L δ :=
      ⟨hUZδ (hNU (Subgroup.subset_closure ⟨y, hy, rfl⟩)),
        hNZ (Subgroup.subset_closure ⟨y, hy, rfl⟩)⟩
    rw [uloc_inf_zloc h hfull δ] at hmem
    exact hmem
  have hQδμ : Qv (puAmalgam h.le) δ ≤ Qv _ μ := by
    intro y hy
    refine S46.stab_inf_centralizer_uloc_le_qv h hH.2.2 hμ ⟨hQδs hy, ?_⟩
    show y ∈ Subgroup.centralizer (Uloc h.le L μ : Set (puAmalgam h.le).Universal)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have := hx1 u (uloc_le_zm h hfull hμ hu) y hy
    rw [commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hfinμ : Finite ↥(Qv (puAmalgam h.le) μ) := by
    have := finite_stab h hμ
    exact Finite.of_injective _ (Subgroup.inclusion_injective (qv_le_stab _ μ))
  have hcardQ : Nat.card ↥(Qv (puAmalgam h.le) μ) ≤ Nat.card ↥(Qv (puAmalgam h.le) δ) := by
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ hμ hδM
    rw [← hg, qv_smul, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hQeq : Qv (puAmalgam h.le) δ = Qv _ μ := Subgroup.eq_of_le_of_card_ge hQδμ hcardQ
  have hbot : ⁅ZM (puAmalgam h.le) δ, Qv (puAmalgam h.le) μ⁆ = ⊥ := by
    rw [← hQeq]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (zm_le_centralizer_qv _ h20 hδM)
  obtain ⟨-, hUμq, -, -⟩ := concl433_edge h hfull h42 h431A h431B hH hC hs hμ hμν
  rw [hcomm] at hbot
  rw [hbot, Subgroup.card_bot] at hUμq
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have : 1 < Fintype.card F ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  omega

theorem exists_mem_nablaSet_of_dual {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ) :
    ∃ ν γ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj μ ν ∧
      (puAmalgam h.le).treeGraph.Adj ν γ ∧ γ ∈ nablaSet h.le L μ := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  obtain ⟨μ', hsμ⟩ := exists_star_at _ hs hμ
  have hnab := mem_nablaSet_geo_two h hfull hC hb2 hsμ.1
  have hd : (puAmalgam h.le).treeGraph.dist μ μ' = critDist (puAmalgam h.le) := hsμ.1.2.1
  have hμβ : (puAmalgam h.le).treeGraph.Adj μ (geo (puAmalgam h.le) μ μ' 1) :=
    adj_geo_one_of_isCritical _ hb0 hsμ.1
  have hβγ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) μ μ' 1)
      (geo (puAmalgam h.le) μ μ' 2) := adj_geo _ (i := 1) (by omega)
  have hγ : IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) μ μ' 2) := isMVtx_geo_two _ h20 hb0 hsμ.1
  exact ⟨_, _, hμβ, hβγ, mem_nablaSet_of_dual h hfull hH hC h42 h431A h431B hb hs hk hCH hγ
    hβγ.symm hμβ.symm hnab⟩

theorem hloc_eq_uloc_of_dual {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ) :
    Hloc h.le L μ = Uloc h.le L μ := by
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  obtain ⟨ν, γ, hμν, hνγ, hγ⟩ :=
    exists_mem_nablaSet_of_dual h hfull hH hC h42 h431A h431B hb hs hk hCH hμ
  obtain ⟨hcomm, -⟩ := commutator_zm_qv_eq_usup_of_dual h hfull hH hC h42 h431A h431B hb hs
    hk hCH hμ hμν hνγ hγ
  have hVs : Vv (puAmalgam h.le) μ ≤ stab _ μ := (vv_le_qv h hb2 hμ).trans (qv_le_stab _ μ)
  have hVn := stab_le_normalizer_vv h μ
  have hUn : stab (puAmalgam h.le) μ ≤
      Subgroup.normalizer (Uloc h.le L μ : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) μ
  have hZγs : ZM (puAmalgam h.le) γ ≤ stab _ μ := (zm_le_vv_of_mem_nablaSet h hμ hγ).2.trans hVs
  have hVcV : Vcirc h.le L μ ≤ Vv _ μ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp ((ltil_le_stab h μ).trans hVn)
  apply le_antisymm
  · rw [Hloc]
    refine (Subgroup.commutator_mono (vcirc_le_conjCl_of_star h hH h431A hs hμ hγ) le_rfl).trans
      ?_
    refine commutator_conjCl_le hUn (stab_le_normalizer_qv _ μ) (hZγs.trans hUn) ?_
    rw [hcomm, usup_eq_commutator_uloc h hfull hμ hμν]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_adj _ hμν.symm).trans hUn)
  · have hHZ : Hloc h.le L μ ≤ ZM (puAmalgam h.le) μ :=
      (Subgroup.commutator_mono hVcV le_rfl).trans
        (commutator_vv_qv_le_zm_of_star h hfull hH hC h42 h431A h431B hs hμ)
    have hVcn : stab (puAmalgam h.le) μ ≤
        Subgroup.normalizer (Vcirc h.le L μ : Set (puAmalgam h.le).Universal) :=
      le_normalizer_commutator hVn (stab_le_normalizer_ltil h μ)
    have hHn : stab (puAmalgam h.le) μ ≤
        Subgroup.normalizer (Hloc h.le L μ : Set (puAmalgam h.le).Universal) :=
      le_normalizer_commutator hVcn (stab_le_normalizer_qv _ μ)
    refine uloc_le_of_normal h hfull hH.2.2 hμ hHZ hHn fun hle => hCH μ hμ ?_
    exact commutator_vv_le_dloc h hfull hb2 hμ (stab_le_normalizer_qv _ μ) le_rfl
      (hle.trans (zloc_le_dloc h μ))

end Dual

end CFSG.Quasithin.MS93.S4A
