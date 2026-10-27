module

public import CFSG.Quasithin.MS93.S4A441C2
public import CFSG.Quasithin.MS93.S4A44U

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace N441

private theorem commutator_sup_right_le {Γ : Type*} [Group Γ] {H₁ H₂ A N : Subgroup Γ}
    (hN₁ : H₁ ≤ Subgroup.normalizer (N : Set Γ)) (hN₂ : H₂ ≤ Subgroup.normalizer (N : Set Γ))
    (h₁ : ⁅A, H₁⁆ ≤ N) (h₂ : ⁅A, H₂⁆ ≤ N) : ⁅A, H₁ ⊔ H₂⁆ ≤ N := by
  let S : Subgroup Γ :=
    { carrier := {y | y ∈ Subgroup.normalizer (N : Set Γ) ∧ ∀ x ∈ A, ⁅y, x⁆ ∈ N}
      one_mem' := ⟨one_mem _, fun x _ => by simp⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁, k₁⟩ ⟨hy₂, k₂⟩
        refine ⟨mul_mem hy₁ hy₂, fun x hx => ?_⟩
        have e : ⁅y₁ * y₂, x⁆ = y₁ * ⁅y₂, x⁆ * y₁⁻¹ * ⁅y₁, x⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact mul_mem ((Subgroup.mem_normalizer_iff.mp hy₁ _).mp (k₂ x hx)) (k₁ x hx)
      inv_mem' := by
        rintro y ⟨hy, k⟩
        refine ⟨inv_mem hy, fun x hx => ?_⟩
        have e : ⁅y⁻¹, x⁆ = y⁻¹ * ⁅y, x⁆⁻¹ * y := by
          simp only [commutatorElement_def]; group
        rw [e]
        have hy' : y⁻¹ ∈ Subgroup.normalizer (N : Set Γ) := inv_mem hy
        have := (Subgroup.mem_normalizer_iff.mp hy' _).mp (inv_mem (k x hx))
        simpa [mul_assoc] using this }
  have hS : H₁ ⊔ H₂ ≤ S := by
    refine sup_le (fun y hy => ⟨hN₁ hy, fun x hx => ?_⟩) (fun y hy => ⟨hN₂ hy, fun x hx => ?_⟩)
    · rw [← commutatorElement_inv]
      exact inv_mem (h₁ (Subgroup.commutator_mem_commutator hx hy))
    · rw [← commutatorElement_inv]
      exact inv_mem (h₂ (Subgroup.commutator_mem_commutator hx hy))
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [← commutatorElement_inv]
  exact inv_mem ((hS hy).2 x hx)

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem usup_le_commutator_sup (hb : 4 < critDist (puAmalgam h.le))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    {B : Subgroup (puAmalgam h.le).Universal}
    (hB : B ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 1))
    (hBZ : ¬ ⁅B, ZM (puAmalgam h.le) α'⁆ ≤ ZM (puAmalgam h.le) α) :
    Usup (puAmalgam h.le) α' (geo (puAmalgam h.le) α' α 1) ≤
      ⁅B, ZM (puAmalgam h.le) α'⁆ ⊔ ZM (puAmalgam h.le) α := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hα' : IsMVtx _ α' := hc'.1
  set ρ := geo (puAmalgam h.le) α' α 1 with hρ
  have hα'ρ : (puAmalgam h.le).treeGraph.Adj α' ρ := adj_geo_one_of_isCritical _ hb0 hc'
  have hρs : Qv (puAmalgam h.le) ρ ≤ stab _ α' := qv_le_stab_of_adj _ hα'ρ.symm
  have hZα : ZM (puAmalgam h.le) α ≤ Qv _ ρ := zm_le_qv_geo_one_left _ h20 hb0 hC hc
  have hZn : ZM (puAmalgam h.le) α' ≤
      Subgroup.normalizer (ZM (puAmalgam h.le) α : Set (puAmalgam h.le).Universal) :=
    (zm_le_stab_of_isCritical _ h20 hb0 hc).trans (stab_le_normalizer_zm _ α)
  have hUle : ∀ {K : Subgroup (puAmalgam h.le).Universal}, K ≤ stab _ α' →
      ⁅Uloc h.le L α', K⁆ ≤ Uloc h.le L α' := fun hK =>
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hK.trans (stab_le_normalizer_uloc h α'))
  have hR : ⁅Uloc h.le L α', ZM (puAmalgam h.le) α⁆ ≤ ZM _ α := by
    rw [← commutator_zm_eq_uloc h hfull hα' (hZα.trans hρs), Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hZn
  have hS : ⁅Uloc h.le L α', B⁆ = ⁅B, ZM (puAmalgam h.le) α'⁆ := by
    rw [← commutator_zm_eq_uloc h hfull hα' (hB.trans hρs), Subgroup.commutator_comm]
  have hUq := card_usup_eq_sq h hφ hC hb hα' hα'ρ
  have hUeq := usup_eq_commutator_uloc h hfull hα' hα'ρ
  have : Finite ↥(Usup (puAmalgam h.le) α' ρ) :=
    Nat.finite_of_card_ne_zero (by rw [hUq]; exact pow_ne_zero _ Fintype.card_ne_zero)
  have hRle : ⁅Uloc h.le L α', ZM (puAmalgam h.le) α⁆ ≤ Usup (puAmalgam h.le) α' ρ := by
    rw [hUeq]
    exact Subgroup.commutator_mono le_rfl hZα
  have hne : ⁅Uloc h.le L α', ZM (puAmalgam h.le) α⁆ ≠ ⊥ := by
    rw [← commutator_zm_eq_uloc h hfull hα' (hZα.trans hρs), Subgroup.commutator_comm]
    exact ms22_ii _ h20 hb0 hC hc
  suffices hkey : Usup (puAmalgam h.le) α' ρ ≤
      ⁅Uloc h.le L α', ZM (puAmalgam h.le) α⁆ ⊔ ⁅Uloc h.le L α', B⁆ by
    rw [hS] at hkey
    exact hkey.trans (sup_le (hR.trans le_sup_right) le_sup_left)
  obtain ⟨d, hd, hcard⟩ := S46.card_commutator_uloc_le h hφ hα' hα'ρ hZα
  interval_cases d
  · exact absurd (Subgroup.card_eq_one.mp (by rw [hcard, pow_zero])) hne
  ·
    have hP : ZM (puAmalgam h.le) α ⊔ B ≤ Qv _ ρ := sup_le hZα hB
    have hPle : ⁅Uloc h.le L α', ZM (puAmalgam h.le) α ⊔ B⁆ ≤ Usup (puAmalgam h.le) α' ρ := by
      rw [hUeq]
      exact Subgroup.commutator_mono le_rfl hP
    rcases S46.commutator_uloc_eq_of_le h hφ hα' hα'ρ hP (by rw [hcard, pow_one]) hUq
        (Subgroup.commutator_mono le_rfl le_sup_left) hPle with heq | heq
    · exact absurd (hS ▸ (Subgroup.commutator_mono le_rfl le_sup_right).trans (heq.le.trans hR))
        hBZ
    · rw [← heq]
      have hNU : ⁅Uloc h.le L α', ZM (puAmalgam h.le) α⁆ ⊔ ⁅Uloc h.le L α', B⁆ ≤
          Uloc h.le L α' := sup_le (hUle (hZα.trans hρs)) (hUle (hB.trans hρs))
      refine commutator_sup_right_le ?_ ?_ le_sup_left le_sup_right
      · exact Subgroup.le_normalizer_iff_commutator_le_left.mpr
          ((Subgroup.commutator_mono hNU le_rfl).trans le_sup_left)
      · exact Subgroup.le_normalizer_iff_commutator_le_left.mpr
          ((Subgroup.commutator_mono hNU le_rfl).trans le_sup_right)
  ·
    have heq : ⁅Uloc h.le L α', ZM (puAmalgam h.le) α⁆ = Usup (puAmalgam h.le) α' ρ :=
      Subgroup.eq_of_le_of_card_ge hRle (by rw [hcard, hUq])
    rw [← heq]
    exact le_sup_left

end Vertex

end N441

namespace C441

theorem s441C2NonCrit_holds : S441C2NonCrit := by
  intro G _ _ M T L h F _ _ φ hH hb α α' μ hc _ hconj _ _ _ _ hN hμQ
  have hφ := hH.2.2
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hc' := ms22_iii _ h20 hb0 h.centHyp hc
  have hα : IsMVtx _ α := hc.1
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  obtain ⟨g, hgμ, hgα⟩ := hconj
  have hdμ : (puAmalgam h.le).treeGraph.dist α μ = 2 := by
    have h1 := MS93.dist_smul (puAmalgam h.le) g μ α
    rw [hgμ, hgα] at h1
    rw [tdist_comm, ← h1, dist_geo _ (by omega)]
  have hρν : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α' α 1)
      (geo (puAmalgam h.le) α' α 2) := adj_geo _ (i := 1) (by rw [hc'.2.1]; omega)
  have hν : IsMVtx _ (geo (puAmalgam h.le) α' α 2) := isMVtx_geo_two _ h20 hb0 hc'
  have hμρ : ZM (puAmalgam h.le) μ ≤ Qv _ (geo (puAmalgam h.le) α' α 1) :=
    hμQ.trans (qv_le_qv _ h20 hν hρν.symm)
  have hB : ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ≤ ZM _ μ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_dist_le_two _ h20 hα hdμ.le).trans (stab_le_normalizer_zm _ μ))
  have hZn : ZM (puAmalgam h.le) α' ≤
      Subgroup.normalizer (ZM (puAmalgam h.le) α : Set (puAmalgam h.le).Universal) :=
    (zm_le_stab_of_isCritical _ h20 hb0 hc).trans (stab_le_normalizer_zm _ α)
  have hBZ : ¬ ⁅⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆, ZM (puAmalgam h.le) α'⁆ ≤
      ZM (puAmalgam h.le) α := fun hle =>
    hN (le_normalizer_sup_of_commutator_le hZn (hle.trans le_sup_right))
  have h1 : ⁅ZM (puAmalgam h.le) μ, ZM (puAmalgam h.le) α'⁆ ≤
      Usup (puAmalgam h.le) α' (geo (puAmalgam h.le) α' α 1) := by
    rw [Subgroup.commutator_comm, Usup, zv_of_isMVtx _ hc'.1]
    exact Subgroup.commutator_mono le_rfl hμρ
  exact h1.trans (N441.usup_le_commutator_sup h hφ hb hc (hB.trans hμρ) hBZ)

end C441

end CFSG.Quasithin.MS93.S4A
