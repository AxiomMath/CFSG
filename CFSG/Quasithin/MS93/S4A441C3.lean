module

public import CFSG.Quasithin.MS93.S4A44Path
public import CFSG.Quasithin.MS93.S46Type

public section

namespace CFSG.Quasithin.MS93.S4A.C441

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S4A
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Claim3

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem commutator_zm_vv_inf_qv_eq (hC : CentHyp (puAmalgam h.le))
    (hb : 4 < critDist (puAmalgam h.le)) {μ μ' ν' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) μ μ') (hν' : (puAmalgam h.le).treeGraph.dist μ' ν' = 2)
    (h2 : ⁅⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) (geo _ μ μ' 2)⁆,
      ZM (puAmalgam h.le) ν'⁆ ≠ ⊥) :
    ⁅ZM (puAmalgam h.le) μ, Vv (puAmalgam h.le) μ' ⊓ Qv (puAmalgam h.le) (geo _ μ μ' 2)⁆ =
      ⁅ZM (puAmalgam h.le) μ, ZM (puAmalgam h.le) μ'⁆ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hμ : IsMVtx _ μ := hc.1
  have hμ' : IsMVtx _ μ' := hc.isMVtx_right _ h20
  have hd : (puAmalgam h.le).treeGraph.dist μ μ' = critDist (puAmalgam h.le) := hc.2.1
  have hν'M : IsMVtx _ ν' :=
    ((even_dist_iff _ μ' ν').mp (by rw [hν']; exact even_two)).mp hμ'
  have hμρ : (puAmalgam h.le).treeGraph.Adj μ (geo _ μ μ' 1) :=
    adj_geo_one_of_isCritical _ hb0 hc
  have hρν : (puAmalgam h.le).treeGraph.Adj (geo _ μ μ' 1) (geo _ μ μ' 2) :=
    adj_geo _ (i := 1) (by omega)
  have hν : IsMVtx _ (geo _ μ μ' 2) := isMVtx_geo_two _ h20 hb0 hc
  have hdν : (puAmalgam h.le).treeGraph.dist μ' (geo _ μ μ' 2) =
      critDist (puAmalgam h.le) - 2 := by
    rw [tdist_comm, dist_geo_right _ (by omega), hd]
  have hQρ : Qv (puAmalgam h.le) (geo _ μ μ' 2) ≤ Qv _ (geo _ μ μ' 1) :=
    qv_le_qv _ h20 hν hρν.symm
  have hZρ : ZM (puAmalgam h.le) μ' ≤ Qv _ (geo _ μ μ' 1) := zm_le_qv_geo_one _ h20 hb0 hc
  have hPρ : Vv (puAmalgam h.le) μ' ⊓ Qv _ (geo _ μ μ' 2) ≤ Qv _ (geo _ μ μ' 1) :=
    inf_le_right.trans hQρ
  have hρs : Qv (puAmalgam h.le) (geo _ μ μ' 1) ≤ stab _ μ := qv_le_stab_of_adj _ hμρ.symm
  have hZQ : ZM (puAmalgam h.le) μ' ≤ Qv _ (geo _ μ μ' 2) :=
    zm_le_qv_of_dist_lt _ hμ' (by omega)
  have hVc : Vv (puAmalgam h.le) μ' ≤
      Subgroup.centralizer (ZM (puAmalgam h.le) ν' : Set (puAmalgam h.le).Universal) :=
    vv_le_centralizer_zm _ h20 hν'M (by rw [tdist_comm, hν']; omega)
  have hZVμ' : ZM (puAmalgam h.le) μ' ≤ Vv _ μ' := zm_le_vv h hμ'
  have hZs : ZM (puAmalgam h.le) μ ≤ stab _ μ' :=
    zm_le_stab_of_isCritical _ h20 hb0 (ms22_iii _ h20 hb0 hC hc)
  rw [commutator_zm_eq_uloc h hfull hμ (hPρ.trans hρs),
    commutator_zm_eq_uloc h hfull hμ (hZρ.trans hρs)]
  rw [commutator_zm_eq_uloc h hfull hμ (hQρ.trans hρs)] at h2
  set R' := ⁅Uloc h.le L μ, ZM (puAmalgam h.le) μ'⁆ with hR'
  set Z := ⁅Uloc h.le L μ, Qv (puAmalgam h.le) (geo _ μ μ' 2)⁆ with hZdef
  set S := ⁅Uloc h.le L μ, Vv (puAmalgam h.le) μ' ⊓ Qv (puAmalgam h.le) (geo _ μ μ' 2)⁆
    with hS
  have hRZ : R' ≤ Z := Subgroup.commutator_mono le_rfl hZQ
  have hRS : R' ≤ S := Subgroup.commutator_mono le_rfl (le_inf hZVμ' hZQ)
  have hSZ : S ≤ Z := Subgroup.commutator_mono le_rfl inf_le_right
  have hSV : S ≤ Vv (puAmalgam h.le) μ' := by
    rw [hS, Subgroup.commutator_comm]
    refine (Subgroup.commutator_mono inf_le_left le_rfl).trans ?_
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (((uloc_le_zm h hfull hμ).trans hZs).trans (stab_le_normalizer_vv h μ'))
  have hRne : R' ≠ ⊥ := by
    rw [hR', ← commutator_zm_eq_uloc h hfull hμ (hZρ.trans hρs)]
    exact ms22_ii _ h20 hb0 hC hc
  have hRZne : R' ≠ Z := by
    intro he
    apply h2
    rw [← he, Subgroup.commutator_eq_bot_iff_le_centralizer]
    have hRZ' : R' ≤ ZM (puAmalgam h.le) μ' := by
      rw [hR', Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        (((uloc_le_zm h hfull hμ).trans hZs).trans (stab_le_normalizer_zm _ μ'))
    exact hRZ'.trans (hZVμ'.trans hVc)
  obtain ⟨d₁, hd₁, hc₁⟩ := S46.card_commutator_uloc_le h hφ hμ hμρ hZρ
  obtain ⟨d₂, hd₂, hc₂⟩ := S46.card_commutator_uloc_le h hφ hμ hμρ hQρ
  have hq : 2 ≤ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card]
    exact Finite.one_lt_card
  have hfinZ : Finite ↥Z := Nat.finite_of_card_ne_zero (by rw [hc₂]; positivity)
  have h1 : 1 ≤ d₁ := by
    by_contra h0
    apply hRne
    rw [← Subgroup.card_eq_one, hc₁, show d₁ = 0 by omega, pow_zero]
  have h12 : d₁ < d₂ := by
    have hle : Fintype.card F ^ d₁ ≤ Fintype.card F ^ d₂ := by
      rw [← hc₁, ← hc₂]
      exact Subgroup.card_le_of_le hRZ
    have hle' : d₁ ≤ d₂ := (Nat.pow_le_pow_iff_right (by omega)).mp hle
    rcases hle'.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      exact hRZne (Subgroup.eq_of_le_of_card_ge hRZ (by rw [hc₁, hc₂, heq]))
  have hcR : Nat.card ↥R' = Fintype.card F := by rw [hc₁, show d₁ = 1 by omega, pow_one]
  have hcZ : Nat.card ↥Z = Fintype.card F ^ 2 := by rw [hc₂, show d₂ = 2 by omega]
  rcases S46.commutator_uloc_eq_of_le h hφ hμ hμρ hPρ hcR hcZ hRS hSZ with he | he
  · exact he
  · exfalso
    apply h2
    rw [← he, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hSV.trans hVc

end Claim3

end CFSG.Quasithin.MS93.S4A.C441
