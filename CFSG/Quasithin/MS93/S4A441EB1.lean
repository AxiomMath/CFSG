module

public import CFSG.Quasithin.MS93.S4A441EBP
public import CFSG.Quasithin.MS93.S4A441EBW
public import CFSG.Quasithin.MS93.S4A441C3
import CFSG.Quasithin.MS93.S4A441E

public section

namespace CFSG.Quasithin.MS93.S4A.X441

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

private theorem stab_le_normalizer_bloc' (ν : Vtx 𝔛) :
    stab 𝔛 ν ≤ Subgroup.normalizer (Bloc h.le L ν : Set 𝔘) :=
  le_normalizer_of_map_conj_le fun g hg => by rw [← bloc_smul h g ν, (mem_stab _).mp hg]

theorem not_commutator_vv_qv_le_bloc {α ν : Vtx 𝔛} (hα : IsMVtx 𝔛 α) (hν : IsMVtx 𝔛 ν)
    (hB : ¬ ⁅Vv 𝔛 α, Qv 𝔛 α⁆ ≤ Bloc h.le L α) : ¬ ⁅Vv 𝔛 ν, Qv 𝔛 ν⁆ ≤ Bloc h.le L ν := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ hα hν
  intro hle
  apply hB
  rw [show Vv 𝔛 (g • α) = (Vv 𝔛 α).map (MulAut.conj g).toMonoidHom from vi_smul _ g α 2,
    qv_smul, bloc_smul h, ← Subgroup.map_commutator] at hle
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective).mp hle

theorem exists_not_mem_bloc (hb : 2 < critDist 𝔛) {ν : Vtx 𝔛} (hν : IsMVtx 𝔛 ν)
    (hB : ¬ ⁅Vv 𝔛 ν, Qv 𝔛 ν⁆ ≤ Bloc h.le L ν) :
    ∃ ρ, IsMVtx 𝔛 ρ ∧ (puAmalgam h.le).treeGraph.dist ν ρ = 2 ∧
      ∃ x ∈ ⁅ZM 𝔛 ρ, Qv 𝔛 ν⁆, x ∉ Bloc h.le L ν := by
  by_contra hall
  push Not at hall
  apply hB
  have hVs : Vv 𝔛 ν ≤ stab 𝔛 ν := (vv_le_qv h hb hν).trans (qv_le_stab _ ν)
  refine L441.commutator_iSup₂_le (stab_le_normalizer_bloc' h ν) (fun ρ hρ =>
    (zv_le_vv h hρ).trans hVs) fun ρ hρ => ?_
  obtain ⟨ρ', hρ', hdρ', hle⟩ := exists_zv_le_zm h hν hρ
  refine (Subgroup.commutator_mono hle le_rfl).trans ?_
  have hev := (even_dist_iff _ ν ρ').mpr ⟨fun _ => hρ', fun _ => hν⟩
  rcases (show (puAmalgam h.le).treeGraph.dist ν ρ' = 0 ∨
      (puAmalgam h.le).treeGraph.dist ν ρ' = 1 ∨
      (puAmalgam h.le).treeGraph.dist ν ρ' = 2 by omega) with h0 | h1 | h2
  · have : ν = ρ' := (dist_eq_zero_iff _).mp h0
    subst this
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      (zm_le_centralizer_qv _ h.hyp20 hν)]
    exact bot_le
  · rw [h1] at hev
    exact absurd hev Nat.not_even_one
  · intro x hx
    exact hall ρ' hρ' h2 x hx

variable {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}

theorem exists_lam_of_not_le_bloc (hH : Hyp40 h φ) (h2c : C441.S441C2Cent)
    (hb : 4 < critDist 𝔛) {α α' : Vtx 𝔛} (hc : IsCritical 𝔛 α α')
    (hfail : ∀ g : 𝔘, ¬ Concl441 h.le L (g • α) (g • geo 𝔛 α α' 2))
    (hc1 : ∀ g : 𝔘, ¬ IsC1 h.le L (Fintype.card F) (g • geo 𝔛 α α' 2)
      (conjCl (stab 𝔛 (g • geo 𝔛 α α' 2)) (ZM 𝔛 (g • α))) (ZM 𝔛 (g • geo 𝔛 α α' 2)))
    (hB : ¬ ⁅Vv 𝔛 α, Qv 𝔛 α⁆ ≤ Bloc h.le L α) :
    ∃ μ lam : Vtx 𝔛,
      (∃ g : 𝔘, g • μ = α ∧ g • α = geo 𝔛 α α' 2) ∧
      IsCritical 𝔛 μ (geo 𝔛 α' α 2) ∧ geo 𝔛 μ (geo 𝔛 α' α 2) 2 = α ∧
      ⁅⁅ZM 𝔛 μ, Qv 𝔛 α⁆, ZM 𝔛 α'⁆ ≠ ⊥ ∧
      IsMVtx 𝔛 lam ∧ (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 2) lam = 2 ∧
      ¬ ZM 𝔛 μ ≤ Subgroup.normalizer
        ((⁅ZM 𝔛 lam, Qv 𝔛 (geo 𝔛 α' α 2)⁆ ⊔ ZM 𝔛 (geo 𝔛 α' α 2) : Subgroup 𝔘) : Set 𝔘) ∧
      IsCritical 𝔛 lam α ∧ geo 𝔛 lam α 2 = geo 𝔛 α' α 2 ∧
      ⁅ZM 𝔛 lam, Vv 𝔛 α ⊓ Qv 𝔛 (geo 𝔛 α' α 2)⁆ ≤ ZM 𝔛 α := by
  have hφ := hH.2.2
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hα : IsMVtx 𝔛 α := hc.1
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist 𝔛 := hc.2.1
  obtain ⟨μ, hconj, hcμ, hgeoμ, h2⟩ := C441.claim2_of h hH C441.s441C2Wlog_holds
    C441.s441C2NonCrit_holds h2c hb hc hfail hc1
  set ν := geo 𝔛 α' α 2 with hνdef
  have hν : IsMVtx 𝔛 ν := isMVtx_geo_two _ h20 hb0 hc'
  have hcμ' := ms22_iii _ h20 hb0 hC hcμ
  have hdνα' : (puAmalgam h.le).treeGraph.dist ν α' = 2 := by
    rw [tdist_comm, hνdef, dist_geo _ (by rw [hc'.2.1]; omega)]
  have h3 : ⁅ZM 𝔛 μ, Vv 𝔛 ν ⊓ Qv 𝔛 (geo 𝔛 μ ν 2)⁆ ≤ ZM 𝔛 ν := by
    have := C441.commutator_zm_vv_inf_qv_eq h hφ hC hb hcμ hdνα' (by rw [hgeoμ]; exact h2)
    rw [this]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp
      ((zm_le_stab_right _ h20 hb0 hC hcμ).trans (stab_le_normalizer_zm _ ν))
  obtain ⟨ρ, hρ, hdρ, x, hx, hxB⟩ :=
    exists_not_mem_bloc h (by omega) hν (not_commutator_vv_qv_le_bloc h hα hν hB)
  obtain ⟨k, hk, hN⟩ := exists_not_le_normalizer_of_not_mem_bloc h hφ hb hcμ' hρ hdρ hx hxB
  have hkρ : IsMVtx 𝔛 (k • ρ) := (isMVtx_smul _ k ρ).mpr hρ
  have hdkρ : (puAmalgam h.le).treeGraph.dist ν (k • ρ) = 2 := by
    have := dist_smul _ k ν ρ
    rwa [(mem_stab _).mp hk, hdρ] at this
  obtain ⟨hcl, hgeol, -, -⟩ :=
    isCritical_relIndex_of_not_normalizer h hφ hb hcμ hkρ hdkρ hN h3
  rw [hgeoμ] at hcl hgeol
  have hdαμ : (puAmalgam h.le).treeGraph.dist α μ = 2 := by
    rw [tdist_comm, ← hgeoμ, dist_geo _ (by rw [hcμ.2.1]; omega)]
  have h2l : ⁅⁅ZM 𝔛 (k • ρ), Qv 𝔛 (geo 𝔛 (k • ρ) α 2)⁆, ZM 𝔛 μ⁆ ≠ ⊥ := by
    rw [hgeol]
    intro hbot
    apply hN
    refine le_normalizer_sup_of_commutator_le
      ((zm_le_stab_right _ h20 hb0 hC hcμ).trans (stab_le_normalizer_zm _ ν)) ?_
    rw [hbot]
    exact bot_le
  have h3l : ⁅ZM 𝔛 (k • ρ), Vv 𝔛 α ⊓ Qv 𝔛 ν⁆ ≤ ZM 𝔛 α := by
    have := C441.commutator_zm_vv_inf_qv_eq h hφ hC hb hcl hdαμ h2l
    rw [hgeol] at this
    rw [this]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp
      ((zm_le_stab_right _ h20 hb0 hC hcl).trans (stab_le_normalizer_zm _ α))
  exact ⟨μ, k • ρ, hconj, hcμ, hgeoμ, h2, hkρ, hdkρ, hN, hcl, hgeol, h3l⟩

end Vertex

end CFSG.Quasithin.MS93.S4A.X441
