module

public import CFSG.Quasithin.MS93.S46I467Dec
public import CFSG.Quasithin.MS93.S4AFMain
public import CFSG.Quasithin.MS93.S46Ker
public import CFSG.Quasithin.MS93.S46Inputs

public section

namespace CFSG.Quasithin.MS93.S46.I467

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46.I464 CFSG.Quasithin.MS93.S46.I466b
open scoped Matrix commutatorElement

theorem relIndex_ne_zero_of_finite {𝔾 : Type*} [Group 𝔾] {H K : Subgroup 𝔾} [Finite K] :
    H.relIndex K ≠ 0 := by
  intro h0
  have := Subgroup.relIndex_mul_card (H := H) (K := K)
  rw [h0, zero_mul] at this
  exact Nat.card_pos.ne' this.symm

section Main

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
  (hsq : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Nat.card ↥(Usup (puAmalgam h.le) δ ρ) = Fintype.card F ^ 2)
  (h466 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    (Qv (puAmalgam h.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2)
  (h465 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
    ⁅Vv (puAmalgam h.le) x, Qv _ x⁆ ≤ ZM _ x)
  (hV' : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
    ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ ZM _ x)
  (hZq : ∀ x ρ : Vtx (puAmalgam h.le), IsMVtx _ x → (puAmalgam h.le).treeGraph.Adj x ρ →
    (ZH (puAmalgam h.le) ρ).relIndex (ZM _ x) = Fintype.card F)
include h

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)

include h465 in
theorem commutator_stab_bloc_le (hfull : IsSL3Full M T L) (hb : 2 < critDist (puAmalgam h.le))
    {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    ⁅stab 𝔛 α, Bloc h.le L α⁆ ≤ ZM 𝔛 α := by
  have hZn := stab_le_normalizer_zm 𝔛 α
  rw [stab_eq_ltil_sup_qv h hfull hα]
  refine S4A.commutator_sup_le_of ?_ ?_ ((ltil_le_stab h α).trans hZn)
    ((qv_le_stab _ α).trans hZn)
  · rw [Subgroup.commutator_le]
    intro l hl x hx
    have := ((mem_bloc_iff h hb hα).mp hx).2 l hl
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ this
  · rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono (bloc_le_vv h α) le_rfl).trans (h465 α hα)

theorem not_bloc_le_centerOf_of_isMVtx {α x : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hx : IsMVtx _ x) (hne : ¬ Bloc h.le L α ≤ centerOf (Vv 𝔛 α)) :
    ¬ Bloc h.le L x ≤ centerOf (Vv 𝔛 x) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ hα hx
  rw [show Vv 𝔛 (g • α) = Vi _ (g • α) 2 from rfl, vi_smul,
    PU.centerOf_map (MulAut.conj g).injective, bloc_smul h g α, map_conj_le_map_conj_iff]
  exact hne

theorem exists_not_bloc_le_qv {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hne : ¬ Bloc h.le L α ≤ centerOf (Vv 𝔛 α)) :
    ∃ β δ : Vtx 𝔛, (puAmalgam h.le).treeGraph.Adj α β ∧
      (puAmalgam h.le).treeGraph.Adj β δ ∧ ¬ Bloc h.le L α ≤ Qv 𝔛 δ := by
  have h20 := h.hyp20
  by_contra hall
  push Not at hall
  apply hne
  refine le_inf (bloc_le_vv h α) ?_
  rw [Subgroup.le_centralizer_iff, vv_eq_iSup_vv hα]
  refine iSup₂_le fun β hβ => ?_
  have hβH : ¬ IsMVtx 𝔛 β := (isMVtx_iff_of_adj _ hβ).mp hα
  rw [vv_eq_iSup_of_not_isMVtx hβH]
  refine iSup₂_le fun δ hδ => ?_
  have hδM : IsMVtx 𝔛 δ := by
    have := isMVtx_iff_of_adj _ (show (puAmalgam h.le).treeGraph.Adj β δ from hδ)
    tauto
  rw [Subgroup.le_centralizer_iff]
  exact (hall β δ hβ hδ).trans (Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hδM))

end Main

end CFSG.Quasithin.MS93.S46.I467

