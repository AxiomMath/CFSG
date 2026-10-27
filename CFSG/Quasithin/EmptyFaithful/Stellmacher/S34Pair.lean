module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S41Module

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

variable {δ δ' : Geo H M}

omit [Finite G] in
theorem PD.symm' (hp : PD δ δ') (h : ¬ Vn δ' ≤ Qv δ) : PD δ' δ :=
  ⟨hp.vδ', hp.vδ, by rw [CosetGeom.dist_comm]; exact hp.dist_eq, h⟩

theorem pd_Vn_le_stab (hG : Glob H M S) (hp : PD δ δ') : Vn δ ≤ stab δ' ∧ Vn δ' ≤ stab δ :=
  let h := hss114_d hG.amalg hG.three_le hp.dist_eq
  ⟨h.1, h.2.1⟩

theorem pairZv_nbr_le_Qv (hG : Glob H M S) {δ μ : Geo H M} (hμ : μ ∈ nbrs δ) : Zv μ ≤ Qv δ := by
  have h1 : dist μ δ = 1 :=
    dist_eq_one_iff_adj.mpr (show (graph (H ⊔ M) H M).Adj μ δ from (nbrs_symm hμ))
  exact Zv_le_Qv_of_dist_lt ((by have := hG.three_le; omega : dist μ δ < bMin H M).trans_le
    (bMin_le_bAt μ))

theorem pairVn_le_Qv (hG : Glob H M S) (δ : Geo H M) : Vn δ ≤ Qv δ :=
  iSup₂_le fun _ hμ => pairZv_nbr_le_Qv hG hμ

theorem pd_Zv_le_Qv (_hG : Glob H M S) (hp : PD δ δ') : Zv δ ≤ Qv δ' ∧ Zv δ' ≤ Qv δ := by
  have h1 : dist δ δ' < bMin H M := by have := hp.dist_eq; omega
  have h2 : dist δ' δ < bMin H M := by rw [CosetGeom.dist_comm]; exact h1
  exact ⟨Zv_le_Qv_of_dist_lt (h1.trans_le (bMin_le_bAt δ)),
    Zv_le_Qv_of_dist_lt (h2.trans_le (bMin_le_bAt δ'))⟩

theorem isElemAbelian_Vn' (hG : Glob H M S) (δ : Geo H M) : IsElemAbelian 2 (Vn δ) :=
  isElemAbelian_Vn hG.amalg hG.three_le δ

theorem comm_Vn_Qv_le (hG : Glob H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    ⁅Vn δ, Qv δ⁆ ≤ Zv δ :=
  EmptyFaithful.Stellmacher.OrdinaryProofs.commutator_Vn_Qv_le hG.amalg hδ (hG.central δ hδ)

theorem pd_not_comm_le (hG : Glob H M S) (hp : PD δ δ') : ¬ ⁅Vn δ, Vn δ'⁆ ≤ Zv δ' := by
  intro hc
  have hz : Zv δ' = quasithinOmegaOneCenter (stab δ') :=
    Zv_eq_omegaOneCenter_of_central hG.amalg (hG.central δ' hp.vδ')
  refine hp.not_le fun a ha => hss114_e hG.amalg hz a ((pd_Vn_le_stab hG hp).1 ha) fun v hv => ?_
  exact hc (Subgroup.commutator_mem_commutator ha hv)

theorem pd_relIndex (hG : Glob H M S) (hp : PD δ δ') :
    2 ≤ (Vn δ ⊓ Qv δ').relIndex (Vn δ) ∧ (Vn δ ⊓ Qv δ').relIndex (Vn δ) ≤ 4 := by
  refine ⟨?_, ?_⟩
  · have h0 : (Vn δ ⊓ Qv δ').relIndex (Vn δ) ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : (Vn δ ⊓ Qv δ').relIndex (Vn δ) ≠ 1 := by
      intro h
      exact hp.not_le (Subgroup.relIndex_eq_one.mp h |>.trans inf_le_right)
    omega
  · exact relIndex_le_four_of_elemAbelian (quot_stab_five hG.amalg hp.vδ')
      (pd_Vn_le_stab hG hp).1 (isElemAbelian_Vn' hG δ)

theorem card_Zv_eq_of_vtype (_hG : Glob H M S) {δ δ' : Geo H M} (hδ : vtype δ = false)
    (hδ' : vtype δ' = false) : Nat.card (Zv δ) = Nat.card (Zv δ') := by
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq (hδ.trans hδ'.symm)
  rw [Zv_smul]
  exact (Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective).symm

theorem Zv_le_Zv_nbr (hG : Glob H M S) {δ μ : Geo H M} (hδ : vtype δ = false)
    (hμ : μ ∈ nbrs δ) : Zv δ ≤ Zv μ :=
  (Zv_eq_omegaOneCenter_inf hG.amalg hμ (hG.central δ hδ)).2

end S34

end F53.Stellmacher

end CFSG.Quasithin
