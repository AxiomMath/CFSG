module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3A4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53 CFSG.Quasithin.F53Mod
open CFSG.Quasithin.CosetGeom CFSG.LieType.BorelTits

namespace F53B3

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem stab_eq_sup_Qv (hB : B3Base H M S) {μ β δ : Geo H M} (hμ : vtype μ = true)
    (hβδ : β ≠ δ) (hβ : β ∈ nbrs μ) (hδ : δ ∈ nbrs μ) :
    stab μ = (Qv μ ⊔ Qv β) ⊔ (Qv μ ⊔ Qv δ) := by
  rw [hB.prod μ β hβ hμ, hB.prod μ δ hδ hμ]
  exact stab_eq_sup_inf hB.amalgam hμ hβδ hβ hδ

theorem Qv_le_normalizer_inf (hB : B3Base H M S) {μ β δ : Geo H M} (hμ : vtype μ = true)
    (hβ : β ∈ nbrs μ) (hδ : δ ∈ nbrs μ) :
    Qv β ≤ Subgroup.normalizer ((Vn β ⊓ Vn δ : Subgroup G) : Set G) := by
  have hβf : vtype β = false := vtype_nbr_of_true hβ hμ
  have hμδ : μ ∈ nbrs δ := (show (graph (H ⊔ M) H M).Adj μ δ from hδ).symm
  have hμβ : (graph (H ⊔ M) H M).Adj β μ := (show (graph (H ⊔ M) H M).Adj μ β from hβ).symm
  have hZμ : Zv β ≤ Vn δ :=
    (zv_le_zv_of_adj hB hβf hμβ).trans
      (le_iSup₂_of_le (f := fun (ν : Geo H M) (_ : ν ∈ nbrs δ) => Zv ν) μ hμδ le_rfl)
  have key : ∀ q ∈ Qv β, ∀ x ∈ Vn β ⊓ Vn δ, q * x * q⁻¹ ∈ Vn β ⊓ Vn δ := by
    intro q hq x hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp
      (stab_le_normalizer_Vn β (pCoreOf_le 2 _ hq)) x).mp hx.1, ?_⟩
    have h2 : x * q * x⁻¹ * q⁻¹ ∈ Zv β :=
      comm_vn_qv_le hB hβf (Subgroup.commutator_mem_commutator hx.1 hq)
    have e : q * x * q⁻¹ = (x * q * x⁻¹ * q⁻¹)⁻¹ * x := by group
    rw [e]
    exact (Vn δ).mul_mem ((Vn δ).inv_mem (hZμ h2)) hx.2
  intro q hq
  refine mem_normalizer_of_conj_le (fun x hx => ?_) (fun x hx => ?_)
  · have hx' := mem_conjSub.mp hx
    have := key q hq _ hx'
    simpa [mul_assoc] using this
  · have hx' := mem_conjSub.mp hx
    have := key q⁻¹ ((Qv β).inv_mem hq) _ hx'
    simpa [mul_assoc] using this

theorem vn_inf_normal_of (hB : B3Base H M S) {μ β δ : Geo H M} (hδβ : δ ≠ β)
    (hμ : vtype μ = true) (hβ : β ∈ nbrs μ) (hδ : δ ∈ nbrs μ) :
    stab μ ≤ Subgroup.normalizer ((Vn β ⊓ Vn δ : Subgroup G) : Set G) := by
  have hA := hB.amalgam
  have hβf : vtype β = false := vtype_nbr_of_true hβ hμ
  have hμβ : μ ∈ nbrs β := (show (graph (H ⊔ M) H M).Adj μ β from hβ).symm
  have hμδ : μ ∈ nbrs δ := (show (graph (H ⊔ M) H M).Adj μ δ from hδ).symm
  have hQμ : Qv μ ≤ Subgroup.normalizer ((Vn β ⊓ Vn δ : Subgroup G) : Set G) :=
    le_normalizer_inf
      ((Qv_le_stab_of_mem_nbrs hA hβ).trans (stab_le_normalizer_Vn β))
      ((Qv_le_stab_of_mem_nbrs hA hδ).trans (stab_le_normalizer_Vn δ))
  have hQβ := Qv_le_normalizer_inf hB hμ hβ hδ
  have hQδ : Qv δ ≤ Subgroup.normalizer ((Vn β ⊓ Vn δ : Subgroup G) : Set G) := by
    rw [inf_comm]
    exact Qv_le_normalizer_inf hB hμ hδ hβ
  rw [stab_eq_sup_Qv hB hμ hδβ.symm hβ hδ]
  exact sup_le (sup_le hQμ hQβ) (sup_le hQμ hQδ)

end F53B3

end CFSG.Quasithin
