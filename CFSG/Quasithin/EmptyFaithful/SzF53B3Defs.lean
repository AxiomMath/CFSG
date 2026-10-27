module

public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs
public import CFSG.Quasithin.EmptyFaithful.SzF53BasC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53 CFSG.Quasithin.F53Mod
open CFSG.Quasithin.CosetGeom

namespace F53B3

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Cv (β : Geo H M) : Subgroup G :=
  Vn β ⊓ Subgroup.centralizer (oTwoRes (stab β) : Set G)

@[expose] def Kq (β : Geo H M) : Subgroup G := Qv β ⊓ Subgroup.centralizer (Vn β : Set G)

structure B3Base (H M S : Subgroup G) : Prop where
  amalgam : F53Amalgam H M S
  b_eq : bMin H M = 3
  crit : ∀ α : Geo H M, vtype α = true → bAt α = bMin H M
  central : ∀ β : Geo H M, vtype β = false → Zv β ≤ centerOf (stab β)
  prod : ∀ α β : Geo H M, (graph (H ⊔ M) H M).Adj α β → vtype α = true →
    Qv α ⊔ Qv β = stab α ⊓ stab β
  card_two : ∀ β : Geo H M, vtype β = false → Nat.card (Zv β) = 2

structure B3Facts (H M S : Subgroup G) : Prop extends B3Base H M S where
  nat : ∀ β : Geo H M, vtype β = false → IsNatSec (stab β) (Cv β) (Vn β)

structure B3FactsO (H M S : Subgroup G) : Prop extends B3Base H M S where
  orth : ∀ β : Geo H M, vtype β = false → IsOrthSec (stab β) (Cv β) (Vn β)

structure B3Block (H M S : Subgroup G) : Prop where
  three_le_bAt : ∀ x : Geo H M, 3 ≤ bAt x
  zv_le_qv : ∀ x y : Geo H M, dist x y ≤ 2 → Zv x ≤ Qv y
  zv_le_stab : ∀ x y : Geo H M, dist x y ≤ 3 → Zv x ≤ stab y
  vn_le_qv : ∀ x y : Geo H M, dist x y ≤ 1 → Vn x ≤ Qv y
  vn_le_stab : ∀ x y : Geo H M, dist x y ≤ 2 → Vn x ≤ stab y
  elemAbelian_vn : ∀ x : Geo H M, IsElemAbelian 2 (Vn x)
  card_zv_s3 : ∀ α : Geo H M, vtype α = true → Nat.card (Zv α) = 4
  zv_le_zv : ∀ β α : Geo H M, vtype β = false → (graph (H ⊔ M) H M).Adj β α → Zv β ≤ Zv α
  comm_vn_qv : ∀ β : Geo H M, vtype β = false → ⁅Vn β, Qv β⁆ = Zv β
  cv_inf_zv : ∀ β α : Geo H M, vtype β = false → (graph (H ⊔ M) H M).Adj β α →
    Cv β ⊓ Zv α = Zv β
  kq_le_qv : ∀ β α : Geo H M, vtype β = false → (graph (H ⊔ M) H M).Adj β α → Kq β ≤ Qv α
  vn_inf_normal : ∀ δ μ β : Geo H M, δ ≠ β → vtype μ = true →
    (graph (H ⊔ M) H M).Adj μ β → (graph (H ⊔ M) H M).Adj μ δ →
    stab μ ≤ Subgroup.normalizer ((Vn β ⊓ Vn δ : Subgroup G) : Set G)
  comm_vn_vn : ∀ β γ : Geo H M, dist β γ = 2 → ⁅Vn β, Vn γ⁆ ≤ Vn β ⊓ Vn γ
  not_vn_le_qv : ∀ β γ : Geo H M, vtype β = false → dist β γ = 2 → ¬ Vn β ≤ Qv γ

omit [Finite G] in
theorem vtype_nbr_of_false {β α : Geo H M} (h : (graph (H ⊔ M) H M).Adj β α)
    (hβ : vtype β = false) : vtype α = true := by
  have := vtype_ne_of_adj h
  cases hα : vtype α
  · exact absurd (hβ.trans hα.symm) this
  · rfl

end F53B3

end CFSG.Quasithin
