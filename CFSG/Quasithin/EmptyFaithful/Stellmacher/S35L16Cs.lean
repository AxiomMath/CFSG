module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Lat
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35L16Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.L16

open S35.Std S35.Fin S35.At S35.Ch2
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def cI (hS : Sit H M S) (δ : Geo H M) {q : G} (hq : q ∈ stab δ) : Subgroup G :=
  commImg (Vn_isElemAbelian hS δ).1 (Vn_normal δ hq)

theorem mem_cI {hS : Sit H M S} {δ : Geo H M} {q : G} {hq : q ∈ stab δ} {x : G} :
    x ∈ cI hS δ hq ↔ ∃ a ∈ Vn δ, x = q * a * q⁻¹ * a⁻¹ := mem_commImg

theorem comm_mem_cI (hS : Sit H M S) (δ : Geo H M) {q : G} (hq : q ∈ stab δ) {a : G}
    (ha : a ∈ Vn δ) : q * a * q⁻¹ * a⁻¹ ∈ cI hS δ hq := y_mul_mem_commImg ha

theorem relIndex_cI_Zv (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) {q : G}
    (hq : q ∈ stab δ) :
    (cI hS δ hq ⊓ Zv δ).relIndex (cI hS δ hq) = secIdx (Subgroup.zpowers q) (Zv δ) (Vn δ) :=
  relIndex_commImg (Vn_isElemAbelian hS δ).1 (Vn_normal δ hq)
    (stab_le_normalizer_Zv hS.glob.amalg δ hq) (Zv_le_Vn_S5 hS hδ)

theorem relIndex_cI_Cb (hS : Sit H M S) (δ : Geo H M) {q : G} (hq : q ∈ stab δ) :
    (cI hS δ hq ⊓ Cb δ).relIndex (cI hS δ hq) = secIdx (Subgroup.zpowers q) (Cb δ) (Vn δ) :=
  relIndex_commImg (Vn_isElemAbelian hS δ).1 (Vn_normal δ hq)
    (S34.bl12_stab_le_normalizer_Cb δ hq) (S34.Cb_le_Vn δ)

omit [Finite G] in
theorem secIdx_Zv_eq_idx (hRk : S35.II.RkZvEq H M) {δ : Geo H M} (c : Chart2 δ)
    (hδ : vtype δ = false) {q : G} (hq : q ∈ stab δ) :
    secIdx (Subgroup.zpowers q) (Zv δ) (Vn δ) = idx orth (c.θ ⟨q, hq⟩) := by
  rw [hRk δ hδ q hq]
  exact c.secIdx_eq_idx hq

end S35.L16

end F53.Stellmacher

end CFSG.Quasithin
