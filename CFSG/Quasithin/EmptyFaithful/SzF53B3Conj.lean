module

public import CFSG.Quasithin.EmptyFaithful.SzF53MConj
public import CFSG.Quasithin.EmptyFaithful.SzF53B3Defs
public import CFSG.Quasithin.EmptyFaithful.SzF53BasE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53 CFSG.Quasithin.F53Mod
open CFSG.Quasithin.CosetGeom

namespace F53B3

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem Cv_smul (g : ↥(H ⊔ M)) (β : Geo H M) : Cv (g • β) = conjSub (g : G) (Cv β) := by
  unfold Cv
  rw [Vn_smul, stab_smul, ← conjSub_oTwoRes, conjSub_centralizer, ← conjSub_inf]

omit [Finite G] in
theorem isModelSec_of_vtype_eq {n : ℕ} {R : Model n} {β₀ β : Geo H M} (hv : vtype β₀ = vtype β)
    (h : IsModelSec R (stab β₀) (Cv β₀) (Vn β₀)) : IsModelSec R (stab β) (Cv β) (Vn β) := by
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq hv
  rw [stab_smul, Cv_smul, Vn_smul]
  exact h.conj (g : G)

theorem isNatSec_all (_hA : F53Amalgam H M S) {β₀ : Geo H M} (hβ₀ : vtype β₀ = false)
    (h : IsNatSec (stab β₀) (Cv β₀) (Vn β₀)) :
    ∀ β : Geo H M, vtype β = false → IsNatSec (stab β) (Cv β) (Vn β) := fun _ hβ =>
  isModelSec_of_vtype_eq (hβ₀.trans hβ.symm) h

theorem isOrthSec_all (_hA : F53Amalgam H M S) {β₀ : Geo H M} (hβ₀ : vtype β₀ = false)
    (h : IsOrthSec (stab β₀) (Cv β₀) (Vn β₀)) :
    ∀ β : Geo H M, vtype β = false → IsOrthSec (stab β) (Cv β) (Vn β) := fun _ hβ =>
  isModelSec_of_vtype_eq (hβ₀.trans hβ.symm) h

end F53B3

end CFSG.Quasithin
