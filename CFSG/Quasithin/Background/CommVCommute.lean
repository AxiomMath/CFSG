module

public import CFSG.Quasithin.Background.CommVBasics

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem apply_mem_commV_of_forall_commute {X : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ x ∈ X, g * x = x * g) {u : V} (hu : u ∈ commV X) : g u ∈ commV X :=
  commV_apply_mem_of_normalizes (fun x hx => by rw [hg x hx, mul_inv_cancel_right]; exact hx) hu

theorem apply_mem_commV_zpowers_of_commute {x g : MulAut V} (hgx : g * x = x * g) {u : V}
    (hu : u ∈ commV (Subgroup.zpowers x)) : g u ∈ commV (Subgroup.zpowers x) :=
  apply_mem_commV_of_forall_commute (fun y hy => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right hgx k).eq) hu

end CFSG.Quasithin
