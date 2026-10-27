module

import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open

variable {Q : Type*} [Group Q]

theorem isElemAbelian_sup {p : ℕ} {A₁ A₂ : Subgroup Q} (h1 : IsElemAbelian p A₁)
    (h2 : IsElemAbelian p A₂) (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) :
    IsElemAbelian p (A₁ ⊔ A₂) := CFSG.Open.IsElemAbelian.sup_of_commute h1 h2 hc

theorem isElemAbelian_zpowers {p : ℕ} {x : Q} (hx : x ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
