module

public import CFSG.Quasithin.Background.GoldschmidtE23Two
public import CFSG.Quasithin.Background.GoldschmidtE23One

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B2F

namespace GE23

section Main

variable {Γ : Type} [Group Γ] [Finite Γ] {H T M V : Subgroup Γ} (hV : IsElemAbelian 2 V)

@[expose] def ThreeClause (H T V : Subgroup Γ) (hV : IsElemAbelian 2 V) : Prop :=
  (∀ L ∈ B69.blkFamily (autI hV H), E2.IsA5Module L) →
    autI hV (baum T) = autI hV (thompsonJ T) ∧
    autI hV (thompsonJ T) = ⨆ L ∈ B69.blkFamily (autI hV H), (L ⊓ autI hV (thompsonJ T)) ∧
    ∀ L ∈ B69.blkFamily (autI hV H), Nat.card ↥(L ⊓ autI hV (thompsonJ T)) = 4 ∧
      ∃ θ : ↥L ≃* Equiv.Perm (Fin 5), L ⊓ autI hV (thompsonJ T) =
        Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ autI hV T ∧ (θ ⟨x, hx⟩).IsSwap}

theorem e23Concl_of_three (hP4 : AsB15Part4)
    (hComp : B69.AsB69Component) (hone : B69One) (h22 : E2.E22StatementNoN)
    (h : MinParabolic H T M) (hsq : SQTKGroup ↥H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ)) (hns : ¬ Group.IsSolvable ↥H)
    (hthree : ThreeClause H T V hV) : E2.E23Concl H T V hV := by
  obtain ⟨hK, hcard, hJI, hcomm, hind, hconj, htype⟩ :=
    e23_one hV hP4 hComp h22 h hsq hred hJ hns
  obtain ⟨hsup, hinf⟩ := e23_one_module hV hP4 hComp h22 h hsq hred hJ hns
  exact ⟨hK, B69.blkFamily (autI hV H), hcard, hJI, hcomm, hind, hconj, htype, hsup, hinf,
    fun hnat => e23_two_nat hV hP4 hComp hone h22 h hsq hred hJ hns hnat, hthree⟩

end Main

end GE23

end CFSG.Quasithin
