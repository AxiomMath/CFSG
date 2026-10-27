module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35LpMain
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChCent

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Lp

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem claimLP (hS : Sit H M S) (hI : CaseI H M)
    (hZ : ∀ δ : Geo H M, vtype δ = false → IsOrthSec (stab δ) (Zv δ) (Vn δ))
    (hR : ∀ β l δ δ' : Geo H M, vtype β = false → l ∈ nbrs β → l ∈ nbrs δ → l ∈ nbrs δ' →
      δ ≠ β → δ' ≠ β → δ' ≠ δ →
        Vn β ⊓ Vn δ = Vn β ⊓ Vn δ' ∧ Vn β ⊓ Vn δ = Vn δ ⊓ Vn δ' ∧
          stab l ≤ Subgroup.normalizer ((Vn β ⊓ Vn δ : Subgroup G) : Set G))
    (_hclaimR : ClaimR H M) : ClaimLP H M := by
  have hC : Ch.Ctx H M S := ⟨hS, hI, hZ, hR⟩
  refine claimLP_of_dict hS (fun δ hδ => hC.nonempty_chart hδ) (fun δ c l hδ hl ε hε hne => ?_)
    (fun δ c l hδ hl => c.img_Zv_nbr hS hδ hl)
  rw [← hC.Rl_eq hδ hl hε hne]
  exact c.img_Rl hC hδ hl

end S35.Lp

end F53.Stellmacher

end CFSG.Quasithin
