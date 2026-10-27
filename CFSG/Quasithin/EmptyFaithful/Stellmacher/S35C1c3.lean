module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1c2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Sit

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open scoped commutatorElement

namespace S35.C1

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem faithful_on_order_eight (hS : Sit H M S) {δ μ : Geo H M} (hδ : vtype δ = false)
    (hμ : μ ∈ nbrs δ) {U : Subgroup G} (hCU : S34.Cb δ ≤ U) (hUV : U ≤ Vn δ)
    (hUn : stab δ ⊓ stab μ ≤ Subgroup.normalizer (U : Set G))
    (hidx : (S34.Cb δ).relIndex U = 8) {x : G} (hx : x ∈ stab δ ⊓ stab μ)
    (hxU : ∀ u ∈ U, ⁅x, u⁆ ∈ S34.Cb δ) : x ∈ Qv δ := by
  obtain ⟨θ, hθ, hs, hk, hker, hPS, hfaith, -⟩ := S34.exists_vmodel hS.glob hδ hμ
  have hker' : θ.ker = (cSecIn (stab δ) (S34.Cb δ) (Vn δ)).subgroupOf (stab δ) :=
    le_antisymm hk ((secModule_faithful_iff hs θ hθ hk).mp hfaith)
  have hgood : S34.Good δ := Or.inr (hS.orth δ hδ)
  rcases (S34.good_iff_iso hS.glob hδ hθ hs hk hker).mp hgood with he | he
  · obtain ⟨e⟩ := he
    have h := map_eq_one_of_comm_sec hs θ hθ hk e (inf_le_left : stab δ ⊓ stab μ ≤ stab δ) hPS
      hCU hUV (fun k hk' u hu => (Subgroup.mem_normalizer_iff.mp (hUn hk') u).mp hu) hidx hx
      (fun u hu => by simpa [commutatorElement_def] using hxU u hu)
    exact (hker ⟨x, hx.1⟩).mp h
  · obtain ⟨e⟩ := he
    exact absurd (isModelSec_of_iso hs θ hθ hker' e.symm)
      (fun h => not_isOrthSec_and_isNatSec (hS.orth δ hδ) h)

end S35.C1

end F53.Stellmacher

end CFSG.Quasithin
