module

public import CFSG.Quasithin.EmptyFaithful.S146P1
public import CFSG.Quasithin.EmptyFaithful.S146zHCore

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

theorem input14613AP_proof : Input14613AP := by
  intro G _ _ T M S H PQ p hred H₀ H₁ H₂ t h γ γ' g hs hD
  have tv := S.tvData hred.isHTM hs hD
  rcases h.exists_nontrivial S hred tv with ⟨x, hx, u, hu, hn⟩ | ⟨x, hx, u, hu, hn⟩
  · exact Or.inl (h.case13One_of_tv S hred tv hx hu hn)
  · exact Or.inr (h.swap.case13One_of_tv S hred tv hx hu hn)

end CFSG.Quasithin
