module

public import CFSG.Quasithin.EmptyFaithful.E22PFinal

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open

@[expose] def E114ResRestL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup (ASInputs.FStar G) → quasithinIsSylowTwo T →
    CFSG.generalizedFitting G ⊔ T = ⊤ →
    (∃ p : ℕ, p.Prime ∧ 3 < p ∧ IsPSL 2 p 2 (ASInputs.FStar G)) → E1.nParam (⊤ : Subgroup G) ≤ 1

@[expose] def E114ResRestL3Eps : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup (ASInputs.FStar G) → quasithinIsSylowTwo T →
    CFSG.generalizedFitting G ⊔ T = ⊤ →
    (∃ (s : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ (s = true → p % 4 = 3) ∧ (s = false → p % 4 = 1) ∧
      IsPSLEps3 s p 1 (ASInputs.FStar G)) → E1.nParam (⊤ : Subgroup G) ≤ 1

theorem e114OneResRest_of_L2_L3Eps (hL2 : E114ResRestL2) (hL3 : E114ResRestL3Eps) :
    E114OneResRest := by
  intro G _ _ T hSQ hFs hT hFT hres
  rcases hres with ⟨p, hp, hp3, hP, -⟩ | h3
  · exact hL2 G T hSQ hFs hT hFT ⟨p, hp, hp3, hP⟩
  · exact hL3 G T hSQ hFs hT hFT h3

end CFSG.Quasithin.E2.E22N
