module

public import CFSG.Quasithin.Vol2.Ch11SecE3LieMain
public import CFSG.Quasithin.EmptyFaithful.E22PRes

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3

open CFSG.Open CFSG.Quasithin

@[expose] def E114ForE22R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup (ASInputs.FStar G) → quasithinIsSylowTwo T →
    CFSG.generalizedFitting G ⊔ T = ⊤ →
      (∀ n : ℕ, 1 ≤ n → SecB.TypeLie n (ASInputs.FStar G) → E1.nParam (⊤ : Subgroup G) = n) ∧
      (E2.E22N.TypeOneRes (ASInputs.FStar G) → E1.nParam (⊤ : Subgroup G) ≤ 1)

theorem e114ForE22R_of (hC : E114LieCited) (h1 : E2.E22N.E114OneRes) : E114ForE22R := by
  intro G _ _ T hSQ hFs hT hFT
  exact ⟨fun _ hn hty => nParam_eq_of_typeLie hC hSQ hFs hT hFT
    (fun h => h1 G T hSQ hFs hT hFT (h.imp_right Or.inl)) hn hty, h1 G T hSQ hFs hT hFT⟩

end CFSG.Quasithin.Vol2.Ch11.SecE3
