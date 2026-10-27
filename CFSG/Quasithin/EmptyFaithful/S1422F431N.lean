module

public import CFSG.Quasithin.EmptyFaithful.S1422Inputs
public import CFSG.Quasithin.Vol2.GoldschmidtF431q2G2Main

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

@[expose] def F431TitsTwoF4 : Prop :=
  (∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ (H₁ H₂ : Subgroup G) (z : G),
      IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H₁ H₂)
        (fun Y _ => Nonempty (Y ≃* quasithinTits)) →
      (Nonempty (oTwoQuot ↥H₁ ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥H₁ ≃* ↥(Sz 0))) → z ∈ H₁ →
      z ≠ 1 → z ^ 2 = 1 →
      H₁ ≤ Subgroup.centralizer ({z} : Set G) → Subgroup.centralizer ({z} : Set G) ≤ H₁ →
      Nonempty (G ≃* quasithinTits)) ∧
  (∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ (H₁ H₂ : Subgroup G) (z : G),
      IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H₁ H₂) (IsTwistedF4Over 1) →
      Nonempty (oTwoQuot ↥H₁ ≃* Sz 0) → z ∈ H₁ → z ≠ 1 → z ^ 2 = 1 →
      H₁ ≤ Subgroup.centralizer ({z} : Set G) → Subgroup.centralizer ({z} : Set G) ≤ H₁ →
      Nonempty (G ≃* MulAut quasithinTits))

theorem f431Statement_of_titsTwoF4
    (h : F431TitsTwoF4) : F431Statement :=
  ⟨h.1, h.2, H13.F431.G2Two.f431_clause_G2⟩

end CFSG.Quasithin
