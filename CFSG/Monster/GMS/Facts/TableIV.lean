module

public import CFSG.Monster.GMS.Facts.TableV

public section

namespace CFSG.Monster.GMS

variable {G : Type*} [Group G]

@[expose] def IsTwoACls (a b x : G) : Prop :=
  ∃ g ∈ Subgroup.centralizer ({a} : Set G), g * x * g⁻¹ = b ∨ g * x * g⁻¹ = a * b

@[expose] def TableIVProduct (a b : G) : Prop :=
  ∀ x ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ Subgroup.centralizer ({a} : Set G),
    IsTwoACls a b x → IsTwoACls a b y → x * y = y * x → x ≠ y → x ≠ a * y →
      ¬ IsTwoACls a b (x * y)

@[expose] def TableIVStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a b z u : G), IsTwoBabyCentralizer a → TableV a b z u →
    TableIVProduct a b

@[expose] def TableIVIn (G : Type*) [Group G] : Prop :=
  ∀ a b z u : G, IsTwoBabyCentralizer a → TableV a b z u → TableIVProduct a b

theorem TableIVStatement.inG (h : TableIVStatement) {G : Type} [Group G] [Finite G] :
    TableIVIn G :=
  fun a b z u ha hT => h G a b z u ha hT

end CFSG.Monster.GMS
