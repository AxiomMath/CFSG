module

public import CFSG.Quasithin.EmptyFaithful.S1422Elim
public import CFSG.GH74.M12.Statements

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

structure Lemma14221Local : Prop where
  tits : ∀ (G : Type) [Group G] [Finite G] (T M Y H : Subgroup G), Setting1422 T M Y H →
    CaseTits H (Y ⊔ T) → H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)
  twoF4 : ∀ (G : Type) [Group G] [Finite G] (T M Y H : Subgroup G), Setting1422 T M Y H →
    Case2F4 H (Y ⊔ T) → H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)
  g2 : ∀ (G : Type) [Group G] [Finite G] (T M Y H : Subgroup G), Setting1422 T M Y H →
    CaseG2 H (Y ⊔ T) → H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)
  g22p : ∀ (G : Type) [Group G] [Finite G] (T M Y H : Subgroup G), Setting1422 T M Y H →
    CaseG22P H (Y ⊔ T) → H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)
  m12 : ∀ (G : Type) [Group G] [Finite G] (T M Y H : Subgroup G), Setting1422 T M Y H →
    CaseM12 H (Y ⊔ T) → H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)
  autM12 : ∀ (G : Type) [Group G] [Finite G] (T M Y H : Subgroup G), Setting1422 T M Y H →
    CaseAutM12 H (Y ⊔ T) → H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)

@[expose] def F431Statement : Prop :=
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
      Nonempty (G ≃* MulAut quasithinTits)) ∧
  (∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ (H₁ H₂ : Subgroup G) (z : G),
      IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H₁ H₂) (IsG2Over 1) →
      IsL2Quot 1 (oTwoQuot ↥H₁) → IsSpecialPow 2 2 2 ↥(pCoreOf 2 H₁) → z ∈ H₁ → z ≠ 1 →
      z ^ 2 = 1 → H₁ ≤ Subgroup.centralizer ({z} : Set G) →
      Subgroup.centralizer ({z} : Set G) ≤ H₁ →
      Nonempty (G ≃* MulAut (PSU3 3 1)))

@[expose] def ModelNotSimple : Prop :=
  ¬ IsSimpleGroup (MulAut quasithinTits) ∧ ¬ IsSimpleGroup (MulAut (PSU3 3 1))

@[expose] def G22pAmalgamFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P₁ P₂ : Subgroup G),
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups P₁ P₂)
      (fun Y _ => Nonempty (Y ≃* PSU3 3 1)) →
    Nonempty (↥(P₁ ⊓ P₂) ≃* WreathedTwoGroup 2)

@[expose] def M12AmalgamFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H₁ H₂ : Subgroup G),
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H₁ H₂)
      (fun Y _ => Nonempty (Y ≃* quasithinM12)) →
    IsL2Quot 1 (oTwoQuot ↥H₁) → IsQ8Sq ↥(pCoreOf 2 H₁) → IsL2Quot 1 (oTwoQuot ↥H₂) →
    Nat.card (pCoreOf 2 H₂) = 2 ^ 5 →
    (∀ X : Sylow 3 ↥H₁, ∀ q ∈ CFSG.pCore 2 ↥H₁, (∀ x ∈ X, x * q = q * x) →
      ∀ y ∈ CFSG.pCore 2 ↥H₁, q * y = y * q) ∧
    ∃ K ∈ CFSG.GH74.M12.q8Subgroups (CFSG.pCore 2 ↥H₁), K.Normal

@[expose] def AmalgamFusion {G : Type*} [Group G] (P₁ P₂ : Subgroup G) : G → G → Prop :=
  Relation.ReflTransGen fun x y => x ∈ P₁ ⊓ P₂ ∧ y ∈ P₁ ⊓ P₂ ∧
    ((∃ h ∈ P₁, h * x * h⁻¹ = y) ∨ ∃ h ∈ P₂, h * x * h⁻¹ = y)

@[expose] def AutM12AmalgamFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P₁ P₂ : Subgroup G),
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups P₁ P₂)
      (fun Y _ => Nonempty (Y ≃* MulAut quasithinM12)) →
    IsL2Quot 1 (oTwoQuot ↥P₁) → IsAutM12Vertex P₁ → IsL2Quot 1 (oTwoQuot ↥P₂) →
    Nat.card (pCoreOf 2 P₂) = 2 ^ 6 →
    ∃ R : Subgroup G, R ≤ P₁ ⊓ P₂ ∧ R.relIndex (P₁ ⊓ P₂) = 2 ∧
      IsElemAbelian 2 (thompsonJ (P₁ ⊓ P₂)) ∧
      P₂ ≤ Subgroup.normalizer (thompsonJ (P₁ ⊓ P₂) : Set G) ∧
      (∃ j ∈ thompsonJ (P₁ ⊓ P₂), j ∉ R) ∧
      (∀ j ∈ thompsonJ (P₁ ⊓ P₂), j ∉ R → ∀ y ∈ P₂, y * j * y⁻¹ ∉ R) ∧
      ∀ r ∈ R, r ^ 2 = 1 → ∃ j ∈ thompsonJ (P₁ ⊓ P₂) ⊓ R, AmalgamFusion P₁ P₂ r j

end CFSG.Quasithin
