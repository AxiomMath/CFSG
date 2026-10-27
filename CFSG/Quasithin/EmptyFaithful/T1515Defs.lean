module

public import CFSG.Quasithin.EmptyFaithful.T1515Stage
public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.Quasithin.Background.C2Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def s1516 (T Z₁ : Subgroup G) : Subgroup G := T ⊓ Subgroup.centralizer (Z₁ : Set G)

@[expose] def g1_1516 (Z₁ : Subgroup G) : Subgroup G := Subgroup.centralizer (Z₁ : Set G)

@[expose] def mZ1516 (Mc Z₁ : Subgroup G) : Subgroup G := g1_1516 Z₁ ⊓ Mc

@[expose] def q1_1516 (Mc Z₁ : Subgroup G) : Subgroup G := pCoreOf 2 (mZ1516 Mc Z₁)

@[expose] noncomputable def vE1516 (T Mc M : Subgroup G) : Subgroup G :=
  V154 T Mc M ⊓ Subgroup.centralizer (thompsonJi T 1 : Set G)

omit [Finite G] in
theorem s1516_le (T Z₁ : Subgroup G) : s1516 T Z₁ ≤ T := inf_le_left

omit [Finite G] in
theorem s1516_le_g1 (T Z₁ : Subgroup G) : s1516 T Z₁ ≤ g1_1516 Z₁ := inf_le_right

omit [Finite G] in
theorem mZ1516_le_g1 (Mc Z₁ : Subgroup G) : mZ1516 Mc Z₁ ≤ g1_1516 Z₁ := inf_le_left

omit [Finite G] in
theorem mZ1516_le_mc (Mc Z₁ : Subgroup G) : mZ1516 Mc Z₁ ≤ Mc := inf_le_right

omit [Finite G] in
theorem q1_1516_le (Mc Z₁ : Subgroup G) : q1_1516 Mc Z₁ ≤ mZ1516 Mc Z₁ := by
  unfold q1_1516
  exact CFSG.LieType.BorelTits.pCoreOf_le 2 _

@[expose] def Seven1516P (T Mc M Z₁ Z₂ V₂ : Subgroup G) : Prop :=
  IsPOnePlusTwo 3 ↥(pCoreOf 3 (autOn M (V154 T Mc M))) ∧
  ∃ P₁ P₂ : Subgroup (MulAut ↥(V154 T Mc M)),
    Nat.card P₁ = 3 ∧ Nat.card P₂ = 3 ∧ P₁ ≤ mBar0 T Mc M ∧ P₂ ≤ mBar0 T Mc M ∧
    (∃ t ∈ autOn (T ⊓ m0Of T Mc M) (V154 T Mc M),
      (∀ x ∈ P₁, t * x * t⁻¹ = x⁻¹) ∧ ∀ x ∈ P₂, t * x * t⁻¹ = x⁻¹) ∧
    ((centerOf (pCoreOf 3 (autOn M (V154 T Mc M))) : Set (MulAut ↥(V154 T Mc M))) *
        (P₁ : Set (MulAut ↥(V154 T Mc M))) * (P₂ : Set (MulAut ↥(V154 T Mc M))) =
      (pCoreOf 3 (autOn M (V154 T Mc M)) : Set (MulAut ↥(V154 T Mc M)))) ∧
    Z₁ = V154 T Mc M ⊓ Subgroup.centralizer (preOn M (V154 T Mc M) P₁ : Set G) ∧
    Z₂ = V154 T Mc M ⊓ Subgroup.centralizer (preOn M (V154 T Mc M) P₂ : Set G) ∧
    V₂ = ⁅V154 T Mc M, preOn M (V154 T Mc M) P₁⁆

structure Setting1516Extra (T Mc M Z₁ : Subgroup G) : Prop where
  s_normal : T ≤ Subgroup.normalizer (s1516 T Z₁ : Set G)
  prime_o2 : (Nat.card (oTwoUpper (autOn (M ⊓ g1_1516 Z₁) (V154 T Mc M)))).Prime

structure Setting1516 (T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G) : Prop where
  ce15 : Ce15 T Mc M
  hV : V154 T Mc M = VZ T M
  z1_ne : Z₁ ≠ ⊥
  z1_le : Z₁ ≤ vE1516 T Mc M
  z2_le : Z₂ ≤ vE1516 T Mc M
  vE_sup : Z₁ ⊔ Z₂ ≤ vE1516 T Mc M ∧ quasithinOmegaOneCenter T ≤ Z₁ ⊔ Z₂
  vE_sup_small : Ce15Small T Mc M → Z₁ ⊔ Z₂ = vE1516 T Mc M
  vE_inf : Z₁ ⊓ Z₂ = ⊥
  caseI : ¬ (M ⊓ g1_1516 Z₁) ≤ Mc
  caseI_small : Ce15Small T Mc M → (M ⊓ g1_1516 Z₁) ⊔ T = M
  sylow : IsSylowTwoOf (s1516 T Z₁) (g1_1516 Z₁ ⊓ M)
  extra_small : Ce15Small T Mc M → Setting1516Extra T Mc M Z₁
  v2_le : V₂ ≤ V154 T Mc M
  v2_comm : ⁅V₂, oTwoUpper (M ⊓ g1_1516 Z₁)⁆ = V₂
  z2_le_v2 : ¬ Ce15Seven T Mc M → Z₂ ≤ V₂
  decomp_seven : Ce15Seven T Mc M → Z₁ ⊔ V₂ = V154 T Mc M ∧ Z₁ ⊓ V₂ = ⊥
  decomp_other : ¬ Ce15Seven T Mc M →
    V₁ ≤ V154 T Mc M ∧ Z₁ ≤ V₁ ∧ V₁ ⊔ V₂ = V154 T Mc M ∧ V₁ ⊓ V₂ = ⊥
  swap_small : Ce15Small T Mc M → ¬ Ce15Seven T Mc M →
    ∀ t ∈ T, t ∉ s1516 T Z₁ → conjByElt t V₂ = V₁
  ranks_four : Ce15Four T Mc M →
    Nat.card V₁ = 4 ∧ Nat.card V₂ = 4 ∧ Nat.card Z₁ = 2 ∧ Nat.card Z₂ = 2
  ranks_six : (∃ p : ℕ, (p = 3 ∨ p = 5) ∧ Ce15Six T Mc M p) →
    Nat.card V₁ = 16 ∧ Nat.card V₂ = 16 ∧
      (Ce15Small T Mc M → Nat.card Z₁ = 4 ∧ Nat.card Z₂ = 4)
  ranks_seven : Ce15Seven T Mc M →
    Nat.card Z₁ = 4 ∧ Nat.card Z₂ = 4 ∧ Nat.card V₂ = 16 ∧ Nat.card (vE1516 T Mc M) = 16
  seven_P : Ce15Seven T Mc M → Seven1516P T Mc M Z₁ Z₂ V₂
  index_two : Ce15Small T Mc M → ¬ Ce15Seven T Mc M → (s1516 T Z₁).relIndex T = 2
  diagonal : Ce15Small T Mc M → ¬ Ce15Seven T Mc M →
    g1_1516 Z₁ ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) =
        g1_1516 Z₁ ⊓ Subgroup.centralizer (Z₂ : Set G) ∧
      s1516 T Z₁ = T ⊓ Subgroup.centralizer (Z₂ : Set G)
  index_v1 : Ce15Small T Mc M → ¬ Ce15Seven T Mc M →
    (Subgroup.centralizer (V₁ : Set G) ⊓ s1516 T Z₁).relIndex (s1516 T Z₁) = 2
  y_facts : Ce15Small T Mc M →
    (Nat.card (autOn (oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁)) (V154 T Mc M)) = 3 ∧
      ¬ oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) ≤ mZ1516 Mc Z₁ ∧
      ⁅V₂, oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁)⁆ = V₂ ∧
      oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) ≤ Subgroup.normalizer (V₂ : Set G)) ∧
    (¬ Ce15Seven T Mc M → ⁅V₁, oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁)⁆ = ⊥)
  p_sub : ∃ p : ℕ, (p = 3 ∨ p = 5) ∧ ∃ Y' : Subgroup G,
    Y' ≤ M ⊓ g1_1516 Z₁ ∧ Y' ≤ Subgroup.normalizer (thompsonJ T : Set G) ∧ IsPGroup p Y' ∧
      ((s1516 T Z₁ : Set G) * (Y' : Set G) = (Y' : Set G) * (s1516 T Z₁ : Set G)) ∧
      ⁅V₂, Y'⁆ = V₂

structure Setting1516X (T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G) : Prop extends
    Setting1516 T Mc M Z₁ Z₂ V₁ V₂ where
  s_normal : T ≤ Subgroup.normalizer (s1516 T Z₁ : Set G)
  prime_o2 : (Nat.card (oTwoUpper (autOn (M ⊓ g1_1516 Z₁) (V154 T Mc M)))).Prime

theorem Setting1516X.toExtra {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}
    (h : Setting1516X T Mc M Z₁ Z₂ V₁ V₂) : Setting1516Extra T Mc M Z₁ :=
  ⟨h.s_normal, h.prime_o2⟩

end CFSG.Quasithin
