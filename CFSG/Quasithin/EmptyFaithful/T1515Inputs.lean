module

public import CFSG.Quasithin.EmptyFaithful.T1515Concl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure Ctx1515 (T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G) : Prop where
  qtfe : quasithinQTFE14Cat G T Mc
  mf : IsMf T Mc M
  ce : IsCE1513 T M
  setting : Setting1516 T Mc M Z₁ Z₂ V₁ V₂

@[expose] def Construction1516Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → Ce15Four T Mc M →
    ∃ Z₁ Z₂ V₁ V₂ : Subgroup G, Setting1516X T Mc M Z₁ Z₂ V₁ V₂

@[expose] def Construction1516Six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → (∃ p : ℕ, (p = 3 ∨ p = 5) ∧ Ce15Six T Mc M p) →
    ∃ Z₁ Z₂ V₁ V₂ : Subgroup G, Setting1516X T Mc M Z₁ Z₂ V₁ V₂

@[expose] def Construction1516Seven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → Ce15Seven T Mc M →
    ∃ Z₁ Z₂ V₁ V₂ : Subgroup G, Setting1516X T Mc M Z₁ Z₂ V₁ V₂

structure Construction1516 : Prop where
  four : Construction1516Four
  six : Construction1516Six
  seven : Construction1516Seven

theorem Construction1516.exists_setting (h : Construction1516) {G : Type} [Group G] [Finite G]
    {T Mc M : Subgroup G} (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) (hCE : IsCE1513 T M)
    (hce : Ce15 T Mc M) : ∃ Z₁ Z₂ V₁ V₂ : Subgroup G, Setting1516X T Mc M Z₁ Z₂ V₁ V₂ := by
  rcases hce with h4 | h6 | h7
  · exact h.four G T Mc M hq hM hCE h4
  · exact h.six G T Mc M hq hM hCE h6
  · exact h.seven G T Mc M hq hM hCE h7

@[expose] def AS116Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], quasithinEvenCharacteristic G →
    ∀ (B H S T M : Subgroup G) (z : G), IsPGroup 2 B → B ≠ ⊥ →
      B ⊔ Subgroup.centralizer (B : Set G) ≤ H → H ≤ Subgroup.normalizer (B : Set G) →
      IsSylowTwoOf S H → IsSylowTwoOf T ⊤ → S ≤ T → z ∈ T →
      z ∈ Subgroup.centralizer (T : Set G) → z ≠ 1 → z ^ 2 = 1 → quasithinIsMaxTwoLocal M →
      Subgroup.centralizer ({z} : Set G) ≤ M → Lemma115Hyp H S M z

@[expose] def Lemma15119Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Concl T Mc M Z₁ V₂

@[expose] def Lemma15120Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Concl T Mc M Z₁ V₂ → IsL1520 T Mc Z₁ L →
    (CharTwo L → ⁅L, thompsonJ (s1516 T Z₁)⁆ = L ∧
      (Case15120TwoA T Mc Z₁ L ∨ Case15120TwoB T Mc Z₁ L ∨ Case15120TwoC Mc Z₁ L)) ∧
    (IsComponentOf L (g1_1516 Z₁) → IsPGroup 2 (Subgroup.center ↥L) ∧
      (Case15120ThreeA Mc Z₁ L ∨ Case15120ThreeB Mc Z₁ L ∨ Case15120ThreeC T Mc Z₁ L ∨
        Case15120ThreeD T Mc Z₁ L ∨ Case15120ThreeE T Mc Z₁ L))

@[expose] def Lemma15121Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Concl T Mc M Z₁ V₂ → Lemma15121Concl Mc Z₁ L

@[expose] def Lemma15122Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Concl T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15120Concl T Mc M Z₁ L →
    Lemma15121Concl Mc Z₁ L → Lemma15122Concl T Mc M Z₁ L

@[expose] def Lemma15123Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Concl T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15122Concl T Mc M Z₁ L →
    ∀ p : ℕ, (p = 3 ∨ p = 5) → Ce15Six T Mc M p → p = 3

@[expose] def Lemma15124Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Concl T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15122Concl T Mc M Z₁ L →
    Ce15Small T Mc M → (Ce15Four T Mc M ∨ Ce15Six T Mc M 3) ∧ ¬ IsLnBlock L 3

@[expose] def Lemma15125Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Concl T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15122Concl T Mc M Z₁ L →
    Lemma15124Concl T Mc M Z₁ V₁ V₂ L →
    L = oPrimeResidualOf 3 (g1_1516 Z₁) ∧ ¬ IsSporadic .M11 ↥L ∧
      ¬ V₁ ≤ Subgroup.centralizer (L : Set G) ∧ ¬ IsAltBlockType L 7

@[expose] def Lemma15127Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Concl T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15122Concl T Mc M Z₁ L →
    Lemma15124Concl T Mc M Z₁ V₁ V₂ L → Lemma15125Concl T Z₁ V₁ L → Lemma15126Concl L →
    Lemma15127Concl Z₂ L

@[expose] def Lemma15128Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Concl T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15122Concl T Mc M Z₁ L →
    Lemma15124Concl T Mc M Z₁ V₁ V₂ L → Lemma15125Concl T Z₁ V₁ L → Lemma15126Concl L →
    Lemma15127Concl Z₂ L → Lemma15128Concl T Mc Z₁ Z₂ L

@[expose] def Lemma15129Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Concl T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15122Concl T Mc M Z₁ L →
    Lemma15124Concl T Mc M Z₁ V₁ V₂ L → Lemma15125Concl T Z₁ V₁ L → Lemma15126Concl L →
    Lemma15127Concl Z₂ L → Lemma15128Concl T Mc Z₁ Z₂ L → Lemma15129Concl Z₂ L

end CFSG.Quasithin
