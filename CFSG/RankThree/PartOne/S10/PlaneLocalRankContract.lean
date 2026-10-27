module

public import CFSG.RankThree.PartOne.S10.CentralCoverContract
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCommutatorFactorization

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.CentralCover
open CFSG.LocalAnalysis.ComponentInitial

@[expose] noncomputable def centerQuotientConjOfLe {H : Type} [Group H] (X M : Subgroup H)
    (hM : M ≤ Subgroup.normalizer (X : Set H)) : M →* MulAut (↥X ⧸ Subgroup.center ↥X) :=
  (ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥X).comp
    (X.normalizerMonoidHom.comp (Subgroup.inclusion hM))

@[expose] def innerAutomorphisms (V : Type*) [Group V] : Subgroup (MulAut V) :=
  (MulAut.conj : V →* MulAut V).range

structure SourceSixThirteenSetup {H : Type} [Group H] (X A₀ : Subgroup H) (b c y : H) : Prop where
  quasisimple : CFSG.IsQuasisimple ↥X
  normalizes : A₀ ≤ Subgroup.normalizer (X : Set H)
  elementary : IsElementaryAbelian 5 A₀
  card : Nat.card A₀ = 125
  generated : A₀ = Subgroup.zpowers b ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers y
  centralizer_eq : A₀ ⊓ Subgroup.centralizer (X : Set H) = Subgroup.zpowers b
  y_mem : y ∈ X

theorem SourceSixThirteenSetup.b_mem {H : Type} [Group H] {X A₀ : Subgroup H} {b c y : H}
    (h : SourceSixThirteenSetup X A₀ b c y) : b ∈ A₀ := by
  rw [h.generated]
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))

theorem SourceSixThirteenSetup.c_mem {H : Type} [Group H] {X A₀ : Subgroup H} {b c y : H}
    (h : SourceSixThirteenSetup X A₀ b c y) : c ∈ A₀ := by
  rw [h.generated]
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))

theorem SourceSixThirteenSetup.c_normalizes {H : Type} [Group H] {X A₀ : Subgroup H}
    {b c y : H} (h : SourceSixThirteenSetup X A₀ b c y) :
    c ∈ Subgroup.normalizer (X : Set H) :=
  h.normalizes h.c_mem

theorem SourceSixThirteenSetup.bigM_le {H : Type} [Group H] {X A₀ : Subgroup H} {b c y : H}
    (h : SourceSixThirteenSetup X A₀ b c y) : X ⊔ A₀ ≤ Subgroup.normalizer (X : Set H) :=
  sup_le Subgroup.le_normalizer h.normalizes

theorem SourceSixThirteenSetup.bigMOne_le {H : Type} [Group H] {X A₀ : Subgroup H}
    {b c y : H} (h : SourceSixThirteenSetup X A₀ b c y) :
    X ⊔ Subgroup.zpowers c ≤ Subgroup.normalizer (X : Set H) :=
  sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr h.c_normalizes)

namespace SourceSixThirteen

variable {H : Type} [Group H] {X A₀ : Subgroup H} {b c y : H}

@[expose] noncomputable def lam (h : SourceSixThirteenSetup X A₀ b c y) :
    A₀ →* MulAut (↥X ⧸ Subgroup.center ↥X) :=
  centerQuotientConjOfLe X A₀ h.normalizes

@[expose] noncomputable def beta (h : SourceSixThirteenSetup X A₀ b c y) :
    MulAut (↥X ⧸ Subgroup.center ↥X) :=
  lam h ⟨c, h.c_mem⟩

@[expose] noncomputable def eta (h : SourceSixThirteenSetup X A₀ b c y) :
    MulAut (↥X ⧸ Subgroup.center ↥X) :=
  MulAut.conj (centerQuotientMap ↥X ⟨y, h.y_mem⟩)

@[expose] noncomputable def Lambda (h : SourceSixThirteenSetup X A₀ b c y) :
    Subgroup (MulAut (↥X ⧸ Subgroup.center ↥X)) :=
  (lam h).range

@[expose] noncomputable def Gamma (h : SourceSixThirteenSetup X A₀ b c y) :
    Subgroup (MulAut (↥X ⧸ Subgroup.center ↥X)) :=
  innerAutomorphisms (↥X ⧸ Subgroup.center ↥X) ⊔ Lambda h

@[expose] noncomputable def psi (h : SourceSixThirteenSetup X A₀ b c y) :
    ↥(X ⊔ A₀) →* MulAut (↥X ⧸ Subgroup.center ↥X) :=
  centerQuotientConjOfLe X (X ⊔ A₀) h.bigM_le

@[expose] noncomputable def psiOne (h : SourceSixThirteenSetup X A₀ b c y) :
    ↥(X ⊔ Subgroup.zpowers c) →* MulAut (↥X ⧸ Subgroup.center ↥X) :=
  centerQuotientConjOfLe X (X ⊔ Subgroup.zpowers c) h.bigMOne_le

variable (h : SourceSixThirteenSetup X A₀ b c y)

@[expose] def ActionFacts : Prop :=
  (lam h).ker.map A₀.subtype = Subgroup.zpowers b ∧
    Lambda h = Subgroup.zpowers (beta h) ⊔ Subgroup.zpowers (eta h) ∧ Nat.card (Lambda h) = 25 ∧
    orderOf (beta h) = 5 ∧ orderOf (eta h) = 5

@[expose] def PsiFacts : Prop :=
  (psi h).range = Gamma h ∧ (psiOne h).range = Gamma h ∧
    (psi h).ker = ((X ⊔ A₀) ⊓ Subgroup.centralizer (X : Set H)).subgroupOf (X ⊔ A₀) ∧
    (psiOne h).ker = ((X ⊔ Subgroup.zpowers c) ⊓ Subgroup.centralizer (X : Set H)).subgroupOf
      (X ⊔ Subgroup.zpowers c) ∧
    (∀ x : ↥X, psi h ⟨x, Subgroup.mem_sup_left x.2⟩ = MulAut.conj (centerQuotientMap ↥X x) ∧
      (psi h ⟨x, Subgroup.mem_sup_left x.2⟩ = 1 ↔ x ∈ Subgroup.center ↥X)) ∧
    (∀ x : ↥X, psiOne h ⟨x, Subgroup.mem_sup_left x.2⟩ = MulAut.conj (centerQuotientMap ↥X x) ∧
      (psiOne h ⟨x, Subgroup.mem_sup_left x.2⟩ = 1 ↔ x ∈ Subgroup.center ↥X))

@[expose] def AlmostSimpleFacts : Prop :=
  innerAutomorphisms (↥X ⧸ Subgroup.center ↥X) ≤ Gamma h ∧
    ((innerAutomorphisms (↥X ⧸ Subgroup.center ↥X)).subgroupOf (Gamma h)).Normal ∧
    IsSimpleGroup (innerAutomorphisms (↥X ⧸ Subgroup.center ↥X)) ∧
    (∃ u v : innerAutomorphisms (↥X ⧸ Subgroup.center ↥X), u * v ≠ v * u) ∧
    Gamma h ⊓ Subgroup.centralizer
      ((innerAutomorphisms (↥X ⧸ Subgroup.center ↥X) : Subgroup _) : Set _) = ⊥ ∧
    ((innerAutomorphisms (↥X ⧸ Subgroup.center ↥X)).relIndex (Gamma h) = 1 ∨
      (innerAutomorphisms (↥X ⧸ Subgroup.center ↥X)).relIndex (Gamma h) = 5)

@[expose] def RankFacts [Finite H] : Prop :=
  evenRank H ≤ 3 →
  (∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 5 →
      localRank p (Gamma h) = localRank p (↥X ⧸ Subgroup.center ↥X)) ∧
    (¬ 5 ∣ Nat.card (Subgroup.center ↥X) → localRank 5 (Gamma h) ≤ localRank 5 H ∧
      localRank 5 H ≤ 3) ∧
    (evenRank (↥X ⧸ Subgroup.center ↥X) ≤ 3 → ¬ 5 ∣ Nat.card (Subgroup.center ↥X) →
      evenRank (Gamma h) ≤ 3)

@[expose] def InnerFacts [Finite H] : Prop :=
  (∃ v : ↥X ⧸ Subgroup.center ↥X, beta h = MulAut.conj v) →
    Gamma h = innerAutomorphisms (↥X ⧸ Subgroup.center ↥X) ∧
    localRank 5 (Gamma h) = localRank 5 (↥X ⧸ Subgroup.center ↥X) ∧
    (3 < localRank 5 (Gamma h) ↔
      ∃ U : Subgroup (↥X ⧸ Subgroup.center ↥X), IsPGroup 2 U ∧ U ≠ ⊥ ∧
        ∃ E : Subgroup (↥X ⧸ Subgroup.center ↥X),
          E ≤ Subgroup.normalizer (U : Set (↥X ⧸ Subgroup.center ↥X)) ∧
          IsElementaryAbelian 5 E ∧ Nat.card E = 5 ^ 4)

@[expose] def OuterLocalConfiguration : Prop :=
  ∀ U : Subgroup (MulAut (↥X ⧸ Subgroup.center ↥X)), U ≤ Gamma h → IsPGroup 2 U → U ≠ ⊥ →
  ∀ E : Subgroup (MulAut (↥X ⧸ Subgroup.center ↥X)), E ≤ Gamma h → E ≤ Subgroup.normalizer
      (U : Set (MulAut (↥X ⧸ Subgroup.center ↥X))) → IsElementaryAbelian 5 E →
    Nat.card E = 5 ^ 4 → ¬ E ≤ innerAutomorphisms (↥X ⧸ Subgroup.center ↥X) →
  ∃ T : Subgroup H, T ≤ X ⊔ Subgroup.zpowers c ∧
    T.subgroupOf (X ⊔ Subgroup.zpowers c) ≤ U.comap (psiOne h) ∧ IsPGroup 2 T ∧
    (∀ T' : Subgroup H, T' ≤ X ⊔ Subgroup.zpowers c →
      T'.subgroupOf (X ⊔ Subgroup.zpowers c) ≤ U.comap (psiOne h) → IsPGroup 2 T' → T' ≤ T) ∧
    (T.subgroupOf (X ⊔ Subgroup.zpowers c)).map (psiOne h) = U ∧
    (Subgroup.normalizer (U : Set (MulAut (↥X ⧸ Subgroup.center ↥X)))).comap (psiOne h) =
      (Subgroup.normalizer (T : Set H)).subgroupOf (X ⊔ Subgroup.zpowers c) ∧
    (Subgroup.center ↥X).map X.subtype ≤ Subgroup.normalizer (T : Set H) ∧
  ∀ P : Subgroup H, P ≤ ((E.comap (psiOne h)).map (X ⊔ Subgroup.zpowers c).subtype) →
    IsPGroup 5 P →
    (∀ P' : Subgroup H, P' ≤ ((E.comap (psiOne h)).map (X ⊔ Subgroup.zpowers c).subtype) →
      IsPGroup 5 P' → P ≤ P' → P' = P) →
    (centerPCore 5 ↥X).map X.subtype ≠ ⊥ ∧ P ≤ Subgroup.normalizer (T : Set H) ∧
    CFSG.pRank 5 ↥P ≤ 3 ∧
    P ⊓ (Subgroup.center ↥X).map X.subtype = (centerPCore 5 ↥X).map X.subtype ∧
    (P.subgroupOf (X ⊔ Subgroup.zpowers c)).map (psiOne h) = E ∧
    ((P ⊓ X).subgroupOf P).Normal ∧ (P ⊓ X).relIndex P = 5 ∧
    ((P ⊓ X).subgroupOf (X ⊔ Subgroup.zpowers c)).map (psiOne h) =
      E ⊓ innerAutomorphisms (↥X ⧸ Subgroup.center ↥X) ∧
    Nat.card (E ⊓ innerAutomorphisms (↥X ⧸ Subgroup.center ↥X) : Subgroup _) = 5 ^ 3 ∧
    (centerPCore 5 ↥X).map X.subtype ≤ P ⊓ X ∧
    (∀ x ∈ P ⊓ X, ∀ a ∈ (centerPCore 5 ↥X).map X.subtype, x * a = a * x) ∧
    CFSG.pRank 5 ↥((centerPCore 5 ↥X).map X.subtype) ≤ 3 ∧
    (∃ _ : (((centerPCore 5 ↥X).map X.subtype).subgroupOf (P ⊓ X)).Normal,
      IsElementaryAbelian 5 (↥(P ⊓ X) ⧸ ((centerPCore 5 ↥X).map X.subtype).subgroupOf (P ⊓ X))) ∧
    ((∀ x ∈ P, ∀ a ∈ (centerPCore 5 ↥X).map X.subtype, x * a = a * x) ↔
      (∀ a ∈ (centerPCore 5 ↥X).map X.subtype, c * a = a * c)) ∧
    ((∀ a ∈ (centerPCore 5 ↥X).map X.subtype, c * a = a * c) →
      ∃ d : ℕ, Nat.card {a : ↥P // a ∈ ((centerPCore 5 ↥X).map X.subtype).subgroupOf P ∧
          a ^ 5 = 1} = 5 ^ d ∧
        ∃ _ : (((centerPCore 5 ↥X).map X.subtype).subgroupOf P).Normal,
          CentralOddExtensionExactlyOneCase (((centerPCore 5 ↥X).map X.subtype).subgroupOf P)
            5 d) ∧
    ((¬ ∀ a ∈ (centerPCore 5 ↥X).map X.subtype, c * a = a * c) →
      ∃ hc : c ∈ Subgroup.normalizer (((centerPCore 5 ↥X).map X.subtype : Subgroup H) : Set H),
        orderOf (((centerPCore 5 ↥X).map X.subtype).normalizerMonoidHom ⟨c, hc⟩) = 5) ∧
    ∀ d ∈ P, d ∉ X → ∃ u ∈ X, ∃ i : ℕ, 1 ≤ i ∧ i ≤ 4 ∧ d = u * c ^ i ∧
      ∀ z ∈ (Subgroup.center ↥X).map X.subtype, d * z * d⁻¹ = c ^ i * z * (c ^ i)⁻¹

@[expose] def OuterFacts : Prop :=
  (¬ ∃ v : ↥X ⧸ Subgroup.center ↥X, beta h = MulAut.conj v) →
    X ⊓ Subgroup.zpowers c = ⊥ ∧
    (psiOne h).ker.map (X ⊔ Subgroup.zpowers c).subtype = (Subgroup.center ↥X).map X.subtype ∧
    (innerAutomorphisms (↥X ⧸ Subgroup.center ↥X)).relIndex (Gamma h) = 5 ∧
    OuterLocalConfiguration h

@[expose] def SubgroupFacts : Prop :=
  ∀ S : Subgroup H, S ≤ X → A₀ ≤ Subgroup.normalizer (S : Set H) →
    (∀ φ ∈ Lambda h, ((S.subgroupOf X).map (centerQuotientMap ↥X)).map φ.toMonoidHom =
      (S.subgroupOf X).map (centerQuotientMap ↥X)) ∧
    (⁅S, Subgroup.zpowers c⁆ = S →
      actionCommutator (Subgroup.zpowers (beta h))
        ((S.subgroupOf X).map (centerQuotientMap ↥X)) =
      (S.subgroupOf X).map (centerQuotientMap ↥X)) ∧
    ∀ x ∈ S.subgroupOf X, centerQuotientMap ↥X x = 1 ↔ x ∈ Subgroup.center ↥X

end SourceSixThirteen

end CFSG.RankThree.PartOne
