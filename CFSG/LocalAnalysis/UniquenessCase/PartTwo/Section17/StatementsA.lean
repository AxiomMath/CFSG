module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FSqIndex
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UCFront14
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 CFSG.LocalAnalysis.UniquenessCase.UC22.F14
open scoped Pointwise commutatorElement
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def IsL2Over17 (X : Type) [Group X] (q : ℕ) : Prop :=
  ∃ (r f : ℕ), r.Prime ∧ r ≠ 2 ∧ q = r ^ f ∧ 1 ≤ f ∧ LieModel X .PSL 2 r f

@[expose] def IsL3EpsOdd17 (X : Type) [Group X] (r : ℕ) : Prop :=
  LieModel X .PSL 3 r 1 ∨ LieModel X .PSU 3 r 1

@[expose] def IsReeOver17 (X : Type) [Group X] (q : ℕ) : Prop :=
  ∃ n : ℕ, q = 3 ^ (2 * n + 1) ∧ LieModel X .twistedG2 0 3 (2 * n + 1)

@[expose] def IsLieOverOdd17 (X : Type) [Group X] (r q : ℕ) : Prop :=
  r.Prime ∧ r ≠ 2 ∧
    ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n f : ℕ),
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n r f ∧ q = r ^ f ∧ LieModel X t n r f

@[expose] noncomputable def O2ZIn17 (L : Subgroup G) : Subgroup ↥L :=
  (Subgroup.center (Bar2 L)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))

instance O2ZIn17_normal (L : Subgroup G) : (O2ZIn17 L).Normal := by
  unfold O2ZIn17
  infer_instance

abbrev BarO2Z17 (L : Subgroup G) : Type := ↥L ⧸ O2ZIn17 L

@[expose] def Concl17_6 (D : Data G) (L : Subgroup G) (r : ℕ) : Prop :=
  IsL2Over17 (Bar2 L) r ∧
    (5 < r → ∃ g : G, g ∉ D.M ∧
      3 ∈ piSet (L ⊓ D.M.map (MulAut.conj g).toMonoidHom)) ∧
    (5 < r → (∃! K : Subgroup G, K ∈ calC D.M ∧ Thin8 K ∧ CFSG.Open.pRank 3 K = 1) ∧
      ∀ K : Subgroup G, K ∈ calC D.M → ∀ n : ℕ, ¬ IsU3 (Bar2 K) (2 * n))

@[expose] def IsCounterexample17_6 (D : Data G) (L : Subgroup G) (r : ℕ) : Prop :=
  L ∈ calC D.M ∧ r ≠ 2 ∧ IsChev (BarInf L) r ∧ ¬ Concl17_6 D L r

structure Ctx17_6 (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ) : Prop where
  hyp125 : Hyp125 D V₀ V
  memL : L ∈ calC D.M
  lie : IsLieOverOdd17 (BarInf L) r q
  not_l2_five : ¬ IsL2Over17 (BarInf L) 5
  violates : ¬ Concl17_6 D L r
  prefer_not_l2 : IsL2Over17 (Bar2 L) r →
    ∀ (L' : Subgroup G) (r' : ℕ), IsCounterexample17_6 D L' r' → IsL2Over17 (Bar2 L') r'
  prefer_r7 : IsL2Over17 (Bar2 L) r →
    (∃ (L' : Subgroup G) (r' : ℕ), IsCounterexample17_6 D L' r' ∧ r' = 7) → r = 7

@[expose] def NTL17 (D : Data G) (L : Subgroup G) : Subgroup G :=
  D.T ⊓ normalizer (L : Set G)

@[expose] def P17_12_1 (r q : ℕ) (L : Subgroup G) : Prop :=
  IsL2Over17 (BarInf L) q ∨ IsL3EpsOdd17 (BarInf L) r

@[expose] def P17_12_2 (q : ℕ) (L : Subgroup G) : Prop :=
  IsReeOver17 (Bar2 L) q

@[expose] noncomputable def Delta17_12
    (D : Data G) (𝔉 : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop)
    (r q : ℕ) (L : Subgroup G) : Set (Subgroup G) := by
  classical
  exact if _ : P17_12_1 r q L then
    {H | ∃ x ∈ D.M, H = D.T ⊔ L.map (MulAut.conj x).toMonoidHom}
  else if _ : P17_12_2 q L then
    {H | ∃ X : Subgroup G, X ≤ L ∧ Permutes X (NTL17 D L) ∧ IsL2Over17 (Bar2 X) q ∧
      H = D.T ⊔ X}
  else
    {H | ∃ x ∈ D.M, ∃ X : Subgroup G,
      (let Lx := L.map (MulAut.conj x).toMonoidHom
       X ≤ Lx ∧ CFSG.Open.pCoreOf 2 Lx ≤ X ∧ H = D.T ⊔ X ∧
       (X.subgroupOf Lx).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)) ∈
         FunSet 𝔉 (Bar2 Lx)
           (((NTL17 D L ⊓ Lx).subgroupOf Lx).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx))))}

@[expose] noncomputable def iL17_12
    (D : Data G) (𝔉 : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop)
    (r q : ℕ) (L : Subgroup G) : ℕ∞ :=
  fIndexMax (Delta17_12 D 𝔉 r q L)

@[expose] def R17_1At (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : Prop :=
  (∀ X : Subgroup G, ¬ InPStar D V₀ X) ∧
    ((∃ X : Subgroup G, F11.InP11 D X) → V₀ = ⊥ ∧ D.k = 2 ∧
      mBar D.M V₀ V hV.isElemAbelian = 4)

@[expose] def R17_2_1At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (p : ℕ) (Dsub : Subgroup G),
    p.Prime → p ≠ 2 → Dsub ≤ D.M → IsPGroup p ↥Dsub → ¬ IsCyclic ↥Dsub →
    (∀ x ∈ Dsub, x ^ p = 1) → ⁅⁅Dsub, Dsub⁆, Dsub⁆ = ⊥ →
    ((Dsub ⊔ CFSG.Open.pCoreOf 2 D.M).subgroupOf D.M).Normal →
    F11.InP11 D Dsub

@[expose] def R17_2_2At (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : Prop :=
  ∀ (p : ℕ) (Dsub : Subgroup G),
    p.Prime → p ≠ 2 → Dsub ≤ D.M → IsPGroup p ↥Dsub → ¬ IsCyclic ↥Dsub →
    (∀ x ∈ Dsub, x ^ p = 1) → ⁅⁅Dsub, Dsub⁆, Dsub⁆ = ⊥ →
    ((Dsub ⊔ CFSG.Open.pCoreOf 2 D.M).subgroupOf D.M).Normal →
    Nat.card ↥Dsub = p ^ 2 ∧ V₀ = ⊥ ∧ D.k = 2 ∧
      mBar D.M V₀ V hV.isElemAbelian = 4

@[expose] def R17_2_3At (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : Prop :=
  ∀ (p : ℕ) (Dsub : Subgroup G),
    p.Prime → p ≠ 2 → Dsub ≤ D.M → IsPGroup p ↥Dsub → ¬ IsCyclic ↥Dsub →
    (∀ x ∈ Dsub, x ^ p = 1) → ⁅⁅Dsub, Dsub⁆, Dsub⁆ = ⊥ →
    ((Dsub ⊔ CFSG.Open.pCoreOf 2 D.M).subgroupOf D.M).Normal →
    ¬ IrrOn (D.M ⊓ normalizer (Dsub : Set G)) Dsub ∧
      Nat.card ↥(barSub V₀ V hV.isElemAbelian Dsub) = p

@[expose] def R17_2_4At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (p : ℕ) (Dsub : Subgroup G),
    p.Prime → p ≠ 2 → Dsub ≤ D.M → IsPGroup p ↥Dsub → ¬ IsCyclic ↥Dsub →
    (∀ x ∈ Dsub, x ^ p = 1) → ⁅⁅Dsub, Dsub⁆, Dsub⁆ = ⊥ →
    ((Dsub ⊔ CFSG.Open.pCoreOf 2 D.M).subgroupOf D.M).Normal →
    p ≤ 5

@[expose] def R17_2_5At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (p : ℕ) (Dsub : Subgroup G),
    p.Prime → p ≠ 2 → Dsub ≤ D.M → IsPGroup p ↥Dsub → ¬ IsCyclic ↥Dsub →
    (∀ x ∈ Dsub, x ^ p = 1) → ⁅⁅Dsub, Dsub⁆, Dsub⁆ = ⊥ →
    ((Dsub ⊔ CFSG.Open.pCoreOf 2 D.M).subgroupOf D.M).Normal →
    p ∈ D.sig → p = 5 ∧ 3 ∉ piSet D.M ∧
      ∀ q ∈ piSet D.M, q ≠ 2 → q ≠ 5 →
        CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M

@[expose] def R17_2At (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : Prop :=
  R17_2_1At D V₀ V ∧ R17_2_2At D V₀ V hV ∧ R17_2_3At D V₀ V hV ∧
    R17_2_4At D V₀ V ∧ R17_2_5At D V₀ V

@[expose] def R17_3At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L ∈ calC D.M, Thin8 L → ∀ X : Subgroup G,
    (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ Nat.card X = q ∧ X ≤ L) →
    normalizer (X : Set G) ≤ D.M

@[expose] def R17_5At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L ∈ calC D.M, ∀ n : ℕ, 5 < n →
    ¬ Nonempty (BarO2Z17 L ≃* alternatingGroup (Fin n))

@[expose] def R17_6_1At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L ∈ calC D.M, ∀ r : ℕ, r ≠ 2 → IsChev (BarInf L) r →
    IsL2Over17 (Bar2 L) r

@[expose] def R17_6_2At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L ∈ calC D.M, ∀ r : ℕ, r ≠ 2 → IsChev (BarInf L) r → 5 < r →
    ∃ g : G, g ∉ D.M ∧
      3 ∈ piSet (L ⊓ D.M.map (MulAut.conj g).toMonoidHom)

@[expose] def R17_6_3At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L ∈ calC D.M, ∀ r : ℕ, r ≠ 2 → IsChev (BarInf L) r → 5 < r →
    (∃! K : Subgroup G, K ∈ calC D.M ∧ Thin8 K ∧ CFSG.Open.pRank 3 K = 1) ∧
      ∀ K : Subgroup G, K ∈ calC D.M → ∀ n : ℕ, ¬ IsU3 (Bar2 K) (2 * n)

@[expose] def R17_6At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  R17_6_1At D V₀ V ∧ R17_6_2At D V₀ V ∧ R17_6_3At D V₀ V

@[expose] def R17_7_1At (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  UniqueMax D.M L

@[expose] def R17_7_2At (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  IsL2Over17 (Bar2 L) 7 →
    ∀ g : G, g ∉ D.M →
      3 ∉ piSet (L ⊓ D.M.map (MulAut.conj g).toMonoidHom)

@[expose] def R17_7At (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  R17_7_1At D V₀ V L r q hC ∧ R17_7_2At D V₀ V L r q hC

@[expose] def R17_8At (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  ¬ IsL3Odd (Bar2 L) 3 ∧ ¬ LieModel (Bar2 L) .PSU 3 3 1

@[expose] def R17_9At (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  3 < q

@[expose] def R17_10At (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  barSub V₀ V hC.hyp125.isElemAbelian L ≠ ⊥ →
  MBarGT D.M V₀ V 7 ∨
    (MBarGT D.M V₀ V 3 ∧ (IsL2Over17 (Bar2 L) r ∨ IsL2Over17 (Bar2 L) 25)) ∨
    IsL2Over17 (Bar2 L) 7

@[expose] def R17_11At (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  barSub V₀ V hC.hyp125.isElemAbelian L ≠ ⊥ →
  bBar (conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian = 1 ∨
    (bBar (conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian = 2 ∧ q ≤ 9)

@[expose] def R17_13At (D : Data G)
    (𝔉 : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop)
    (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  iL17_12 D 𝔉 r q L = 1 ∨ (q ≤ 9 ∧ iL17_12 D 𝔉 r q L = 2) ∨
    (q = 9 ∧ iL17_12 D 𝔉 r q L = 3)

@[expose] def R17_14At (D : Data G)
    (𝔉 : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop)
    (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  (mBar D.M V₀ V hC.hyp125.isElemAbelian : ℕ∞) >
      (D.k : ℕ∞) + iL17_12 D 𝔉 r q L +
        (bBar (conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian : ℕ∞) ∨
    (D.k = 2 ∧ (IsL2Over17 (Bar2 L) r ∨ IsL2Over17 (Bar2 L) 25)) ∨
    IsL2Over17 (Bar2 L) 7

@[expose] def R17_15At (D : Data G)
    (𝔉 : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop)
    (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  (mBar D.M V₀ V hC.hyp125.isElemAbelian : ℕ∞) >
    (D.k : ℕ∞) + iL17_12 D 𝔉 r q L +
      (bBar (conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian : ℕ∞)

@[expose] def R17_16At (D : Data G)
    (𝔉 : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop)
    (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  UniqueMax D.M (⨆ H ∈ Delta17_12 D 𝔉 r q L, H)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

