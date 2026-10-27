module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R15_3 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp151 D V₀ V L),
    (∃ φ ∈ Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
        InducesTransvection φ (wStar D.M V₀ V h.isElemAbelian L)) →
      Desc153 D V₀ V h.isElemAbelian L

@[expose] def R15_13 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp154 D V₀ V L),
    barSub V₀ V h.hyp151.isElemAbelian L ≠ ⊥ →
      gamma15 D.M V₀ V h.hyp151.isElemAbelian L ≤ 3 ∧
        s15 D.M V₀ V h.hyp151.isElemAbelian L = 2

section Four

variable {W : Type} [CommGroup W]

@[expose] def conjSubs (A : Subgroup (MulAut W)) (U : Subgroup W) : Set (Subgroup W) :=
  {X | ∃ g ∈ A, X = U.map g.toMonoidHom}

@[expose] def DeltaSym (A : Subgroup (MulAut W)) (t : MulAut W) (Wsub : Subgroup W) (r m : ℕ) :
    Prop :=
  ∃ Δ : Fin (r + 1) → Subgroup W,
    Function.Injective Δ ∧ (∀ i, rk ↥(Δ i) = m) ∧ sSupIndep (Set.range Δ) ∧
      (⨆ i, Δ i) = Wsub ∧
      ∃ σ : ↥(A ⊓ stabSub Wsub) →* Equiv.Perm (Fin (r + 1)),
        Function.Surjective σ ∧
          (∀ (g : ↥(A ⊓ stabSub Wsub)) (i : Fin (r + 1)),
            (Δ i).map (g : MulAut W).toMonoidHom = Δ (σ g i)) ∧
          ∃ ht : t ∈ A ⊓ stabSub Wsub, (σ ⟨t, ht⟩).IsSwap ∧
            (2 < r → ∀ i, σ ⟨t, ht⟩ i = i → ∀ x ∈ Δ i, t x = x)

@[expose] def Conc4_133 (A : Subgroup (MulAut W)) (t : MulAut W) (L : Subgroup (MulAut W)) : Prop :=
  ∃ p : ℕ, p.Prime ∧ L ≤ pCoreOf p A ∧ ⁅L, Subgroup.zpowers t⁆ ≠ ⊥ ∧
    sSupIndep (conjSubs A (commSub ⊤ L)) ∧
    ((IsCyclicOrd ↥L 3 ∧ (rk ↥(commSub ⊤ L) = 2 ∨ rk ↥(commSub ⊤ L) = 4 ∨
          rk ↥(commSub ⊤ L) = 6)) ∨
      (IsCyclicOrd ↥L 5 ∧ rk ↥(commSub ⊤ L) = 4) ∨
      (IsPOnePlusTwo 3 ↥L ∧ rk ↥(commSub ⊤ L) = 6) ∨
      (IsElemAbelianOfRank 3 2 ↥L ∧ rk ↥(commSub ⊤ L) = 8 ∧
        (∀ x ∈ L, x ≠ 1 → rk ↥(commSub ⊤ (Subgroup.zpowers x)) = 6) ∧
        rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3) ∨
      (IsCyclicOrd ↥L 7 ∧ (rk ↥(commSub ⊤ L) = 3 ∨ rk ↥(commSub ⊤ L) = 6)) ∨
      (∃ r m : ℕ, ((p = 3 ∧ m = 2) ∨ (p = 7 ∧ m = 3)) ∧ 2 ≤ r ∧ IsElemAbelianOfRank p r ↥L ∧
        rk ↥(commSub ⊤ L) = (r + 1) * m ∧ DeltaSym A t (commSub ⊤ L) r m) ∨
      (IsElemAbelianOfRank 3 2 ↥L ∧ rk ↥(commSub ⊤ L) = 6 ∧ ∀ x ∈ L, t * x * t⁻¹ = x⁻¹))

@[expose] def Conc4_135 (H : Subgroup (MulAut W)) (U Z : Subgroup W) (m : ℕ) : Prop :=
  (∃ n : ℕ, (IsSLn ↥H n m ∧ BinaryNaturalSL H U Z n m) ∨ (IsSpn ↥H n m ∧ NatSpn H U Z n m) ∨
      (IsOmegaPlus ↥H n m ∧ NatOmegaPlus H U Z n m) ∨
      (IsOmegaMinus ↥H n m ∧ NatOmegaMinus H U Z n m)) ∨
    (∃ n : ℕ, (IsSLn ↥H n 1 ∧ BinaryNaturalSL H U Z n 1) ∨ (IsSpn ↥H n 1 ∧ NatSpn H U Z n 1) ∨
      (IsOmegaPlus ↥H n 1 ∧ NatOmegaPlus H U Z n 1) ∨
      (IsOmegaMinus ↥H n 1 ∧ NatOmegaMinus H U Z n 1) ∨ (IsSUn ↥H n 1 ∧ NatSUn H U Z n 1)) ∨
    G2NaturalDerived H U Z 1 ∨
    TripleA6Six H U Z ∨
    ((∃ S : Type, ∃ _ : Group S, CFSG.Blueprint.LieModel S .PSU 4 3 1 ∧ IsHat ↥H S) ∧
      E3.mQuot U Z = 12) ∨
    (∃ n : ℕ, UC22.IsAlt ↥H n ∧ AlternatingNatural H U Z n) ∨
    A7Four H U Z ∨
    (IsSpn ↥H 6 1 ∧ E3.mQuot U Z = 8) ∨
    (IsLn ↥H 5 1 ∧ E3.mQuot U Z = 10) ∨
    (UC22.IsSpor ↥H .M22 ∧ E3.mQuot U Z = 10) ∨
    (IsLn ↥H 3 2 ∧ E3.mQuot U Z = 9) ∨
    (IsL3 ↥H 1 ∧ E3.mQuot U Z = 8)

@[expose] def SumOfAtMostThreeNat (L : Subgroup (MulAut W)) (U Z : Subgroup W) : Prop :=
  ∃ k : ℕ, k ≤ 3 ∧ ∃ n : ℕ,
    (IsSLn ↥L n 1 ∧ SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) L U Z k) ∨
    (IsSpn ↥L n 1 ∧ SumOfNat (fun H U Z => NatSpn H U Z n 1) L U Z k) ∨
    (IsOmegaPlus ↥L n 1 ∧ SumOfNat (fun H U Z => NatOmegaPlus H U Z n 1) L U Z k) ∨
    (IsOmegaMinus ↥L n 1 ∧ SumOfNat (fun H U Z => NatOmegaMinus H U Z n 1) L U Z k) ∨
    (UC22.IsAlt ↥L n ∧ SumOfNat (fun H U Z => AlternatingNatural H U Z n) L U Z k)

@[expose] def Conc4_136W (A : Subgroup (MulAut W)) (t : MulAut W) (L : Subgroup (MulAut W)) :
    Prop :=
  (⨆ X ∈ conjSubs A (commSub ⊤ L), X) = ⊤ ∧
    (∀ g ∈ A, g ∉ normalizer (L : Set (MulAut W)) →
      ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
        commSub (commSub ⊤ L) (L.map (MulAut.conj g).toMonoidHom) = ⊥) ∧
    (Conc4_133 A t L ∨
      (∃ K ∈ {K | IsComponentOf K A}, ∃ g ∈ A, K ≠ K.map (MulAut.conj g).toMonoidHom ∧
        L = K ⊔ K.map (MulAut.conj g).toMonoidHom ∧
        ((IsL3 ↥K 1 ∧ NatTensor L (commSub ⊤ L) ⊥ 3 1) ∨
          (UC22.IsL2 ↥K 2 ∧ NatTensor L (commSub ⊤ L) ⊥ 2 2) ∨
          (UC22.IsL2 ↥K 3 ∧ NatTensor L (commSub ⊤ L) ⊥ 2 3))) ∨
      (IsComponentOf L A ∧ SumOfAtMostThreeNat L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ∧
        ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
          ∃ g ∈ A ⊓ normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom) ∨
      (commSub ⊤ L ∈ irrSet L ∧ ⁅L, Subgroup.zpowers t⁆ = L ∧ IsComponentOf L A ∧
        Conc4_135 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)
          (E3.mQuot (commSub (commSub ⊤ L) (Subgroup.zpowers t) ⊔ (commSub ⊤ L ⊓ fixV L))
            (commSub ⊤ L ⊓ fixV L))))

end Four

@[expose] def Conc4_136 (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L : Subgroup G) : Prop :=
  ∃ t ∈ Mbar D.M V₀ V hV, t ^ 2 = 1 ∧ t ≠ 1 ∧ rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3 ∧
    Conc4_136W (Mbar D.M V₀ V hV) t (lBar V₀ V hV L)

@[expose] def R4_136 (D : Data G) : Prop :=
  ∀ (V₀ V : Subgroup G) (h : Hyp16 D V₀ V),
    ∃ L : Subgroup G, Setting16 D V₀ V L ∧
      barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥ ∧
      Conc4_136 D V₀ V h.hyp125.isElemAbelian L

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
