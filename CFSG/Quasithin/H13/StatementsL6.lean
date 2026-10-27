module

public import CFSG.Quasithin.H13.StatementsL5
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.H13.StatementsL1
public import CFSG.Quasithin.Vol2.Ch4Sec4Hyp
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import Mathlib.GroupTheory.Frattini
public import CFSG.Foundations
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative Pointwise Matrix

section Vocabulary

variable {G : Type} [Group G]

@[expose] def oTwoFrattini (X : Subgroup G) : Subgroup G :=
  ((frattini (↥X ⧸ CFSG.pCore 2 ↥X)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥X))).map X.subtype

@[expose] def oTwoP (p : ℕ) (X : Subgroup G) : Subgroup G :=
  ((CFSG.pCore p (↥X ⧸ CFSG.pCore 2 ↥X)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥X))).map
    X.subtype

@[expose] def IsIrrSecIn (X C J : Subgroup G) : Prop :=
  C < J ∧ ∀ K : Subgroup G, C ≤ K → K ≤ J → X ≤ Subgroup.normalizer (K : Set G) → K = C ∨ K = J

@[expose] def IsSemisimpleSecIn (X C V : Subgroup G) : Prop :=
  ∀ J : Subgroup G, C ≤ J → J ≤ V → X ≤ Subgroup.normalizer (J : Set G) →
    ∃ K : Subgroup G, C ≤ K ∧ K ≤ V ∧ X ≤ Subgroup.normalizer (K : Set G) ∧ J ⊓ K = C ∧
      J ⊔ K = V

@[expose] def IsHomCompSecIn (X C V W : Subgroup G) : Prop :=
  ∃ J₀ : Subgroup G, J₀ ≤ V ∧ X ≤ Subgroup.normalizer (J₀ : Set G) ∧ IsIrrSecIn X C J₀ ∧
    W = C ⊔ ⨆ (J : Subgroup G) (_ : J ≤ V ∧ X ≤ Subgroup.normalizer (J : Set G) ∧
      IsIrrSecIn X C J ∧ IsXSectionIso₂ X J C J₀ C), J

@[expose] def IsTISetUnder (V M : Subgroup G) : Prop :=
  ∀ g ∈ M, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ CFSG.conjugate V g = ⊥

end Vocabulary

@[expose] noncomputable def tensorNatModel (d : ℕ) (K : Type) [Field K] : FFModel where
  Gam := ↥(StatedSL d K) × ↥(StatedSL d K)
  Amb := Multiplicative (Matrix (Fin d) (Fin d) K)
  act g X := Multiplicative.ofAdd
    ((((g.1 : ↥(StatedSL d K)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      Multiplicative.toAdd X *
        ((((g.2 : ↥(StatedSL d K)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))ᵀ)
  sec := ⊤
  ker := ⊥

section Blocks

variable {G : Type} [Group G]

@[expose] def IsA6Block (L : Subgroup G) : Prop :=
  QuasithinUnique.IsShort2 L ∧ Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∧
    ∃ _ : IsMulCommutative ↥(QuasithinUnique.blockU L),
      AlternatingNatural (V := ↥(QuasithinUnique.blockU L)) (autOn L (QuasithinUnique.blockU L)) ⊤
        ((QuasithinUnique.blockZ L).subgroupOf (QuasithinUnique.blockU L)) 6

@[expose] def IsExcA7Block (L : Subgroup G) : Prop :=
  QuasithinUnique.IsShort2 L ∧ Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 7)) ∧
    Nat.card (QuasithinUnique.blockU L) = 2 ^ 4 * Nat.card (QuasithinUnique.blockZ L)

@[expose] def IsHatA6Block (L : Subgroup G) : Prop :=
  QuasithinUnique.IsShort2 L ∧
    (Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧
      Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
        alternatingGroup (Fin 6))) ∧
    Nat.card (QuasithinUnique.blockU L) = 2 ^ 6 ∧
    L ⊓ Subgroup.centralizer (QuasithinUnique.blockU L : Set G) = QuasithinUnique.blockQ L

@[expose] def IsG2Block (L : Subgroup G) : Prop :=
  QuasithinUnique.IsShort2 L ∧
    (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆)) ∧
    ∃ _ : IsMulCommutative ↥(QuasithinUnique.blockU L),
      G2NaturalDerived (V := ↥(QuasithinUnique.blockU L)) (autOn L (QuasithinUnique.blockU L)) ⊤
        ((QuasithinUnique.blockZ L).subgroupOf (QuasithinUnique.blockU L)) 1

end Blocks

structure Hyp3_2_2 (G : Type) [Group G] [Finite G] (T M Mp V₀ : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : QuasithinUnique.quasithinIsQTKECat G
  sylow : quasithinIsSylowTwo T
  maxTwoLocal : quasithinIsMaxTwoLocal M
  T_le : T ≤ M
  Mp_le : Mp ≤ M
  Mp_normal : M ≤ Subgroup.normalizer (Mp : Set G)
  Mp_residual : oTwoUpper Mp = Mp
  cases_i_ii : (∃ L : Subgroup G, quasithinIsFaithfulLocal T L ∧
      CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧ Mp = conjClosure L T) ∨
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Mp = oTwoP p Mp ∧ IsIrrSecIn T (oTwoFrattini Mp) Mp
  irrPlus : IsIrrPlusIn Mp (reducedAggregate (Mp ⊔ T)) T V₀

@[expose] def Case3_2_6_iii {G : Type} [Group G] (T L V₀ : Subgroup G) : Prop :=
  ∃ _ : IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G))),
    LieModel ↥(autOn L (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))) .PSL 3 2 1 ∧
    DirectSumOfCopies
      (V := ↥(conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
      (autOn L (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
      ((⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)),
          L⁆).subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) ⊥
      (FFModel.nat (StatedSL 3 (ZMod 2))) 4 ∧
    (Nat.card ↥(oTwoUpper
        (autOn (Subgroup.normalizer (conjClosure L T : Set G))
            (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) ⊓
          Subgroup.centralizer ((autOn (conjClosure L T)
            (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) :
              Subgroup _) : Set _))) = 5 ∨
      (Nat.card ↥(oTwoUpper
          (autOn (Subgroup.normalizer (conjClosure L T : Set G))
              (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) ⊓
            Subgroup.centralizer ((autOn (conjClosure L T)
              (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) :
                Subgroup _) : Set _))) = 25 ∧
        ∀ x ∈ oTwoUpper
          (autOn (Subgroup.normalizer (conjClosure L T : Set G))
              (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) ⊓
            Subgroup.centralizer ((autOn (conjClosure L T)
              (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) :
                Subgroup _) : Set _)), x ^ 5 = 1))

@[expose] def Stmt3_2_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V₀ : Subgroup G), FSU G T L V₀ →
    L ≠ conjClosure L T →
      (∃ _ : IsMulCommutative ↥(conjClosure V₀ T),
        qhatOf (V := ↥(conjClosure V₀ T)) (autOn (conjClosure L T ⊔ T) (conjClosure V₀ T)) ≤ 2) ∧
      ∃ _ : IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))),
        qhatOf (V := ↥(conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G))))
          (autOn (Subgroup.normalizer (conjClosure L T : Set G))
            (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) ≤ 2 ∧
        ((∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
            LieModel ↥(autOn L (conjClosure (conjClosure V₀ T)
              (Subgroup.normalizer (conjClosure L T : Set G)))) .PSL 2 2 n ∧
            V₀ = conjClosure V₀ T ∧
            conjClosure V₀ T =
              conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∧
            (tensorNatModel 2 K).Realizes
              (V := ↥(conjClosure (conjClosure V₀ T)
                (Subgroup.normalizer (conjClosure L T : Set G))))
              (autOn (conjClosure L T) (conjClosure (conjClosure V₀ T)
                (Subgroup.normalizer (conjClosure L T : Set G)))) ⊤ ⊥) ∨
          (LieModel ↥(autOn L (conjClosure (conjClosure V₀ T)
              (Subgroup.normalizer (conjClosure L T : Set G)))) .PSL 3 2 1 ∧
            V₀ = conjClosure V₀ T ∧
            conjClosure V₀ T =
              conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∧
            (tensorNatModel 3 (ZMod 2)).Realizes
              (V := ↥(conjClosure (conjClosure V₀ T)
                (Subgroup.normalizer (conjClosure L T : Set G))))
              (autOn (conjClosure L T) (conjClosure (conjClosure V₀ T)
                (Subgroup.normalizer (conjClosure L T : Set G)))) ⊤ ⊥) ∨
          ((∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) →
              ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊔
                  CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
                    (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t ⊔
                  (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
                    Subgroup.centralizer (conjClosure L T : Set G)) =
                conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∧
              (⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊔
                  (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
                    Subgroup.centralizer (conjClosure L T : Set G))) ⊓
                (CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
                    (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t ⊔
                  (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
                    Subgroup.centralizer (conjClosure L T : Set G))) =
                conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
                  Subgroup.centralizer (conjClosure L T : Set G) ∧
              ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ≤
                Subgroup.centralizer (CFSG.conjugate L t : Set G)) ∧
            (∀ A ∈ QhatStar (V := ↥(conjClosure (conjClosure V₀ T)
                (Subgroup.normalizer (conjClosure L T : Set G))))
                (autOn (Subgroup.normalizer (conjClosure L T : Set G))
                  (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))),
              ∀ a ∈ A, ∀ u : ↥(conjClosure (conjClosure V₀ T)
                  (Subgroup.normalizer (conjClosure L T : Set G))),
                (u : G) ∈ ⁅conjClosure (conjClosure V₀ T)
                  (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ →
                ((a u : ↥(conjClosure (conjClosure V₀ T)
                  (Subgroup.normalizer (conjClosure L T : Set G)))) : G) ∈
                  ⁅conjClosure (conjClosure V₀ T)
                    (Subgroup.normalizer (conjClosure L T : Set G)), L⁆) ∧
            (∃ _ : IsMulCommutative ↥⁅conjClosure (conjClosure V₀ T)
                (Subgroup.normalizer (conjClosure L T : Set G)), L⁆,
              qhatOf (V := ↥⁅conjClosure (conjClosure V₀ T)
                  (Subgroup.normalizer (conjClosure L T : Set G)), L⁆)
                (autOn (conjClosure L T ⊔ T) ⁅conjClosure (conjClosure V₀ T)
                  (Subgroup.normalizer (conjClosure L T : Set G)), L⁆) ≤ 2) ∧
            ((⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ =
                  V₀ ∧
                conjClosure V₀ T =
                  conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) ∨
              (Nonempty (↥(autOn (autOn (Subgroup.normalizer (conjClosure L T : Set G))
                    (conjClosure (conjClosure V₀ T)
                      (Subgroup.normalizer (conjClosure L T : Set G))))
                  (autOn L (conjClosure (conjClosure V₀ T)
                    (Subgroup.normalizer (conjClosure L T : Set G))))) ≃*
                  MulAut ↥(StatedSL 3 (ZMod 2))) ∧
                conjClosure V₀ T =
                  conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∧
                (∃ s ∈ T ⊓ Subgroup.normalizer (L : Set G),
                  s ∉ L ⊔ pCoreOf 2 (L ⊔ (T ⊓ Subgroup.normalizer (L : Set G)))) ∧
                (∀ s ∈ T ⊓ Subgroup.normalizer (L : Set G),
                  s ∉ L ⊔ pCoreOf 2 (L ⊔ (T ⊓ Subgroup.normalizer (L : Set G))) →
                  ⁅conjClosure (conjClosure V₀ T)
                      (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ =
                    V₀ ⊔ CFSG.conjugate V₀ s ∧ V₀ ⊓ CFSG.conjugate V₀ s = ⊥) ∧
                Nat.card V₀ = 2 ^ 3) ∨
              Case3_2_6_iii T L V₀)))

@[expose] def Stmt3_2_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V₀ : Subgroup G), FSU G T L V₀ →
    IsTISetUnder (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∨
      (LieModel ↥(autOn L (conjClosure V₀ T)) .PSL 3 2 1 ∧ L ≠ conjClosure L T ∧
        Case3_2_6_iii T L V₀)

@[expose] def Case326Four {G : Type} [Group G] (T L V₀ : Subgroup G)
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))] : Prop :=
  ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
    LieModel ↥(autOn L (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))) .PSL 2 2 n ∧
    DirectSumOfCopies (V := ↥(conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))))
      (autOn L (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))))
      ((⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆).subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
      ((⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊓
          Subgroup.centralizer (conjClosure L T : Set G)).subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
      (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 2 K)) 2

@[expose] def Case326VM {G : Type} [Group G] (T L V₀ : Subgroup G) : Prop :=
  Case3_2_6_iii T L V₀ ∨
    ∃ _ : IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))), Case326Four T L V₀

@[expose] def IsVplus {G : Type} [Group G] (T L V₀ Vp : Subgroup G) : Prop :=
  (L ≠ conjClosure L T ∧ Case326VM T L V₀ ∧
      Vp = conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) ∨
    (¬ (L ≠ conjClosure L T ∧ Case326VM T L V₀) ∧ Vp = conjClosure V₀ T)

@[expose] def Stmt3_2_10_eight : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V₀ Vp : Subgroup G), FSU G T L V₀ →
    IsVplus T L V₀ Vp → thompsonJ T ≤ Subgroup.centralizer (Vp : Set G) →
      ∀ S : Subgroup G, IsPGroup 2 ↥S → thompsonJ T ≤ S →
        thompsonJ T = thompsonJ S ∧
          Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (conjClosure L T : Set G)

@[expose] def Stmt3_2_10_nine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V₀ Vp : Subgroup G), FSU G T L V₀ →
    IsVplus T L V₀ Vp → thompsonJ T ≤ Subgroup.centralizer (Vp : Set G) →
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (conjClosure L T : Set G) = ⊥ ∧
        Vp ⊓ Subgroup.centralizer (conjClosure L T : Set G) = ⊥

@[expose] def Stmt3_2_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsLocal T L → ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
      (CFSG.solvableRadical ↥L).map L.subtype ≤
        Subgroup.centralizer (reducedAggregate (L ⊔ T) : Set G)

@[expose] def Stmt4_4_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H S MH : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    pCoreOf 2 H ≠ ⊥ → 1 < E1.nParam H → QuasithinUnique.IsSylowTwoOf S H →
    IsUniqueMaxOver H S MH →
      (∃ P : Subgroup G, QuasithinUnique.IsSylowTwoOf P (MH ⊓ oTwoUpper H) ∧
        MH ⊓ oTwoUpper H ≤ Subgroup.normalizer (P : Set G)) ∧
      ∀ B : Subgroup G, B ≤ MH → Odd (Nat.card B) → (∃ k : ℕ, B.relIndex MH = 2 ^ k) →
        (∀ (p : ℕ) (A : Subgroup G), p.Prime → A ≤ B → IsElemAbelian p A →
          (A : Set G) * (S : Set G) = (S : Set G) * (A : Set G) →
            H = MH ⊔ (H ⊓ Subgroup.normalizer (A : Set G)) ∧
              ¬ H ⊓ Subgroup.normalizer (A : Set G) ≤ MH) ∧
        ∀ M Mp : Subgroup G, quasithinIsMaxTwoLocal M → S ≤ M → MH = M ⊓ H →
          oTwoUpper Mp = Mp → Mp ≤ M → M ≤ Subgroup.normalizer (Mp : Set G) →
            {b | b ∈ B ∧ ∀ m ∈ Mp, b * m * b⁻¹ * m⁻¹ ∈ pCoreOf 2 Mp} * (S : Set G) =
              (S : Set G) * {b | b ∈ B ∧ ∀ m ∈ Mp, b * m * b⁻¹ * m⁻¹ ∈ pCoreOf 2 Mp}

@[expose] def Stmt4_4_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V₀ H : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L → L ≤ M →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    V₀ ≤ conjClosure L T ⊔ T → IsPrimeReduced 2 (V₀.subgroupOf (conjClosure L T ⊔ T)) →
    IsHStar T M H →
    ⁅V₀, conjClosure L T⁆ ≠ ⊥ →
    V₀ = conjClosure (V₀ ⊓ Subgroup.centralizer (T : Set G)) (conjClosure L T) →
    (∃ _ : IsMulCommutative ↥⁅V₀, conjClosure L T⁆,
      ¬ IsFFModule (V := ↥⁅V₀, conjClosure L T⁆)
        (autOn (conjClosure L T ⊔ T) ⁅V₀, conjClosure L T⁆)) →
    1 < E1.nParam H →
      ((∃ P : Subgroup G, QuasithinUnique.IsSylowTwoOf P (oTwoUpper H ⊓ M) ∧
          oTwoUpper H ⊓ M ≤ Subgroup.normalizer (P : Set G)) ∧
        ∀ B : Subgroup G, B ≤ H ⊓ M → Odd (Nat.card B) → (∃ k : ℕ, B.relIndex (H ⊓ M) = 2 ^ k) →
          ∀ b ∈ B, (∀ m ∈ conjClosure L T, b * m * b⁻¹ * m⁻¹ ∈ pCoreOf 2 (conjClosure L T)) →
            b = 1) ∨
      (∃ n : ℕ, 1 ≤ n ∧
        LieModel (↥(conjClosure L T) ⧸ CFSG.pCore 2 ↥(conjClosure L T)) .PSL 2 2 (2 * n) ∧
        ∃ _ : IsMulCommutative ↥⁅V₀, conjClosure L T⁆,
          BinaryOrthogonalFour (V := ↥⁅V₀, conjClosure L T⁆)
            (autOn (conjClosure L T) ⁅V₀, conjClosure L T⁆) ⊤ ⊥ n) ∨
      (LieModel (↥(conjClosure L T) ⧸ CFSG.pCore 2 ↥(conjClosure L T)) .PSL 3 2 1 ∧
        ∃ _ : IsMulCommutative ↥⁅V₀, conjClosure L T⁆,
          FanoCoreModule (V := ↥⁅V₀, conjClosure L T⁆)
            (autOn (conjClosure L T) ⁅V₀, conjClosure L T⁆) ⊤ ⊥)

end CFSG.Quasithin.H13
