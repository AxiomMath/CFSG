module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6Basic
public import CFSG.Milestones.ASVolI.I2
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ASVolI.ChIJK (IsGraphFieldAut IsWeaklyClosedIn F4)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def conjOn (K : Subgroup G) {t : G} (ht : t ∈ normalizer (K : Set G)) : K ≃* K where
  toFun x := ⟨t * x * t⁻¹, (mem_normalizer_iff.1 ht _).1 x.2⟩
  invFun x := ⟨t⁻¹ * x * t, by
    have := (mem_normalizer_iff.1 (inv_mem ht) _).1 x.2
    simpa using this⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

@[expose] noncomputable def inftyOf (H : Subgroup G) : Subgroup G :=
  (derivedSeries ↥H (Nat.card H)).map H.subtype

@[expose] def InducesGraphField (t : G) (K : Subgroup G) : Prop :=
  ∃ ht : t ∈ normalizer (K : Set G), IsGraphFieldAut (conjOn K ht)

@[expose] def InducesTransposition (t : G) (L : Subgroup G) : Prop :=
  ∃ ht : t ∈ normalizer (L : Set G), ∃ (e : ↥L ≃* alternatingGroup (Fin 11))
    (τ : Equiv.Perm (Fin 11)), τ.IsSwap ∧ ∀ x : ↥L,
      ((e (conjOn L ht x) : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)) =
        τ * (e x : Equiv.Perm (Fin 11)) * τ⁻¹

@[expose] def GraphFieldShape (t : G) (L : Subgroup G) : Prop :=
  ((Nonempty (↥L ≃* PSL(3, F4)) ∨ Nonempty (↥L ≃* SL(3, F4))) ∧ InducesGraphField t L) ∨
    ∃ L₁ L₂ : Subgroup G, L = L₁ ⊔ L₂ ∧ (∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) ∧
      Nonempty (↥L₁ ≃* SL(3, F4)) ∧ Nonempty (↥L₂ ≃* SL(3, F4)) ∧
      L₁ ⊓ L₂ = (Subgroup.center ↥L₁).map L₁.subtype ∧
      InducesGraphField t L₁ ∧ InducesGraphField t L₂

@[expose] def R6_7 (D : Data G) : Prop :=
  D.sig ⊆ D.sig1 → ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ E : Subgroup G, E ≤ D.M →
    CFSG.Open.IsElemAbelian r E → Nat.card E = r ^ 2 → rankThreeGamma 1 r E ≤ D.M →
    ∀ H : Subgroup G, E ≤ H → H ≠ ⊤ → CFSG.Open.pCoreOf 2 (H ⊓ D.M) ≠ ⊥ → ¬ H ≤ D.M →
      r = 3 ∧ ∃ t : G, orderOf t = 2 ∧ CFSG.Open.pCoreOf 2 (H ⊓ D.M) = zpowers t ∧
        ∃ L : Subgroup G, L ≤ H ∧ (L.subgroupOf H).Normal ∧ H = (H ⊓ D.M) ⊔ L ∧
          (GraphFieldShape t L ∨ (Nonempty (↥L ≃* alternatingGroup (Fin 11)) ∧
            InducesTransposition t L))

structure Hyp612 (D : Data G) (p : ℕ) (P P₀ : Subgroup G) : Prop where
  mem_sig2 : p ∈ D.sig2
  sylow : CFSG.ABGLocalTools.IsSylowOf p P D.M
  le : P₀ ≤ P
  card : Nat.card P₀ = p
  not_le : ¬ centralizer (P₀ : Set G) ≤ D.M

@[expose] def R6_13 (D : Data G) : Prop :=
  ∀ (p : ℕ) (P P₀ : Subgroup G), Hyp612 D p P P₀ →
    (3 < p ∧ Group.IsSolvable D.M ∧ IsWeaklyClosedIn P₀ P ∧
      rankThreeGamma 1 p (P ⊓ inftyOf (centralizer (P₀ : Set G))) ≤ D.M ∧
      (∃ n : ℕ, 1 < n ∧ LieModel (inftyOf (centralizer (P₀ : Set G))) .PSL 2 p n) ∧
      CFSG.Open.uniqueFourIsFrobenius
        (CFSG.Open.uniqueFourPrimeCore p D.M ⊔
          centralizer (inftyOf (centralizer (P₀ : Set G)) : Set G))
        (CFSG.Open.pCoreOf 2 D.M) (centralizer (inftyOf (centralizer (P₀ : Set G)) : Set G))) ∧
    CFSG.IsStronglyClosedIn P ((P ⊓ inftyOf (centralizer (P₀ : Set G)) : Subgroup G) : Set G) ∧
    (∀ X : Subgroup G, X ≤ P ⊓ inftyOf (centralizer (P₀ : Set G)) → X ≠ ⊥ →
      InU D.M X) ∧
    ((∀ m ∈ D.M, (∀ x ∈ P ⊓ inftyOf (centralizer (P₀ : Set G)),
        m * x * m⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) →
      m ∈ centralizer (inftyOf (centralizer (P₀ : Set G)) : Set G) ⊔
        (P ⊓ inftyOf (centralizer (P₀ : Set G))) ⊔ CFSG.Open.pCoreOf 2 D.M) ∧
      D.M ≤ normalizer ((P ⊓ inftyOf (centralizer (P₀ : Set G)) ⊔
        CFSG.Open.pCoreOf 2 D.M : Subgroup G) : Set G) ∧
      ∀ t ∈ D.T, (∀ x ∈ P ⊓ inftyOf (centralizer (P₀ : Set G)),
        t * x * t⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) → t ∈ CFSG.Open.pCoreOf 2 D.M) ∧
    IrrOn (D.M ⊓ normalizer ((P ⊓ inftyOf (centralizer (P₀ : Set G)) : Subgroup G) : Set G))
      (P ⊓ inftyOf (centralizer (P₀ : Set G)))

@[expose] def calCGS (S : Subgroup G) : Subgroup G :=
  ⨆ (C : Subgroup G) (_ : C ≠ ⊥) (_ : C ≤ S) (_ : (C.subgroupOf S).Characteristic),
    normalizer (C : Set G)

@[expose] def R6_40_1 (_D : Data G) : Prop :=
  ∀ N : Subgroup G, rankThreeIsMaxTwoLocal N → ∀ L : Subgroup ↥N,
    ¬ CFSG.RankThree.PartOne.IsBlockInX L

@[expose] def R6_40_2 (D : Data G) : Prop :=
  calCGS D.T = ⊤ ∧
    ⊤ = calCGS (D.T ⊓ centralizer
      ((CFSG.inSubgroup (fun K _ => CFSG.elemThompsonCenterTorsion K 2) D.T : Subgroup G) :
        Set G)) ⊔ centralizer (D.Z : Set G)

end CFSG.LocalAnalysis.UniquenessCase.UC6
