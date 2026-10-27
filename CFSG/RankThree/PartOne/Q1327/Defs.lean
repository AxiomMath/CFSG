module

public import CFSG.RankThree.PartOne.S12.Facts13
public import CFSG.RankThree.PartOne.S12.KFTransfer
public import CFSG.RankThree.PartOne.Census3.Interface

public section

namespace CFSG.RankThree.PartOne.Q1327

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.PartOne
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

structure Hyp (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G)
    (f r : ℕ) (R : Subgroup G) (s s' zs : MulAut E) : Prop where
  h12 : Sec12Hyp G p A c L E
  hF : Sec12Facts G p A c L E
  hF13 : Sec13Facts G p A c L E
  hT : ¬ Outcome152Five p E A (lieGenerated p E)
  hEA : E = A
  hnL3 : ¬ IsLThreeTypeAt p L
  hf2 : 2 ≤ f
  hpf : p ∣ 2 ^ f + 1
  hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f
  hweyl : Nonempty (reflectionGroup p E ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))
  hr : r.Prime
  hrf : r ∣ 2 ^ f - 1
  hRcard : Nat.card R = r
  hRL : R ≤ L
  hRE : ∀ x ∈ R, ∀ e ∈ E, x * e = e * x
  hRnorm : ∀ (y : G) (hy : y ∈ Subgroup.normalizer (E : Set G)),
    conjAut E y hy ∈ reflectionGroup p E → conjBy y R = R
  hs : s ∈ reflectionSet p E
  hsL : s ∈ torusImage E L
  hs' : s' ∈ reflectionSet p E
  hs'L : s' ∈ torusImage E L
  hKs : KFAt p E f s
  hKs' : KFAt p E f s'
  hss' : s ≠ s'
  hcomm : s * s' = s' * s
  hRs : R ≤ Subgroup.centralizer (kZero p E s : Set G)
  hRs' : R ≤ Subgroup.centralizer (kZero p E s' : Set G)
  hzs : zs ∈ reflectionSet p E
  hzc : ∀ g ∈ torusImage E L, g * zs = zs * g
  hzL : zs ∉ torusImage E L
  hmov : autMovedInG E zs = Subgroup.zpowers c
  hKz : KFAt p E (2 * f) zs
  hzs_s : kZero p E zs ≤ Subgroup.centralizer (kZero p E s : Set G)
  hzs_s' : kZero p E zs ≤ Subgroup.centralizer (kZero p E s' : Set G)
  hRz : R ≤ kZero p E zs

@[expose] def KF1327S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G)
    (f r : ℕ) (R : Subgroup G) (s s' zs : MulAut E),
    Hyp G p A c L E f r R s s' zs →
    ∃ (a : G) (N A₀ S : Subgroup G),
      a ∈ E ∧ a ≠ 1 ∧
      N ≤ Subgroup.centralizer (({a} : Set G) ∪ (R : Set G)) ∧
      N.subgroupOf (Subgroup.centralizer (({a} : Set G) ∪ (R : Set G))) ∈
        thetaComponents p ↥(Subgroup.centralizer (({a} : Set G) ∪ (R : Set G))) ∧
      kZero p E s ≤ N ∧
      StatedClassicalModel (↥N ⧸ aschbacherSolvableCore p ↥N) .PSU 3 2 f ∧
      A₀ ≤ E ∧ IsElementaryAbelian p ↥A₀ ∧ Nat.card A₀ = p ^ 2 ∧
      S ≤ pElementSubgroup p (Subgroup.centralizer (R : Set G)) ∧ S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧
      A₀ ≤ Subgroup.normalizer (S : Set G) ∧ ⁅S, A₀⁆ = S

structure T123Base {G : Type} [Group G] [Finite G] (p : ℕ) (L A₀ F : Subgroup G) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  quasisimple : CFSG.IsQuasisimple L
  evenRank_le : CFSG.Assembly.evenRank ↥L ≤ 3
  center_pPrime : ¬ p ∣ Nat.card (Subgroup.center L)
  A₀_le : A₀ ≤ L
  A₀_elem : IsElementaryAbelian p A₀
  A₀_card : Nat.card A₀ = p ^ 2
  A₀_invariant : ∃ S : Subgroup G, S ≤ L ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
    A₀ ≤ Subgroup.normalizer (S : Set G) ∧ S = ⁅S, A₀⁆
  F_le : F ≤ L
  F_elem : IsElementaryAbelian p F
  F_card : Nat.card F = p ^ 3
  A₀_le_F : A₀ ≤ F
  F_le_centralizer : F ≤ Subgroup.centralizer (A₀ : Set G)
  F_max : ∀ F' : Subgroup G, F' ≤ L → IsElementaryAbelian p F' →
    F' ≤ Subgroup.centralizer (A₀ : Set G) → F ≤ F' → F' = F

@[expose] def KF1327P5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X A₀ F : Subgroup G), T123Base 5 X A₀ F →
    Census3.TheoremThreeList (↥X ⧸ Subgroup.center ↥X) →
    (∃ (a : G) (N : Subgroup G) (f : ℕ), a ∈ F ∧ a ≠ 1 ∧
      N ≤ X ⊓ Subgroup.centralizer ({a} : Set G) ∧ 2 ≤ f ∧ 5 ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (↥N ⧸ aschbacherSolvableCore 5 ↥N) .PSU 3 2 f) →
    CFSG.Blueprint.EvenLieType (↥X ⧸ Subgroup.center ↥X)

@[expose] def KF1327Row9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ) (X F : Subgroup G),
    p.Prime → 5 ≤ p → 2 ≤ f → p ∣ 2 ^ f + 1 → CFSG.IsQuasisimple X → Subgroup.center ↥X = ⊥ →
    StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU 4 2 f →
    IsElementaryAbelian p F → F ≤ X → Nat.card F = p ^ 3 →
    ∀ (t : MulAut F) (K : Subgroup G), t ∈ torusImage F X → IsAutReflection p F t →
      K ≤ X ⊓ Subgroup.centralizer (autFixedInG F t : Set G) →
      K.subgroupOf (X ⊓ Subgroup.centralizer (autFixedInG F t : Set G)) ∈
        thetaComponents p ↥(X ⊓ Subgroup.centralizer (autFixedInG F t : Set G)) →
      autMovedInG F t ≤ K → StatedClassicalModel ↥K .PSL 2 2 f

@[expose] def KF1327Out : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ) (X E : Subgroup G),
    p.Prime → 5 ≤ p → 2 ≤ f → p ∣ 2 ^ f + 1 → CFSG.IsQuasisimple X → Subgroup.center ↥X = ⊥ →
    StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU 4 2 f →
    IsElementaryAbelian p E → E ≤ X → Nat.card E = p ^ 3 →
    (∀ F : Subgroup G, IsElementaryAbelian p F → F ≤ Subgroup.centralizer (E : Set G) → E ≤ F →
      F = E) →
    ∀ x ∈ Subgroup.normalizer (X : Set G), (∃ k : ℕ, orderOf x = p ^ k) →
      x ∈ X ⊔ Subgroup.centralizer (X : Set G)

end CFSG.RankThree.PartOne.Q1327
