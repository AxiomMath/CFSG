module

public import CFSG.Quasithin.Background.F7Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.WeakClosure81.NineDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

@[expose] def Star914 {G : Type} [Group G] (V N : Subgroup G) : Prop :=
  ∀ g : G, g ∉ normalizer (V : Set G) → conjSubgroup V g ≤ normalizer (V : Set G) →
    ∀ x ∈ N ⊓ normalizer (conjSubgroup V g : Set G), orderOf x ≠ 3

structure NineFourteenBarFacts (X : Type) [Group X] [Finite X] (Lb Tb : Subgroup X) :
    Prop where
  sylow : IsSylowIn 2 Tb ⊤
  sup_eq : Lb ⊔ Tb = ⊤
  normal : Lb.Normal
  three_dvd : 3 ∣ Nat.card Lb
  le_of_normal : ∀ K : Subgroup X, K.Normal → (∃ x ∈ K, orderOf x = 2) → Lb ≤ K
  cent : IsPGroup 3 (centralizer (Lb : Set X))
  pair : ∀ x : X, orderOf x = 2 → ∃ n : X,
    IsPGroup 2 (closure {x, n * x * n⁻¹}) ∧ x * (n * x * n⁻¹) ≠ (n * x * n⁻¹) * x
  table : ∀ A : Subgroup X, A ≤ Tb → IsElemAbelian 2 A → 4 ≤ Nat.card A →
    ∃ (K Y : Subgroup X) (p : ℕ), A ≤ K ∧ TwoPTwoIrred K (K ⊓ Tb) Y p ∧
      CFSG.Quasithin.coreIn (Tb ⊓ centralizer (A : Set X)) Tb ≤ K ⊓ Tb ∧
      (∀ R : Subgroup X, A ≤ R → R ≤ K ⊓ Tb →
        ¬ K ⊔ (Tb ⊓ normalizer ((K ⊓ Tb : Subgroup X) : Set X)) ≤ normalizer (R : Set X)) ∧
      (p = 3 ∨ ∀ H : Subgroup X, Tb ≤ H → H = Tb ∨ H = ⊤)
  close : ∀ E : Subgroup X, E ≤ Tb → Tb ≤ normalizer (E : Set X) → IsElemAbelian 2 E →
    4 ≤ Nat.card E →
    ∃ Ks : Finset (Subgroup X), (∀ K ∈ Ks, ∃ Y : Subgroup X,
        TwoPTwoIrred K (K ⊓ Tb) Y 3 ∧ E ≤ pCoreOf 2 K ∧ Tb ⊓ centralizer (E : Set X) ≤ K) ∧
      (⨆ K ∈ Ks, K) ⊔ Tb = ⊤

@[expose] def NFAbstract : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V T N L : Subgroup G), Hyp9 V T → T ≤ N →
    N ≤ normalizer (V : Set G) → L ≤ N → (L.subgroupOf N).Normal → Star914 V N →
    ∀ (X : Type) [Group X] [Finite X] (π : ↥N →* X), Function.Surjective π →
      (∀ x : ↥N, π x = 1 ↔ (x : G) ∈ pCoreOf 2 N) →
      NineFourteenBarFacts X ((L.subgroupOf N).map π) ((T.subgroupOf N).map π) →
      normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G) ∨
        N ≤ normalizer (E3.wClos V 0 T : Set G)

@[expose] def NFPGL27 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Quasithin.F6.IsPGL2 7 X →
    ∀ Lb Tb : Subgroup X, Lb.Normal → Lb ≠ ⊥ → ⁅Lb, Lb⁆ = Lb → IsSylowIn 2 Tb ⊤ →
      NineFourteenBarFacts X Lb Tb

end CFSG.LocalAnalysis.WeakClosure81

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

@[expose] def W3Lem914N (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (V T N L : Subgroup G), Hyp9 V T → T ≤ N → N ≤ normalizer (V : Set G) → N = T ⊔ L →
    L = CFSG.Quasithin.perfectCore (L ⊔ pCoreOf 2 N) →
    T ≤ normalizer (L : Set G) →
    (∃ (Z : Type) (_ : Group Z) (ψ : ↥N →* Z), Function.Surjective ψ ∧
      (∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N) ∧
      CFSG.IsComponent ((L.subgroupOf N).map ψ)) →
    (∃ (A : Type) (_ : Group A) (φ : ↥(N ⊓ normalizer (L : Set G)) →* A),
      Function.Surjective φ ∧
      (∀ x : ↥(N ⊓ normalizer (L : Set G)),
        φ x = 1 ↔ (x : G) ∈ S17.centSection N L (oTwoThreeIn L)) ∧
      (CFSG.Quasithin.F6.IsPGL2 7 A ∨
        Inputs1719.IsAutOf A (alternatingGroup (Fin 6)) ∨ Inputs1719.IsM10 A ∨
        CFSG.Quasithin.F6.IsPGL2 9 A)) →
    Star914 V N →
    normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G) ∨
      N ≤ normalizer (E3.wClos V 0 T : Set G)

@[expose] def W3Lem914N7 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (V T N L : Subgroup G), Hyp9 V T → T ≤ N → N ≤ normalizer (V : Set G) → N = T ⊔ L →
    L = CFSG.Quasithin.perfectCore (L ⊔ pCoreOf 2 N) →
    T ≤ normalizer (L : Set G) →
    (∃ (Z : Type) (_ : Group Z) (ψ : ↥N →* Z), Function.Surjective ψ ∧
      (∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N) ∧
      CFSG.IsComponent ((L.subgroupOf N).map ψ)) →
    (∃ (A : Type) (_ : Group A) (φ : ↥(N ⊓ normalizer (L : Set G)) →* A),
      Function.Surjective φ ∧
      (∀ x : ↥(N ⊓ normalizer (L : Set G)),
        φ x = 1 ↔ (x : G) ∈ S17.centSection N L (oTwoThreeIn L)) ∧
      CFSG.Quasithin.F6.IsPGL2 7 A) →
    Star914 V N →
    normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G) ∨
      N ≤ normalizer (E3.wClos V 0 T : Set G)

@[expose] def StarOfSylThreeStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V N : Subgroup G),
    (∀ P : Subgroup G, IsSylowIn 3 P N → P ∈ calP V) → Star914 V N

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
