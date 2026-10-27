module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

@[expose] def tA (T A : Subgroup G) : Subgroup G :=
  E1.tauOf ⊤ T A

theorem mem_tA {T A : Subgroup G} {t : G} :
    t ∈ tA T A ↔ t ∈ T ∧ t ∈ normalizer (pCoreOf 2 (⊤ : Subgroup G) : Set G) ∧
      ∀ a ∈ A, ⁅t, a⁆ ∈ pCoreOf 2 (⊤ : Subgroup G) :=
  E1.mem_tauOf

@[expose] def ECaseI (A K : Subgroup G) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ E1.oTwoPTwo ↥K p = ⊤ ∧
    CFSG.fittingSubgroup (Bar2 K) =
      ⁅E1.barO2 ↥K (A.subgroupOf K), CFSG.fittingSubgroup (Bar2 K)⁆ ∧
    (pCoreOf 2 K).relIndex A = 2

@[expose] def normAIn (A K : Subgroup G) (L : Subgroup (↥K ⧸ CFSG.solvableRadical ↥K)) : Subgroup G :=
  ((A.subgroupOf K ⊓ (normalizer (L : Set (↥K ⧸ CFSG.solvableRadical ↥K))).comap
    (QuotientGroup.mk' (CFSG.solvableRadical ↥K))).map K.subtype)

@[expose] def ECaseII (T A K : Subgroup G) : Prop :=
  E1.IsTwoClosed (CFSG.solvableRadical ↥K) ∧
    CFSG.pCore 2 (↥K ⧸ oInftyE ↥K) = ⊤ ∧
    twoResidual (⊤ : Subgroup ↥K) = perfectCore (⊤ : Subgroup ↥K) ∧
    ∃ L : Subgroup (↥K ⧸ CFSG.solvableRadical ↥K), CFSG.IsComponent L ∧
      CFSG.layer (↥K ⧸ CFSG.solvableRadical ↥K) =
        ⨆ t ∈ ((tA T A).subgroupOf K).map (QuotientGroup.mk' (CFSG.solvableRadical ↥K)),
          L.map (MulAut.conj t).toMonoidHom ∧
      (L = ⁅L, E1.barRad ↥K (A.subgroupOf K)⁆ ∨
        ((normAIn A K L).relIndex A = 2 ∧ normAIn A K L = A ⊓ pCoreOf 2 K))

@[expose] def InCalE (T A K : Subgroup G) : Prop :=
  tA T A ≤ T ⊓ K ∧ CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K) K ∧ ¬ A ≤ pCoreOf 2 K ∧
    (ECaseI A K ∨ ECaseII T A K)

@[expose] def InCalEi (i : ℕ) (T A K : Subgroup G) : Prop :=
  InCalE T A K ∧ E3.mQuot A (pCoreOf 2 K) ≤ i

@[expose] def calEi (i : ℕ) (T A : Subgroup G) : Set (Subgroup G) :=
  {K | InCalEi i T A K}

@[expose] def genEi (i : ℕ) (T : Subgroup G) (Ω : Set (Subgroup G)) : Subgroup G :=
  ⨆ A ∈ Ω, ⨆ (_ : A ≤ T), ⨆ K ∈ calEi i T A, K

structure IsOmegaColl (Ω : Set (Subgroup G)) : Prop where
  nonempty : Ω.Nonempty
  ne_bot : ∀ A ∈ Ω, A ≠ ⊥
  elemAbelian : ∀ A ∈ Ω, IsElemAbelian 2 A
  conj : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω

@[expose] def InEOmega (i : ℕ) (T : Subgroup G) (Ω : Set (Subgroup G)) : Prop :=
  genEi i T Ω ⊔ normalizer (E1.weakClosure T Ω : Set G) = ⊤

@[expose] def InFOmega (i : ℕ) (T : Subgroup G) (Ω : Set (Subgroup G)) : Prop :=
  ((genEi i T Ω : Subgroup G) : Set G) * (T : Set G) = Set.univ

@[expose] def InEGroup (i : ℕ) (Q : Type) [Group Q] : Prop :=
  ∀ T : Subgroup Q, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ →
    ∀ Ω : Set (Subgroup Q), IsOmegaColl Ω → InEOmega i T Ω

@[expose] def InFGroup (i : ℕ) (Q : Type) [Group Q] : Prop :=
  ∀ T : Subgroup Q, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ →
    ∀ Ω : Set (Subgroup Q), IsOmegaColl Ω → InFOmega i T Ω

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
