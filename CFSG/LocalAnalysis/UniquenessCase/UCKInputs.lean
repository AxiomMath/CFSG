module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6R2
public import CFSG.RankThree.FFModules.Offenders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.RankThree.FFModules (fixSub)
open scoped MatrixGroups

@[expose] def fixV {G : Type} [Group G] {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ρ : Representation (ZMod p) G V) (A : Subgroup G) : Submodule (ZMod p) V where
  carrier := {w | ∀ a ∈ A, ρ a w = w}
  add_mem' {v w} hv hw a ha := by rw [map_add, hv a ha, hw a ha]
  zero_mem' a _ := map_zero _
  smul_mem' c v hv a ha := by rw [map_smul, hv a ha]

@[expose] def ExtraspecialExpP {G : Type} [Group G] (p : ℕ) (P : Subgroup G) : Prop :=
  Nat.card P = p ^ 3 ∧ ¬ IsMulCommutative ↥P ∧ ∀ x ∈ P, x ^ p = 1

@[expose] def omegaOne {G : Type} [Group G] (p : ℕ) (P : Subgroup G) : Subgroup G :=
  closure {x | x ∈ P ∧ x ^ p = 1}

@[expose] def K318 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G → commutator G = ⊤ →
    CFSG.Open.pCoreOf 2 (CFSG.solvableRadical G) = ⊥ → IsSimpleGroup (G ⧸ CFSG.solvableRadical G) →
    (∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (CFSG.solvableRadical G) ≤ 3) →
    centralizer ((CFSG.solvableRadical G : Subgroup G) : Set G) ≤ CFSG.solvableRadical G →
      ((∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (LieModel (G ⧸ CFSG.solvableRadical G) .PSL 2 p 1 ∨
          LieModel (G ⧸ CFSG.solvableRadical G) .PSL 3 p 1)) ∨
        IsAlt (G ⧸ CFSG.solvableRadical G) 6 ∨ IsAlt (G ⧸ CFSG.solvableRadical G) 7 ∨
        ((∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (LieModel (G ⧸ CFSG.solvableRadical G) .PSp 2 p 1 ∨
            LieModel (G ⧸ CFSG.solvableRadical G) .PSL 2 p 2)) ∧
          ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ CFSG.Open.pRank q (CFSG.solvableRadical G) = 3 ∧
            3 < CFSG.Open.pRank q (⊤ : Subgroup G))) ∧
      (IsAlt (G ⧸ CFSG.solvableRadical G) 6 →
        2 ∣ Nat.card (CFSG.solvableRadical G) ∨ 3 ∣ Nat.card (CFSG.solvableRadical G))

@[expose] def K332 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ Z : Subgroup G, Nat.card Z = p → IsWeaklyClosedIn Z (normalizer (Z : Set G)) →
    CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 3 →
    (3 < p → ∀ q : ℕ, q.Prime → q ≠ 2 → 3 < CFSG.Open.twoLocalPrimeRank q G →
      ∃ N : Subgroup G, IsStronglyPEmbedded q N ∧ ∀ Q : Subgroup G, IsPGroup q Q → ¬ IsCyclic Q →
        Q ≤ N → ∀ N' ∈ calMOf Q, N' ≤ N) →
    ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P (Subgroup.normalClosure (Z : Set G)) → Z ≤ P →
      CFSG.Open.pRank p (Subgroup.normalClosure (Z : Set G)) = 1 ∨
      (LieModel ↥((Subgroup.normalClosure (Z : Set G)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore p G))) .PSU 3 p 1 ∧ ExtraspecialExpP p P) ∨
      (p = 3 ∧ (∃ (r f : ℕ), r.Prime ∧ LieModel ↥((Subgroup.normalClosure (Z : Set G)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore p G))) .G2 0 r f) ∧
        ¬ IsMulCommutative ↥(omegaOne p P)) ∨
      (p = 3 ∧ ExtraspecialExpP 3 P ∧ IsSpor ↥((Subgroup.normalClosure (Z : Set G)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore p G))) .J2) ∨
      (p = 5 ∧ ExtraspecialExpP 5 P ∧ ∃ s : TauCeti.SporadicName,
          (s = .McL ∨ s = .HS ∨ s = .Co3 ∨ s = .Co2) ∧
          IsSpor ↥((Subgroup.normalClosure (Z : Set G)).map
            (QuotientGroup.mk' (CFSG.pPrimeCore p G))) s) ∨
      (p = 11 ∧ ExtraspecialExpP 11 P ∧ IsSpor ↥((Subgroup.normalClosure (Z : Set G)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore p G))) .J4)

@[expose] def K35 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ M : Subgroup G, IsStronglyPEmbedded p M → 1 < CFSG.Open.pRank p (⊤ : Subgroup G) →
    CFSG.pPrimeCore p G = ⊥ → ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P M →
      (IsSimpleGroup ↥(genFittingFStar G) ∧
        genFittingFStar G = (genFittingLayer ↥(Opp p (⊤ : Subgroup G))).map
          (Opp p (⊤ : Subgroup G)).subtype) ∧
      ((∃ n : ℕ, (LieModel ↥(Opp p (⊤ : Subgroup G)) .PSL 2 p n ∨
          LieModel ↥(Opp p (⊤ : Subgroup G)) .PSU 3 p n) ∧ M = normalizer (P : Set G)) ∨
      (Nonempty (↥(Opp p (⊤ : Subgroup G)) ≃* alternatingGroup (Fin (2 * p))) ∧
        Nonempty (↥(genFittingFStar ↥M) ≃*
          (alternatingGroup (Fin p) × alternatingGroup (Fin p)))) ∨
      (p = 3 ∧ ((∃ f : ℕ, LieModel ↥(Opp p (⊤ : Subgroup G)) .twistedG2 0 3 f) ∨
          ∃ X : Type, ∃ _ : Group X, LieModel X .PSL 2 2 3 ∧
            Nonempty (↥(Opp p (⊤ : Subgroup G)) ≃* MulAut X)) ∧ M = normalizer (P : Set G)) ∨
      (∃ n : ℕ, LieModel ↥(Opp p (⊤ : Subgroup G)) .twistedG2 0 3 n ∧
        (p ∣ 3 ^ n + 3 ^ ((n + 1) / 2) + 1 ∨ p ∣ 3 ^ n - 3 ^ ((n + 1) / 2) + 1)) ∨
      (p = 3 ∧ (IsSpor ↥(Opp p (⊤ : Subgroup G)) .M11 ∨
          LieModel ↥(Opp p (⊤ : Subgroup G)) .PSL 3 2 2) ∧ M = normalizer (P : Set G)) ∨
      (p = 5 ∧ IsSpor ↥(Opp p (⊤ : Subgroup G)) .Fi22 ∧ ∃ X : Type, ∃ _ : Group X,
          LieModel X .POmegaPlus 4 2 1 ∧
            Nonempty (↥(Opp p (⊤ : Subgroup G) ⊓ M) ≃* MulAut X)) ∨
      (p = 5 ∧ (LieModel ↥(Opp p (⊤ : Subgroup G)) .Tits 0 2 1 ∨
          (∃ X : Type, ∃ _ : Group X, LieModel X .twistedB2 0 2 5 ∧
            Nonempty (↥(Opp p (⊤ : Subgroup G)) ≃* MulAut X)) ∨
          IsSpor ↥(Opp p (⊤ : Subgroup G)) .McL) ∧ M = normalizer (P : Set G)) ∨
      (p = 11 ∧ IsSpor ↥(Opp p (⊤ : Subgroup G)) .J4 ∧ M = normalizer (P : Set G)))

@[expose] def K36 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G → ∀ M : Subgroup G, M ≠ ⊤ → CFSG.Open.pCoreOf 2 M ≠ ⊥ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ E : Subgroup G, CFSG.Open.IsElemAbelian p E → Nat.card E = p ^ 2 →
    rankThreeGamma 1 p E ≤ M → calMOf E = {M} →
    (∀ q : ℕ, q.Prime → q ≠ 2 → 3 < CFSG.Open.twoLocalPrimeRank q G →
      ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf q S ⊤ →
        (rankThreeGamma 1 q S ⊔ ⨆ (Y : Subgroup G) (_ : Y ≤ S) (_ : 1 < CFSG.Open.pRank q Y),
          ⨆ N ∈ calMOf Y, N) ≠ ⊤ ∨
        (3 < q ∧ (3 ∣ Nat.card G → ∃ N : Subgroup G, IsStronglyPEmbedded 3 N))) →
      p = 3 ∧ ∃ t : G, orderOf t = 2 ∧ CFSG.Open.pCoreOf 2 M = zpowers t ∧
        ∃ L : Subgroup G, L.Normal ∧ L ⊔ M = ⊤ ∧
          (UC6.GraphFieldShape t L ∨
            (Nonempty (↥L ≃* alternatingGroup (Fin 11)) ∧ UC6.InducesTransposition t L))

@[expose] def NatSL2 {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (n : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (φ : G ≃* SL(2, F)) (ψ : V ≃+ (Fin 2 → F)),
    Nat.card F = 2 ^ n ∧ ∀ (g : G) (v : V), ψ (ρ g v) = ((φ g : Matrix (Fin 2) (Fin 2) F)).mulVec (ψ v)

@[expose] def K42 : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Finite V]
      (ρ : Representation (ZMod p) G V), Function.Injective ρ →
    ∀ q r : ℕ, q.Prime → r.Prime → q ≠ p → r ≠ p → q ≠ r →
    ∀ D : Subgroup G, Nat.card D = r → fixV ρ D = ⊥ →
    ∀ Q : Subgroup G, IsPGroup q Q → Q ≠ ⊥ → D ≤ normalizer (Q : Set G) → ⁅D, Q⁆ = Q →
      ¬ IsMulCommutative ↥Q ∧ q = 2 ∧ ∃ k : ℕ, orderOf (2 : ZMod r) = 2 ^ k

@[expose] def K461 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (ρ : Representation (ZMod 2) G V), Function.Injective ρ → ρ.IsIrreducible →
    ∀ D : Subgroup G, Nat.card D = 3 → Subgroup.normalClosure (D : Set G) = ⊤ → fixSub ρ D = ⊥ →
      CFSG.Open.pRank 3 (⊤ : Subgroup G) = 1 → commutator G = ⊤ → ∃ n : ℕ, NatSL2 ρ n

@[expose] def K47 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (ρ : Representation (ZMod 2) G V), Function.Injective ρ →
    ∀ q r : ℕ, q.Prime → r.Prime → q ≠ 2 → r ≠ 2 → q ≠ r →
    ∀ D : Subgroup G, Nat.card D = r → Module.finrank (ZMod 2) (fixSub ρ D) ≤ 1 →
      (∀ R : Subgroup G, IsPGroup r R → D ≤ R → ∀ c ∈ R,
        (∀ d ∈ D, c * d * c⁻¹ * d⁻¹ ∈ (Subgroup.center ↥R).map R.subtype) →
          ∀ d ∈ D, c * d = d * c) ∧
      (∀ Q : Subgroup G, IsPGroup q Q → IsMulCommutative ↥Q → D ≤ normalizer (Q : Set G) →
        ⁅D, Q⁆ = Q → IsCyclic ↥Q)

end CFSG.LocalAnalysis.UniquenessCase.UCK
