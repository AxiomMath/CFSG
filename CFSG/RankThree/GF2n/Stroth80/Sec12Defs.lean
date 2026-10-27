module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def SpMNat (hc : Ctx M Q Z B) (t : G) (m : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
    NaturalRep (ι := Fin m ⊕ Fin m) K (StatedSp m K) (Rt M (LB M Q B) t)
      (Vt M (LB M Q B) B Z t) Z (hc.CN t)

@[expose] def OmegaPlusNat (hc : Ctx M Q Z B) (t : G) (m : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
    NaturalRep (ι := Fin m ⊕ Fin m) K (StatedOmega (StatedQuadPlus m K)) (Rt M (LB M Q B) t)
      (Vt M (LB M Q B) B Z t) Z (hc.CN t)

@[expose] def OmegaMinusNat (hc : Ctx M Q Z B) (t : G) (m : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧ ∃ b c : K,
    (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
      NaturalRep (ι := Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K
        (StatedOmega (StatedQuadMinus m K b c)) (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z
        (hc.CN t)

@[expose] def SLMNat (hc : Ctx M Q Z B) (t : G) (m : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
    NaturalRep (ι := Fin m) K (StatedSL m K) (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z
      (hc.CN t)

@[expose] def SLlike (hc : Ctx M Q Z B) (t : G) : Prop :=
  ∃ m : ℕ, 2 ≤ m ∧ (SLMNat hc t m ∨ (m = 2 ∧ SpMNat hc t 1))

structure Stroth6Hyp (hc : Ctx M Q Z B) (n : ℕ) (t : G) : Prop where
  toSec5 : Sec5Hyp hc n t
  cardN : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z

structure Stroth12Hyp (hc : Ctx M Q Z B) (n : ℕ) : Prop where
  width : Width Q Z n
  n_gt : 2 < n
  noA2 : NoA2 Q Z (LB M Q B)
  gen : GenByB M Q B
  notTI : ¬ IsTIMod M Q (LB M Q B)
  large : ∀ τ ∈ LB M Q B, τ ∉ Q → Nat.card Q * Nat.card Z < Nat.card ↥(hc.CN τ)

theorem Stroth12Hyp.toSec5 {hc : Ctx M Q Z B} {n : ℕ} (h : Stroth12Hyp hc n) {t : G}
    (ht : t ∈ LB M Q B) (htQ : t ∉ Q) : Sec5Hyp hc n t :=
  ⟨h.width, h.n_gt, h.noA2, h.gen, ht, htQ⟩

@[expose] def StronglyClosedMod (M N L : Subgroup G) : Prop :=
  ∀ x ∈ N, ∀ g ∈ M, g * x * g⁻¹ ∈ L → g * x * g⁻¹ ∈ N

@[expose] def IsIrredModule (R P I : Subgroup G) : Prop :=
  (∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ I) ∧ (∀ x ∈ P, x ^ 2 ∈ I) ∧ I < P ∧
    ∀ A : Subgroup G, I ≤ A → A ≤ P → (∀ r ∈ R, conjSubgroup r A = A) → A = I ∨ A = P

@[expose] def FStarU6 (M Q Z : Subgroup G) [(Q.subgroupOf M).Normal] : Prop :=
  IsPSUModel 6 (Nat.card Z) ↥(generalizedFitting ↥(bar M Q (H0 M Z)))

@[expose] def FStarL6 (M Q Z : Subgroup G) [(Q.subgroupOf M).Normal] : Prop :=
  IsPSLModel 6 (Nat.card Z) ↥(generalizedFitting ↥(bar M Q (H0 M Z)))

@[expose] def Sec12Iii (M Q Z S : Subgroup G) : Prop :=
  (∃ hN : (Q.subgroupOf M).Normal, haveI := hN
    layer (↥M ⧸ Q.subgroupOf M) = (S.subgroupOf M).map (QuotientGroup.mk' (Q.subgroupOf M))) ∧
    (QuotSat S Q (IsPSUModel 6 (Nat.card Z)) ∨ QuotSat S Q (IsPSLModel 6 (Nat.card Z)))

@[expose] def IsCentrePre (Z0 R Q : Subgroup G) : Prop :=
  ∀ x, x ∈ Z0 ↔ x ∈ R ∧ ∀ r ∈ R, ⁅x, r⁆ ∈ Q

@[expose] def StrothC2 (Q Z S : Subgroup G) : Prop :=
  Nat.card Q = Nat.card Z ^ 5 ∧ QuotSat S Q (IsSLModel 2 (Nat.card Z))

@[expose] def StrothC3 (M Q Z S : Subgroup G) : Prop :=
  Nat.card Q = Nat.card Z ^ 9 ∧ QuotSat S Q (IsSLModel 2 (Nat.card Z ^ 3)) ∧ CentTrivial M Q Z S

@[expose] def StrothCi (M Q Z B : Subgroup G) (t : G) : Prop :=
  Nat.card Q = Nat.card Z ^ 9 ∧ Nat.card (Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z ∧
    (QuotSat (Rt M (LB M Q B) t) (Nt M (LB M Q B) t) (IsOmegaPlus 2 (Nat.card Z)) ∨
      QuotSat (Rt M (LB M Q B) t) (Nt M (LB M Q B) t) (IsOmegaMinus 2 (Nat.card Z)))

@[expose] def StrothCii (M Q Z B : Subgroup G) (t : G) : Prop :=
  ∃ m : ℕ, 2 ≤ m ∧ Nat.card Q = Nat.card Z ^ (4 * m + 1) ∧
    Nat.card (Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z ∧
    ((QuotSat (Rt M (LB M Q B) t) (Nt M (LB M Q B) t) (IsOmegaPlus m (Nat.card Z)) ∧
        QuotSat (Lgen M (LB M Q B)) Q
          (IsProdOf (IsSLModel 2 (Nat.card Z)) (IsOmegaPlus m (Nat.card Z)))) ∨
      (QuotSat (Rt M (LB M Q B) t) (Nt M (LB M Q B) t) (IsOmegaMinus m (Nat.card Z)) ∧
        QuotSat (Lgen M (LB M Q B)) Q
          (IsProdOf (IsSLModel 2 (Nat.card Z)) (IsOmegaMinus m (Nat.card Z)))))

@[expose] def StrothCiii (M Q Z S : Subgroup G) : Prop :=
  Nat.card Q = Nat.card Z ^ 21 ∧ Sec12Iii M Q Z S

@[expose] def StrothCiv (M Q Z B : Subgroup G) (t : G) : Prop :=
  Nat.card Q = Nat.card Z ^ 33 ∧
    Nat.card (Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z ^ 17 ∧
    QuotSat (Rt M (LB M Q B) t) (Nt M (LB M Q B) t) (IsOmegaPlus 4 (Nat.card Z)) ∧
    SubConfig M Q Z (Nt M (LB M Q B) t)

@[expose] def StrothCv (M Q Z B : Subgroup G) (t : G) : Prop :=
  Nat.card Q = Nat.card Z ^ 57 ∧
    Nat.card (Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z ^ 33 ∧
    QuotSat (Rt M (LB M Q B) t) (Nt M (LB M Q B) t) (IsOmegaPlus 6 (Nat.card Z)) ∧
    SubConfig M Q Z (Nt M (LB M Q B) t)

theorem strothConclusion_of {M Q Z B : Subgroup G} (hf : FrobClause M Z)
    (h : (∃ n : ℕ, Nat.card Z = 2 ^ n ∧ Tim79.IsL3Type n Q) ∨
      StrothC2 Q Z (Lgen M (LB M Q B)) ∨ StrothC3 M Q Z (Lgen M (LB M Q B)) ∨
      (¬ IsTIMod M Q (LB M Q B) ∧
        ((NoA2All M Q Z ∧ ∃ t ∈ LB M Q B, t ∉ Q ∧ CentTrivial M Q Z (Lgen M (LB M Q B)) ∧
          (StrothCi M Q Z B t ∨ StrothCii M Q Z B t ∨ StrothCiii M Q Z (Lgen M (LB M Q B)) ∨
            StrothCiv M Q Z B t ∨ StrothCv M Q Z B t)) ∨
        CaseVI M Q Z (Lgen M (LB M Q B))))) :
    StrothConclusion M Q Z B :=
  ⟨h, hf⟩

end CFSG.RankThree.GF2n.Stroth80
