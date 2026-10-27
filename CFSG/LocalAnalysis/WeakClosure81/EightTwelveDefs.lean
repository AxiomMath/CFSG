module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (IsL2 IsSz IsL3 IsU3 IsSp4 IsU4 IsU5 IsOmega8m Is3D4 IsAlt IsSL3 Bar2 OInf Opp)

variable {G : Type} [Group G] [Finite G]

@[expose] def Concl812 (V H T : Subgroup G) (i : ℕ) (A : Subgroup G) : Prop :=
  rk ↥V = 3 ∧ i = 1 ∧ rk ↥A = 2 ∧
    (∀ K : Subgroup G, CFSG.LocalAnalysis.UniquenessCase.UC22.F12.IsEP 1 H T A K →
      K ≤ normalizer (V : Set G)) ∧
    ¬ InFSq 1 H

@[expose] def eGrp (H T : Subgroup G) : Subgroup G :=
  conjClosure (omegaOneCenterOf T) H

@[expose] def cGrp (H T : Subgroup G) : Subgroup G :=
  H ⊓ centralizer (eGrp H T : Set G)

@[expose] def cenTMod (C L T : Subgroup G) : Set G :=
  {t | t ∈ T ∧ ∀ l ∈ L, t * l * t⁻¹ * l⁻¹ ∈ C}

@[expose] def oddResMod (N P : Subgroup G) : Subgroup G :=
  ⨅ Q ∈ {Q : Subgroup G | N ≤ Q ∧ Q ≤ P ∧ (Q.subgroupOf P).Normal ∧ Odd (Q.relIndex P)}, Q

structure Concl813 (V H T A L K : Subgroup G) : Prop where
  comp : IsComponentModN (cGrp H T) H L
  sub_L : K ≤ L
  ge_C : cGrp H T ≤ K
  a_le : ∀ x ∈ A, ∃ k ∈ K, ∃ t ∈ cenTMod (cGrp H T) L T, (k * t)⁻¹ * x ∈ cGrp H T
  b_not_le : ¬ ∀ x ∈ A, ∃ o ∈ oTwoMod (cGrp H T) K, ∃ t ∈ cenTMod (cGrp H T) L T,
    (o * t)⁻¹ * x ∈ cGrp H T
  c_shape : HasQuotShape K (oTwoMod (cGrp H T) K : Set G) (fun X _ => IsL2 X 2)
  d_index : (K ⊓ normalizer (V : Set G)).relIndex K = 5
  e_shape :
    (HasQuotShape L (cGrp H T : Set G) (fun X _ => IsL2 X 2) ∨
        HasQuotShape L (cGrp H T : Set G) (fun X _ => IsU3 X 2)) ∨
      ((HasQuotShape L (cGrp H T : Set G) (fun X _ => IsL3 X 2) ∨
          HasQuotShape L (cGrp H T : Set G) (fun X _ => IsSL3 X 2) ∨
          HasQuotShape L (cGrp H T : Set G) (fun X _ => IsSp4 X 2)) ∧
        ((∃ P : Subgroup G, IsMaxParabolicMod (cGrp H T) L P ∧ K = oddResMod (cGrp H T) P) ∨
          ∀ a ∈ A, ∀ t ∈ T ⊓ conjClosure L H, a * t * a⁻¹ * t⁻¹ ∈ cGrp H T))
  t_sylow : IsSylowIn 2 (T ⊓ K) K

structure Sit813 (V H T : Subgroup G) (i : ℕ) (A L K : Subgroup G) : Prop where
  minCex : MinCex88 V H T i
  calH0 : IsCalH0 V H
  mem : A ∈ E3.gammaSet V i T
  notLe : ∃ x ∈ H, ¬ conjSubgroup A x ≤ normalizer (V : Set G)
  concl812 : Concl812 V H T i A
  concl813 : Concl813 V H T A L K

@[expose] def rGrp (H T K : Subgroup G) : Subgroup G :=
  Subgroup.closure {t : G | t ∈ T ∧ t ∈ normalizer (K : Set G) ∧
    ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ oTwoMod (cGrp H T) K}

@[expose] def sGrp (H T A K : Subgroup G) : Subgroup G :=
  rGrp H T K ⊔ A

@[expose] def uGrp (V K : Subgroup G) : Subgroup G :=
  conjClosure V K

@[expose] def v1Grp (V H T A K : Subgroup G) : Subgroup G :=
  V ⊓ centralizer (sGrp H T A K : Set G)

@[expose] def u1Grp (V H T A K : Subgroup G) : Subgroup G :=
  conjClosure (v1Grp V H T A K) K

@[expose] def IsNaturalSL2Module (K U D : Subgroup G) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    ∃ (φ : ↥K →* Matrix.SpecialLinearGroup (Fin 2) F) (ψ : ↥U →* Multiplicative (Fin 2 → F)),
      Function.Surjective φ ∧ Function.Surjective ψ ∧
      (∀ u : ↥U, ψ u = 1 ↔ (u : G) ∈ D) ∧
      ∀ (k : ↥K) (u u' : ↥U), (u' : G) = (k : G) * (u : G) * (k : G)⁻¹ →
        Multiplicative.toAdd (ψ u') =
          (φ k : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (ψ u))

end CFSG.LocalAnalysis.WeakClosure81

end
