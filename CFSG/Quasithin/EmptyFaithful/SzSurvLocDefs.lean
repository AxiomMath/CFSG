module

public import CFSG.Quasithin.EmptyFaithful.S1421Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section SurvivorsLoc

variable {G : Type} [Group G]

@[expose] def Survivor10Loc (K1 _L2 S : Subgroup G) : Prop :=
  IsL2Quot 2 (OTwoQuot K1) ∧ IsQ8D8 ↥(pCoreOf 2 K1) ∧ S ≤ K1

@[expose] def Survivor11Loc (K1 L2 S : Subgroup G) : Prop :=
  Nonempty (OTwoQuot (K1 ⊔ S) ≃* Equiv.Perm (Fin 5)) ∧ IsQ8D8 ↥(pCoreOf 2 K1) ∧
    ∃ (Y : Type) (_ : Group Y), Nonempty (Y ≃* MulAut quasithinJ2) ∧
      ∃ (TY M₁ : Subgroup Y) (_ : ↥(K1 ⊔ bigB K1 L2 S) ≃* ↥M₁), IsSylowTwoOf TY ⊤ ∧ TY ≤ M₁

@[expose] def F112SurvivorLoc (K1 L2 S : Subgroup G) : Prop :=
  Survivor4LegacyBare K1 L2 S ∨ Survivor10Loc K1 L2 S ∨ Survivor11Loc K1 L2 S

end SurvivorsLoc

@[expose] def Lemma14216QLoc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 →
    F112SurvivorLoc K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) →
    pCoreOf 2 (mcOf T) = pCoreOf 2 K1

@[expose] def Lemma14216TailLoc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 →
    F112SurvivorLoc K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) →
    oTwoUpper H = K1 ∧ T = S1421.sOf T K1 ∧ pCoreOf 2 (mcOf T) = pCoreOf 2 K1

@[expose] def Lemma14217J2Loc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 →
    (Survivor10Loc K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) ∨
      Survivor11Loc K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1)) →
    (oTwoUpper H = K1 ∧ T = S1421.sOf T K1 ∧ pCoreOf 2 (mcOf T) = pCoreOf 2 K1) →
    ∃ z : G, z ^ 2 = 1 ∧ z ≠ 1 ∧ CharTwo (Subgroup.centralizer ({z} : Set G)) ∧
      IsQ8D8 ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ∧
      Nonempty (OTwoQuot (Subgroup.centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 5)) ∧
      (∃ g : G, g * z * g⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
        g * z * g⁻¹ ≠ z) ∧
      (involutionClassCount G = 1 ∨ involutionClassCount G = 2)

end CFSG.Quasithin
