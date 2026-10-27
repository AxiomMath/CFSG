module

public import CFSG.Quasithin.EmptyFaithful.S1421Surv
public import CFSG.Quasithin.EmptyFaithful.S1421Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Survivors

variable {G : Type} [Group G]

@[expose] def Survivor4LegacyBare (K1 L2 S : Subgroup G) : Prop :=
  IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (K1 ⊔ bigB K1 L2 S) (L2 ⊔ bigB K1 L2 S))
      (IsLieOverTwo .trialityD4 0 1) ∧ IsL2Quot 3 (OTwoQuot K1) ∧
    IsSpecialPow 2 2 4 ↥(pCoreOf 2 K1) ∧ IsL2Quot 1 (OTwoQuot L2) ∧
    Nat.card (pCoreOf 2 L2) = 2 ^ 11

@[expose] def Survivor10LegacyBare (K1 L2 S : Subgroup G) : Prop :=
  IsParabolicAmalgamOfGroup
      (RankTwoAmalgam.ofSubgroups (K1 ⊔ bigB K1 L2 S) (L2 ⊔ bigB K1 L2 S))
      (fun Y _ => Nonempty (Y ≃* quasithinJ2)) ∧
    IsL2Quot 2 (OTwoQuot K1) ∧ IsQ8D8 ↥(pCoreOf 2 K1) ∧ IsL2Quot 1 (OTwoQuot L2) ∧
    Nat.card (pCoreOf 2 L2) = 2 ^ 6

@[expose] def Survivor11LegacyBare (K1 L2 S : Subgroup G) : Prop :=
  IsParabolicAmalgamOfGroup
      (RankTwoAmalgam.ofSubgroups (K1 ⊔ bigB K1 L2 S) (L2 ⊔ bigB K1 L2 S))
      (fun Y _ => Nonempty (Y ≃* MulAut quasithinJ2)) ∧
    Nonempty (OTwoQuot (K1 ⊔ S) ≃* Equiv.Perm (Fin 5)) ∧ IsQ8D8 ↥(pCoreOf 2 K1) ∧
    Nonempty (OTwoQuot L2 ≃* Equiv.Perm (Fin 3)) ∧ Nat.card (pCoreOf 2 L2) = 2 ^ 6

@[expose] def Survivor4Vertex (K1 L2 S : Subgroup G) : Prop :=
  IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (K1 ⊔ bigB K1 L2 S) (L2 ⊔ bigB K1 L2 S))
      (IsLieOverTwo .trialityD4 0 1) ∧ IsL2Quot 3 (OTwoQuot K1) ∧
    IsSpecialPow 2 2 4 ↥(pCoreOf 2 (K1 ⊔ bigB K1 L2 S)) ∧ IsL2Quot 1 (OTwoQuot L2) ∧
    Nat.card (pCoreOf 2 (L2 ⊔ bigB K1 L2 S)) = 2 ^ 11

@[expose] def Survivor10Vertex (K1 L2 S : Subgroup G) : Prop :=
  IsParabolicAmalgamOfGroup
      (RankTwoAmalgam.ofSubgroups (K1 ⊔ bigB K1 L2 S) (L2 ⊔ bigB K1 L2 S))
      (fun Y _ => Nonempty (Y ≃* quasithinJ2)) ∧
    IsL2Quot 2 (OTwoQuot K1) ∧ IsQ8D8 ↥(pCoreOf 2 (K1 ⊔ bigB K1 L2 S)) ∧
    IsL2Quot 1 (OTwoQuot L2) ∧ Nat.card (pCoreOf 2 (L2 ⊔ bigB K1 L2 S)) = 2 ^ 6

@[expose] def Survivor11Vertex (K1 L2 S : Subgroup G) : Prop :=
  IsParabolicAmalgamOfGroup
      (RankTwoAmalgam.ofSubgroups (K1 ⊔ bigB K1 L2 S) (L2 ⊔ bigB K1 L2 S))
      (fun Y _ => Nonempty (Y ≃* MulAut quasithinJ2)) ∧
    Nonempty (OTwoQuot (K1 ⊔ S) ≃* Equiv.Perm (Fin 5)) ∧
    IsQ8D8 ↥(pCoreOf 2 (K1 ⊔ bigB K1 L2 S)) ∧
    Nonempty (OTwoQuot L2 ≃* Equiv.Perm (Fin 3)) ∧
    Nat.card (pCoreOf 2 (L2 ⊔ bigB K1 L2 S)) = 2 ^ 6

abbrev Survivor4 (K1 L2 S : Subgroup G) : Prop := Survivor4Vertex K1 L2 S

theorem f112Survivor_iff (K1 L2 S : Subgroup G) :
    F112Survivor K1 L2 S ↔
      Survivor4Vertex K1 L2 S ∨ Survivor10Vertex K1 L2 S ∨ Survivor11Vertex K1 L2 S :=
  Iff.rfl

theorem f112SurvivorLegacyBare_iff (K1 L2 S : Subgroup G) :
    F112SurvivorLegacyBare K1 L2 S ↔
      Survivor4LegacyBare K1 L2 S ∨ Survivor10LegacyBare K1 L2 S ∨ Survivor11LegacyBare K1 L2 S :=
  Iff.rfl

end Survivors

section D4

variable {G : Type} [Group G]

@[expose] def autStab {D : Type} [Group D] (P : Subgroup D) : Subgroup (MulAut D) where
  carrier := {φ | ∀ x : D, x ∈ P ↔ φ x ∈ P}
  one_mem' := fun x => Iff.rfl
  mul_mem' := fun {φ ψ} hφ hψ x => (hψ x).trans (hφ (ψ x))
  inv_mem' := fun {φ} hφ x => by
    have := hφ (φ⁻¹ x)
    simpa using this.symm

@[expose] def IsExtensionOfLieAmalgam (D : Type) [Group D] (M₁ M₂ : Subgroup G) : Prop :=
  ∃ (Mbar : Subgroup (MulAut D)) (TD P₁ P₂ : Subgroup D),
    (MulAut.conj : D →* MulAut D).range ≤ Mbar ∧ IsYAmalgamPair TD P₁ P₂ ∧
    (∀ φ ∈ Mbar, φ ∈ autStab (P₁ ⊓ P₂) → φ ∈ autStab P₁) ∧
    Nonempty ((RankTwoAmalgam.ofSubgroups M₁ M₂).Iso
      (RankTwoAmalgam.ofSubgroups (Mbar ⊓ autStab P₁) (Mbar ⊓ autStab P₂)))

end D4

@[expose] def F431D4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (M₁ M₂ : Subgroup G) (z : G),
      (∃ (D : Type) (_ : Group D), IsLieOverTwo .trialityD4 0 1 D ∧
        IsExtensionOfLieAmalgam D M₁ M₂) →
      z ^ 2 = 1 → z ≠ 1 → z ∈ twoPrimeResidual M₁ →
      z ∈ Subgroup.centralizer (twoPrimeResidual M₁ : Set G) →
      Subgroup.centralizer ({z} : Set G) ≤ M₁ →
      ∃ (D : Type) (_ : Group D), IsLieOverTwo .trialityD4 0 1 D ∧ Nonempty (G ≃* D)

@[expose] def TrialityD4Bridge : Prop :=
  ∀ (D : Type) [Group D], IsLieOverTwo .trialityD4 0 1 D → Nonempty (D ≃* quasithinTrialityD4Two)

@[expose] noncomputable def involutionClassCount (G : Type) [Group G] : ℕ :=
  Set.ncard {c : ConjClasses G | ∃ x : G, x ^ 2 = 1 ∧ x ≠ 1 ∧ ConjClasses.mk x = c}

@[expose] def I47Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ z : G, z ^ 2 = 1 → z ≠ 1 →
      CharTwo (Subgroup.centralizer ({z} : Set G)) →
      IsQ8D8 ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) →
      Nonempty (OTwoQuot (Subgroup.centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 5)) →
      (∃ g : G, g * z * g⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
        g * z * g⁻¹ ≠ z) →
      (involutionClassCount G = 2 → Nonempty (G ≃* quasithinJ2)) ∧
        (involutionClassCount G = 1 → Nonempty (G ≃* quasithinJ3))

@[expose] def Facts1422Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M → Facts1422 T M

@[expose] def E22Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G), Hyp1421 G T M → Facts1422 T M →
    IsHStar T M H → E1.nParam H ≠ 1 →
    ∃ K1 : Subgroup G, Notation1428 T M H K1 ∧ Shape1428 T H K1

@[expose] def Lemma14213 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    ¬ pCoreOf 2 M ≤ S1421.sOf T K1 → pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1

@[expose] def Hyp111fInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    ¬ pCoreOf 2 M ≤ S1421.sOf T K1 → pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 →
    CharTwo (S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1 ⊔ borelOf K1 (S1421.sOf T K1))

@[expose] def Lemma14215 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    S1421.sOf T K1 < T → pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 →
    pCoreOf 2 (K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1) = ⊥

@[expose] def Lemma14216Tail : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 →
    F112Survivor K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) →
    oTwoUpper H = K1 ∧ T = S1421.sOf T K1 ∧ pCoreOf 2 (mcOf T) = pCoreOf 2 K1

@[expose] def Lemma14217J2LegacyBare : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 →
    (Survivor10LegacyBare K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) ∨
      Survivor11LegacyBare K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1)) →
    (oTwoUpper H = K1 ∧ T = S1421.sOf T K1 ∧ pCoreOf 2 (mcOf T) = pCoreOf 2 K1) →
    ∃ z : G, z ^ 2 = 1 ∧ z ≠ 1 ∧ CharTwo (Subgroup.centralizer ({z} : Set G)) ∧
      IsQ8D8 ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ∧
      Nonempty (OTwoQuot (Subgroup.centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 5)) ∧
      (∃ g : G, g * z * g⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
        g * z * g⁻¹ ≠ z) ∧
      (involutionClassCount G = 1 ∨ involutionClassCount G = 2)

@[expose] def Lemma14218D4LegacyBare : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 →
    Survivor4LegacyBare K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) →
    (oTwoUpper H = K1 ∧ T = S1421.sOf T K1 ∧ pCoreOf 2 (mcOf T) = pCoreOf 2 K1) →
    ∃ (M₁ M₂ : Subgroup G) (z : G),
      (∃ (D : Type) (_ : Group D), IsLieOverTwo .trialityD4 0 1 D ∧
        IsExtensionOfLieAmalgam D M₁ M₂) ∧
      z ^ 2 = 1 ∧ z ≠ 1 ∧ z ∈ twoPrimeResidual M₁ ∧
      z ∈ Subgroup.centralizer (twoPrimeResidual M₁ : Set G) ∧
      Subgroup.centralizer ({z} : Set G) ≤ M₁

@[expose] def Lemma14216TailLegacyBare : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 →
    F112SurvivorLegacyBare K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) →
    oTwoUpper H = K1 ∧ T = S1421.sOf T K1 ∧ pCoreOf 2 (mcOf T) = pCoreOf 2 K1

@[expose] def Lemma14217J2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 →
    (Survivor10Vertex K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) ∨
      Survivor11Vertex K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1)) →
    (oTwoUpper H = K1 ∧ T = S1421.sOf T K1 ∧ pCoreOf 2 (mcOf T) = pCoreOf 2 K1) →
    ∃ z : G, z ^ 2 = 1 ∧ z ≠ 1 ∧ CharTwo (Subgroup.centralizer ({z} : Set G)) ∧
      IsQ8D8 ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ∧
      Nonempty (OTwoQuot (Subgroup.centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 5)) ∧
      (∃ g : G, g * z * g⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
        g * z * g⁻¹ ≠ z) ∧
      (involutionClassCount G = 1 ∨ involutionClassCount G = 2)

@[expose] def Lemma14218D4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 →
    Survivor4Vertex K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) →
    (oTwoUpper H = K1 ∧ T = S1421.sOf T K1 ∧ pCoreOf 2 (mcOf T) = pCoreOf 2 K1) →
    ∃ (M₁ M₂ : Subgroup G) (z : G),
      (∃ (D : Type) (_ : Group D), IsLieOverTwo .trialityD4 0 1 D ∧
        IsExtensionOfLieAmalgam D M₁ M₂) ∧
      z ^ 2 = 1 ∧ z ≠ 1 ∧ z ∈ twoPrimeResidual M₁ ∧
      z ∈ Subgroup.centralizer (twoPrimeResidual M₁ : Set G) ∧
      Subgroup.centralizer ({z} : Set G) ≤ M₁

end CFSG.Quasithin
