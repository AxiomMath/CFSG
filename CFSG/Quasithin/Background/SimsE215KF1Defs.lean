module

public import CFSG.Quasithin.Vol2.Ch3E213MDefs
public import CFSG.Quasithin.Background.SimsE2Defs

public section

namespace CFSG.Quasithin.SimsE2.KF1

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch3E213M

section Defs

variable {Γ : Type} [Group Γ]

@[expose] def KF1All (H T M V : Subgroup Γ) : Prop :=
  ∀ (I : Subgroup Γ) (g : Γ), IsInIHTV H T M V I → g ∈ I → I = V ⊔ conjSubgroup V g →
    ⁅(conjSubgroup V g ⊓ pCoreOf 2 I) ⊔ (V ⊓ pCoreOf 2 I), I⁆ ≤ pCoreOf 2 H

@[expose] def StarCentral (H T M V : Subgroup Γ) : Prop :=
  ∃ F₀ : Subgroup (E2.StarQuot M H), F₀.Normal ∧ E2.star M H V ≤ F₀ ∧
    E2.star M H V ≤
      Subgroup.centralizer ((E2.star M H T ⊓ F₀ : Subgroup (E2.StarQuot M H)) :
        Set (E2.StarQuot M H))

end Defs

@[expose] def PkgL2PairedKF1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case1 H T M K → ∀ n : ℕ, 2 ≤ n → IsPSL 2 2 n ↥(E2.star M H K) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → StarCentral H T M V

@[expose] def PkgSzPairedKF1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case1 H T M K → ∀ n : ℕ, 2 ≤ n → IsSz n ↥(E2.star M H K) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → StarCentral H T M V

@[expose] def PkgOddPairedKF1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case1 H T M K → ∀ p : ℕ, p.Prime → (p % 8 = 1 ∨ p % 8 = 7) →
    IsPSL 2 p 1 ↥(E2.star M H K) →
    E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)) →
    8 < E2.autCard (E2.star M H T) (E2.star M H K) → StarCentral H T M V

@[expose] def PkgBenderSingleKF1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K → ∀ n : ℕ, E2.IsBenderOf n ↥(E2.star M H K) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → StarCentral H T M V

@[expose] def PkgL3KF1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K → ∀ n : ℕ, 1 ≤ n → IsPSL 3 2 n ↥(E2.star M H K) →
    E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → StarCentral H T M V

@[expose] def PkgSp4TwoKF1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K → ∀ n : ℕ, 2 ≤ n → E2.IsSp4Prime n ↥(E2.star M H K) →
    E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → StarCentral H T M V

@[expose] def PkgSp4OneKF1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K → E2.IsSp4Prime 1 ↥(E2.star M H K) →
    E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → StarCentral H T M V

@[expose] def PkgOddSingleKF1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K → ∀ p e : ℕ, p.Prime → 3 < p → (e = 1 ∨ e = 2) →
    (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) → IsPSL 2 p e ↥(E2.star M H K) →
    E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)) →
    8 < E2.autCard (E2.star M H T) (E2.star M H K) → StarCentral H T M V

@[expose] def PkgOddL3KF1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ((p % 4 = 1 ∧ IsPSU 3 p 1 ↥(E2.star M H K)) ∨
      (p % 4 = 3 ∧ IsPSL 3 p 1 ↥(E2.star M H K) ∧
        E2.InducesOuter (E2.star M H T) (E2.star M H K))) →
    E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)) →
    StarCentral H T M V

@[expose] def SolvableKF1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V : Subgroup G), E2.Hyp28 H T M V → CharTwo H →
    Group.IsSolvable H → KF1All H T M V

end CFSG.Quasithin.SimsE2.KF1
