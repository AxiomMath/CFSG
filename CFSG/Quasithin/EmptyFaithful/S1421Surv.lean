module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

structure ListedGroupFacts : Prop where
  l2_ne_perm3 : ∀ (f : ℕ), 2 ≤ f → ∀ (X : Type) [Group X], IsL2Quot f X →
    ¬ Nonempty (X ≃* Equiv.Perm (Fin 3))
  l2_one_solvable : ∀ (X : Type) [Group X], IsL2Quot 1 X → Group.IsSolvable X
  dihedral5_solvable : ∀ (X : Type) [Group X], Nonempty (X ≃* DihedralGroup 5) → Group.IsSolvable X
  sz0_solvable : ∀ (X : Type) [Group X], Nonempty (X ≃* ↥(Sz 0)) → Group.IsSolvable X
  perm4_solvable : ∀ (X : Type) [Group X], Nonempty (X ≃* Equiv.Perm (Fin 4)) →
    Group.IsSolvable X
  z2perm4_solvable : ∀ (X : Type) [Group X],
    Nonempty (X ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) → Group.IsSolvable X
  sz_ne_perm3 : ∀ (a : ℕ) (X : Type) [Group X], Nonempty (X ≃* ↥(Sz a)) →
    ¬ Nonempty (X ≃* Equiv.Perm (Fin 3))
  su3_ne_perm3 : ∀ (X : Type) [Group X] (F : Type) [Field F] [Finite F], Nat.card F = 4 ^ 2 →
    Nonempty (X ≃* StatedSU 3 4 F) → ¬ Nonempty (X ≃* Equiv.Perm (Fin 3))
  dihedral5_ne_perm3 : ∀ (X : Type) [Group X], Nonempty (X ≃* DihedralGroup 5) →
    ¬ Nonempty (X ≃* Equiv.Perm (Fin 3))
  perm5_not_solvable : ∀ (X : Type) [Group X], Nonempty (X ≃* Equiv.Perm (Fin 5)) →
    ¬ Group.IsSolvable X

section Survivor

variable {G : Type} [Group G]

@[expose] def F112SurvivorLegacyBare (K1 L2 S : Subgroup G) : Prop :=
  let α := RankTwoAmalgam.ofSubgroups (K1 ⊔ bigB K1 L2 S) (L2 ⊔ bigB K1 L2 S)
  (IsAmalgamOfGroup α (IsLieOverTwo .trialityD4 0 1) ∧ IsL2Quot 3 (OTwoQuot K1) ∧
      IsSpecialPow 2 2 4 ↥(pCoreOf 2 K1) ∧ IsL2Quot 1 (OTwoQuot L2) ∧
      Nat.card (pCoreOf 2 L2) = 2 ^ 11) ∨
  (IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinJ2)) ∧
      IsL2Quot 2 (OTwoQuot K1) ∧ IsQ8D8 ↥(pCoreOf 2 K1) ∧ IsL2Quot 1 (OTwoQuot L2) ∧
      Nat.card (pCoreOf 2 L2) = 2 ^ 6) ∨
  (IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* MulAut quasithinJ2)) ∧
      Nonempty (OTwoQuot (K1 ⊔ S) ≃* Equiv.Perm (Fin 5)) ∧ IsQ8D8 ↥(pCoreOf 2 K1) ∧
      Nonempty (OTwoQuot L2 ≃* Equiv.Perm (Fin 3)) ∧ Nat.card (pCoreOf 2 L2) = 2 ^ 6)

@[expose] def F112Survivor (K1 L2 S : Subgroup G) : Prop :=
  let P1 := K1 ⊔ bigB K1 L2 S
  let P2 := L2 ⊔ bigB K1 L2 S
  let α := RankTwoAmalgam.ofSubgroups P1 P2
  (IsAmalgamOfGroup α (IsLieOverTwo .trialityD4 0 1) ∧ IsL2Quot 3 (OTwoQuot K1) ∧
      IsSpecialPow 2 2 4 ↥(pCoreOf 2 P1) ∧ IsL2Quot 1 (OTwoQuot L2) ∧
      Nat.card (pCoreOf 2 P2) = 2 ^ 11) ∨
  (IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinJ2)) ∧
      IsL2Quot 2 (OTwoQuot K1) ∧ IsQ8D8 ↥(pCoreOf 2 P1) ∧ IsL2Quot 1 (OTwoQuot L2) ∧
      Nat.card (pCoreOf 2 P2) = 2 ^ 6) ∨
  (IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* MulAut quasithinJ2)) ∧
      Nonempty (OTwoQuot (K1 ⊔ S) ≃* Equiv.Perm (Fin 5)) ∧ IsQ8D8 ↥(pCoreOf 2 P1) ∧
      Nonempty (OTwoQuot L2 ≃* Equiv.Perm (Fin 3)) ∧ Nat.card (pCoreOf 2 P2) = 2 ^ 6)

abbrev F112SurvivorVertex (K1 L2 S : Subgroup G) : Prop := F112Survivor K1 L2 S

end Survivor

end CFSG.Quasithin
