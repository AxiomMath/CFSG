module

public import CFSG.LocalAnalysis.ZStar.ModularBrauerQuotient
public import CFSG.LocalAnalysis.ZStar.RegularIdempotent

public section

namespace CFSG

namespace ZStar.RegularBrauerQuotient

open ZStar.BrauerPrincipal
open ZStar.BrauerProjection
open ZStar.Helpers
open ZStar.ModularBrauerQuotient
open ZStar.PrincipalBlockKernel
open ZStar.RegularIdempotent

noncomputable section

universe u v

variable {G : Type u} [Group G] [Fintype G]
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

noncomputable local instance subgroupFintype (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

private theorem principalBlockCandidate_mul_regularIdempotent
    (X : Type*) [Group X] [Fintype X] :
    principalBlockCandidate X * regularIdempotent X =
      principalBlockCandidate X := by
  exact
    ZStar.principalBlockCandidate_mul_eq_self_of_augmentation_one
      X (regularIdempotent X) (regularIdempotent_central X)
      (regularIdempotent_idempotent X)
      (regularIdempotent_augmentation X)

private theorem regularIdempotentActsAsIdentity
    (ρ : Representation (ZMod 2) G V)
    (hρ : PrincipalBlockActsAsIdentity ρ) :
    ρ.asAlgebraHom (regularIdempotent G) =
      (1 : Module.End (ZMod 2) V) := by
  have hmap := congrArg ρ.asAlgebraHom
    (principalBlockCandidate_mul_regularIdempotent G)
  change ρ.asAlgebraHom (principalBlockCandidate G) = 1 at hρ
  simpa only [map_mul, hρ, one_mul] using hmap

private theorem brauerProjectionActsAsIdentity_brauerQuotient
    (ρ : Representation (ZMod 2) G V) (w : G) (hw2 : w * w = 1)
    (a : GroupAlgebraTwo G) (ha : IsGroupCentral G a)
    (haction : ρ.asAlgebraHom a = (1 : Module.End (ZMod 2) V)) :
    (brauerQuotientRepresentation ρ w).asAlgebraHom
        (brauerProjection w a) =
      (1 : Module.End (ZMod 2) (BrauerQuotient ρ w)) := by
  apply LinearMap.ext
  intro q
  refine Submodule.Quotient.induction_on (brauerRangeInKernel ρ w) q ?_
  intro x
  change
    (brauerQuotientRepresentation ρ w).asAlgebraHom
        (brauerProjection w a) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x
  rw [brauerProjection_action_mk ρ w hw2 a ha]
  have happ := congrArg
    (fun f : Module.End (ZMod 2) V => f (x : V)) haction
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  simpa using happ

private theorem regularIdempotentActsAsIdentity_brauerQuotient
    (ρ : Representation (ZMod 2) G V) (w : G) (hw2 : w * w = 1)
    (hρ : PrincipalBlockActsAsIdentity ρ) :
    (brauerQuotientRepresentation ρ w).asAlgebraHom
        (regularIdempotent (involutionCentralizer w)) =
      (1 : Module.End (ZMod 2) (BrauerQuotient ρ w)) := by
  rw [← brauerProjection_regularIdempotent w hw2]
  exact brauerProjectionActsAsIdentity_brauerQuotient
    ρ w hw2 (regularIdempotent G) (regularIdempotent_central G)
      (regularIdempotentActsAsIdentity ρ hρ)

private theorem oddNormal_action_eq_one_brauerQuotient
    (ρ : Representation (ZMod 2) G V) (w : G) (hw2 : w * w = 1)
    (hρ : PrincipalBlockActsAsIdentity ρ)
    (N : Subgroup (involutionCentralizer w)) [N.Normal]
    (hNodd : Odd (Nat.card N)) (n : N) :
    brauerQuotientRepresentation ρ w (n : involutionCentralizer w) =
      (1 : Module.End (ZMod 2) (BrauerQuotient ρ w)) := by
  have hfix :=
    single_mul_regularIdempotent_of_mem_odd_normal N hNodd n
  have hmap := congrArg
    (brauerQuotientRepresentation ρ w).asAlgebraHom hfix
  have hr := regularIdempotentActsAsIdentity_brauerQuotient ρ w hw2 hρ
  simpa only [map_mul, Representation.asAlgebraHom_single_one, hr, mul_one]
    using hmap

private theorem oddNormal_action_apply_brauerQuotient
    (ρ : Representation (ZMod 2) G V) (w : G) (hw2 : w * w = 1)
    (hρ : PrincipalBlockActsAsIdentity ρ)
    (N : Subgroup (involutionCentralizer w)) [N.Normal]
    (hNodd : Odd (Nat.card N)) (n : N) (q : BrauerQuotient ρ w) :
    brauerQuotientRepresentation ρ w (n : involutionCentralizer w) q = q := by
  have h := congrArg
    (fun f : Module.End (ZMod 2) (BrauerQuotient ρ w) => f q)
    (oddNormal_action_eq_one_brauerQuotient ρ w hw2 hρ N hNodd n)
  simpa using h

theorem oddNormal_action_sub_mem_involutionDifference_range
    (ρ : Representation (ZMod 2) G V) (w : G) (hw2 : w * w = 1)
    (hρ : PrincipalBlockActsAsIdentity ρ)
    (N : Subgroup (involutionCentralizer w)) [N.Normal]
    (hNodd : Odd (Nat.card N)) (n : N)
    (x : brauerKernel ρ w) :
    ρ ((n : involutionCentralizer w) : G) (x : V) - (x : V) ∈
      (involutionDifference ρ w).range := by
  have hq := oddNormal_action_apply_brauerQuotient
    ρ w hw2 hρ N hNodd n (Submodule.Quotient.mk x)
  rw [brauerQuotientRepresentation_mk] at hq
  have hmem := (Submodule.Quotient.eq (brauerRangeInKernel ρ w)).mp hq
  exact hmem

end

end ZStar.RegularBrauerQuotient

end CFSG
