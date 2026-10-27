module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmFrame
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmGlue

public section

namespace CFSG.StandardType

namespace CoordOm

open Multiplicative CFSG.Assembly
open CFSG.RankThree.Classical2 (orthDerived)

section Hyp

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

structure GGOmA3Hyp (F : SevOm.Frame Q p A r) (E J : Subgroup (V ≃ₗ[K] V)) : Prop where
  nondeg : (QuadraticMap.polarBilin Q).Nondegenerate
  tsub : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0
  ne_two : p ≠ 2
  le_orthDerived : A ≤ orthDerived Q
  max : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A
  four_le : 4 ≤ r
  moves : FrameMoves F (CoordSpNs.galSigns p (Nat.card K))
  le_A : E ≤ A
  card_E : Nat.card E = p ^ 2
  isComponent : IsComponentOf J (orthDerived Q ⊓ Subgroup.centralizer (E : Set (V ≃ₗ[K] V)))
  centralizer_le : A ⊓ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) ≤ E
  card_dvd : Nat.card J ∣ 40320
  central_pow : ∀ z ∈ J, (∀ g ∈ J, z * g = g * z) → z ^ p = 1 → z = 1

variable {F : SevOm.Frame Q p A r} {E J : Subgroup (V ≃ₗ[K] V)}

theorem GGOmA3Hyp.mem_E_of_mem_centralizer (H : GGOmA3Hyp F E J) {y : V ≃ₗ[K] V} (hyA : y ∈ A)
    (hy : y ∈ Subgroup.centralizer (J : Set (V ≃ₗ[K] V))) : y ∈ E :=
  H.centralizer_le (Subgroup.mem_inf.mpr ⟨hyA, hy⟩)

theorem GGOmA3Hyp.comm_of_mem (H : GGOmA3Hyp F E J) {e g : V ≃ₗ[K] V} (he : e ∈ E)
    (hg : g ∈ J) : g * e = e * g :=
  (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (H.isComponent.1 hg)).2 e he).symm

theorem GGOmA3Hyp.le_centralizer (H : GGOmA3Hyp F E J) :
    E ≤ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) := fun e he =>
  Subgroup.mem_centralizer_iff.mpr fun g hg => H.comm_of_mem he hg

end Hyp

end CoordOm

end CFSG.StandardType
