module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaSignalizer
public import CFSG.GroupTheory.SteinbergBSSolvableSignalizer

public section

namespace CFSG.RankThree.Coprime

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThreeEvenClassification.Helpers
open scoped Pointwise

theorem theta_centralizer_full_actor_signalizer {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (A : Subgroup X) (hA : IsElementaryAbelian p A)
    (_hAcard : p ^ 2 ≤ Nat.card A)
    (hmixed : ∀ c ∈ A, c ≠ 1 → ∀ d ∈ A, d ≠ 1 →
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({d} : Set X)) ⊓
          centralizer ({c} : Set X), A⁆ ≤
        inSubgroup (aschbacherSolvableCore p) (centralizer ({c} : Set X))) :
    let R : X → Subgroup X := fun a =>
      inSubgroup (aschbacherSolvableCore p) (centralizer ({a} : Set X))
    let U : Subgroup X := inSubgroup (aschbacherSolvableCore p) (centralizer (A : Set X))
    let γ : X → Subgroup X := fun a => ⁅R a, A⁆ ⊔ U
    (∀ a ∈ A, a ≠ 1 →
      ((γ a : Subgroup X) : Set X) = ((⁅R a, A⁆ : Subgroup X) : Set X) * (U : Set X)) ∧
      CFSG.Open.IsSolvableSignalizerFunctor p A γ ∧
      ∀ a ∈ A, a ≠ 1 → γ a ⊓ centralizer (A : Set X) = U := by
  intro R U γ
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : IsMulCommutative A := hA.toIsMulCommutative
  have hpA : IsPGroup p A := IsElementaryAbelian.isPGroup p A
  have hR : ∀ a, R a = thetaCoreOf p (centralizer ({a} : Set X)) := fun a =>
    inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp _
  have hU : U = thetaActorFixedCore p A := inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp _
  have hγ : γ = thetaActorSignalizer p A := by
    funext a
    change ⁅R a, A⁆ ⊔ U = _
    rw [hR, hU]
    rfl
  refine ⟨fun a ha _ => ?_, ?_, fun a ha _ => ?_⟩
  · change ((⁅R a, A⁆ ⊔ U : Subgroup X) : Set X) = _
    rw [hR, hU]
    exact coe_mul_of_right_le_normalizer_left _ _
      (thetaActorFixedCore_normalizes_commutator p hp A a ha)
  · rw [hγ]
    refine thetaActorSignalizer_isSolvableSignalizerFunctor p hp A hcomm hpA ?_
    intro first hfirst hfirst1 second hsecond hsecond1
    have h := hmixed second hsecond hsecond1 first hfirst hfirst1
    rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
      inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp, inf_comm] at h
    exact h
  · rw [hγ, hU]
    exact thetaActorSignalizer_fixed_eq_core p hp A hcomm a ha


theorem theta_centralizer_full_actor_signalizer_datum {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (A : Subgroup X) (hA : IsElementaryAbelian p A)
    (hAcard : p ^ 2 ≤ Nat.card A)
    (hmixed : ∀ c ∈ A, c ≠ 1 → ∀ d ∈ A, d ≠ 1 →
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({d} : Set X)) ⊓
          centralizer ({c} : Set X), A⁆ ≤
        inSubgroup (aschbacherSolvableCore p) (centralizer ({c} : Set X))) :
    CFSG.GroupTheory.SteinbergBS.IsSolvableSignalizerDatum p A X
      ((MulAut.conj : X →* MulAut X).comp A.subtype)
      (fun a : A => ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({(a : X)} : Set X)), A⁆ ⊔
        inSubgroup (aschbacherSolvableCore p) (centralizer (A : Set X))) := by
  obtain ⟨-, hγ, -⟩ := theta_centralizer_full_actor_signalizer hp A hA hAcard hmixed
  have hne : ∀ a : A, a ≠ 1 → (a : X) ≠ 1 := fun a ha h => ha (Subtype.ext h)
  refine
    { prime := hp
      finite_actor := inferInstance
      elementary := hA
      card_actor := hAcard
      finite := inferInstance
      invariant := fun a ha b => hγ.invariant a a.2 (hne a ha) b b.2
      solvable := fun a ha => hγ.solvable a a.2 (hne a ha)
      coprime := fun a ha => hγ.coprime a a.2 (hne a ha)
      le_fixed := fun a ha g hg => ?_
      balance := fun a b ha hb g hg hgb => ?_ }
  · have hc := mem_centralizer_iff.mp (hγ.le_centralizer a a.2 (hne a ha) hg) a rfl
    change (a : X) * g * (a : X)⁻¹ = g
    rw [hc, mul_inv_cancel_right]
  · refine hγ.balance a a.2 (hne a ha) b b.2 (hne b hb) ⟨hg, ?_⟩
    show g ∈ centralizer ({(b : X)} : Set X)
    rw [mem_centralizer_iff]
    rintro _ rfl
    change (b : X) * g * (b : X)⁻¹ = g at hgb
    calc (b : X) * g = (b : X) * g * (b : X)⁻¹ * b := by group
      _ = g * b := by rw [hgb]

end CFSG.RankThree.Coprime
