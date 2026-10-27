module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingModule
public import CFSG.RankThree.GroupTheory.SteinbergCDCentralPrimeActorField

public section

namespace CFSG.RankThree.PartOne.FiveAction.Red

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.Lifting36

theorem four_le_finrank {q : ℕ} [Fact q.Prime] (hq5 : q % 5 = 2 ∨ q % 5 = 3)
    {Γ : Type*} [Group Γ] [Finite Γ] {M : Type*} [AddCommGroup M] [Module (ZMod q) M] [Finite M]
    (σ : Representation (ZMod q) Γ M) {U : Subrepresentation σ} (hU : IsAtom U) {n : Γ}
    (hn : n ∈ Subgroup.center Γ) (hnord : orderOf n = 5) (hnu : ∃ u ∈ U, σ n u ≠ u) :
    4 ≤ Module.finrank (ZMod q) U.toSubmodule := by
  have hq : q.Prime := Fact.out
  have hρ : U.toRepresentation.IsIrreducible := isIrreducible_of_isAtom σ hU
  have : Nontrivial U.toSubmodule := nontrivial_of_isIrreducible hρ
  have : Finite U.toSubmodule := Subtype.finite
  have : Module.Finite (ZMod q) U.toSubmodule := Module.Finite.of_finite
  let ρu : Γ →* LinearMap.GeneralLinearGroup (ZMod q) U.toSubmodule :=
    U.toRepresentation.toHomUnits
  have hT : ρu n ≠ 1 := by
    intro h
    obtain ⟨u, hu, hnu'⟩ := hnu
    apply hnu'
    have h1 : (ρu n : Module.End (ZMod q) U.toSubmodule) = 1 := by rw [h]; rfl
    have h2 := congrArg (fun f : Module.End (ZMod q) U.toSubmodule => (f ⟨u, hu⟩ : M)) h1
    exact h2
  obtain ⟨E, hE⟩ : ∃ E : Subalgebra (ZMod q) (Module.End (ZMod q) U.toSubmodule),
      E = Algebra.adjoin (ZMod q) {((ρu n : LinearMap.GeneralLinearGroup (ZMod q) U.toSubmodule) :
        Module.End (ZMod q) U.toSubmodule)} := ⟨_, rfl⟩
  obtain ⟨hEf, e, -, -, hrest, he4⟩ := central_prime_actor_scalar_field_degree (p := 5) (q := q)
    (by norm_num) hq hn hnord ρu (fun W hW => eq_bot_or_eq_top_of_isIrreducible hρ W hW) hT E hE
  let _ : Field E := hEf.toField
  let _ : Module E U.toSubmodule := Module.compHom U.toSubmodule
    (E.val : E →+* Module.End (ZMod q) U.toSubmodule)
  obtain ⟨-, -, hfix⟩ := hrest
  obtain ⟨W, hWset, hWdim⟩ := hfix 1
  have h4 : e = 4 := he4 rfl hq5
  have hker : LinearMap.ker ((ρu 1 : LinearMap.GeneralLinearGroup (ZMod q) U.toSubmodule) -
      1 : Module.End (ZMod q) U.toSubmodule) = ⊤ := by
    rw [map_one, Units.val_one, sub_self, LinearMap.ker_zero]
  have hdimV : Module.finrank (ZMod q) ↥(LinearMap.ker ((ρu 1 :
      LinearMap.GeneralLinearGroup (ZMod q) U.toSubmodule) - 1 :
      Module.End (ZMod q) U.toSubmodule)) = Module.finrank (ZMod q) U.toSubmodule := by
    have h6 := Module.natCard_eq_pow_finrank (K := ZMod q) (V := ↥(LinearMap.ker ((ρu 1 :
      LinearMap.GeneralLinearGroup (ZMod q) U.toSubmodule) - 1 :
      Module.End (ZMod q) U.toSubmodule)))
    have h7 := Module.natCard_eq_pow_finrank (K := ZMod q) (V := U.toSubmodule)
    rw [Nat.card_zmod] at h6 h7
    have h8 : Nat.card ↥(LinearMap.ker ((ρu 1 :
        LinearMap.GeneralLinearGroup (ZMod q) U.toSubmodule) - 1 :
        Module.End (ZMod q) U.toSubmodule)) = Nat.card U.toSubmodule := by
      rw [hker]
      exact Nat.card_congr (Equiv.subtypeUnivEquiv fun x => Submodule.mem_top)
    exact Nat.pow_right_injective hq.two_le (h6.symm.trans (h8.trans h7))
  rw [hdimV, h4] at hWdim
  obtain ⟨v, hv⟩ := exists_ne (0 : U.toSubmodule)
  have hvW : v ∈ W := by
    have : v ∈ (W : Set U.toSubmodule) := by
      rw [hWset]
      show (ρu 1 : Module.End (ZMod q) U.toSubmodule) v = v
      rw [map_one, Units.val_one]
      rfl
    exact this
  have : Module.Finite E U.toSubmodule := Module.Finite.of_finite
  have hW1 : 1 ≤ Module.finrank E W := Submodule.one_le_finrank_iff.mpr (fun h => by
    rw [h, Submodule.mem_bot] at hvW
    exact hv hvW)
  rw [hWdim]
  omega

end CFSG.RankThree.PartOne.FiveAction.Red
