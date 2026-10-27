module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.RankThree.GroupTheory.SteinbergCDBinaryPrimeActionDegree

public section

namespace CFSG.RankThree.PartOne.Quotient36

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
open scoped IsMulCommutative

theorem binary_action_data {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {A S : Type*} [Group A] [Group S]
    [Finite A] [Finite S] [IsElementaryAbelian p A] [MulDistribMulAction A S] (hS : IsPGroup 2 S)
    (hirr : NontrivIrredFrattini A S) :
    ∃ d : ℕ, Nat.card (S ⧸ frattini S) = 2 ^ d ∧
      (d ≤ 4 → (p = 7 ∧ d = 3) ∨ (p = 5 ∧ d = 4)) ∧ (Even d → d ≤ 6 → p = 5 ∧ d = 4) ∧
      IsCyclic (MulDistribMulAction.toMulAut A S).range ∧
      Nat.card (MulDistribMulAction.toMulAut A S).range = p ∧
      (∀ a : A, (∀ s : S, a • s = s) ↔
        (letI := frattiniQuotientAction A S; ∀ v : S ⧸ frattini S, a • v = v)) ∧
      (Nat.card A = p ^ 2 → Nat.card (MulDistribMulAction.toMulAut A S).ker = p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup 2 S) := ⟨hS⟩
  obtain ⟨hnt, hirr'⟩ := hirr
  let ρ : A →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive (S ⧸ frattini S)) :=
    (frattiniRep (E := A) (X := S) 2).toHomUnits
  have hρ : ∀ a : A, (ρ a : Module.End (ZMod 2) (Additive (S ⧸ frattini S))) =
      frattiniRep (E := A) (X := S) 2 a := fun a => rfl
  have : Nontrivial (Additive (S ⧸ frattini S)) := by
    obtain ⟨a, v, hav⟩ := hnt
    exact ⟨⟨Additive.ofMul v, Additive.ofMul (letI := frattiniQuotientAction A S; a • v),
      fun h => hav (Additive.ofMul.injective h).symm⟩⟩
  have : FiniteDimensional (ZMod 2) (Additive (S ⧸ frattini S)) := Module.Finite.of_finite
  have hirrρ : ∀ W : Submodule (ZMod 2) (Additive (S ⧸ frattini S)),
      (∀ a : A, ∀ v ∈ W, (ρ a : Additive (S ⧸ frattini S) →ₗ[ZMod 2] _) v ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hinv := toSubgroup_invariant (E := A) (X := S) 2 W fun e w hw => by
      have := hW e w hw
      rwa [hρ] at this
    rcases hirr' _ hinv with h0 | h1
    · exact Or.inl ((toSubgroup_eq_bot_iff 2 W).mp h0)
    · exact Or.inr ((toSubgroup_eq_top_iff 2 W).mp h1)
  have hρtriv : ∀ a : A, ρ a = 1 ↔ (letI := frattiniQuotientAction A S;
      ∀ v : S ⧸ frattini S, a • v = v) := by
    intro a
    constructor
    · intro h v
      have h1 : frattiniRep (E := A) (X := S) 2 a = 1 := by
        rw [← hρ, h]
        rfl
      have h2 := congrArg (fun f : Module.End (ZMod 2) (Additive (S ⧸ frattini S)) =>
        f (Additive.ofMul v)) h1
      simp only [frattiniRep_apply, Module.End.one_apply] at h2
      exact Additive.ofMul.injective h2
    · intro h
      apply Units.ext
      refine LinearMap.ext fun w => ?_
      obtain ⟨v, rfl⟩ : ∃ v : S ⧸ frattini S, Additive.ofMul v = w := ⟨Additive.toMul w, rfl⟩
      rw [Units.val_one]
      change frattiniRep (E := A) (X := S) 2 a (Additive.ofMul v) = Additive.ofMul v
      rw [frattiniRep_apply]
      exact congrArg Additive.ofMul (h v)
  have hnt' : ρ.range ≠ ⊥ := by
    intro hbot
    obtain ⟨a, v, hav⟩ := hnt
    apply hav
    have : ρ a = 1 := by
      have : ρ a ∈ ρ.range := ⟨a, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    exact (hρtriv a).mp this v
  obtain ⟨hcyc, hcard, -, h4, h6⟩ := binary_irreducible_prime_action_degree hp ρ hirrρ hnt'
  have hodd : ∀ a : A, ¬ 2 ∣ orderOf a := by
    intro a h2
    have h3 : a ^ p = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p A) a
    have h4 : 2 ∣ p := h2.trans (orderOf_dvd_of_pow_eq_one h3)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h4
    omega
  have hker : ∀ a : A, (∀ s : S, a • s = s) ↔ (letI := frattiniQuotientAction A S;
      ∀ v : S ⧸ frattini S, a • v = v) := by
    intro a
    constructor
    · intro h v
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective v
      exact congrArg (fun y : S => (y : S ⧸ frattini S)) (h s)
    · intro h
      exact smul_eq_of_smul_mk_eq hS a (hodd a) (fun x => h (x : S ⧸ frattini S))
  have hkereq : (MulDistribMulAction.toMulAut A S).ker = ρ.ker := by
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hρtriv, ← hker, MulEquiv.ext_iff]
    simp [MulDistribMulAction.toMulAut_apply]
  have hcardker : Nat.card (MulDistribMulAction.toMulAut A S).range = p := by
    have h1 := Subgroup.card_ker_mul_card_range (MulDistribMulAction.toMulAut A S)
    have h2 := Subgroup.card_ker_mul_card_range ρ
    rw [hkereq] at h1
    rw [← h2] at h1
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h1).trans hcard
  refine ⟨Module.finrank (ZMod 2) (Additive (S ⧸ frattini S)), ?_, fun h => h4 hp3 h,
    fun he h6' => h6 hp3 he h6', ?_, hcardker, hker, ?_⟩
  · have : Nat.card (Additive (S ⧸ frattini S)) =
        2 ^ Module.finrank (ZMod 2) (Additive (S ⧸ frattini S)) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact this
  · have e : (MulDistribMulAction.toMulAut A S).range ≃* ρ.range :=
      (QuotientGroup.quotientKerEquivRange (MulDistribMulAction.toMulAut A S)).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hkereq).trans (QuotientGroup.quotientKerEquivRange ρ))
    exact (MulEquiv.isCyclic e).mpr hcyc
  · intro hAcard
    have h1 := Subgroup.card_ker_mul_card_range (MulDistribMulAction.toMulAut A S)
    rw [hcardker, hAcard] at h1
    have : Nat.card (MulDistribMulAction.toMulAut A S).ker * p = p * p := by
      rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos this

end CFSG.RankThree.PartOne.Quotient36
