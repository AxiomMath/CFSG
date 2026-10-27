
module

public import CFSG.Sporadic.Schreier.J4SAutBase1

public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SProfile
public meta import CFSG.Sporadic.Schreier.J4SProfile
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.J4.Local
public import CFSG.Sporadic.Schreier.J4SFrattini

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.SmallF2
open CFSG.OrderReductions.FrattiniAutomorphisms

section Generic

variable {P : Type*} [Group P] {f : P →* Multiplicative (Fin 5 → ZMod 2)}

variable (hf : Function.Surjective f) (hker : f.ker = frattini P)
include hf hker

omit hf hker

end Generic

theorem fiberCount_fS0
    (a : Multiplicative (Fin 5 → ZMod 2)) (d : ℕ) :
    fiberCount fS0 a d = hcount a d := rfl

theorem huniq_S0 :
    ∀ a ∈ ({5, 6, 7, 8, 17} : Set ℕ), ∀ w : Fin 5 → ZMod 2,
    (∀ j : Fin 5, fiberCount fS0 (Multiplicative.ofAdd w) (2 ^ j.val) =
      fiberCount fS0 (Multiplicative.ofAdd (toVecD 5 a)) (2 ^ j.val)) → w = toVecD 5 a :=
  fun a ha w hw => R3E_J4_Sylow_two_Frattini_basis_unique_order_profiles.2.2.2.2.2.2.1 a ha w
    (funext fun j => by rw [hprof, hprof, ← fiberCount_fS0, ← fiberCount_fS0]; exact hw j)

theorem aut_S0_trivial
    (σ : MulAut S0) (s : S0) :
    QuotientGroup.mk' (frattini S0) (σ s) = QuotientGroup.mk' (frattini S0) s := by
  have h := aut_trivial_of_profiles fS0_surjective ker_fS0 huniq_S0
  exact h σ s

theorem isPGroup_aut_S0 :
    IsPGroup 2 (MulAut S0) := by
  have h := isPGroup_aut_of_profiles fS0_surjective ker_fS0 isPGroup_S0 huniq_S0
  exact h

theorem nonempty_equiv_S0
    (S : Sylow 2 J) : Nonempty (S0 ≃* S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P0, hP0⟩ := R3E_J4_five_generator_Sylow_two_subgroup.2.2.2.2.2.2.2.2.2.1
  exact ⟨(MulEquiv.subgroupCongr hP0).symm.trans (Sylow.equiv P0 S)⟩

theorem R3E_J4_Sylow_two_automorphism_group_is_two_group
    (S : Sylow 2 J) :
    (∀ (σ : MulAut S) (s : S),
      QuotientGroup.mk' (frattini S) (σ s) = QuotientGroup.mk' (frattini S) s) ∧
      IsPGroup 2 (MulAut S) := by
  obtain ⟨e⟩ := nonempty_equiv_S0 S
  have h1 := @aut_trivial_of_equiv S0 (Subgroup.toGroup S0) S (Subgroup.toGroup (S : Subgroup J))
    e aut_S0_trivial
  have h2 := @isPGroup_aut_of_equiv S0 (Subgroup.toGroup S0) S (Subgroup.toGroup (S : Subgroup J))
    e isPGroup_aut_S0
  exact ⟨h1, h2⟩

end CFSG.Sporadic.J4Schreier
