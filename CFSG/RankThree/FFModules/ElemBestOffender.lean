module

public import CFSG.RankThree.FFModules.Offenders

public section

namespace CFSG.RankThree.FFModules

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def IsElemBestOffender (ρ : Representation (ZMod 2) G W) (A : Subgroup G) : Prop :=
  CFSG.IsElementaryAbelian 2 ↥A ∧ IsBestOffender ρ A

variable {ρ : Representation (ZMod 2) G W} {A : Subgroup G}

theorem IsElemBestOffender.isElementaryAbelian (h : IsElemBestOffender ρ A) :
    CFSG.IsElementaryAbelian 2 ↥A :=
  h.1

theorem IsElemBestOffender.isBestOffender (h : IsElemBestOffender ρ A) : IsBestOffender ρ A :=
  h.2

theorem isBestOffender_bot (ρ : Representation (ZMod 2) G W) : IsBestOffender ρ ⊥ := by
  intro B hB
  rw [le_bot_iff.mp hB]

theorem isElementaryAbelian_bot : CFSG.IsElementaryAbelian 2 ↥(⊥ : Subgroup G) where
  is_comm := ⟨fun _ _ => Subsingleton.elim _ _⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun _ => Subsingleton.elim _ _

theorem isElemBestOffender_bot (ρ : Representation (ZMod 2) G W) : IsElemBestOffender ρ ⊥ :=
  ⟨isElementaryAbelian_bot, isBestOffender_bot ρ⟩

theorem IsElemBestOffender.conj (h : IsElemBestOffender ρ A) (g : G) :
    IsElemBestOffender ρ (A.map (MulAut.conj g).toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.1
  exact ⟨CFSG.IsElementaryAbelian.map (A := A) _, isBestOffender_conj h.2 g⟩

end CFSG.RankThree.FFModules
