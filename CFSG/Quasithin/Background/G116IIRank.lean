module

public import CFSG.Quasithin.Background.G10Basic
public import CFSG.Quasithin.Background.G11Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_card_eq_two_pow_of_sq_eq_one [Finite V] (Y : Subgroup (GLV V))
    (h : ∀ y ∈ Y, y * y = 1) : ∃ m : ℕ, Nat.card ↥Y = 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥Y := fun g => ⟨1, by
    apply Subtype.ext
    show (g : GLV V) ^ 2 ^ 1 = 1
    rw [pow_one, pow_two]
    exact h g g.2⟩
  exact hP.exists_card_eq

theorem finrank_le_of_fullTransvections [Finite V] {Y : Subgroup (GLV V)}
    {U : Submodule (ZMod 2) V} {c : V} (hc : c ∈ U) (hc0 : c ≠ 0)
    (hFT : FullTransvections Y U c hc) {m : ℕ} (hY : Nat.card ↥Y = 2 ^ m) :
    Module.finrank (ZMod 2) ↥U ≤ m + 1 := by
  classical
  obtain ⟨-, hFT2⟩ := hFT
  let ev : Module.Dual (ZMod 2) ↥U →ₗ[ZMod 2] ZMod 2 := Module.Dual.eval (ZMod 2) ↥U ⟨c, hc⟩
  have hev : ∀ f, ev f = f ⟨c, hc⟩ := fun f => rfl
  have hrank := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2)
    (V := Module.Dual (ZMod 2) ↥U) (V₂ := ZMod 2) ev
  have hrange : Module.finrank (ZMod 2) ↥(LinearMap.range ev) ≤ 1 :=
    (Submodule.finrank_le _).trans (Module.finrank_self (ZMod 2)).le
  have hdual : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) ↥U) =
      Module.finrank (ZMod 2) ↥U := Subspace.dual_finrank_eq
  have hex : ∀ f : ↥(LinearMap.ker ev), ∃ y ∈ Y, ∀ u : ↥U,
      y (u : V) = (u : V) + (f : Module.Dual (ZMod 2) ↥U) u • c := fun f =>
    hFT2 f.1 (by rw [← hev]; exact f.2)
  choose g hgY hg using hex
  have hinj : Function.Injective fun f : ↥(LinearMap.ker ev) => (⟨g f, hgY f⟩ : ↥Y) := by
    intro f f' h
    have h1 : g f = g f' := congrArg Subtype.val h
    apply Subtype.ext
    apply LinearMap.ext
    intro u
    have h2 := hg f u
    have h3 := hg f' u
    rw [h1] at h2
    have h4 : (f : Module.Dual (ZMod 2) ↥U) u • c = (f' : Module.Dual (ZMod 2) ↥U) u • c :=
      add_left_cancel (h2.symm.trans h3)
    exact smul_left_injective (ZMod 2) hc0 h4
  have hcard : Nat.card ↥(LinearMap.ker ev) ≤ Nat.card ↥Y := Nat.card_le_card_of_injective _ hinj
  have hcardker : Nat.card ↥(LinearMap.ker ev) =
      2 ^ Module.finrank (ZMod 2) ↥(LinearMap.ker ev) := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(LinearMap.ker ev))
    rwa [Nat.card_zmod] at this
  rw [hY, hcardker] at hcard
  have := (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 hcard
  omega

end G11

end CFSG.Quasithin
