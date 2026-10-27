module

import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem omq_exists_pow_of_units_hom {F k : Type} [Field F] [Finite F] [Field k] (ι : F →+* k)
    (θ : Fˣ →* k) : ∃ c : ℕ, c < Nat.card Fˣ ∧ ∀ a : Fˣ, θ a = ι (a : F) ^ c := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have horder_g : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hinj : Function.Injective ι := RingHom.injective ι
  let φ : Fˣ →* k := ι.toMonoidHom.comp (Units.coeHom F)
  have hφ : Function.Injective φ := fun a b hab => Units.ext (hinj hab)
  have horder_ig : orderOf (ι (g : F)) = Nat.card Fˣ := by
    have h := orderOf_injective φ hφ g
    rw [horder_g] at h
    exact h
  have hprim : IsPrimitiveRoot (ι (g : F)) (Nat.card Fˣ) :=
    { pow_eq_one := by rw [← horder_ig]; exact pow_orderOf_eq_one _
      dvd_of_pow_eq_one := fun l hl => by
        rw [← horder_ig]
        exact orderOf_dvd_iff_pow_eq_one.mpr hl }
  have hzN : (θ g) ^ Nat.card Fˣ = 1 := by
    rw [← map_pow, ← horder_g, pow_orderOf_eq_one, map_one]
  obtain ⟨c, hc, hcz⟩ := hprim.eq_pow_of_pow_eq_one hzN
  refine ⟨c, hc, fun a => ?_⟩
  obtain ⟨j, rfl⟩ :=
    (Submonoid.mem_powers_iff a g).mp ((mem_powers_iff_mem_zpowers).mpr (hg a))
  have hcoe : ((g ^ j : Fˣ) : F) = (g : F) ^ j := map_pow (Units.coeHom F) g j
  calc θ (g ^ j) = (θ g) ^ j := map_pow θ g j
    _ = ((ι (g : F)) ^ c) ^ j := by rw [hcz]
    _ = (ι (g : F)) ^ (c * j) := by rw [pow_mul]
    _ = (ι (g : F)) ^ (j * c) := by rw [mul_comm c j]
    _ = ((ι (g : F)) ^ j) ^ c := by rw [pow_mul]
    _ = (ι (((g ^ j : Fˣ) : F))) ^ c := by
          congr 1
          rw [hcoe, map_pow]

end CFSG.LocalAnalysis.WeakClosure81
