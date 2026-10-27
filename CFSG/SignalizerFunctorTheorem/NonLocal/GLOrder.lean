module

public import CFSG.SignalizerFunctorTheorem.NonLocal.ModuleOfV
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

open scoped IsMulCommutative

namespace CFSG.SignalizerFunctorTheorem.NonLocal

theorem card_dvd_of_faithful {X : Type*} [Group X] (C : Subgroup X) [Finite C]
    (V : Subgroup X) [Finite V] [IsMulCommutative V] {s m : ℕ} (hs : s.Prime)
    (hexp : ∀ v ∈ V, v ^ s = 1) (hcard : Nat.card V = s ^ m)
    (hnorm : ∀ c ∈ C, ∀ v ∈ V, c * v * c⁻¹ ∈ V)
    (hfaith : ∀ c ∈ C, (∀ v ∈ V, c * v * c⁻¹ = v) → c = 1) :
    Nat.card C ∣ ∏ i : Fin m, (s ^ m - s ^ (i : ℕ)) := by
  classical
  have : Fact s.Prime := ⟨hs⟩
  obtain ⟨m', ρ, hcard', hρ1⟩ := exists_rep_of_elementary_abelian C.subtype V hs hexp
    (fun c v hv => hnorm c c.2 v hv) (ZMod s)
  have hmm : m' = m := by
    have : s ^ m' = s ^ m := by rw [← hcard', hcard]
    exact Nat.pow_right_injective hs.two_le this
  subst hmm
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    exact Subtype.ext (hfaith c c.2 (hρ1 c hc))
  let ρu : C →* (Module.End (ZMod s) (Fin m' → ZMod s))ˣ := ρ.toHomUnits
  have hρu : Function.Injective ρu := by
    intro a b hab
    apply hρinj
    exact congrArg Units.val hab
  let e : GL (Fin m') (ZMod s) ≃* (Module.End (ZMod s) (Fin m' → ZMod s))ˣ :=
    Units.mapEquiv (Matrix.toLinAlgEquiv' (R := ZMod s) (n := Fin m')).toMulEquiv
  have h1 : Nat.card C ∣ Nat.card (Module.End (ZMod s) (Fin m' → ZMod s))ˣ :=
    Subgroup.card_dvd_of_injective ρu hρu
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field] at h1
  simpa [ZMod.card] using h1

end CFSG.SignalizerFunctorTheorem.NonLocal
