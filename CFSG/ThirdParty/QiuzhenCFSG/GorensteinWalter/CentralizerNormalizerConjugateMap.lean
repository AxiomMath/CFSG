module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Conjugating centralizer-invariant subgroups

Centralizer containment in a subgroup normalizer transports along an inner
automorphism, together with the distinguished element and the subgroup.
-/

namespace CFSG.GorensteinWalter

universe u

/-- If `g` conjugates `t` to `s`, then conjugation by `g` carries a subgroup
normalized by `C(t)` to one normalized by `C(s)`. -/
public theorem centralizer_le_normalizer_map_conj_of_eq_conj
    {G : Type u} [Group G] (P : Subgroup G) {t s g : G}
    (hgt : g * t * g⁻¹ = s)
    (hPinv : Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer (P : Set G)) :
    Subgroup.centralizer ({s} : Set G) ≤
      Subgroup.normalizer
        ((P.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  intro c hc
  have hccomm : c * s = s * c :=
    Subgroup.mem_centralizer_singleton_iff.mp hc
  let e : G ≃* G := MulAut.conj g
  let d : G := g⁻¹ * c * g
  have hdt : d * t = t * d := by
    calc
      d * t = g⁻¹ * c * (g * t * g⁻¹) * g := by simp [d]; group
      _ = g⁻¹ * c * s * g := by rw [hgt]
      _ = g⁻¹ * s * c * g := by simp only [mul_assoc, hccomm]
      _ = t * d := by rw [← hgt]; simp [d]; group
  have hdN : d ∈ Subgroup.normalizer (P : Set G) := by
    apply hPinv
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzt : z = t := by simpa using hz
    subst z
    exact hdt.symm
  have hmap : c ∈
      (Subgroup.normalizer (P : Set G)).map e.toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨d, hdN, ?_⟩
    dsimp [e, d]
    group
  rw [Subgroup.map_equiv_normalizer_eq] at hmap
  exact hmap

end CFSG.GorensteinWalter
