module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

namespace FiveTransitive.SylowKernelImagePrimeFree

theorem prime_not_dvd_map_card
    {p : ℕ} [Fact p.Prime]
    {H N A : Type*} [Group H] [Finite H] [Group N] [Finite N] [Group A]
    (S : Sylow p H) (K : Subgroup N)
    (i : K →* H) (hi : Function.Injective i) (hS : (S : Subgroup H) ≤ i.range)
    (f : N →* A) (hkill : ∀ x : K, i x ∈ S → f x.val = 1) :
    ¬ p ∣ Nat.card (K.map f) := by
  let T : Sylow p K := S.comapOfInjective i hi hS
  let phi : K →* A := f.comp K.subtype
  have hker : (T : Subgroup K) ≤ phi.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact hkill x hx
  have hdiv : phi.ker.index ∣ (T : Subgroup K).index := Subgroup.index_dvd_of_le hker
  rw [Subgroup.index_ker] at hdiv
  have hrange : phi.range = K.map f := by
    change (f.comp K.subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange] at hdiv
  intro hp
  exact T.not_dvd_index (hp.trans hdiv)

end FiveTransitive.SylowKernelImagePrimeFree

end CFSG
