module

public import CFSG.Quasithin.EmptyFaithful.ModHGen
public import CFSG.Quasithin.EmptyFaithful.SBd13El

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.R3c14

variable {X : Type} [Group X] [Finite X]

theorem not_elConfig_of_center
    (hpt : ∀ (T : Sylow 2 X) (α : MulAut X), (∀ t ∈ (T : Subgroup X), α t = t) →
      ∃ z : (T : Subgroup X), z ∈ Subgroup.center (T : Subgroup X) ∧
        ∀ g : X, α g = (z : X) * g * (z : X)⁻¹)
    (hcs : CenterSmall X) : ¬ ElConfig X := by
  rintro ⟨T, V, H, ζ, hT, hd⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT
  let P : Sylow 2 X := hp.toSylow hi
  obtain ⟨z, hzc, hz⟩ := hpt P ζ hd.fixT
  obtain ⟨v₀, hv₀V, hv₀1, hv₀T⟩ := SBd13.exists_fixed_ne_one hp hd.TV hd.V4
  have hzT : (z : X) ∈ T := z.2
  have hzcomm : ∀ t ∈ T, (z : X) * t = t * z := by
    intro t ht
    have := Subgroup.mem_center_iff.1 hzc ⟨t, ht⟩
    exact congrArg Subtype.val this.symm
  rcases hcs T hT v₀ z (hd.VT hv₀V) hzT hv₀T hzcomm with h | h | h
  · exact hv₀1 h
  · apply hd.ne
    ext g
    rw [hz g, h]
    simp
  · refine hv₀1 (hd.fix v₀ hv₀V fun k hk => ?_)
    have h1 := hd.fixH k hk
    rw [hz k, ← h] at h1
    calc k * v₀ = (v₀ * k * v₀⁻¹) * v₀ := by rw [h1]
      _ = v₀ * k := by group

end CFSG.Quasithin.ModH
