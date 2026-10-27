module

public import CFSG.Quasithin.Background.FLc2Lift
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.FLc

open scoped commutatorElement

variable {G : Type} [Group G]

theorem ud_decomp [Finite G] {L SL U Z₂ : Subgroup G} (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hU2 : ∀ a ∈ U, a ^ 2 = 1)
    (hodd : Odd (SL.relIndex L)) (hZU : Z₂ ≤ U) (hSL : ∀ s ∈ SL, ∀ z ∈ Z₂, s * z * s⁻¹ = z) :
    ∀ z ∈ Z₂, ∃ u ∈ ⁅U, L⁆, ∀ h ∈ L, h * (z * u) * h⁻¹ = z * u := by
  intro z hz
  refine exists_fixed_mul (H := L) (SL := SL) (U := U) (A := ⁅U, L⁆) hLU hUc hU2 hodd (hZU hz) ?_
    (fun s hs => hSL s hs z hz)
  intro h hh
  have h1 : ⁅z, h⁆ ∈ ⁅U, L⁆ := Subgroup.commutator_mem_commutator (hZU hz) hh
  have h2 : h * z * h⁻¹ * z⁻¹ = ⁅z, h⁆⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [h2]
  exact (⁅U, L⁆).inv_mem h1

@[expose] def projZU (Z₂ L U : Subgroup G) : Subgroup G :=
  (Z₂ ⊔ (U ⊓ Subgroup.centralizer (L : Set G))) ⊓ ⁅U, L⁆

theorem centralizer_zU_eq {L U Z₂ : Subgroup G}
    (hd : ∀ z ∈ Z₂, ∃ u ∈ ⁅U, L⁆, ∀ h ∈ L, h * (z * u) * h⁻¹ = z * u) (hZU : Z₂ ≤ U)
    (hUL : ⁅U, L⁆ ≤ U) (l : G) (hl : l ∈ L) :
    l ∈ Subgroup.centralizer (Z₂ : Set G) ↔ l ∈ Subgroup.centralizer (projZU Z₂ L U : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hsup : Z₂ ⊔ (U ⊓ Subgroup.centralizer (L : Set G)) ≤ Subgroup.centralizer ({l} : Set G) := by
      refine sup_le (fun z hz => ?_) (fun c hc => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.1 h z hz
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have := Subgroup.mem_centralizer_iff.1 hc.2 l hl
        exact this.symm
    have := hsup hy.1
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨u, hu, hfix⟩ := hd z hz
    have hc : z * u ∈ U ⊓ Subgroup.centralizer (L : Set G) := by
      refine ⟨U.mul_mem (hZU hz) (hUL hu), Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
      have := hfix k hk
      calc k * (z * u) = (k * (z * u) * k⁻¹) * k := by group
        _ = (z * u) * k := by rw [this]
    have hzu : u ∈ projZU Z₂ L U := by
      refine ⟨?_, hu⟩
      have : u = z⁻¹ * (z * u) := by group
      rw [this]
      exact Subgroup.mul_mem_sup (Z₂.inv_mem hz) hc
    have h1 : u * l = l * u := Subgroup.mem_centralizer_iff.1 h u hzu
    have h2 : (z * u) * l = l * (z * u) := (Subgroup.mem_centralizer_iff.1 hc.2 l hl).symm
    have h3 : z * l = l * z := by
      have e : z = (z * u) * u⁻¹ := by group
      have hu1 : u⁻¹ * l = l * u⁻¹ := by
        calc u⁻¹ * l = u⁻¹ * (l * u) * u⁻¹ := by group
          _ = u⁻¹ * (u * l) * u⁻¹ := by rw [h1]
          _ = l * u⁻¹ := by group
      calc z * l = ((z * u) * u⁻¹) * l := by rw [← e]
        _ = (z * u) * (u⁻¹ * l) := by group
        _ = (z * u) * (l * u⁻¹) := by rw [hu1]
        _ = ((z * u) * l) * u⁻¹ := by group
        _ = (l * (z * u)) * u⁻¹ := by rw [h2]
        _ = l * ((z * u) * u⁻¹) := by group
        _ = l * z := by rw [← e]
    exact h3

end CFSG.Quasithin.FLc
