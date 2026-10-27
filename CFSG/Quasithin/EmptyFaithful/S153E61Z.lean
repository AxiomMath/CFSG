module

public import CFSG.Quasithin.EmptyFaithful.S153E61AZ
public import CFSG.Quasithin.EmptyFaithful.S153E61BZ
public import CFSG.Quasithin.EmptyFaithful.S153E61CZ
public import CFSG.Quasithin.EmptyFaithful.S153E61DZ

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

section Assembly61

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem lemma_61two (cx : Ctx15350 T Mc M V₁ V₂ t) (hD : S153E61.Data61 cx)
    (c : Chain15359 cx N₁ N₂ g s y t₁) {DM JM : Subgroup G} {v z : G} (hN8 : N8Data153 cx DM JM v z) :
    ∀ x ∈ oTwoUpper Mc, orderOf x = 2 →
      (∃ g', g' * z * g'⁻¹ = x) ∨ (∃ g', g' * v * g'⁻¹ = x) := by
  intro x hxK hord
  have hx2 : x * x = 1 := by
    rw [← pow_two, ← hord]
    exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hord
  have hfuse := fuse_V cx hN8.z_gen hN8.v_gen hN8.v_ne
  have hU : ∀ u ∈ UH153 T M V₁ Mc, u * u = 1 → u ≠ 1 →
      (∃ g', g' * z * g'⁻¹ = u) ∨ (∃ g', g' * v * g'⁻¹ = u) := by
    intro u hu hu2 hu1
    obtain ⟨h, -, hw⟩ := inv_U_conj_V cx hD c u hu hu2
    have hw1 : h * u * h⁻¹ ≠ 1 := fun e => hu1 (by simpa using e)
    rcases hfuse _ hw hw1 with ⟨m, -, e⟩ | ⟨m, -, e⟩
    · left
      refine ⟨h⁻¹ * m, ?_⟩
      calc h⁻¹ * m * z * (h⁻¹ * m)⁻¹ = h⁻¹ * (m * z * m⁻¹) * h := by group
        _ = u := by rw [e]; group
    · right
      refine ⟨h⁻¹ * m, ?_⟩
      calc h⁻¹ * m * v * (h⁻¹ * m)⁻¹ = h⁻¹ * (m * v * m⁻¹) * h := by group
        _ = u := by rw [e]; group
  by_cases hxU : x ∈ UH153 T M V₁ Mc
  · exact hU x hxU hx2 hx1
  · obtain ⟨k, -, a, ha, u, hu, hcomm, hkx⟩ := inv_K_not_U cx hD c x hxK hxU hx2
    have haP : a ∈ Pgp153 T M V₁ Mc g := by
      have := c.h54.two_center ha
      exact this.1
    have huP : u ∈ Pgp153 T M V₁ Mc g :=
      S153E55.centralizer_le_P c.h54.one cx
        ⟨(le_sup_right : UH153 T M V₁ Mc ≤ Y153 Mc M ⊔ UH153 T M V₁ Mc) hu,
          Subgroup.mem_centralizer_iff.mpr fun w hw => (hcomm w hw).symm⟩
    have hxP : a * u ∈ Pgp153 T M V₁ Mc g := (Pgp153 T M V₁ Mc g).mul_mem haP huP
    have hx'2 : (a * u) * (a * u) = 1 := by
      rw [← hkx]
      have : k * x * k⁻¹ * (k * x * k⁻¹) = k * (x * x) * k⁻¹ := by group
      rw [this, hx2]
      group
    obtain ⟨γ, -, hγU⟩ := inv_P_conj_U_of cx hD c (Pi_elemAbelian cx c) (inv_P_mem_Pi cx c) (a * u) hxP hx'2
    have hu'2 : (γ * (a * u) * γ⁻¹) * (γ * (a * u) * γ⁻¹) = 1 := by
      have : γ * (a * u) * γ⁻¹ * (γ * (a * u) * γ⁻¹) = γ * ((a * u) * (a * u)) * γ⁻¹ := by group
      rw [this, hx'2]
      group
    have hu'1 : γ * (a * u) * γ⁻¹ ≠ 1 := by
      intro e
      apply hx1
      have h1 : a * u = 1 := by simpa using e
      rw [← hkx] at h1
      simpa using h1
    rcases hU _ hγU hu'2 hu'1 with ⟨g', e⟩ | ⟨g', e⟩
    · left
      refine ⟨k⁻¹ * γ⁻¹ * g', ?_⟩
      have e' : γ * (k * x * k⁻¹) * γ⁻¹ = g' * z * g'⁻¹ := by rw [hkx]; exact e.symm
      calc k⁻¹ * γ⁻¹ * g' * z * (k⁻¹ * γ⁻¹ * g')⁻¹
          = k⁻¹ * γ⁻¹ * (g' * z * g'⁻¹) * γ * k := by group
        _ = x := by rw [← e']; group
    · right
      refine ⟨k⁻¹ * γ⁻¹ * g', ?_⟩
      have e' : γ * (k * x * k⁻¹) * γ⁻¹ = g' * v * g'⁻¹ := by rw [hkx]; exact e.symm
      calc k⁻¹ * γ⁻¹ * g' * v * (k⁻¹ * γ⁻¹ * g')⁻¹
          = k⁻¹ * γ⁻¹ * (g' * v * g'⁻¹) * γ * k := by group
        _ = x := by rw [← e']; group

end Assembly61

end S153E

end CFSG.Quasithin
