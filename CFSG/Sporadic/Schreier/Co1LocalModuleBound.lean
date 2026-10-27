module

public import CFSG.Sporadic.Schreier.Co1LocalModule
public import CFSG.Sporadic.Schreier.Co1LocalEnd

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix WeightProj

theorem z_ne_one :
    ThreeLocal.z ≠ 1 := by
  intro h
  apply zM_mulVec_ne_self (q_ne_zero 0)
  change ((ThreeLocal.z : GL24) : Mat24) *ᵥ q 0 = q 0
  rw [h, Units.val_one, one_mulVec]

theorem elementary_three_local_module_degree_bound :
    (∀ χ : E →* F4ˣ, ∃! f : Fin 6 → ZMod 3, χ = charE f) ∧
    (∀ f b : Fin 6 → ZMod 3, charE f ⟨eProd b, eProd_mem b⟩ = ω ^ (∑ i, f i * b i).val) ∧
    (∀ f, charOrbit f =
      {f' | ∃ x ∈ A, ∀ e ∈ E, charV f' e = charV f (x⁻¹ * e * x)}) ∧
    Set.ncard (Set.range charOrbit) = 4 ∧
    (∀ f, (charOrbit f).ncard = 1 ∨ (charOrbit f).ncard = 24 ∨ (charOrbit f).ncard = 264 ∨
      (charOrbit f).ncard = 440) ∧
    (∀ n ∈ ({1, 24, 264, 440} : Finset ℕ), ∃ f, (charOrbit f).ncard = n) ∧
    (∀ f, (charOrbit f).ncard = 24 ↔ charOrbit f = {f' | ∃ j, f' = γ j ∨ f' = -γ j}) ∧
    (∀ S : Submodule Kbar (Fin 24 → Kbar),
      (∀ x : A, ∀ v ∈ S, ((x : GL24) : Mat24).map (algebraMap (ZMod 2) Kbar) *ᵥ v ∈ S) →
        S = ⊥ ∨ S = ⊤) ∧
    (∀ T : Mat24, (∀ x ∈ A, T * ((x : GL24) : Mat24) = ((x : GL24) : Mat24) * T) →
      T = 0 ∨ T = 1) ∧
    ∀ (n : ℕ) (ρ : A →* GL (Fin n) (ZMod 2)), (∃ e : E, ρ ⟨e, E_le_A e.2⟩ ≠ 1) →
      24 ≤ n ∧ (n = 24 →
        (∀ S : Submodule Kbar (Fin n → Kbar), (∀ x : A, ∀ v ∈ S, rhoK ρ x *ᵥ v ∈ S) →
          S = ⊥ ∨ S = ⊤) ∧
        ∀ χ : E →* Kbarˣ,
          ((∃ j, χ = charK (γ j) ∨ χ = charK (-γ j)) → Module.finrank Kbar (wtChar ρ χ) = 1) ∧
          ((¬ ∃ j, χ = charK (γ j) ∨ χ = charK (-γ j)) →
            Module.finrank Kbar (wtChar ρ χ) = 0)) := by
  have hgen : ∀ (n : ℕ) (ρ : A →* GL (Fin n) (ZMod 2)), (∃ e : E, ρ ⟨e, E_le_A e.2⟩ ≠ 1) →
      24 ≤ n ∧ (n = 24 →
        (∀ S : Submodule Kbar (Fin n → Kbar), (∀ x : A, ∀ v ∈ S, rhoK ρ x *ᵥ v ∈ S) →
          S = ⊥ ∨ S = ⊤) ∧
        ∀ χ : E →* Kbarˣ,
          ((∃ j, χ = charK (γ j) ∨ χ = charK (-γ j)) → Module.finrank Kbar (wtChar ρ χ) = 1) ∧
          ((¬ ∃ j, χ = charK (γ j) ∨ χ = charK (-γ j)) →
            Module.finrank Kbar (wtChar ρ χ) = 0)) := by
    intro n ρ hE
    obtain ⟨h24, h⟩ := degree_bound ρ hE
    refine ⟨h24, fun hn => ⟨(h hn).2, fun χ => ?_⟩⟩
    obtain ⟨f, rfl⟩ := exists_charK_eq χ
    rw [wtChar_charK, (h hn).1 f]
    have hiff : f ∈ orbSet 1 ↔ ∃ j, charK f = charK (γ j) ∨ charK f = charK (-γ j) := by
      have := Set.ext_iff.mp orbSet_one f
      simp only [Finset.mem_coe, Set.mem_ofPred_eq] at this
      rw [this]
      constructor
      · rintro ⟨j, h | h⟩
        · exact ⟨j, Or.inl (by rw [h])⟩
        · exact ⟨j, Or.inr (by rw [h])⟩
      · rintro ⟨j, h | h⟩
        · exact ⟨j, Or.inl (charK_injective h)⟩
        · exact ⟨j, Or.inr (charK_injective h)⟩
    constructor
    · intro hj
      simp only [hiff.mpr hj, ↓reduceIte]
    · intro hj
      simp only [mt hiff.mp hj, ↓reduceIte]
  refine ⟨fun χ => ?_, charE_eProd, fun _ => rfl, charOrbit_facts.1, charOrbit_facts.2.1,
    charOrbit_facts.2.2.1, charOrbit_facts.2.2.2, fun S hS => ?_, fun T hT => end_A hT, hgen⟩
  · obtain ⟨f, rfl⟩ := exists_charE_eq χ
    exact ⟨f, rfl, fun f' h => charE_injective h.symm⟩
  · have hE : ∃ e : E, A.subtype ⟨e, E_le_A e.2⟩ ≠ 1 := by
      refine ⟨⟨a 0, a_mem_E 0⟩, fun h => z_ne_one ?_⟩
      rw [← a_zero]
      exact h
    exact ((hgen 24 A.subtype hE).2 rfl).1 S hS

end CFSG.Sporadic.Co1Schreier
