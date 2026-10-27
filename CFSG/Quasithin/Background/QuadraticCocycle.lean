module

public import CFSG.Quasithin.Background.JonesParshallBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.JonesParshall

section ClassComparison

variable {Γ V : Type*} [Group Γ] [Finite Γ]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_coboundary_of_not_mem_B1_of_finrank_H1_le_one
    (ρ : Representation (ZMod 2) Γ V)
    (hH1 : Module.finrank (ZMod 2) (H1 ρ) ≤ 1)
    (f d : ↥(Z1 ρ))
    (hf : (f : Γ → V) ∉ B1 ρ) (hd : (d : Γ → V) ∉ B1 ρ) :
    ∃ ℓ : V, (f : Γ → V) = (d : Γ → V) + coboundary ρ ℓ := by
  let P : Submodule (ZMod 2) ↥(Z1 ρ) := (B1 ρ).comap (Z1 ρ).subtype
  let mk : ↥(Z1 ρ) → H1 ρ := fun x => Submodule.Quotient.mk x
  have hf0 : mk f ≠ 0 := by
    intro h0
    change (Submodule.Quotient.mk f : H1 ρ) = 0 at h0
    have hmem : f ∈ P := (Submodule.Quotient.mk_eq_zero P).mp h0
    exact hf (by simpa [P] using hmem)
  have hd0 : mk d ≠ 0 := by
    intro h0
    change (Submodule.Quotient.mk d : H1 ρ) = 0 at h0
    have hmem : d ∈ P := (Submodule.Quotient.mk_eq_zero P).mp h0
    exact hd (by simpa [P] using hmem)
  have hfin : Finite (H1 ρ) := by
    have : Finite (Γ → V) := Pi.finite
    have : Finite ↥(Z1 ρ) := Subtype.finite
    exact Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have : Module.Finite (ZMod 2) (H1 ρ) := Module.Finite.of_finite
  have hpos : 0 < Module.finrank (ZMod 2) (H1 ρ) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨mk f, hf0⟩
  have hdim : Module.finrank (ZMod 2) (H1 ρ) = 1 := le_antisymm hH1 (by omega)
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim hf0 (mk d)
  have hc1 : c = 1 := by
    have hc_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hc_cases c with h0 | h1
    · rw [h0, zero_smul] at hc
      exact absurd hc.symm hd0
    · exact h1
  have hclass : mk f = mk d := by
    rw [← hc, hc1, one_smul]
  have hmem : f - d ∈ P := (Submodule.Quotient.eq P).mp hclass
  have hB : ((f - d : ↥(Z1 ρ)) : Γ → V) ∈ B1 ρ := by
    simpa [P] using hmem
  obtain ⟨ℓ, hℓ⟩ := hB
  refine ⟨ℓ, ?_⟩
  funext x
  have h := congrFun hℓ x
  have h' : (coboundary ρ) ℓ x = (f : Γ → V) x - (d : Γ → V) x := by
    simpa [Submodule.coe_sub, Pi.sub_apply] using h
  simp only [Pi.add_apply]
  rw [h']
  abel

theorem exists_coboundary_of_mem_Z1_of_not_mem_B1_of_finrank_H1_le_one
    (ρ : Representation (ZMod 2) Γ V)
    (hH1 : Module.finrank (ZMod 2) (H1 ρ) ≤ 1)
    {f d : Γ → V} (hfZ : f ∈ Z1 ρ) (hdZ : d ∈ Z1 ρ)
    (hf : f ∉ B1 ρ) (hd : d ∉ B1 ρ) :
    ∃ ℓ : V, f = d + coboundary ρ ℓ :=
  exists_coboundary_of_not_mem_B1_of_finrank_H1_le_one ρ hH1 ⟨f, hfZ⟩ ⟨d, hdZ⟩ hf hd

end ClassComparison

end CFSG.Quasithin.JonesParshall
