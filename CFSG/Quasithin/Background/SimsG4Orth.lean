module

public import CFSG.Quasithin.Background.SimsG4OrthA
public import CFSG.Quasithin.Background.SimsG4OrthMinus
public import CFSG.Quasithin.Background.SimsG4OrthPlus

public section

namespace CFSG.Quasithin.SimsG4

theorem orthIdent_holds : OrthIdent := by
  intro K _ _ _ W _ _ Q hdim hnd R hR1 hfield hirr hprim
  by_cases hplus : ∃ U : Submodule K W, Module.finrank K U = 2 ∧ ∀ u ∈ U, Q u = 0
  · exact orthIdent_plus Q hdim hnd hplus R hR1 hfield hirr hprim
  · refine orthIdent_minus Q hdim hnd ?_ R hR1 hfield hirr hprim
    intro U hU
    by_contra hlt
    push Not at hlt
    apply hplus
    haveI : FiniteDimensional K W := Module.finite_of_finrank_pos (by rw [hdim]; norm_num)
    let b := Module.finBasis K U
    have h2 : 2 ≤ Module.finrank K U := hlt
    let i₀ : Fin (Module.finrank K U) := ⟨0, by omega⟩
    let i₁ : Fin (Module.finrank K U) := ⟨1, by omega⟩
    have hne : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
    let v : Fin 2 → W := ![(b i₀ : W), (b i₁ : W)]
    have hv : LinearIndependent K v := by
      have hb : LinearIndependent K (fun i => (b i : W)) :=
        b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
      have hinj : Function.Injective ![i₀, i₁] := by
        intro x y hxy
        fin_cases x <;> fin_cases y <;> simp_all
      have := hb.comp ![i₀, i₁] hinj
      convert this using 1
      ext x
      fin_cases x <;> rfl
    refine ⟨Submodule.span K (Set.range v), ?_, ?_⟩
    · rw [finrank_span_eq_card hv]
      simp
    · intro u hu
      have hle : Submodule.span K (Set.range v) ≤ U := by
        rw [Submodule.span_le]
        rintro _ ⟨x, rfl⟩
        fin_cases x
        · exact (b i₀).2
        · exact (b i₁).2
      exact hU u (hle hu)

end CFSG.Quasithin.SimsG4
