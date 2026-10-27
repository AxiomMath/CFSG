module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3Defs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFam
public import CFSG.LocalAnalysis.StandardType.GGFamRatComp

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableCRes

private theorem l10lA_jointChar_apply {τ : Tag} {L : Type} [Field L]
    (a₁ a₂ : Fin τ.rank → Lˣ) (v : Multiplicative (Fin τ.rank → ℤ)) :
    jointChar a₁ a₂ v = (rootChar a₁ (Multiplicative.toAdd v),
      rootChar a₂ (Multiplicative.toAdd v)) := rfl

theorem kernelRoots_jointChar_eq_famCharHom {τ : Tag} {L : Type} [Field L]
    (a₁ a₂ : Fin τ.rank → Lˣ) :
    kernelRoots (jointChar a₁ a₂) =
      kernelRoots (famCharHom (![a₁, a₂] : Fin 2 → Fin τ.rank → Lˣ)) := by
  ext γ
  rw [mem_kernelRoots_famChar]
  constructor
  · rintro ⟨hroot, hχ⟩
    refine ⟨hroot, fun u => ?_⟩
    have h2 : (rootChar a₁ γ, rootChar a₂ γ) = 1 := by
      rw [l10lA_jointChar_apply] at hχ
      simpa using hχ
    fin_cases u
    · exact (Prod.mk_eq_one.1 h2).1
    · exact (Prod.mk_eq_one.1 h2).2
  · rintro ⟨hroot, hχ⟩
    refine ⟨hroot, ?_⟩
    rw [l10lA_jointChar_apply, Prod.mk_eq_one]
    exact ⟨by simpa using hχ 0, by simpa using hχ 1⟩

theorem exists_famComponent_of_jointChar {τ : Tag} {L : Type} [Field L]
    (a₁ a₂ : Fin τ.rank → Lˣ) (i : KernelComponent (jointChar a₁ a₂)) :
    ∃ j : KernelComponent (famCharHom (![a₁, a₂] : Fin 2 → Fin τ.rank → Lˣ)),
      componentRoots (jointChar a₁ a₂) i =
        componentRoots (famCharHom (![a₁, a₂] : Fin 2 → Fin τ.rank → Lˣ)) j :=
  exists_componentRoots_eq (kernelRoots_jointChar_eq_famCharHom a₁ a₂) i

theorem exists_jointComponent_of_famCharHom {τ : Tag} {L : Type} [Field L]
    (a₁ a₂ : Fin τ.rank → Lˣ)
    (j : KernelComponent (famCharHom (![a₁, a₂] : Fin 2 → Fin τ.rank → Lˣ))) :
    ∃ i : KernelComponent (jointChar a₁ a₂),
      componentRoots (famCharHom (![a₁, a₂] : Fin 2 → Fin τ.rank → Lˣ)) j =
        componentRoots (jointChar a₁ a₂) i := by
  obtain ⟨i, hi⟩ := exists_componentRoots_eq (kernelRoots_jointChar_eq_famCharHom a₁ a₂).symm j
  exact ⟨i, hi⟩

theorem centralizer_closure_pair_eq_range {τ : Tag} {L : Type} [Field L] (a₁ a₂ : Fin τ.rank → Lˣ) :
    Subgroup.centralizer
        ((Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂} : Subgroup (ModGL τ L)) :
          Set (ModGL τ L)) =
      Subgroup.centralizer (Set.range fun u : Fin 2 =>
        rootDiagUnit τ ((![a₁, a₂] : Fin 2 → Fin τ.rank → Lˣ) u)) := by
  have hrange : Set.range (fun u : Fin 2 =>
      rootDiagUnit τ ((![a₁, a₂] : Fin 2 → Fin τ.rank → Lˣ) u)) =
      ({rootDiagUnit τ a₁, rootDiagUnit τ a₂} : Set (ModGL τ L)) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      fin_cases u <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  rw [Subgroup.centralizer_closure, hrange]

theorem ratComp_eq_rationalComponentM
    {τ : Tag} {L : Type} [Field L] {M : Type*} [CommGroup M]
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (Γ : Subgroup (ModGL τ L))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ) :
    ratComp ρ Γ (componentRoots χ i) = rationalComponentM ρ Γ χ i :=
  rfl

end CFSG.StandardType.LieCore
