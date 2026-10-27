module

public import CFSG.LinearAlgebra.RootGroupSL.Transport
public import CFSG.LinearAlgebra.RootGroupSL.DatumEquiv
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms

public section

namespace CFSG.StandardType.StarFour

open CFSG.LinearAlgebra.RootGroupSL CFSG.Open

theorem items_of_datum {k E V G : Type} [Field k] [Finite k] [CharP k 2] [Field E] [Algebra k E]
    [Finite E] [AddCommGroup V] [Module k V] [Module.Finite k V] [Group G]
    (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E) (h1 : ∀ t, π (ι t) = 0) (h2 : ∀ t, π (ι₁ t) = t)
    (h3 : ∀ t, π₁ (ι t) = t) (h4 : ∀ t, π₁ (ι₁ t) = 0)
    (hV : 3 * Module.finrank k E ≤ Module.finrank k V)
    (hstar : 2 ≤ Module.finrank k E ∨
      (Module.finrank k E = 1 ∧ 4 ≤ Nat.card k ∧ 4 ≤ Module.finrank k V))
    (ψ : SpecialLinearGroup k V →* G) (hψ : Function.Injective ψ) :
    pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (((datumRoot ι π h1).map ψ : Subgroup G) : Set G)) ⊔
        (datumJ0 ι ι₁ π π₁ h1 h4).map ψ = ψ.range ∧
      GGRootInnerAt ψ.range ((datumRoot ι π h1).map ψ) ∧
      GGRootNoCentralAt ψ.range ((datumRoot ι π h1).map ψ) ∧
      (∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (ψ.range : Set G) →
        Y ≤ Subgroup.normalizer (((datumRoot ι π h1).map ψ : Subgroup G) : Set G) →
        ⁅Y, ψ.range ⊓ Subgroup.normalizer (((datumRoot ι π h1).map ψ : Subgroup G) : Set G)⁆ ≤
          pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer
            (((datumRoot ι π h1).map ψ : Subgroup G) : Set G)) →
        Y ≤ ψ.range ⊔ Subgroup.centralizer (ψ.range : Set G)) := by
  have hEpos : 0 < Module.finrank k E := Module.finrank_pos (R := k) (M := E)
  haveI : Module.Finite k E := Module.finite_of_finrank_pos hEpos
  obtain ⟨X', hXadd, hXmod, hXfin, e, hroot, hrootNeg, hfin⟩ :=
    exists_datumEquiv ι ι₁ π π₁ h1 h2 h3 h4
  letI : AddCommGroup X' := hXadd
  letI : Module k X' := hXmod
  letI : Module.Finite k X' := hXfin
  let ι' : SpecialLinearGroup k (DSpace E X') →* G := ψ.comp e.symm.toMonoidHom
  have hι' : Function.Injective ι' := by
    intro x y hxy
    change ψ (e.symm x) = ψ (e.symm y) at hxy
    exact e.symm.injective (hψ hxy)
  have hι'range : ι'.range = ψ.range := by
    change (ψ.comp e.symm.toMonoidHom).range = ψ.range
    rw [MonoidHom.range_comp]
    have htop : e.symm.toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top_of_surjective _ e.symm.surjective
    rw [htop]
    exact (MonoidHom.range_eq_map ψ).symm
  have hcomp : ι'.comp e.toMonoidHom = ψ := by
    change (ψ.comp e.symm.toMonoidHom).comp e.toMonoidHom = ψ
    ext x
    simp
  have hroot_map : Subgroup.map e.toMonoidHom (datumRoot ι π h1) = rootSL k E X' := by
    change (datumRoot ι π h1).map e = rootSL k E X'
    rw [datumRoot, MonoidHom.map_closure]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x ⟨a, ⟨t, rfl⟩, rfl⟩
      change e (datumElt ι π h1 t) ∈ rootSL k E X'
      rw [hroot t]
      exact rootElt_mem_rootSL t
    · intro g hg
      obtain ⟨t, ht⟩ := mem_rootSL_iff.mp hg
      refine Subgroup.subset_closure ⟨datumElt ι π h1 t, ⟨t, rfl⟩, ?_⟩
      change e (datumElt ι π h1 t) = g
      rw [hroot t]
      exact (Subtype.ext ht).symm
  have himg1 : e '' Set.range (datumElt ι π h1) = Set.range (rootElt k X' (E := E)) := by
    ext g
    constructor
    · rintro ⟨a, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, (hroot t).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨datumElt ι π h1 t, ⟨t, rfl⟩, hroot t⟩
  have himg2 : e '' Set.range (datumElt ι₁ π₁ h4) =
      Set.range (rootNegElt k X' (E := E)) := by
    ext g
    constructor
    · rintro ⟨a, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, (hrootNeg t).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨datumElt ι₁ π₁ h4 t, ⟨t, rfl⟩, hrootNeg t⟩
  have hj0_map : Subgroup.map e.toMonoidHom (datumJ0 ι ι₁ π π₁ h1 h4) = J0SL k E X' := by
    change (datumJ0 ι ι₁ π π₁ h1 h4).map e = J0SL k E X'
    rw [datumJ0, J0SL, MonoidHom.map_closure, Set.image_union]
    change Subgroup.closure (⇑e '' Set.range (datumElt ι π h1) ∪
        ⇑e '' Set.range (datumElt ι₁ π₁ h4)) =
      Subgroup.closure (Set.range (rootElt k X' (E := E)) ∪
        Set.range (rootNegElt k X' (E := E)))
    rw [himg1, himg2]
  have hmaproot : (datumRoot ι π h1).map ψ = (rootSL k E X').map ι' := by
    rw [← hcomp, ← Subgroup.map_map, hroot_map]
  have hmapj0 : (datumJ0 ι ι₁ π π₁ h1 h4).map ψ = (J0SL k E X').map ι' := by
    rw [← hcomp, ← Subgroup.map_map, hj0_map]
  have hdX : Module.finrank k E ≤ Module.finrank k X' := by omega
  have hstar' : 2 ≤ Module.finrank k E ∨
      (Module.finrank k E = 1 ∧ 4 ≤ Nat.card k ∧ 2 ≤ Module.finrank k X') := by
    rcases hstar with h | ⟨hE1, hk, hV4⟩
    · exact Or.inl h
    · exact Or.inr ⟨hE1, hk, by omega⟩
  have hXpos : 0 < Module.finrank k X' := lt_of_lt_of_le hEpos hdX
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rw [hmaproot, hmapj0, ← hι'range]
    rw [pCoreOf_inf_normalizer_eq_map_QK hXpos ι' hι']
    rw [← Subgroup.map_sup, QK_sup_J0SL_eq_top hdX]
    exact (MonoidHom.range_eq_map ι').symm
  ·
    rw [hmaproot, ← hι'range]
    exact ggRootInnerAt_map hdX hstar' ι' hι'
  ·
    rw [hmaproot, ← hι'range]
    exact ggRootNoCentralAt_map hdX hstar' ι' hι'
  ·
    intro Y hY hYG hYR hc
    have hYG' : Y ≤ Subgroup.normalizer (ι'.range : Set G) := by
      simpa only [hι'range] using hYG
    have hYR' : Y ≤ Subgroup.normalizer
        (((rootSL k E X').map ι' : Subgroup G) : Set G) := by
      simpa only [← hmaproot] using hYR
    have hc' : ⁅Y, ι'.range ⊓ Subgroup.normalizer
          (((rootSL k E X').map ι' : Subgroup G) : Set G)⁆ ≤
        pCoreOf 2 (ι'.range ⊓ Subgroup.normalizer
          (((rootSL k E X').map ι' : Subgroup G) : Set G)) := by
      simpa only [hι'range, ← hmaproot] using hc
    have hres := item_three_map hdX hstar' ι' hι' Y hY hYG' hYR' hc'
    simpa only [hι'range] using hres

end CFSG.StandardType.StarFour
