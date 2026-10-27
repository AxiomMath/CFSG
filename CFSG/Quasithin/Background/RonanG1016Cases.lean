module

public import CFSG.Quasithin.Background.RonanG1016McL
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLaughlin

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

open CFSG.ComponentClassification.OutcomeLocal

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

section Cases

variable {K : Subgroup (GLV V)} {J : Submodule (ZMod 2) V}

theorem restrictRange_eq_top_of_restrictG (hJ : IsIrr K J) (h : restrictG K J hJ.1 = ⊤) :
    restrictRange K J hJ.1 = ⊤ := by
  refine eq_top_iff.2 fun g _ => ?_
  have h1 : (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) ↥J).symm g ∈
      restrictG K J hJ.1 := h ▸ Subgroup.mem_top _
  have h2 := (mem_restrictG_iff hJ.1 _).1 h1
  rwa [MulEquiv.apply_symm_apply] at h2

theorem mem_restrictRange_of_bilin (hJ : IsIrr K J) (f : LinearMap.BilinForm (ZMod 2) ↥J)
    (h : restrictG K J hJ.1 = CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup f) (g : ↥J ≃ₗ[ZMod 2] ↥J) :
    g ∈ restrictRange K J hJ.1 ↔ ∀ x y, f (g x) (g y) = f x y := by
  have h1 : g ∈ restrictRange K J hJ.1 ↔
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) ↥J).symm g ∈ restrictG K J hJ.1 := by
    rw [mem_restrictG_iff, MulEquiv.apply_symm_apply]
  rw [h1, h]
  constructor
  · intro hg x y
    have := (CFSG.LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup.1 hg) x y
    rwa [coe_symm_generalLinearEquiv, coe_symm_generalLinearEquiv] at this
  · intro hg
    rw [CFSG.LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup]
    intro x y
    rw [coe_symm_generalLinearEquiv, coe_symm_generalLinearEquiv]
    exact hg x y

theorem mem_restrictRange_of_orth (hJ : IsIrr K J) (Q : QuadraticForm (ZMod 2) ↥J)
    (h : restrictG K J hJ.1 = (TauCeti.QuadraticMap.orthogonalGroup Q).comap
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) ↥J).toMonoidHom)
    (g : ↥J ≃ₗ[ZMod 2] ↥J) :
    g ∈ restrictRange K J hJ.1 ↔ ∀ x, Q (g x) = Q x := by
  have h1 : g ∈ restrictRange K J hJ.1 ↔
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) ↥J).symm g ∈ restrictG K J hJ.1 := by
    rw [mem_restrictG_iff, MulEquiv.apply_symm_apply]
  rw [h1, h, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff]

theorem mclaughlin_cases (hJ : IsIrr K J)
    (hgen : K ≤ Subgroup.closure {s | s ∈ K ∧ IsTransvOn J s}) :
    restrictRange K J hJ.1 = ⊤ ∨
    (∃ f : LinearMap.BilinForm (ZMod 2) ↥J, f.Nondegenerate ∧ f.IsAlt ∧
      restrictG K J hJ.1 = CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup f) ∨
    (∃ Q : QuadraticForm (ZMod 2) ↥J, (QuadraticMap.polarBilin Q).Nondegenerate ∧
      restrictG K J hJ.1 = (TauCeti.QuadraticMap.orthogonalGroup Q).comap
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) ↥J).toMonoidHom) ∨
    (Even (Module.finrank (ZMod 2) ↥J) ∧
      ((∃ β : ↥J ≃ₗ[ZMod 2] sumZero (Module.finrank (ZMod 2) ↥J + 1),
          (restrictG K J hJ.1).map
            (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
              (sumZeroRep (Module.finrank (ZMod 2) ↥J + 1)).range) ∨
        ∃ β : ↥J ≃ₗ[ZMod 2] sumZero (Module.finrank (ZMod 2) ↥J + 2) ⧸
            onesLine (Module.finrank (ZMod 2) ↥J + 2),
          (restrictG K J hJ.1).map
            (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
              (heartRep (Module.finrank (ZMod 2) ↥J + 2)).range)) := by
  have : FiniteDimensional (ZMod 2) ↥J := inferInstance
  have hn : 1 ≤ Module.finrank (ZMod 2) ↥J := Submodule.one_le_finrank_iff.2 hJ.ne_bot
  rcases mclaughlin_transvection_groups_F2 hn (restrictG K J hJ.1) (restrictG_gen hJ hgen)
      (restrictG_irr hJ) with h | ⟨-, f, hnd, halt, h⟩ | ⟨-, Q, hQ, h⟩ | h
  · exact Or.inl (restrictRange_eq_top_of_restrictG hJ h)
  · exact Or.inr (Or.inl ⟨f, hnd, halt, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨Q, hQ, h⟩))
  · exact Or.inr (Or.inr (Or.inr h))

theorem selfDual_of_ne_top (hJ : IsIrr K J)
    (hgen : K ≤ Subgroup.closure {s | s ∈ K ∧ IsTransvOn J s})
    (h2 : 2 ≤ Module.finrank (ZMod 2) ↥J) (hne : restrictRange K J hJ.1 ≠ ⊤) :
    SelfDual K J := by
  have : FiniteDimensional (ZMod 2) ↥J := inferInstance
  have hgenT : GenByTransvections (restrictG K J hJ.1) := restrictG_gen hJ hgen
  have hirr : IsIrreducibleOn (restrictG K J hJ.1) := fun W hW => restrictG_irr hJ W hW
  have hne' : restrictG K J hJ.1 ≠ ⊤ := fun h => hne (restrictRange_eq_top_of_restrictG hJ h)
  have hno : NoDihedralPair (restrictG K J hJ.1) := fun φ ψ a b ha hψ hφa hψb hφb hψa =>
    hne' (eq_top_of_dihedral hgenT hirr ha hψ hφa hψb hφb hψa)
  obtain ⟨f, halt, hcomm, hnd, hF4, hF5⟩ := exists_symplectic_form hgenT hirr hno
    (centres_nonempty hgenT hirr h2)
  have hle := le_bilinIsometryGroup hF4 hgenT hcomm
  refine ⟨f, ⟨fun u hu => hnd u hu, fun u hu => hnd u fun v => by rw [hcomm]; exact hu v⟩, ?_⟩
  intro k hk i j i' j' hki hkj
  have hmem : (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) ↥J).symm
      (restrictEquiv k J (hJ.1.conjSub_eq hk)) ∈ restrictG K J hJ.1 := by
    rw [mem_restrictG_iff, MulEquiv.apply_symm_apply]
    exact restrictEquiv_mem_restrictRange hJ.1 hk
  have h := hle hmem i j
  rw [coe_symm_generalLinearEquiv, coe_symm_generalLinearEquiv] at h
  have e1 : restrictEquiv k J (hJ.1.conjSub_eq hk) i = i' := Subtype.ext hki
  have e2 : restrictEquiv k J (hJ.1.conjSub_eq hk) j = j' := Subtype.ext hkj
  rwa [e1, e2] at h

end Cases

end G11

end CFSG.Quasithin
