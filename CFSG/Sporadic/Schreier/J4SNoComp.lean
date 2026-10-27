module

public import CFSG.Sporadic.Schreier.J4SNoCompLocal
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporInputs

public section

namespace CFSG.Sporadic.J4Schreier.NoComp

open CFSG CFSG.Sporadic.J4

theorem map_centralizer_singleton {A B : Type*} [Group A] [Group B] (f : A ≃* B) (t : A) :
    (Subgroup.centralizer ({t} : Set A)).map f.toMonoidHom =
      Subgroup.centralizer ({f t} : Set B) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨f.symm y, ?_, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply f.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]

theorem not_isComponent_of_mulEquiv {A Q : Type*} [Group A] [Group Q] (f : A ≃* Q) (t : A)
    (P : Q → Prop) (hP : P (f t))
    (h : ∀ s, P s → ∀ C : Subgroup (Subgroup.centralizer ({s} : Set Q)), ¬ IsComponent C)
    (B : Subgroup (Subgroup.centralizer ({t} : Set A))) : ¬ IsComponent B := fun hB =>
  h (f t) hP _ (CFSG.LocalCores.isComponent_map_mulEquiv
    ((f.subgroupMap _).trans (MulEquiv.subgroupCongr (map_centralizer_singleton f t))) hB)

theorem not_isComponent_centralizer_J
    (s : J) (hs : s = η 1 ∨ s = η 14)
    (B : Subgroup (Subgroup.centralizer ({s} : Set J))) : ¬ IsComponent B := by
  rcases hs with rfl | rfl
  · exact not_isComponent_centralizer_η1 B
  · exact not_isComponent_centralizer_η14 B

end CFSG.Sporadic.J4Schreier.NoComp

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp

theorem j4NoComponentsInput :
    J4NoComponentsInput := by
  intro G _ hG t ht B hB
  obtain ⟨e⟩ := hG
  obtain ⟨ψ, -⟩ : ∃ ψ : G ≃* J, True := ⟨e.trans (seedEquiv j4Facts.mat), trivial⟩
  have ho : orderOf (ψ t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  obtain ⟨-, g, hg⟩ := CTU_J4_every_inner_involution_conjugate_into_local_binary_subgroup _ ho
  obtain ⟨θ, hθt⟩ : ∃ θ : G ≃* J, θ t = g * ψ t * g⁻¹ :=
    ⟨ψ.trans (@MulAut.conj J (Subgroup.toGroup J) g), by
      rw [MulEquiv.trans_apply, MulAut.conj_apply]⟩
  exact @not_isComponent_of_mulEquiv G J _ (Subgroup.toGroup J) θ t
    (fun s => s = η 1 ∨ s = η 14) (by rw [hθt]; exact hg) not_isComponent_centralizer_J B hB

end CFSG.ComponentClassification.RestrictedStd.Spor
