module

public import CFSG.LieType.Steinberg.Adjoint.Datum
public import CFSG.LocalAnalysis.StandardType.PhanEChevModel

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} (F : RootOperatorFamily τ) (k : Type) [Field k] [CharP k 2]

theorem adj_nm_mul_self (i : Fin τ.rank) :
    weylElement τ k i * weylElement τ k i = 1 := by
  have hneg : (-1 : kˣ) = 1 :=
    Units.ext (by rw [Units.val_neg, Units.val_one]; exact CharTwo.neg_eq 1)
  apply Subtype.ext
  change weylElt τ k i 1 * weylElt τ k i 1 = 1
  rw [← sq, weylElt_one_sq (τ := τ) (R := k) i, hneg, torusElt_one i]

theorem adj_nm_conj (i : Fin τ.rank) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : k) :
    weylElement τ k i * xPar F γ c *
        (weylElement τ k i)⁻¹ =
      xPar F (weylAction (adjDatum F k).isFiniteType
        ((coxeterMatrix (adjDatum F k).isFiniteType).toCoxeterSystem.simple i) γ) c := by
  obtain ⟨ε, hε, hconj⟩ := weylElement_xPar_conj (F := F) (K := k) i hγ
  have heps : (ε : k) = 1 := by
    rcases hε with h | h
    · rw [h, Int.cast_one]
    · rw [h, Int.cast_neg, Int.cast_one, CharTwo.neg_eq]
  have hrefl : reflection τ.cartan i γ = reflect τ i γ := by
    rw [reflection_apply]
    rfl
  have h1 : CFSG.LieType.Steinberg.weylElement (xPar F) i 1 = weylElement τ k i :=
    (weylElement_eq_xPar (F := F) (K := k) i).symm
  have h := hconj 1 c
  rw [h1] at h
  rw [h, hrefl, ← weylAction_simple_eq_reflect (adjDatum F k).isFiniteType i γ, heps]
  simp

theorem adj_hh_conj (i : Fin τ.rank) (t : kˣ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : k) :
    torusElement τ k i t * xPar F γ c * (torusElement τ k i t)⁻¹ =
      xPar F γ (((t ^ (∑ j, τ.cartan i j * γ j) : kˣ) : k) * c) := by
  rw [xPar_of_isRoot hγ c,
    xPar_of_isRoot hγ (((t ^ (∑ j, τ.cartan i j * γ j) : kˣ) : k) * c)]
  exact F.torusElement_mul_eltElement_mul_inv i t ⟨γ, hγ⟩ c

theorem adj_nm_def (i : Fin τ.rank) :
    weylElement τ k i =
      xPar F (Pi.single i 1) 1 * xPar F (-Pi.single i 1) (-1) * xPar F (Pi.single i 1) 1 := by
  rw [weylElement_eq_xPar (F := F) (K := k) i, CFSG.LieType.Steinberg.weylElement]
  simp only [Units.val_neg, Units.val_inv_eq_inv_val, Units.val_one, inv_one]

theorem adj_hh_def (i : Fin τ.rank) (t : kˣ) :
    torusElement τ k i t =
      (xPar F (Pi.single i 1) (t : k) * xPar F (-Pi.single i 1) (-((t⁻¹ : kˣ) : k)) *
        xPar F (Pi.single i 1) (t : k)) * (weylElement τ k i)⁻¹ := by
  simpa only [CFSG.LieType.Steinberg.weylElement, Units.val_neg] using
    eq_mul_inv_of_mul_eq (weylElement_xPar (F := F) (K := k) i t).symm

@[expose] noncomputable def adjChevModel :
    ChevModel2 (adjDatum F k) (weylElement τ k) (torus (τ := τ) k) k where
  x := xPar F
  x_mem γ hγ g := mem_rootGroup_iff ((mem_adjDatum_roots).1 hγ) g
  x_add γ _ c d := xPar_add γ c d
  x_inj γ hγ := xPar_injective ((mem_adjDatum_roots).1 hγ)
  nm_conj i γ hγ c := adj_nm_conj F k i ((mem_adjDatum_roots).1 hγ) c
  nm_sq i := adj_nm_mul_self k i
  hh i := torusHom k i
  hh_range i := rfl
  hh_conj i t γ hγ c := adj_hh_conj F k i t ((mem_adjDatum_roots).1 hγ) c
  nm_def i := adj_nm_def F k i
  hh_def i t := adj_hh_def F k i t

end CFSG.ClassicalInvolution.Phan.PhanE
