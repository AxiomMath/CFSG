module

public import CFSG.LocalAnalysis.StandardType.AlternatingEightCoverSmallModules
public import CFSG.LocalAnalysis.StandardType.SpFixedNorm
public import CFSG.LocalAnalysis.StandardType.SpFixedSpaceDual
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public section

namespace CFSG.StandardType

namespace SpFixed

open Matrix
open CFSG.Open (StatedSp)

theorem IsAlternatingEightCover.statedSp_map_eq_one {J : Type*} [Group J] [Finite J]
    (hJ : IsAlternatingEightCover J) {F : Type} [Field F] [CharP F 2] {m : ℕ} (hm : m ≤ 2)
    (ρ : J →* StatedSp m F) (g : J) : ρ g = 1 := by
  let E := AlgebraicClosure F
  haveI : IsAlgClosed E := inferInstance
  haveI : CharP E 2 := charP_of_injective_algebraMap (algebraMap F E).injective 2
  let φ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F →+*
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) E := RingHom.mapMatrix (algebraMap F E)
  let ρ' : J →* Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) E :=
    φ.toMonoidHom.comp ((matHom F m).comp ρ)
  let G : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) E := (gram F m).map (algebraMap F E)
  have hρg : ∀ x : J, ρ' x = (matHom F m (ρ x)).map (algebraMap F E) := fun x => rfl
  have hGeq : G = (gram F m).map (algebraMap F E) := rfl
  have hG : IsUnit G := by
    have hgram : gram F m * -(gram F m) = 1 := by
      rw [Matrix.mul_neg, gram_mul_gram, neg_neg]
    refine IsUnit.of_mul_eq_one (-G) ?_
    rw [show G = φ (gram F m) from rfl, ← map_neg, ← map_mul, hgram, map_one]
  have hcard : Fintype.card (Fin m ⊕ Fin m) ≤ 5 := by
    rw [Fintype.card_sum, Fintype.card_fin]
    omega
  have hρ' : ∀ x, (ρ' x)ᵀ * G * (ρ' x).map (RingEquiv.refl E) = G := by
    intro x
    have hmain := matHom_transpose_mul_gram_mul (ρ x)
    have hmap := congrArg (fun M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F =>
        M.map (algebraMap F E)) hmain
    simp only [Matrix.map_mul, Matrix.transpose_map] at hmap
    have hρg' : (ρ' x).map (RingEquiv.refl E) =
        (matHom F m (ρ x)).map (algebraMap F E) := by
      rw [hρg x, Matrix.map_map]
      rfl
    rw [hρg', hρg x, hGeq]
    exact hmap
  have h1 : ρ' g = 1 :=
    IsAlternatingEightCover.map_eq_one_of_card_le_five_of_form hJ (RingEquiv.refl E)
      (fun η _ => ⟨0, by simp⟩) hG hcard ρ' hρ' g
  have hmat : matHom F m (ρ g) = 1 := by
    apply Matrix.map_injective (algebraMap F E).injective
    change (matHom F m (ρ g)).map (algebraMap F E) =
      (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F).map (algebraMap F E)
    rw [show (matHom F m (ρ g)).map (algebraMap F E) = 1 by rw [← hρg g]; exact h1,
      Matrix.map_one (algebraMap F E) (map_zero _) (map_one _)]
  exact matHom_injective (by rw [hmat, map_one])

end SpFixed

end CFSG.StandardType
