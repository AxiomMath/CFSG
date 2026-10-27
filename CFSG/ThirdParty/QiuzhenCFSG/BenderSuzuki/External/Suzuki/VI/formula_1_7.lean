module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_7_Core

namespace CFSG
end CFSG
open CFSG

/-!
# Suzuki VI.(1.7)

The row and column orthogonality relations for a complete family of
irreducible complex characters.
-/

noncomputable section

open scoped BigOperators

namespace CFSG.BenderSuzuki
namespace External
namespace Suzuki
namespace VI

universe u v

/-- Suzuki, *Group Theory II*, Chapter 6, formula (1.7). -/
public theorem suzuki_ch6_formula_1_7
    {G : Type u} [Group G] [Finite G]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (chi : ι → Theory.Character.ConjClassFunction G)
    (hchi : Theory.Character.IsCompleteIrreducibleCharacterFamily chi) :
    (∀ i j : ι,
      Theory.Character.classFunctionInner (chi i) (chi j) =
        if i = j then 1 else 0) ∧
      ∀ x y : G,
        (ConjClasses.mk x = ConjClasses.mk y →
          ∑ i : ι, chi i (ConjClasses.mk x) * chi i (ConjClasses.mk y⁻¹) =
            (Nat.card {z : G // z * x = x * z} : ℂ)) ∧
        (ConjClasses.mk x ≠ ConjClasses.mk y →
          ∑ i : ι, chi i (ConjClasses.mk x) * chi i (ConjClasses.mk y⁻¹) = 0) := by
  classical
  constructor
  · exact fun i j => Section1.representation_completeFamily_orthonormal hchi i j
  · rcases Theory.Character.second_orthogonality (G := G) with
      ⟨kappa, hkappa, psi, hpsi, horth⟩
    letI : Fintype kappa := hkappa
    let f : ι → kappa := fun i =>
      Classical.choose (hpsi.2.1 (chi i) (hchi.1 i))
    have hf (i : ι) : psi (f i) = chi i :=
      Classical.choose_spec (hpsi.2.1 (chi i) (hchi.1 i))
    have hf_injective : Function.Injective f := by
      intro i j hij
      apply hchi.2.2
      rw [← hf i, ← hf j, hij]
    have hf_surjective : Function.Surjective f := by
      intro k
      obtain ⟨i, hi⟩ := hchi.2.1 (psi k) (hpsi.1 k)
      refine ⟨i, hpsi.2.2 ?_⟩
      rw [hf i, hi]
    let e : ι ≃ kappa := Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩
    have he (i : ι) : psi (e i) = chi i := hf i
    have h_inv (i : ι) (y : G) :
        chi i (ConjClasses.mk y⁻¹) = star (chi i (ConjClasses.mk y)) := by
      rcases (hchi.1 i).1 with ⟨n, rho, hrho⟩
      rw [hrho]
      change rho.character y⁻¹ = star (rho.character y)
      exact Theory.Representation.representation_character_inv_eq_star_character rho y
    intro x y
    constructor
    · intro hxy
      calc
        (∑ i : ι, chi i (ConjClasses.mk x) * chi i (ConjClasses.mk y⁻¹)) =
            ∑ i : ι, chi i (ConjClasses.mk x) *
              star (chi i (ConjClasses.mk y)) := by
                apply Finset.sum_congr rfl
                intro i _
                rw [h_inv]
        _ = ∑ i : ι, psi (e i) (ConjClasses.mk x) *
              star (psi (e i) (ConjClasses.mk y)) := by
                apply Finset.sum_congr rfl
                intro i _
                rw [he]
        _ = ∑ k : kappa, psi k (ConjClasses.mk x) *
              star (psi k (ConjClasses.mk y)) :=
                Equiv.sum_comp e (fun k : kappa =>
                  psi k (ConjClasses.mk x) * star (psi k (ConjClasses.mk y)))
        _ = (Nat.card {z : G // z * x = x * z} : ℂ) := (horth x y).1 hxy
    · intro hxy
      calc
        (∑ i : ι, chi i (ConjClasses.mk x) * chi i (ConjClasses.mk y⁻¹)) =
            ∑ i : ι, chi i (ConjClasses.mk x) *
              star (chi i (ConjClasses.mk y)) := by
                apply Finset.sum_congr rfl
                intro i _
                rw [h_inv]
        _ = ∑ i : ι, psi (e i) (ConjClasses.mk x) *
              star (psi (e i) (ConjClasses.mk y)) := by
                apply Finset.sum_congr rfl
                intro i _
                rw [he]
        _ = ∑ k : kappa, psi k (ConjClasses.mk x) *
              star (psi k (ConjClasses.mk y)) :=
                Equiv.sum_comp e (fun k : kappa =>
                  psi k (ConjClasses.mk x) * star (psi k (ConjClasses.mk y)))
        _ = 0 := (horth x y).2 hxy

end VI
end Suzuki
end External
end CFSG.BenderSuzuki
