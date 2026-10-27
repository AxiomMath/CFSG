module

public import CFSG.LocalAnalysis.StandardType.GGTBJParabolicComponents
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.RankThree.E6 CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime]

theorem kernelRoots_zetaVec_eq_rootKernel {ζ : Kˣ} (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) (z : Fin Tag.E6.rank → ZMod p) :
    kernelRoots (rootCharHom (CFSG.StandardType.TableBExc.E6Three.zetaVec ζ hζ z)) =
      rootKernel z := by
  ext γ
  change (IsRoot Tag.E6 γ ∧
    rootChar (CFSG.StandardType.TableBExc.E6Three.zetaVec ζ hζ z) γ = 1) ↔
      (IsRoot Tag.E6 γ ∧ charVal z γ = 0)
  rw [CFSG.StandardType.NoOffE8Five.rootChar_zetaVec]
  constructor
  · rintro ⟨hγ, h⟩
    have he : Multiplicative.ofAdd (charVal z γ) = 1 :=
      zmodPowHom_injective hζo hζ (h.trans (map_one (zmodPowHom ζ hζ)).symm)
    exact ⟨hγ, congrArg Multiplicative.toAdd he⟩
  · rintro ⟨hγ, h⟩
    refine ⟨hγ, ?_⟩
    change zmodPowHom ζ hζ (Multiplicative.ofAdd (charVal z γ)) = 1
    rw [h]
    exact map_one _


theorem exists_componentRoots_eq_smul_parabolicRoots_e6 (hp5 : 5 < p) {ζ : Kˣ}
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (z : Fin Tag.E6.rank → ZMod p)
    (i : KernelComponent
      (rootCharHom (CFSG.StandardType.TableBExc.E6Three.zetaVec ζ hζ z))) :
    ∃ (u : WeylGroup Tag.E6) (J : Set (Fin Tag.E6.rank)),
      componentRoots (rootCharHom (CFSG.StandardType.TableBExc.E6Three.zetaVec ζ hζ z)) i =
        (u • ·) '' parabolicRoots Tag.E6 J ∧ (z ≠ 0 → J ≠ Set.univ) := by
  classical
  obtain ⟨u, S, hS, hSproper⟩ :=
    CFSG.RankThree.Lattice.exists_smul_rootKernel_eq_parabolicRoots hp5 z
  rw [← kernelRoots_zetaVec_eq_rootKernel hζo hζ z] at hS
  obtain ⟨J, hJS, hJ⟩ := componentRoots_eq_smul_parabolicRoots_of_kernel
    (τ := Tag.E6) (fun j => by fin_cases j <;> rfl) _ i u hS
  refine ⟨u⁻¹, J, hJ, fun hz hJu => hSproper hz ?_⟩
  exact Set.eq_univ_of_forall fun j => hJS (hJu ▸ Set.mem_univ j)

end CFSG.LieType.Chevalley

end
