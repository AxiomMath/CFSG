module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListG2
import CFSG.Quasithin.EmptyFaithful.S151CLG2F4Step
import CFSG.Quasithin.Background.RonanF918Four

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open scoped commutatorElement

@[expose] def K_G2ParabolicGen : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → UC22.IsG2 X n →
    ∀ S : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ → ∃ Y₁ Y₂ : Subgroup X,
      ⁅Y₁, Y₁⁆ = Y₁ ∧ ⁅Y₂, Y₂⁆ = Y₂ ∧ IsL2 (Bar2 Y₁) n ∧ IsL2 (Bar2 Y₂) n ∧
      Y₁ ⊔ Y₂ ⊔ S = ⊤ ∧
      ∀ α : MulAut X, S.map α.toMonoidHom = S →
        Y₁.map α.toMonoidHom = Y₁ ∧ Y₂.map α.toMonoidHom = Y₂

theorem k_G2ParabolicGen_holds :
    K_G2ParabolicGen := by
  intro X _ _ n hn hX S hS
  classical
  have hCE : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 2 n :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hX (by decide)
  obtain ⟨K, hF, hFin, hcp, φ, hK, -, hres, -⟩ :=
    CFSG.QuasithinUnique.Setup.X6.even_rank_two_residual_G2 hCE hS
  set P : Fin 2 → Subgroup X := fun j =>
    ((CFSG.LieType.Chevalley.parabolicSubgroup CFSG.Blueprint.Chevalley.Tag.G2 K
      {CFSG.QuasithinUnique.Setup.X6.g2Index j}).subgroupOf
      (CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2 K)).map
      φ.symm.toMonoidHom with hPdef
  have hL2 : ∀ j, IsL2 (Bar2 (perfectCore (P j))) n ∧
      ¬ Group.IsSolvable ↥(perfectCore (P j)) := by
    intro j
    obtain ⟨g, hg, hgk⟩ := CFSG.Quasithin.CLG2.exists_hom_perfectCore_map φ.symm
      (CFSG.QuasithinUnique.Vol2Native.A312L.exists_levi_hom_adjoint hK hn
        (CFSG.QuasithinUnique.Setup.X6.g2Index j))
    exact ⟨CFSG.Quasithin.RonanF918.lieModel_of_isPSL
      (CFSG.Quasithin.CLG2.sl2_quotient hK hn g hg hgk).1,
      CFSG.Quasithin.CLG2.not_isSolvable_perfectCore_of_levi
        (Or.inl ⟨K, inferInstance, inferInstance, inferInstance, n, hK, by omega, g, hg, hgk⟩)⟩
  have hgen := CFSG.Quasithin.CLG2.sup_perfectCore_eq_top_of_res hres fun j => (hL2 j).2
  obtain ⟨-, -, -, hIM⟩ := CFSG.QuasithinUnique.Setup.X6.even_G2_model_two_extensions hCE
  obtain ⟨Q₁, Q₂, -, hmax, -, -, -, hQinv⟩ := hIM S hS
  have hPinv : ∀ α : MulAut X, S.map α.toMonoidHom = S → ∀ j,
      (P j).map α.toMonoidHom = P j := by
    intro α hα j
    have hPj : P j ⋖ ⊤ := (hres.2.2.1 (P j) (hres.2.1 j)).2 ⟨j, rfl⟩
    rcases (hmax (P j) (hres.2.1 j)).1 hPj with h | h
    · rw [h]
      exact (hQinv α hα).1
    · rw [h]
      exact (hQinv α hα).2
  refine ⟨perfectCore (P 0), perfectCore (P 1), CFSG.Quasithin.perfectCore_perfect _,
    CFSG.Quasithin.perfectCore_perfect _, (hL2 0).1, (hL2 1).1, hgen, fun α hα => ⟨?_, ?_⟩⟩
  · rw [CFSG.Quasithin.map_perfectCore α.toMonoidHom (P 0), hPinv α hα 0]
  · rw [CFSG.Quasithin.map_perfectCore α.toMonoidHom (P 1), hPinv α hα 1]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
