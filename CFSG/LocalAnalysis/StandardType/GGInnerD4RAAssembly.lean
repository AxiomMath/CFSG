module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4RABranchDefs
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RAMarking
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RegimeDefs

public section

namespace CFSG.StandardType.GGInnerD4RAParts

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA

private theorem ltrra3c_sel_data (hSel : S2MathAs51600RAMarking.RASelectedMarking) {X : Type}
    [Group X] (A : Subgroup (MulAut X)) (σ : MulAut X) (hσ : σ ∈ A)
    (hmark : LargeEvenMarking X
      (fun lab _ _ I _ θ => GGKacRA lab 3 ∧ GGInducedInn A θ I)) :
    ∃ (lab : LargeEvenLabel) (R : Type) (_ : Group R) (θ : X ⧸ Subgroup.center X ≃* R),
      LargeEvenInLambda2 lab ∧ GGKacRA lab 3 ∧ Subgroup.center R = ⊥ ∧
      Y10GField.InnDiagKind R lab (ggInducedAut θ σ) := by
  obtain ⟨_hX, lab, hΛ, hraw⟩ := hSel X A σ hσ hmark
  obtain ⟨R, hR, I, F, hsimple, hna, θ, hP⟩ :=
    CFSG.StandardType.largeEvenRawDatum_exists hraw
  obtain ⟨⟨hRA, _hInd⟩, hkind⟩ := hP
  have hcen : Subgroup.center R = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a)) b).symm
  exact ⟨lab, R, hR, θ, hΛ, hRA, hcen, hkind⟩

theorem raComponentLabel_of_branches
    (hSel : S2MathAs51600RAMarking.RASelectedMarking) (hLin : RALinearBranch)
    (hUni : RAUnitaryBranch) : S2MathAs51600.RAComponentLabel := by
  intro X _ _ A σ J hA hσ hJ hmark
  obtain ⟨lab, R, hR, θ, hΛ, hRA, hcen, hkind⟩ := ltrra3c_sel_data hSel A σ hσ hmark
  let π : X →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hπ : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerEq : π.ker = Subgroup.center X := by
    ext x
    simp [π, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hker : π.ker ≤ Subgroup.center X := le_of_eq hkerEq
  have hcomm : ∀ x : X, π (σ x) = ggInducedAut θ σ (π x) := by
    intro x
    exact (ggInducedAut_apply θ σ x).symm
  haveI : Finite R := Finite.of_surjective π hπ
  obtain ⟨hJb, hequiv⟩ :=
    S2MathAs51600.centralFixedComponentTransfer_holds π hπ hker σ (ggInducedAut θ σ) hcomm J hJ
  obtain ⟨e⟩ := hequiv
  have hβ3 : (ggInducedAut θ σ) ^ 3 = 1 := by
    rw [← map_pow (ggInducedAut θ) σ 3, hA.2 σ hσ, map_one]
  rcases hRA with ⟨htag, -, -⟩ | ⟨htag, -, -⟩
  · obtain ⟨labC, hΛC, hTypeA, hlabC⟩ :=
      hLin R lab (ggInducedAut θ σ) (J.map π) hcen hΛ htag hβ3 hkind hJb
    exact ⟨labC, hΛC, hTypeA, ggHasLabel_of_mulEquiv e.symm hlabC⟩
  · obtain ⟨labC, hΛC, hTypeA, hlabC⟩ :=
      hUni R lab (ggInducedAut θ σ) (J.map π) hcen hΛ htag hβ3 hkind hJb
    exact ⟨labC, hΛC, hTypeA, ggHasLabel_of_mulEquiv e.symm hlabC⟩

end CFSG.StandardType.GGInnerD4RAParts

end
