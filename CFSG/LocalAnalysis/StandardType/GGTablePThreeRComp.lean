module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicTransfer
import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem ggFix_eq_ggAutFixedSubgroup {R : Type*} [Group R] (σ : MulAut R) :
    ggFix σ = ggAutFixedSubgroup σ :=
  Subgroup.ext fun _ => Iff.rfl

theorem leafRComp_holds :
    ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
      ∀ (R : Type) [Group R] (θ : X ⧸ Subgroup.center X ≃* R) (δ : MulAut X),
        (∀ J : Subgroup X, IsComponentOf J (ggAutFixedSubgroup δ) →
            IsComponentOf (J.map (proj θ)) (ggAutFixedSubgroup (ggInducedAut θ δ))) ∧
          ∀ Q : Subgroup R, IsComponentOf Q (ggAutFixedSubgroup (ggInducedAut θ δ)) →
            ∃ J : Subgroup X, IsComponentOf J (ggAutFixedSubgroup δ) ∧ J.map (proj θ) = Q := by
  intro X _ _ _ R _ θ δ
  set π : X →* R := proj θ with hπdef
  have hπ_apply : ∀ x : X, π x = θ (x : X ⧸ Subgroup.center X) := by
    intro x
    rw [hπdef]
    rfl
  have hπ_surj : Function.Surjective π := by
    intro r
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) q
    exact ⟨x, hπ_apply x⟩
  have hπ_ker : π.ker ≤ Subgroup.center X := by
    intro x hx
    rw [MonoidHom.mem_ker, hπ_apply] at hx
    exact (QuotientGroup.eq_one_iff x).mp ((θ.map_eq_one_iff).mp hx)
  have hαβ : ∀ x : X, π (δ x) = ggInducedAut θ δ (π x) := by
    intro x
    rw [hπ_apply (δ x), hπ_apply x, ggInducedAut_apply]
  have hβα : ∀ x : X, ggInducedAut θ δ (π x) = π (δ x) := fun x => (hαβ x).symm
  refine ⟨?_, ?_⟩
  · intro J hJ
    have hJ' : IsComponentOf J (ggFix δ) := by
      rw [ggFix_eq_ggAutFixedSubgroup]
      exact hJ
    have hmap := CFSG.StandardType.LayerCC.isComponentOf_map_ggFix
      (f := π) (α := δ) (β := ggInducedAut θ δ) hπ_surj hπ_ker hαβ hJ'
    rw [ggFix_eq_ggAutFixedSubgroup] at hmap
    exact hmap
  · intro Q hQ
    have hQ' : IsComponentOf Q (ggFix (ggInducedAut θ δ)) := by
      rw [ggFix_eq_ggAutFixedSubgroup]
      exact hQ
    have hlift := CFSG.StandardType.USixTwo.isComponentOf_lift_fix
      (π := π) (a := δ) (ab := ggInducedAut θ δ) hπ_surj hπ_ker hβα hQ'
    rw [ggFix_eq_ggAutFixedSubgroup] at hlift
    exact ⟨⁅Subgroup.comap π Q, Subgroup.comap π Q⁆, hlift.1, hlift.2⟩

end CFSG.StandardType.TablePThreeKG

end
