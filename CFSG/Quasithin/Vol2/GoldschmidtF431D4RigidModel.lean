module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4RigidComp
public import CFSG.Quasithin.EmptyFaithful.S1421QA18Rig
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F424

public noncomputable section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion


theorem amalgamRigid_d4 (hD : IsSimpleGroup D) : S1421QA18.AmalgamRigid d4H d4N := by
  refine ⟨d4H_sup_d4N, fun a₁ a₂ hag => ?_⟩
  obtain ⟨β, hβ1, hβ2, hβf⟩ := exists_d4_completion a₁ a₂ hag
  have : Finite D := finite_D'
  have hle : Nat.card D ≤ Nat.card d4Setting.Yb := by
    rw [card_d4Setting_Yb, card_trialityGroup8]
  have hs : β.IsSmall d4Setting.m :=
    isSmall_of_card_le d4Setting rfl d4_titsModel d4_hpoly β hβf hle
  obtain ⟨θ, hθ1, hθ2⟩ := f48_equiv_small d4Setting (k := 4) rfl d4_titsModel d4_hpoly
    (dvd_of_eq (card_d4Setting_Yb.trans rfl : Nat.card d4Setting.Yb = f48Order))
    d4Geom.d4_ptRigid (d4Geom.d4_toPerm_injective (act_injective hD)) β hβf hs
  let ρ₀ : D →* D := (β.φ1.range ⊔ β.φ2.range).subtype.comp (θ.symm.toMonoidHom.comp d4Phi)
  have hρ₀ : ∀ x, ρ₀ x = ((θ.symm (d4Phi x) : β.G0) : D) := fun x => rfl
  have hinj : Function.Injective ρ₀ := by
    intro x y h
    rw [hρ₀, hρ₀] at h
    exact d4Phi_injective (θ.symm.injective (Subtype.ext h))
  have hsurj : Function.Surjective ρ₀ := Finite.surjective_of_injective hinj
  refine ⟨MulEquiv.ofBijective ρ₀ ⟨hinj, hsurj⟩, fun x h => ?_, fun x h => ?_⟩
  · have e1 : d4Phi x = f1 (c := d4Setting.ι) (show d4Setting.α.G1 from ⟨x, h⟩) := rfl
    have e2 : θ.symm (d4Phi x) = f1 (c := β) (show d4Setting.α.G1 from ⟨x, h⟩) :=
      θ.symm_apply_eq.2 ((hθ1 _).trans e1.symm).symm
    show ((θ.symm (d4Phi x) : β.G0) : D) = _
    rw [e2]
    exact hβ1 ⟨x, h⟩
  · have e1 : d4Phi x = f2 (c := d4Setting.ι) (show d4Setting.α.G2 from ⟨x, h⟩) := rfl
    have e2 : θ.symm (d4Phi x) = f2 (c := β) (show d4Setting.α.G2 from ⟨x, h⟩) :=
      θ.symm_apply_eq.2 ((hθ2 _).trans e1.symm).symm
    show ((θ.symm (d4Phi x) : β.G0) : D) = _
    rw [e2]
    exact hβ2 ⟨x, h⟩

end CFSG.Quasithin.D4Hex
