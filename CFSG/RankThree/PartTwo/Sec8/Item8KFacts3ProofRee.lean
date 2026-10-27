module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res11ProofOmegaRee
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofReeInv

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LieType.Chevalley CFSG.LieType.Ree


theorem kF89ReeFixInv_holds : KF89ReeFixInv := by
  intro k hk K _ _ _ hK τ w hτ3 hτin hτw hw3 _
  obtain ⟨β, hβ, hcoset⟩ := KFacts.largeRee_order_three_inFieldCoset hk hK hτ3 hτin
  obtain ⟨x, hx⟩ := CFSG.RankThree.PartOne.RF4.largeReeOrderThreeFieldConj k K hK β hβ τ hτ3
    hcoset
  obtain ⟨b, _, hcard, -, ι, hιinj, hιrange⟩ :=
    Item8KFactsProof.exists_fixedPoints_reeGammaFieldAut hK β hβ
  have : Finite (fixSubfield β) := Subtype.finite
  set c := MulAut.conj x with hc
  have hτz : ∀ z, τ z = c (ReeTag.F4.reeGammaFieldAut K k β (c⁻¹ z)) := by
    intro z
    rw [hx]
    rfl
  have hcc : ∀ z, c⁻¹ (c z) = z := fun z => by
    simp only [MulAut.inv_apply, MulEquiv.symm_apply_apply]
  have hw' : ReeTag.F4.reeGammaFieldAut K k β (c⁻¹ w) = c⁻¹ w := by
    have h1 := hτw
    rw [hτz] at h1
    calc ReeTag.F4.reeGammaFieldAut K k β (c⁻¹ w) =
        c⁻¹ (c (ReeTag.F4.reeGammaFieldAut K k β (c⁻¹ w))) := (hcc _).symm
      _ = c⁻¹ w := by rw [h1]
  obtain ⟨u, hu⟩ := (hιrange (c⁻¹ w)).mpr hw'
  have hu3 : u ^ 3 = 1 := hιinj (by rw [map_pow, hu, ← map_pow, hw3, map_one, map_one])
  obtain ⟨v₀, hv₀1, hv₀2, hv₀u⟩ :=
    Item8KFacts3Ree.exists_involution_commute_of_pow_three b (fixSubfield β) hcard u hu3
  refine ⟨c (ι v₀), fun h1 => hv₀1 (hιinj ?_), ?_, ?_, ?_⟩
  · apply c.injective
    rw [h1, map_one, map_one]
  · rw [← map_pow, ← map_pow, hv₀2, map_one, map_one]
  · rw [hτz, hcc, (hιrange (ι v₀)).mp ⟨v₀, rfl⟩]
  · have hw : w = c (ι u) := by
      rw [hu]
      simp only [MulAut.inv_apply, MulEquiv.apply_symm_apply]
    have h1 := congrArg (fun z => c (ι z)) hv₀u
    simp only [map_mul] at h1
    rw [hw]
    exact h1

end CFSG.RankThree.PartTwo.Sec8
