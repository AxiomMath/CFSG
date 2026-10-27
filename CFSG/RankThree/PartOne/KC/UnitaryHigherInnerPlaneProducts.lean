module

public import CFSG.RankThree.PartOne.KC.UnitaryRigidityNonsplit
public import CFSG.RankThree.PartOne.KC.UnitaryHigherInnerPlaneProductsOne

public section

namespace CFSG.RankThree.PartOne

open Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryGlue
  CFSG.RankThree.PartOne.KCUnitaryLines CFSG.RankThree.PartOne.KCUnitaryNonsplit

theorem higher_unitary_inner_plane_products_trivial :
    HigherUnitaryInnerPlaneProductsTrivial := by
  intro ℓ f n p K _ h hp hpℓ hn hnp hne B hB A hAH hA hAcard
  by_cases hpq : p ∣ ℓ ^ f + 1
  · exact higher_unitary_inner_plane_products_trivial_of_dvd h hp hpℓ hn hnp hne hpq B hB A hAH hA
      hAcard
  have hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1 := by
    intro c _ hcn hcp
    have hcop : Nat.Coprime n p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt (by omega) hnp)).symm
    have : c ^ Nat.gcd n p = 1 := pow_gcd_eq_one.mpr ⟨hcn, hcp⟩
    rwa [hcop, pow_one] at this
  obtain ⟨⟨Ahat, hAhat, -⟩, hrest⟩ :=
    higher_unitary_inner_plane_commuting_lift_and_kernel_decomposition h hp hpℓ hn hnp hne A hAH hA
      hAcard
  obtain ⟨-, hdec, -, -, he2, hq2, hq3⟩ := hrest Ahat hAhat
  have he : 1 < ordNegQ ℓ f p := by
    have h1 : ordNegQ ℓ f p ≠ 1 := fun h1 => hpq ((ordNegQ_eq_one_iff hp).mp h1)
    have := pos_ordNegQ (f := f) hp hpℓ h.prime
    omega
  have S : PlaneSetup h n p Ahat := ⟨hn, hne, hp, hpℓ, hZp, hAhat.1, hAhat.2.1⟩
  have F : NonsplitFacts h n p Ahat := ⟨hdec, he, he2, hq2, hq3⟩
  refine plane_products_trivial_of_lift S hAhat B ?_ ?_
  · intro a haA ha1 x hx hxa hxp
    obtain ⟨hall, -, hlocal, -⟩ :=
      higher_unitary_inner_plane_all_parameter_local_core_centralization h hn hnp hp hpℓ hne B hB A
        Ahat hAhat a haA x hx hxa hxp
    exact ⟨fun i => (hall i).2.2.2.2, hlocal⟩
  · intro β hcent hblock
    exact rigidity_of_nonsplit F S β hcent hblock

end CFSG.RankThree.PartOne
