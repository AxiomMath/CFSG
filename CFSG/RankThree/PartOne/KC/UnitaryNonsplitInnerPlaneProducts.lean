module

public import CFSG.RankThree.PartOne.KC.UnitaryPlaneStatements
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneProductsGlue
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityNonsplit
public import CFSG.RankThree.PartOne.KC.UnitaryNonsplitInnerPlaneLift
public import CFSG.RankThree.PartOne.KC.UnitaryNonsplitInnerPlaneCentralization

public section

namespace CFSG.RankThree.PartOne

open Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryGlue
  CFSG.RankThree.PartOne.KCUnitaryLines CFSG.RankThree.PartOne.KCUnitaryNonsplit

theorem unitary_nonsplit_inner_plane_products_trivial :
    UnitaryNonsplitInnerPlaneProductsTrivial := by
  intro ℓ f n p K _ h hp hp3 hpℓ hpq hn hne B hB A hAH hA hAcard
  have hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1 := by
    intro c hc _ hcp
    have h1 : c ^ (ℓ ^ f + 1) = 1 := (pow_succ_eq_one_iff_norm h c).mpr hc
    have h2 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
    rcases (Nat.dvd_prime hp).mp h2 with h3 | h3
    · exact orderOf_eq_one_iff.mp h3
    · exact absurd (h3 ▸ orderOf_dvd_of_pow_eq_one h1) hpq
  obtain ⟨⟨Ahat, hAhat, -⟩, hrest⟩ :=
    unitary_nonsplit_all_dimension_inner_plane_lift_and_kernel_decomposition h hp hp3 hpℓ hpq hn
      hne A hAH hA hAcard
  obtain ⟨-, he, hdec, he2, hq2, hq3⟩ := hrest Ahat hAhat
  have S : PlaneSetup h n p Ahat := ⟨hn, hne, hp, hpℓ, hZp, hAhat.1, hAhat.2.1⟩
  have F : NonsplitFacts h n p Ahat := ⟨hdec, he, he2, hq2, hq3⟩
  refine plane_products_trivial_of_lift S hAhat B ?_ ?_
  · intro a haA ha1 x hx hxa hxp
    obtain ⟨hall, -, hlocal, -⟩ :=
      unitary_nonsplit_all_dimension_inner_plane_local_core_centralization h hp hp3 hpℓ hpq hn hne
        B hB A Ahat hAhat a haA x hx hxa hxp
    exact ⟨fun i => (hall i).2.2.2.2, hlocal⟩
  · intro β hcent hblock
    exact rigidity_of_nonsplit F S β hcent hblock

end CFSG.RankThree.PartOne
