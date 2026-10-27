module

public import CFSG.LocalAnalysis.UniquenessCase.UC6R77E3b
public import CFSG.LocalAnalysis.UniquenessCase.UC6R3
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs
import CFSG.LocalAnalysis.UniquenessCase.UC6S9
import CFSG.LocalAnalysis.UniquenessCase.UC6K47d
import CFSG.LocalAnalysis.UniquenessCase.UC6Star36b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)

variable {G : Type} [Group G] [Finite G]

theorem sixNineAt_of_R6_9 {D : UC22.Data G} (h69 : R6_9 D) (hsub : D.sig ⊆ D.sig1) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {X : Subgroup G} (hXM : X ≤ D.M) (hX : IsPGroup r X)
    (hexp : ∀ x ∈ X, x ^ r = 1) (hcl : ⁅⁅X, X⁆, X⁆ = ⊥) : UC6R77.SixNineAt D.M X r := by
  haveI : Fact r.Prime := ⟨hr⟩
  intro E hEM hEel hEcard hΓ x hxX ⟨y, hyX, hxy⟩ hEN
  by_contra hN
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hxy (by rw [one_mul, mul_one])
  have hxo : orderOf x = r := orderOf_eq_prime (hexp x hxX) hx1
  have hZ2 : zpowers x ≤ (Subgroup.upperCentralSeries ↥X 2).map X.subtype := by
    rw [zpowers_le]
    refine ⟨⟨x, hxX⟩, ?_, rfl⟩
    refine (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).2 fun g => ?_
    rw [Subgroup.upperCentralSeries_one, mem_center_iff]
    intro w
    apply Subtype.ext
    have hc : (x * (g : G) * x⁻¹ * (g : G)⁻¹ : G) ∈ centralizer (X : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp hcl (commutator_mem_commutator hxX g.2)
    exact (mem_centralizer_iff.1 hc) w w.2
  obtain ⟨-, -, h3⟩ := h69 hsub r hr hr2 E hEM hEel hEcard hΓ r (zpowers x) hr
    ((zpowers_le.mpr hxX).trans hXM) (by rw [Nat.card_zpowers, hxo]) hEN hN X hXM hX
    (zpowers_le.mpr hxX)
  obtain ⟨z, hz, hzx⟩ := h3 hZ2 (mem_zpowers x)
  have hzx' : (z : G) = x := hzx
  apply hxy
  have h := congrArg Subtype.val (mem_center_iff.1 hz ⟨y, hyX⟩)
  rw [coe_mul, coe_mul, hzx'] at h
  exact h.symm

theorem r77E4_dataOfSetup4 (hSE : StronglyEmbeddedFive) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (h3 : 3 ∉ uniqueFourBeta G)
    (h69 : R6_9 (dataOfSetup4 hS hU S)) : UC22.F07.R77E4 (dataOfSetup4 hS hU S) := by
  intro hsub p hp _ hsp r hr hr2 hrσ X hXM hX hnc hexp hcl h3'
  haveI : Fact p.Prime := ⟨((dataOfSetup4 hS hU S).sig_prime p hp).1⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hpr : p ≠ r := fun h => hrσ (h ▸ hp)
  have hrank : CFSG.Open.pRank r X ≤ 3 :=
    (CFSG.SectionRank.pRank_mono hr.one_lt hXM).trans
      (pRank_le_three_of_not_mem_sigma hU S.maxLocal hr hr2 hrσ)
  exact UC6R77.rankThreeGamma_le_of_three_lt_pRank hr2 hpr hsp
    (conclusion76_dataOfSetup4 hSE hS hU S h3 hp hsp)
    (sixNineAt_of_R6_9 h69 hsub hr hr2 hXM hX hexp hcl) hrank hXM hX hnc hexp hcl h3'

theorem r77Use_dataOfSetup4 (hSE : StronglyEmbeddedFive) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (h3 : 3 ∉ uniqueFourBeta G)
    (h69 : R6_9 (dataOfSetup4 hS hU S)) : UC22.F07.R77Use (dataOfSetup4 hS hU S) :=
  ⟨r77E2_dataOfSetup4 hSE hS hU S h3, r77E4_dataOfSetup4 hSE hS hU S h3 h69⟩

theorem r77Use_dataOfSetup4_of_K36 (hSE : StronglyEmbeddedFive) (hK36 : UCK.K36)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (hC : TheoremCAt S.M) (h3 : 3 ∉ uniqueFourBeta G) :
    UC22.F07.R77Use (dataOfSetup4 hS hU S) :=
  r77Use_dataOfSetup4 hSE hS hU S h3
    (r6_9_of_K47 hS hU S k47_uc6 hC
      (PartTwo.r6_7_of_K36_at (dataOfSetup4 hS hU S) hK36 (r6_3_dataOfSetup4 hS hU S hC)
        (star36_holds G hS hU S hMS hC)))

end CFSG.LocalAnalysis.UniquenessCase.UC6
