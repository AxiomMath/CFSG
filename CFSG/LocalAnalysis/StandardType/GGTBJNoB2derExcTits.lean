module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derA1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapTwF4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Tits
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3ThreeSolv

public section

namespace CFSG.StandardType.S2MathAs4B2der1822

open CFSG CFSG.Assembly CFSG.LieType.Ree
open CFSG.Sporadic.Schreier.Tits (titsD)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem nonempty_recipeTwF4_zero_equiv_titsD {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    Nonempty (LargeEvenCenterQuot (LargeEvenTwF4H 0 K) ≃* titsD) := by
  haveI : CharP K ReeTag.F4.prime :=
    CFSG.StandardType.charP_two_of_card (m := 1) (by rw [hK, pow_one])
  haveI : Fact (Nat.card K = 2) := ⟨hK⟩
  obtain ⟨eT⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GField.nonempty_titsQuot_equiv hK
  exact ⟨eT.trans CFSG.Sporadic.Schreier.Tits.titsDerivedIso⟩

theorem noB2derInput_twF4der : SimpleNoB2derInput fun lab => lab.tag = .twF4der := by
  intro lab hlab hP
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hP hlab
  subst hP
  obtain ⟨-, hl, hn⟩ := hlab
  dsimp only at hl hn
  subst hl
  subst hn
  intro Q hQ
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  have hK2 : Nat.card K = 2 := by simpa using hK
  obtain ⟨eD⟩ := nonempty_recipeTwF4_zero_equiv_titsD hK2
  have hZ : Subgroup.center titsD = ⊥ := CFSG.Sporadic.Schreier.Tits.titsD_center
  intro φ hφ1 hφ3 _ J hJ _
  have hγ3 : MulAut.congr eD φ ^ 3 = 1 := by rw [← map_pow, hφ3, map_one]
  have hγ1 : MulAut.congr eD φ ≠ 1 := fun h =>
    hφ1 ((MulAut.congr eD).injective (by rw [h, map_one]))
  have hsolv := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isSolvable_fixSubgroup_titsD
    hZ hγ3 hγ1
  have hfix := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isSolvable_fixSubgroup_of_congr
    eD hsolv
  have hfix' : ggFixSub φ = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup φ :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hfix'] at hJ
  exact CFSG.StandardType.ResU3Three.not_isComponentOf_of_isSolvable hfix hJ

end CFSG.StandardType.S2MathAs4B2der1822

end
