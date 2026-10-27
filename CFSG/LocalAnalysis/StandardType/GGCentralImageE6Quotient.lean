module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourInputs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTyLabelAux
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.LieType.Universal
  CFSG.LocalAnalysis.GLTheoremA CFSG.StandardType.S2MathFi1035Pos


theorem ggCentralImage_E6_four_labelOf {G : Type} [Group G] {X : Subgroup G}
    (hX : GGCentralImage .E6 0 2 X) : LabelOf X ⟨.E6, 0, 2⟩ := by
  obtain ⟨ψ, hadm, hker, hrange⟩ := hX
  have hU : CFSG.Open.IsQuasisimple (ggU .E6 0 2).K ∧
      LieModel ((ggU .E6 0 2).K ⧸ Subgroup.center (ggU .E6 0 2).K) .E6 0 2 2 := by
    exact CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .E6 0 2 2 Nat.prime_two
      (by trivial) hadm
  letI : Group.IsPerfect (ggU .E6 0 2).K := ⟨hU.1.1⟩
  subst hrange
  have hperf : commutator ↥ψ.range = ⊤ :=
    (Group.IsPerfect.ofSurjective (MonoidHom.rangeRestrict_surjective ψ)).commutator_eq_top
  have hmodel : LieModel (↥ψ.range ⧸ Subgroup.center ↥ψ.range) .E6 0 2 2 :=
    RCKRP.irg_lieModel_quot (by simp [GGPosTag]) hadm ψ rfl hker
  have hm := Canonical.largeEvenMarking_of_lieModel_centerQuot hperf hmodel
  change LargeEvenMarking ↥ψ.range (fun lab _ _ _ _ _ => lab = ⟨.E6, 0, 2⟩)
  obtain ⟨hp, lab, hvalid, hraw⟩ := hm
  refine ⟨hp, lab, hvalid, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, ht, hr, hc, hd⟩
  refine ⟨hs, hna, θ, ?_⟩
  rcases lab with ⟨tag, rank, n⟩
  cases tag <;> simp_all [markTag, markDeg, LargeEvenInLambda2]
  all_goals split_ifs at ht <;> simp_all

end CFSG.StandardType
