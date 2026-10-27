module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1LieOrd
public import CFSG.HardMathSupport.Dickson.Bal207.Fam3D42
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Crit
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Shape

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section D42




theorem rowOf427_d42
    : ∀ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 → q.exponent = 1 →
    RowOf427 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group := by
  intro q hv hq2 hq1
  refine rowOf427_of_noCfgS fun S _ _ _ _ ⟨e⟩ => ?_
  obtain ⟨K₃, _, _, σ, hK₃, hσ, -, ⟨eK⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  obtain ⟨φ8, hcard⟩ := CFSG.HardMathSupport.Seitz.TrialityEven.exists_equiv_trialityGroup8
    hq2 hq1 hv
  obtain ⟨ψ8⟩ := CFSG.HardMathSupport.Dickson.Bal207.Fam3D42.nonempty_mulEquiv_d4P φ8 hcard
  rw [hq2, hq1] at hK₃ hσ
  let e' : S ≃* graphFixedRootGroup TwistTag.D4 K₃ σ.toRingHom := e.trans eK
  haveI : Finite (graphFixedRootGroup TwistTag.D4 K₃ σ.toRingHom) := Finite.of_equiv S e'.toEquiv
  refine ⟨NoCfgS427.of_mulEquiv e' (noCfgS427_of_compShape not_isA5Type_of_g28CompType
    fun β hβ hβ1 => CFSG.HardMathSupport.Dickson.Bal207.Fam3D42.compShape_triD4_two hK₃ σ hσ
      (eK.symm.trans ψ8) β hβ hβ1), noONS427_of_card ?_⟩
  rw [Nat.card_congr (e.trans φ8).toEquiv, hcard]
  norm_num

end D42

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
