module

public import CFSG.RankThree.GF2n.Tim79a34SpRad
public import CFSG.RankThree.GF2n.Tim79a34TwLower
public import CFSG.RankThree.GF2n.Tim79a34TwZR
public import CFSG.RankThree.GF2n.Tim79a34TwWSplit
public import CFSG.RankThree.GF2n.Tim79a34CommPairing
public import CFSG.RankThree.GF2n.Tim79a34TwBound
public import CFSG.RankThree.GF2n.Tim79a34TwStruct

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic

theorem noInvCompStatement_holds : NoInvCompStatement :=
  fun n hn F _ _ _ hF a ha T S hT hS hsup hinf hinv =>
    no_invariant_complement_spRad hn hF ha hT hS hsup hinf hinv

theorem spRadFactsStatement_holds : SpRadFactsStatement :=
  fun n hn F _ _ _ hF a ha =>
    ⟨fun g hg h hh => spRad_comm hF ha hg hh, fun g hg => spRad_sq hF ha hg,
      spRad_card hF hn ha⟩

theorem commPairingStatement_holds : CommPairingStatement :=
  fun G _ _ A B Px K₀ m h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    card_le_of_commutator_pairing A B Px K₀ m h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem tim79a34TwoTwistedStatement_of_cited (hGr : GriessSpMultiplierStatement)
    (hGrE : GriessSpMultiplierExceptionStatement) (hS : Sp62CoverLiftStatement) :
    Tim79a34TwoTwistedStatement :=
  tim79a34TwoTwistedStatement_of_steps (twistedStruct_holds hGr hGrE hS) twistedWLower_holds
    twistedWSplit_holds (twistedZR_holds noInvCompStatement_holds)
    (twistedBound_holds spRadFactsStatement_holds commPairingStatement_holds)

end CFSG.RankThree.GF2n.Tim79a
