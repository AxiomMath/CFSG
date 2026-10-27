module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Asm
public import CFSG.Quasithin.Background.C48SumBound
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4
public import CFSG.Quasithin.Vol2.Ch4Sec2T425H
public import CFSG.Quasithin.H13.L32NA3SQTK
public import CFSG.Quasithin.H13.VolIA36
public import CFSG.Quasithin.H13.VolIC129Holds
public import CFSG.Quasithin.Background.GoldschmidtTDC111Main
public import CFSG.Quasithin.Background.GoldschmidtTDC19
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.Vol2.GoldschmidtCor332
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213HatM
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213HatH
public import CFSG.Quasithin.Vol2.GoldschmidtC58Proved
public import CFSG.Quasithin.Vol2.GoldschmidtTD317
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKNoSum

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Assembly.LowTwoRank

theorem stmt4_2_13FF_of_steps_ff_centk (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (hSum : ∀ (G : Type) [Group G] [Finite G], C48SumBound G) (hNoBig : Conf4212NoSumBig)
    (h425 : Thm4_2_5)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h332 : Stmt3_3_2MTwo) (hKGf : KGHatA6M24He)
    (hKGg : KGG2BlockRu) (hKGr : KGG2BlockRuFF) (hNoSum2 : CentK.Conf4212NoSum2ND)
    (hJ4 : Conf4212NoJ4) :
    Stmt4_2_13FF :=
  stmt4_2_13FF_of_steps h36 h37 h38 h39 h48 h425
    (fun G _ _ T M L _ I H _ hy hIH c hO2 hcase => c.ff_or_orth_of_cases_centk h37 h38 h39 hC58 h317
      h332 hKGr hNoSum2 hNoBig hy hIH (fun m k hm hpsl hsum => hSum G H (pCoreOf 2 I) (H ⊓ M)
        (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ m k c.hypC28
        (lt_of_le_of_ne inf_le_left fun he => c.not_le (he ▸ inf_le_right))
        (fun h => hO2 (h.trans inf_le_right)) hm hpsl hsum) hcase)
    hKGf hKGg hJ4

theorem stmt4_2_13FF_of_open_centk
    (h48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (hSum : ∀ (G : Type) [Group G] [Finite G], C48SumBound G) (hNoBig : Conf4212NoSumBig)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hKGg : KGG2BlockRu) (hKGr : KGG2BlockRuFF) (hNoSum2 : CentK.Conf4212NoSum2ND)
    (hJ4 : Conf4212NoJ4) :
    Stmt4_2_13FF :=
  stmt4_2_13FF_of_steps_ff_centk VolI.a36ForSQTK_holds a3ForSQTK_holds.1 a3ForSQTK_holds.2.1
    a3ForSQTK_holds.2.2 h48 hSum hNoBig
    (thm4_2_5_of (fun G _ _ => ⟨VolI.a36ForSQTK_holds, a3ForSQTK_holds.1, a3ForSQTK_holds.2.1,
      a3ForSQTK_holds.2.2, VolI.asc129Statement_holds G, asc111Statement_holds G,
      asc19Statement_holds G, a3Orbits_of_a37_a38 a3ForSQTK_holds.1 a3ForSQTK_holds.2.1⟩) hC27)
    theoremC58_proved as317Sylow_proved Cor332.stmt3_3_2MTwo_holds (kgHatA6M24He_of
        (MulEquiv.refl _) CFSG.Sporadic.HeldB.heEquivP HatM.hatCoreAmb_m24 HatH.hatCoreAmb_he) hKGg hKGr
    hNoSum2 hJ4

end CFSG.Quasithin.H13.Ch4
