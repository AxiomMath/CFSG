module

public import CFSG.Quasithin.EmptyFaithful.F112SAut
public import CFSG.Quasithin.EmptyFaithful.F112RH
public import CFSG.Quasithin.Recognition.CertTwoF4AmalgamLocalFinal

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152N CFSG.Quasithin.S152N2
open CFSG.Quasithin.F112S CFSG.Sporadic.Schreier.Tits

theorem titsRankLeFive_of_check
    (h : TitsRankCheck) : TitsRankLeFive := by
  intro E hE
  let f : quasithinTits →* Equiv.Perm (Fin 1755) :=
    titsD.subtype.comp quasithinTitsEquivD.toMonoidHom
  have hinj : Function.Injective f :=
    titsD.subtype_injective.comp quasithinTitsEquivD.injective
  have hle : E.map f ≤ titsD := by
    rintro _ ⟨x, -, rfl⟩
    exact (quasithinTitsEquivD x).2
  have := card_le_titsD h hle (isElemAbelian_map' f hE)
  rwa [Subgroup.card_map_of_injective hinj] at this

theorem twistedF4RankLeFive_of_check
    (h : TitsRankCheck) :
    TwistedF4RankLeFive := by
  intro E hE
  let e : MulAut quasithinTits ≃* twoF4M := twoF4AutEquiv titsOutBound
  let f : MulAut quasithinTits →* Equiv.Perm (Fin 1755) := twoF4M.subtype.comp e.toMonoidHom
  have hinj : Function.Injective f := twoF4M.subtype_injective.comp e.injective
  have hle : E.map f ≤ twoF4M := by
    rintro _ ⟨x, -, rfl⟩
    exact (e x).2
  have := card_le_twoF4M h hle (isElemAbelian_map' f hE)
  rwa [Subgroup.card_map_of_injective hinj] at this

theorem stageRankNotTwo_of_basic_inputs_ce28
    (hB42 : AsB42)
    (h113 : StageLemma14113) (h1416 : StageLemma1416)
    (h1515 : StageLemma1515CE) (h157 : StageLemma1517) (h1518 : StageLemma1518)
    (h1519 : StageLemma1519) (h15111 : StageLemma15111) (h15112 : StageLemma15112)
    (h15113 : StageLemma15113) (h15114 : StageLemma15114) (h15115 : StageTheorem15115)
    (hF204 : He9.Input15204F112) (hD204 : He9.Input15204Dichotomy)
    (hB204 : He9.Input15204BranchB)
    (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129StatementUsed G)
    (h37 : A37ForSQTK) (h39 : A39ForSQTK) (h134 : EmptyFaithfulMultiple.Prop134E9He)
    (hA3 : ∀ (G : Type) [Group G] [Finite G], A3Orbits G) (hlist : Lemma115_3_List)
    (hInsp12 : Insp15212) (h122 : Lemma122A)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) (hcover : AsA36NoOddCover)
    (h51 : AsB51) (hI16 : AsI16Cover) (hA8 : AsI16CoverA8) (kR : Input21Rank) (kL : ThreeRankBlocks)
    (kP : Input21ProperRank) (kB : SolvOvergroupsInBorel)
    (hno : Insp15224NoF2) (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) (hc : Cent3RankF2)
    (hcoreW : He12.Tail15215CoreW) (hHeMod : HeNoSmallCommutatorModule)
    (hParGood : Insp15227ParGood)
    (hlift : Input15209Lift) (hGoldP : F6.GoldschmidtCharTwoLargePair.{0})
    (hHay : HayashiFiveThree) (hrank : TitsRankCheck)
    (hR : Input15208F53Res) : StageRankNotTwo :=
  stageRankNotTwo_of_basic_inputs_ce27 hB42 h113 h1416 h1515 h157 h1518 h1519 h15111 h15112
    h15113 h15114 h15115 hF204 hD204 hB204 h129 h37 h39 h134 hA3 hlist hInsp12 h122 hC129 hC27 hcover h51 hI16 hA8 kR kL kP kB hno hF318
    h36 h38 hK hc hcoreW hHeMod hParGood hlift hGoldP hHay (titsRankLeFive_of_check hrank)
    (twistedF4RankLeFive_of_check hrank) hR

end CFSG.Quasithin
