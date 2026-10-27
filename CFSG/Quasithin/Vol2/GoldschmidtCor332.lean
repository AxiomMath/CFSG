module

public import CFSG.Quasithin.Vol2.Ch3Sec3Cor332
public import CFSG.Quasithin.H13.GoldschmidtU3ThreeCase
public import CFSG.Quasithin.Vol2.GoldschmidtCor332Bender
public import CFSG.Quasithin.Vol2.GoldschmidtCor332M11
public import CFSG.Quasithin.Vol2.GoldschmidtCor332L33
public import CFSG.Quasithin.Vol2.GoldschmidtCor332L2p

public section

namespace CFSG.Quasithin.H13.Cor332

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.U3

theorem twoLocalsSolvable_of_uniqueSmallModel
    {G : Type} [Group G] (h : UniqueSmallModel G) : TwoLocalsSolvable G := by
  rcases h with ⟨p, hp, hp7, hpF, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact TwoLocalsSolvable.of_mulEquiv e (twoLocalsSolvable_psl2 hp hp7 hpF)
  · exact TwoLocalsSolvable.of_mulEquiv e twoLocalsSolvable_psl33
  · exact TwoLocalsSolvable.of_mulEquiv e twoLocalsSolvable_catalogM11

theorem stmt3_3_2MTwo_of
    (h3 : UniqueThreeCaseModelReduction) : Stmt3_3_2MTwo := by
  intro G _ _ T hs hnab hK hT L hL _
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  obtain ⟨M, hMmax, hLTM⟩ := CFSG.Quasithin.exists_inM_of_pCoreOf_ne_bot hL.1.2.2.2
  have hTM : T ≤ M := le_sup_right.trans hLTM
  have huniq : ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → T ≤ M' → M' = M := by
    intro M' hM' hTM'
    by_contra hne
    exact hno ⟨M', M, hne, hM', hMmax, hTM', hTM⟩
  have hset : UniqueSetting G T M :=
    { simple := hs
      nonabelian := hnab
      qtke := qtkeCore_of_cat hnab hK
      sylow := CFSG.Quasithin.H13.U3.isSylowTwoOf_top_of_quasithin hT
      maxLocal := hMmax
      le := hTM
      unique := huniq }
  have hsolvG : TwoLocalsSolvable G := by
    rcases h3 G T M hset with hB | hS
    · exact twoLocalsSolvable_of_fusionIsBenderGroup hB
    · exact twoLocalsSolvable_of_uniqueSmallModel hS
  obtain ⟨P, hP1, hP2, hMP⟩ := hMmax.1
  have hMsolv : Group.IsSolvable M := hsolvG P M hP1 hP2 (le_of_eq hMP)
  have hLM : L ≤ M := le_sup_left.trans hLTM
  have hLsolv : Group.IsSolvable L :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLM)
  obtain ⟨hL1, hLperf, -⟩ := hL.1.2.1
  have : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr hL1
  have : Group.IsPerfect L := (Subgroup.isPerfect_iff (H := L)).mpr hLperf
  exact Group.IsPerfect.not_isSolvable L hLsolv

theorem stmt3_3_2MTwo_holds
    : Stmt3_3_2MTwo :=
  stmt3_3_2MTwo_of uniqueThreeCaseModelReduction_holds

end CFSG.Quasithin.H13.Cor332
