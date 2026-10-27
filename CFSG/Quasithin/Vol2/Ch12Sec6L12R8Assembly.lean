module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12Index
public import CFSG.Quasithin.Vol2.Ch12Sec6L12R4M22
public import CFSG.Quasithin.Vol2.Ch12Sec6L12R7cHSB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

theorem lemma12_6_12_of_corrected (h1222 : Stmt12_2_2)
    (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat) (hD2 : Lemma12_6_4_5)
    (hD11 : Lemma12_6_11) (h61 : Lemma12_6_1) (h331 : Stmt3_3_1) (ha : FactKv1262aTwo)
    (hb : FactM22HexadAut) (hHS1 : FactHSNormLv) (hHS2 : FactHSE16Outer) : Lemma12_6_12 := by
  intro G _ _ T L V _ F v Kv S hC hq
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hKG : Kv ≤ S126T2.Gv v := le_of_mem_cComp hC.cComp
  have hLK : S126T2.Lv L v ≤ Kv := hC.lv_le
  obtain ⟨-, hVe⟩ := V_facts h1222 hH
  have hVvO := S126T2.Vv_le_pCoreOf h1222 hH hv
  have hcz := S126T2.center_Kv_eq h1222 h36 hC hq
  have hlist : CFSG.Milestones.SQTKSimpleList (↥Kv ⧸ Subgroup.center ↥Kv) :=
    CFSG.QuasithinUnique.Ch1.sqtkSimpleList_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hcz)
      (S126T2.a23List_Kv h1222 h36 hC)
  have hTv : S126T2.Tv T v ≤ Subgroup.normalizer (S126T2.Lv L v : Set G) := fun t ht =>
    normalizer_le_normalizer_perfectCore _ (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hH.hyp.normalizes ht.1, Subgroup.le_normalizer ht.2⟩)
  have hidx : (S126T2.Tv T v ⊓ Kv).relIndex (S ⊓ Kv) ≤ 2 :=
    S126T2.relIndex_Tv_inf_Kv_le_two h1222 hD2 hC hq
  have hEl : IsElemAbelian 2 (S126T2.Vv L V v) :=
    ⟨⟨⟨fun a b => Subtype.ext (show (a : G) * b = b * a from
      congrArg (fun z : ↥V => (z : G)) (hVe.1.is_comm.comm
        ⟨a, S126T2.Vv_le_V hH v a.2⟩ ⟨b, S126T2.Vv_le_V hH v b.2⟩))⟩⟩,
      fun x hx => hVe.2 x (S126T2.Vv_le_V hH v hx)⟩
  obtain ⟨hdisj, hcent⟩ := ha G Kv (S ⊓ Kv) (S126T2.Tv T v ⊓ Kv) (S126T2.Lv L v)
    (S126T2.Vv L V v) hq hlist (A4.isSylowTwoOf_inf_normal hC.sylow hKG hC.normal)
    (inf_le_inf_right _ hC.tv_le) (inf_le_left.trans hTv) hidx hLK (perfectCore_perfect _)
    ⟨S126T2.psiLv h1222 F hH hv hβ, S126T2.o2Iso_Lv h1222 F hH hv hβ⟩ hVvO hEl
    (S126T2.card_Vv h1222 hH hv hβ) (S126T2.Lv_le_normalizer_Vv hH v)
    (S126T2.comm_Vv_Lv h1222 hH hv) (S126T2.card_Vv_inf h1222 hH hv hβ)
  rcases hdisj with eM | eH
  · exact m22_branch h1222 h36 hb hC hq eM
  · by_cases hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥
    · exact S126T2.hs_branch_B h1222 h36 hHS2 hC hq hcent eH hZ
    · exact S126T2.hs_branch_A h1222 h36 h331 h61 hD11 hHS1 hC hq hcent eH hZ

end CFSG.Quasithin.H13
