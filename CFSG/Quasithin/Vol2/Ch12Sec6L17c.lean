module

public import CFSG.Quasithin.Vol2.Ch12Sec6L17b
public import CFSG.Quasithin.Vol2.Ch12Sec6L17Stmt
public import CFSG.Quasithin.Vol2.KGFact12617
public import CFSG.Quasithin.Vol2.KGFact12617List
public import CFSG.Quasithin.Vol2.Ch12Sec6L14d

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem mk_eq_mk_pe01 {c : ↥(coreMod 8)} (hc : Multiplicative.toAdd (c : PermMod 8) = vSix) :
    (QuotientGroup.mk c : D8) = QuotientGroup.mk (pe 0 1) := by
  have h1 : c * (pe 0 1)⁻¹ = S126FE.eOm := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    have hci := congrFun hc i
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, toAdd_mul, toAdd_inv, Pi.add_apply,
      Pi.neg_apply] at hci ⊢
    rw [hci]
    fin_cases i <;> decide
  have h2 : (QuotientGroup.mk (c * (pe 0 1)⁻¹) : D8) = 1 :=
    (S126FE.mk_eq_one_iff _).2 (Or.inr h1)
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h2
  exact h2

theorem v_mem_Vv (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) : v ∈ Vv L V v := by
  have hx : vSix ∈ c01 := by decide
  obtain ⟨y, hy, hyc⟩ := exists_coordV_eq h1222 hH hv hβ hx
  have hyV := Vv_le_V hH v hy
  obtain ⟨c, -, hcy, hβc⟩ := coordV_spec h1222 hH hv hβ hyV hy
  have hyv : F.β ⟨y, hyV⟩ = F.β ⟨v, hv⟩ := by
    rw [hβc, hβ, mk_eq_mk_pe01 (hcy.trans hyc)]
  have h1 : F.β (⟨y, hyV⟩ * (⟨v, hv⟩ : ↥V)⁻¹) = 1 := by
    rw [map_mul, map_inv, hyv, mul_inv_cancel]
  have h2 := (F.β_ker _).1 h1
  have h3 : y * v⁻¹ ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨V.mul_mem hyV (V.inv_mem hv), h2⟩
  rw [hZ, Subgroup.mem_bot, mul_inv_eq_one] at h3
  rw [h3] at hy
  exact hy

theorem ne_bot_of_moved (h1222 : Stmt12_2_2) {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hC : Ctx1262 F v Kv S) {w : G} (hw : w ∈ Vv L V v ⊓ Subgroup.centralizer (Lv L v : Set G))
    (hwK : w ∉ Subgroup.centralizer (Kv : Set G)) : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := by
  intro hZ
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hvV := v_mem_Vv h1222 hH hv hβ hZ
  have hvC : v ∈ Subgroup.centralizer (Lv L v : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_singleton_iff.1 (Lv_le_Gv L v hl))
  have hcard := card_Vv_inf h1222 hH hv hβ
  have hv1 : v ≠ 1 := v_ne_one F hv hβ
  have hw' : w = 1 ∨ w = v := by
    by_contra hne
    push Not at hne
    have h3 : ({1, v, w} : Set G) ⊆
        ((Vv L V v ⊓ Subgroup.centralizer (Lv L v : Set G) : Subgroup G) : Set G) := by
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact ⟨hvV, hvC⟩
      · exact hw
    have h4 := Set.ncard_le_ncard h3 (Set.toFinite _)
    rw [Set.ncard_insert_of_notMem (by simp [Ne.symm hv1, Ne.symm hne.1]),
      Set.ncard_pair (Ne.symm hne.2)] at h4
    have h5 : ((Vv L V v ⊓ Subgroup.centralizer (Lv L v : Set G) : Subgroup G) :
        Set G).ncard = 2 := by
      rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hcard]
    omega
  apply hwK
  rcases hw' with rfl | rfl
  · exact Subgroup.one_mem _
  · rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.1 (le_of_mem_cComp hC.cComp hk)

theorem isSylowTwoOf_S_top (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V)
    {v : G} {S : Subgroup G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    (hTvS : Tv T v ≤ S) (hS2 : IsPGroup 2 ↥S) (hS4 : (Tv T v).relIndex S = 4) :
    CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
  have hT4 : (Tv T v).relIndex T = 4 := relIndex_Tv h1222 F hH hv hβ
  have hcS := Subgroup.relIndex_mul_card (Tv T v) S
  rw [inf_eq_left.2 hTvS, hS4] at hcS
  have hcT := Subgroup.relIndex_mul_card (Tv T v) T
  rw [inf_eq_left.2 (show Tv T v ≤ T from inf_le_left), hT4] at hcT
  have hST : Nat.card ↥S = Nat.card ↥T := by rw [← hcS, ← hcT]
  have hT := isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow (le_top : T ≤ ⊤)
  refine ⟨le_top, hS2, ?_⟩
  have h1 := (S.subgroupOf ⊤).card_mul_index
  have h2 := (T.subgroupOf ⊤).card_mul_index
  have e1 : Nat.card ↥(S.subgroupOf ⊤) = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv
  have e2 : Nat.card ↥(T.subgroupOf ⊤) = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv
  have hpos : 0 < Nat.card ↥S := Nat.card_pos
  have hidx : (S.subgroupOf ⊤).index = (T.subgroupOf ⊤).index := by
    rw [e1] at h1
    rw [e2, ← hST] at h2
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  rw [hidx]
  exact hT.2.2

end S126T2

theorem lemma12_6_17_of (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    (h56 : AsB56) (hD2 : Lemma12_6_4_5) (hD5 : Lemma12_6_11) (hD7 : Lemma12_6_13)
    (hD9 : Lemma12_6_15) (hD10 : Lemma12_6_16) (hK3 : FactKv12617) (hM1 : FactUv12617) :
    Lemma12_6_17 := by
  intro G _ _ T L V _ F v Kv S hC hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hyp := hH.hyp
  have hRR := S126T2.Rsec_eq_Rv h1222 hD2 hC hN
  have hRU := S126T2.not_Rsec_le_centralizer h1222 hD2 hD5 hD7 hC hN
  obtain ⟨⟨-, hO⟩, -, -⟩ := hD7 G T L V F v Kv S hC
  obtain ⟨-, hRvR, hTvS4, -, -, hOR, -, -, hReq⟩ := hD2 G T L V F v Kv S hC
  set U := Usec Kv S with hU
  set X := Kv ⊔ S with hX
  have hUe := S126T2.isElemAbelian_Usec Kv S
  have : IsMulCommutative ↥U := hUe.1
  have hXU : X ≤ Subgroup.normalizer (U : Set G) :=
    (le_normalizer_pCoreOf 2 _).trans (S126T2.normalizer_le_normalizer_Usec Kv S)
  have hKvU : Kv ≤ Subgroup.normalizer (U : Set G) := S126T2.Kv_le_normalizer_Usec hC
  have hSU : S ≤ Subgroup.normalizer (U : Set G) := (le_sup_right : S ≤ X).trans hXU
  have hLvU : S126T2.Lv L v ≤ Subgroup.normalizer (U : Set G) := hC.lv_le.trans hKvU
  have hRS : Rsec L Kv S v ≤ S := hReq ▸ centralizerSection_le_left _ _ _
  have hRU' : Rsec L Kv S v ≤ Subgroup.normalizer (U : Set G) := hRS.trans hSU
  have hSK : S ≤ Subgroup.normalizer (Kv : Set G) := hC.sylow.1.trans hC.normal
  have hKS : X ≤ S126T2.Gv v := sup_le (le_of_mem_cComp hC.cComp) hC.sylow.1
  have hSX : CFSG.QuasithinUnique.IsSylowTwoOf S X :=
    A4.isSylowTwoOf_mono hC.sylow le_sup_right hKS
  have hred := S126T2.isTwoReducedIn_Usec hD7 hC
  have hO2 : pCoreOf 2 (autOn X U) = ⊥ := QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hred
  have hH2 : pCoreOf 2 (S126T2.Gv v) ≠ ⊥ := S126T2.pCoreOf_Gv_ne_bot h1222 F hH hv hβ
  have hSQ : SQTKGroup ↥X := InternalSec.sqtkGroup_mono
    (sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian hH2) hKS
  have hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ Kv := by
    intro x hx
    have hx' : x ∈ (↑(Kv ⊔ S) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Kv S hSK] at hx'
    obtain ⟨y, hy, t, ht, hyt⟩ := hx'
    obtain ⟨j, hj⟩ := hC.sylow.2.1 ⟨t, ht⟩
    have hj' : t ^ 2 ^ j = 1 := congrArg Subtype.val hj
    obtain ⟨y', hy', hp⟩ := A4.exists_pow_mul_eq hy (hSK ht) (2 ^ j)
    refine ⟨j, ?_⟩
    rw [← hyt, hp, hj', mul_one]
    exact hy'
  have hKs : IsSimpleGroup ↥(autOn Kv U) :=
    (MulEquiv.isSimpleGroup_congr (S126T2.autOn_Kv_equiv hD7 hC)).1
      (S126T2.isSimple_Kv h1222 h36 hC)
  have hBK := S126T2.autOn_Lv_lt' h1222 hD2 hD5 hD7 hC hN
  have hBiso := S126T2.o2Iso_autOn_Lv h1222 hD7 hC
  have hK168 : 168 < Nat.card ↥(autOn Kv U) := by
    obtain ⟨φ, hφs, -⟩ := hBiso
    have h1 : Nat.card ↥(alternatingGroup (Fin 6)) ≤ Nat.card ↥(autOn (S126T2.Lv L v) U) :=
      Nat.card_le_card_of_surjective φ hφs
    have h2 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    have h3 : Nat.card ↥(autOn (S126T2.Lv L v) U) ≤ Nat.card ↥(autOn Kv U) :=
      Subgroup.card_le_of_le hBK.le
    omega
  obtain ⟨hU', hFF⟩ := hD9 G T L V F v Kv S hC
  have hlist := KG12614.b56QL_of_isFFModule h56 (fun w hw => hUe.2 w hw) hXU hSQ hO2
    le_sup_left (sup_le Subgroup.le_normalizer hSK) hKs hK168 hpow hFF
  have hRvTv : Rv T L v ≤ Tv T v := hRvR ▸ inf_le_right
  have hCS : S ⊓ Subgroup.centralizer (U : Set G) ≤ Tv T v := by
    intro x hx
    have h1 : x ∈ pCoreOf 2 X := by
      rw [hO]
      exact ⟨(le_sup_right : S ≤ X) hx.1, hx.2⟩
    exact hRvTv (hRR ▸ hOR h1)
  have hidx := S126T2.relIndex_autOn_eq hC.tv_le hSU hCS
  have hTvN : Tv T v ≤ Subgroup.normalizer (Rsec L Kv S v : Set G) := by
    rw [hRR]
    exact (inf_le_inf_right _ le_sup_right).trans (le_normalizer_pCoreOf 2 _)
  obtain ⟨h4, e, heK, heR⟩ := hK3 (MulAut ↥U) (autOn X U) (autOn Kv U) (autOn S U)
    (autOn (Tv T v) U) (autOn (S126T2.Lv L v) U) (autOn (Rsec L Kv S v) U)
    (InternalSec.autOn_le_autOn_of_le le_sup_left)
    (S126T2.autOn_le_normalizer (sup_le Subgroup.le_normalizer hSK)) hKs hlist
    (QuasithinUnique.Setup.isSylowTwoOf_autOn hSX hXU) (S126T2.autOn_sup_eq hKvU hSU) hO2 hBK
    (InternalSec.autOn_le_autOn_of_le hC.tv_le)
    (by rw [hidx]; exact hTvS4.trans (le_of_eq (S126T2.relIndex_Tv h1222 F hH hv hβ)))
    (S126T2.autOn_le_normalizer (S126T2.Tv_le_normalizer_Lv hH v))
    (S126T2.autOn_perfect hLvU (perfectCore_perfect _)) hBiso
    (S126T2.autOn_ne_bot hRU' hRU) (S126T2.autOn_le_centralizerSection hD2 hC)
    (S126T2.autOn_le_normalizer hTvN) (S126T2.inf_normalizer_le' h1222 hD2 hD7 hC hN)
  have hS := S126T2.isSylowTwoOf_S_top h1222 hH hv hβ hC.tv_le hC.sylow.2.1 (hidx ▸ h4)
  obtain ⟨w, hw, hwK⟩ := hM1 G T L V F v Kv S hC e heK heR
  have hZ := S126T2.ne_bot_of_moved h1222 hC hw hwK
  exact (hD10 G T L V F v Kv S hC hZ hS).1 hN

end CFSG.Quasithin.H13
