module

public import CFSG.Quasithin.EmptyFaithful.Gold14610CmpL3
public import CFSG.Quasithin.EmptyFaithful.A38cAutOn

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Gold14610

variable {G : Type} [Group G]

theorem isBlock2_of_short {H K : Subgroup G} (hs : IsShort2 K) (hKH : K ≤ H)
    (hHN : H ≤ Subgroup.normalizer (K : Set G)) : IsBlock2 H K :=
  ⟨hs, hKH, ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHN).isSubnormal⟩

end Gold14610

theorem gold14610Compare_holds : Gold14610.Gold14610Compare := by
  rintro G _ _ H R M K V hC hK hq - hKH hHN hRN ⟨Y, _, hY, hext⟩
  obtain ⟨h1, -, h3⟩ := hC
  have hNV : K ⊔ R ≤ Subgroup.normalizer (V : Set G) := h1.2.2.2.1
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hNV
  have hO2 : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G) :=
    (pCoreOf_le_pCoreOf_sup_of_normalizer hRN).trans (h1.1.trans inf_le_right)
  have hπ := CFSG.Quasithin.H13.autOnQuot_surjective hKN hO2
  have fin : ∀ N : ℕ, Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = N → 8 ∣ N → Gold14610.AllowedShape H K →
      Gold14610.AllowedShape H K ∧ ¬ Gold14610.Cat3Type (↥K ⧸ CFSG.pCore 2 ↥K) :=
    fun N hN h8 hA => ⟨hA, Gold14610.not_cat3_of_dvd hN h8⟩
  have blk : IsShort2 K → IsBlock2 H K := fun hs => Gold14610.isBlock2_of_short hs hKH hHN
  rcases h3 with ⟨hchi, hi | hii | hiii | hiv⟩ | hb | hc | hd | he | hf | hg | hh
  · obtain ⟨⟨n, hn, hL⟩, -⟩ := hi
    exact (Gold14610.false_of_card hY hext (card_quotPCore_of_isLin2Type hL)
      (Gold14610.excl_sl_two (by omega))).elim
  · exact (Gold14610.false_of_card hY hext (N := 60)
      (by rw [card_quotPCore_of_isAltType (by norm_num) hii.1]; decide)
      Gold14610.excl_60).elim
  · have hA7 : IsAltBlockType K 7 :=
      ⟨hchi.1.1, (isAltType_iff_exists_isAltBlockTypeWith (by decide : Odd 7)).mp hiii.1⟩
    exact fin 2520 (by rw [card_quotPCore_of_isAltType (by norm_num) hiii.1]; decide)
      (by norm_num) (Or.inr ⟨hchi.1, Or.inr (Or.inr (Or.inr (Or.inl hA7)))⟩)
  · have hA7 : IsAltBlockType K 7 :=
      ⟨hchi.1.1, (isAltType_iff_exists_isAltBlockTypeWith (by decide : Odd 7)).mp hiv.1⟩
    exact fin 2520 (by rw [card_quotPCore_of_isAltType (by norm_num) hiv.1]; decide)
      (by norm_num) (Or.inr ⟨hchi.1, Or.inr (Or.inr (Or.inr (Or.inl hA7)))⟩)
  · obtain ⟨⟨n, α, hn5, hn8, hshort, hα, -⟩, -⟩ := hb
    have hQ := card_quotPCore_of_isAltBlockTypeWith (by omega) hα
    interval_cases n
    · exact (Gold14610.false_of_card hY hext (N := 60) (by rw [hQ]; decide)
        Gold14610.excl_60).elim
    · exact fin 360 (by rw [hQ]; decide) (by norm_num)
        (Or.inr ⟨blk hshort, Or.inr (Or.inr (Or.inl ⟨hshort, α, hα⟩))⟩)
    · exact fin 2520 (by rw [hQ]; decide) (by norm_num)
        (Or.inr ⟨blk hshort, Or.inr (Or.inr (Or.inr (Or.inl ⟨hshort, α, hα⟩)))⟩)
    · exact (Gold14610.false_of_card hY hext (N := 20160) (by rw [hQ]; decide)
        Gold14610.excl_20160).elim
  · exact fin 1080 (card_quotPCore_of_isHatA6Block hc.1) (by norm_num)
      (Or.inr ⟨blk hc.1.1, Or.inl hc.1⟩)
  · exact fin 2520 (card_quotPCore_of_isExcA7Block hd.1) (by norm_num)
      (Or.inr ⟨blk hd.1.1, Or.inr (Or.inr (Or.inr (Or.inr hd.1)))⟩)
  · rcases he.1 with ⟨hshort, α, hα⟩ | hSp
    · exact fin 360
        (by rw [card_quotPCore_of_isAltBlockTypeWith (by norm_num) hα]; decide) (by norm_num)
        (Or.inr ⟨blk hshort, Or.inr (Or.inr (Or.inl ⟨hshort, α, hα⟩))⟩)
    · exact (Gold14610.false_of_card hY hext (card_quotPCore_of_isSp4Block hSp)
        Gold14610.excl_979200).elim
  · exact fin 6048 (card_quotPCore_of_isG2Block hf.1) (by norm_num)
      (Or.inr ⟨blk hf.1.1, Or.inr (Or.inl hf.1)⟩)
  · obtain ⟨⟨n, F, _, _, hn1, hF, ⟨e⟩⟩, -, -⟩ := hg
    by_cases hn : n = 1
    · subst hn
      obtain ⟨hQ, ⟨eQ⟩⟩ := Gold14610.g_one hq hY hext (CFSG.Quasithin.H13.autOnQuot hKN hO2) hπ
        (by simpa using hF) e
      refine fin 168 hQ (by norm_num) (Or.inl ?_)
      exact (isPSL_three_two_iff (X := OTwoQuot K)).mpr
        ⟨(QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)).symm.trans eQ⟩
    · exact (Gold14610.g_ge_two (by omega) hq hY hext _ hπ hF e).elim
  · obtain ⟨hSL, -, -⟩ := hh
    rcases hSL with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact (Gold14610.h_four hq hY hext _ hπ e).elim
    · exact (Gold14610.h_five hq hY hext _ hπ e).elim

end CFSG.Quasithin
