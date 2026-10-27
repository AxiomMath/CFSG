module

public import CFSG.Quasithin.EmptyFaithful.QTKELocal
public import CFSG.Quasithin.EmptyFaithful.S152He9Q
public import CFSG.Quasithin.EmptyFaithful.S152He9Y1

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem exists_ctx {T Mc M H : Subgroup G} (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (h1519 : Lemma1519Concl T Mc M) (h1515 : Lemma1515Concl T Mc M)
    (h15201 : Lemma15201Concl T Mc M) (h15203 : Lemma15203Concl T Mc M)
    (φ : Nonempty (OTwoQuot H ≃* W5)) :
    ∃ (π : ↥H →* W5) (K₁ K₂ : Subgroup G), Ctx15204 T Mc M H K₁ K₂ π := by
  have hT : IsSylowTwoOf T H := S152N.isSylowTwoOf_hStar hs hH
  obtain ⟨π, K₁, K₂, wr⟩ := exists_wrH hT φ
  obtain ⟨E, hEX, hEH, hEab, hE9, e, he, heE, hπe⟩ := wr.exists_E_le hs hH h1519
  have hdata : S152Y.Data T Mc M := ⟨hs.qtfe, hs.mf, h1515, h15201⟩
  have hEHM : E ≤ H ⊓ M := hEX.trans (oTwoUpper_le _)
  have hEV : E ≤ Subgroup.centralizer (V154 T Mc M : Set G) := hEX.trans (h1519.four H hH)
  have hPM : pCoreOf 2 M ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hdata.inM.1.1
  have hrk : CFSG.Open.pRank 3 M ≤ 2 :=
    pRank_le_two_of_pCoreOf_ne_bot hs.qtfe.qtke hPM Nat.prime_three (by norm_num)
  have hY : YPack T Mc M := Y_pack hdata h15203 (hEHM.trans inf_le_right) hEV hEab hE9 hrk
  exact ⟨π, K₁, K₂, ⟨⟨hdata, h15203, hY.card_five, hY.cent_le⟩, hs, hH, h1519, wr, hT,
    e, he, (hEHM heE).2, hπe⟩⟩

end CFSG.Quasithin.He9
