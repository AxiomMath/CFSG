module

public import CFSG.Quasithin.Vol2.Ch12Sec6L18a
public import CFSG.Quasithin.Vol2.Ch12Sec6L17c
public import CFSG.Quasithin.Vol2.Ch12Sec6L18Stmt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem sup_eq_sup_Rv (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hD2 : Lemma12_6_4_5)
    {F : Frame126 T L V} {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S)
    (hN : ¬ Subgroup.normalizer (Rv T L v : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    L ⊔ T = L ⊔ Rv T L v := by
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hVL : ⁅V, L⁆ = V := hH.hyp.irrPlus.2.2.2.1
  have hXL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hXV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hRvY := Rv_le_centralizerSection hD2 hC
  have hRT : Rv T L v ≤ T :=
    (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_Tv h1222 F hH hv hβ)).trans inf_le_left
  have hRX : Rv T L v ≤ L ⊔ T := (pCoreOf_le 2 _).trans inf_le_left
  have hQR : ¬ Rv T L v ≤ Qv T V := by
    intro h
    apply hN
    rw [le_antisymm h (Qv_le_Rv h1222 hH hv)]
    exact normalizer_Qv_le_M h331 h1222 hH
  obtain ⟨r, hr, hrQ⟩ := IsConcreteLE.not_le_iff_exists.1 hQR
  obtain ⟨σ, hσ, hσ1⟩ := actsAs_of_mem_centralizerSection h1222 F hH hv hβ (hRvY hr)
  have hrσ : ActsAs F r (Equiv.swap 0 1) := by
    rcases hσ1 with rfl | rfl
    · exact absurd ⟨hRT hr, mem_centralizer_of_actsAs_one F hVL hLV (hXL (hRX hr))
        (hXV (hRX hr)) hσ⟩ hrQ
    · exact hσ
  exact le_antisymm (sup_le_sup_Rv h1222 F hH hv hr hrσ) (sup_le le_sup_left hRX)

end S126T2

theorem lemma12_6_18_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat) (h56 : AsB56) (hD2 : Lemma12_6_4_5)
    (hD5 : Lemma12_6_11) (hD7 : Lemma12_6_13) (hD9 : Lemma12_6_15) (hD10 : Lemma12_6_16)
    (hD11 : Lemma12_6_17) (hBL : BlockL12618) (hK4 : FactKv12618) (hM2 : FactUv12618)
    (hB7 : BlockKv12618) : Lemma12_6_18 := by
  intro G _ _ T L V _ F v Kv S hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hN := hD11 G T L V F v Kv S hC
  have hL8 := hBL G T L V F v Kv S hC hN
  have h4 := S126T2.sup_eq_sup_Rv h331 h1222 hD2 hC hN
  rcases S126T2.k4_cases h1222 h36 h56 hD2 hD5 hD7 hD9 hK4 hC hL8.1 with ⟨hA7, -, -⟩ | ⟨hA8, h4'⟩
  · obtain ⟨w, hw, hwK⟩ := hM2 G T L V F v Kv S hC (Or.inl hA7)
    exact ⟨hL8, hB7 G T L V F v Kv S hC hL8 hA7, S126T2.ne_bot_of_moved h1222 hC hw hwK, h4⟩
  · exfalso
    obtain ⟨w, hw, hwK⟩ := hM2 G T L V F v Kv S hC (Or.inr hA8)
    have hZ := S126T2.ne_bot_of_moved h1222 hC hw hwK
    obtain ⟨-, -, hTvS4, -, -, -, -, -, -⟩ := hD2 G T L V F v Kv S hC
    have hSU : S ≤ Subgroup.normalizer (Usec Kv S : Set G) :=
      (le_sup_right : S ≤ Kv ⊔ S).trans ((le_normalizer_pCoreOf 2 _).trans
        (S126T2.normalizer_le_normalizer_Usec Kv S))
    have hle := S126T2.relIndex_autOn_le hC.tv_le hSU
    have hS4 : (S126T2.Tv T v).relIndex S = 4 :=
      le_antisymm (hTvS4.trans (le_of_eq (S126T2.relIndex_Tv h1222 F hH hv hβ))) (h4' ▸ hle)
    have hS := S126T2.isSylowTwoOf_S_top h1222 hH hv hβ hC.tv_le hC.sylow.2.1 hS4
    exact (hD10 G T L V F v Kv S hC hZ hS).2 hL8

end CFSG.Quasithin.H13
