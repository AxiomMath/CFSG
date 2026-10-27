module

public import CFSG.Quasithin.Vol2.Ch12Sec6L19nf

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126L11f

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem S_eq_Tv (h1222 : Stmt12_2_2) (h1261 : Lemma12_6_1) (hD3 : Lemma12_6_6_9)
    {F : Frame126 T L V} {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S)
    (hLK : Lv L v = Kv) (hJ : ¬ thompsonJ (Tv T v) ≤ Qv T V) : S = Tv T v := by
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  obtain ⟨hJT, -⟩ := (hD3 G T L V F v Kv S hC).2.2.2.2 hJ
  have hGL : Gv v ≤ Subgroup.normalizer (Lv L v : Set G) := hLK ▸ hC.normal
  have hTvM := isSylowTwoOf_Tv_Mv h1222 F hH hv hβ
  have hN : S ⊓ Subgroup.normalizer (Tv T v : Set G) ≤ Tv T v := by
    have hle : S ⊓ Subgroup.normalizer (Tv T v : Set G) ≤
        Subgroup.normalizer (L : Set G) ⊓ Gv v := by
      intro s hs
      have hsG : s ∈ Gv v := hC.sylow.1 hs.1
      have hsL : s ∈ Subgroup.normalizer (Lv L v : Set G) := hGL hsG
      have hsV : s ∈ Subgroup.normalizer (Vv L V v : Set G) := by
        rw [S126NF.Vv_eq_comm h1222 h1261 F hH hv hβ hJT]
        have hsX : s ∈ Subgroup.normalizer ((Lv L v ⊔ Tv T v : Subgroup G) : Set G) :=
          Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hsL, hs.2⟩
        have hsR := normalizer_le_normalizer_pCoreOf 2 _ hsX
        have hsΩ := S126VK.normalizer_le_normalizer_omega _ hsR
        exact MS93.le_normalizer_commutator_of (M := Subgroup.zpowers s)
          (Subgroup.zpowers_le.2 hsΩ) (Subgroup.zpowers_le.2 hsL) (Subgroup.mem_zpowers s)
      exact ⟨mem_M_of_perm_Delta h1222 hC hLK
        (perm_Delta_of_normalizer h1222 hH hv hβ hsV hsL), hsG⟩
    have hTvN : Tv T v ≤ S ⊓ Subgroup.normalizer (Tv T v : Set G) :=
      le_inf hC.tv_le Subgroup.le_normalizer
    exact (A4.isSylowTwoOf_iff_maximal.1 hTvM).2.2 _ (hle) (hC.sylow.2.1.to_le inf_le_left)
      hTvN
  by_contra hne
  have hlt : Tv T v < S := lt_of_le_of_ne hC.tv_le (Ne.symm hne)
  obtain ⟨s, hsS, hsN, hsT⟩ := A4.exists_mem_normalizer_not_mem hC.sylow.2.1 hlt
  exact hsT (hN ⟨hsS, hsN⟩)

end S126L11f

end CFSG.Quasithin.H13
