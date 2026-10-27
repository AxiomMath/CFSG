module

public import CFSG.Quasithin.Vol2.Ch12Sec6L18b
public import CFSG.Quasithin.Vol2.Ch4Sec3C64Coord
public import CFSG.Quasithin.Background.SmithC27AltK1Split
public import CFSG.Quasithin.H13.VolIC113

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.G6 S126
  S126L1a S126P S126E S126F S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

theorem asC113A7_holds :
    ∀ (G : Type) [Group G] [Finite G] (L T : Subgroup G),
      CFSG.QuasithinUnique.IsSylowTwoOf T (L ⊔ T) → T ≤ Subgroup.normalizer (L : Set G) →
        IsAltBlockType L 7 →
          pCoreOf 2 (L ⊔ T) =
            CFSG.QuasithinUnique.blockU L ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) := by
  intro G _ _ L T hT hTN hA
  classical
  obtain ⟨hL, α, hαs, hαk, β, hβs, hβk, hβe⟩ := hA
  have hb : Ch4.C64.A7Blk L α β := ⟨hL, hαs, hαk, hβs, hβk, hβe⟩
  have hZ : blockZ L = ⊥ := hb.blockZ_eq_bot
  let θf : ↥(blockU L) →* ↥(G6.coreMod 7) :=
    { toFun := fun u => ⟨Multiplicative.ofAdd (Ch4.C64.crd β u),
        G6.mem_coreMod.2 (SteinbergCB.mem_evenWeight.1 (Ch4.C64.crd_mem u))⟩
      map_one' := Subtype.ext (by
        show Multiplicative.ofAdd (Ch4.C64.crd β 1) = 1
        rw [Ch4.C64.crd_one]
        rfl)
      map_mul' := fun u v => Subtype.ext (by
        show Multiplicative.ofAdd (Ch4.C64.crd β (u * v)) =
          Multiplicative.ofAdd (Ch4.C64.crd β u) * Multiplicative.ofAdd (Ch4.C64.crd β v)
        rw [Ch4.C64.crd_mul]
        rfl) }
  have hθinj : Function.Injective θf := fun u v h => hb.crd_injective
    (Multiplicative.ofAdd.injective (congrArg Subtype.val h))
  have hθsurj : Function.Surjective θf := by
    intro x
    obtain ⟨u, hu⟩ := Ch4.C64.exists_crd_eq hb (e := Multiplicative.toAdd (x : PermMod 7))
      (SteinbergCB.mem_evenWeight.2 (G6.mem_coreMod.1 x.2))
    exact ⟨u, Subtype.ext (by
      show Multiplicative.ofAdd (Ch4.C64.crd β u) = (x : PermMod 7)
      rw [hu]
      rfl)⟩
  let θ : ↥(blockU L) ≃* ↥(G6.coreMod 7) := MulEquiv.ofBijective θf ⟨hθinj, hθsurj⟩
  have hθ : ∀ (l : ↥L) (u v : ↥(blockU L)), (v : G) = l * u * l⁻¹ →
      θ v = G6.coreAct 7 (α l) (θ u) := by
    intro l u v huv
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    have h := congrFun (Ch4.C64.crd_conj hb l u v huv) i
    rw [SteinbergCB.permAct7_apply] at h
    exact h
  have hX : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTN
  have hQU : ∀ q ∈ pCoreOf 2 (L ⊔ T), ∀ u ∈ blockU L, q * u = u * q := fun q hq u hu =>
    VolI.pCoreOf_comm_blockU hL hT hTN hq hu
  have hker : ∀ l : ↥L, α l = 1 → (l : G) ∈ blockQ L := by
    intro l hl
    have hl' : l ∈ α.ker := hl
    rw [hαk] at hl'
    exact (L246.mem_blockQ_iff l).2 hl'
  have hle := SmithC27.pCoreOf_le_blockU_sup (Or.inr rfl) hL le_sup_left hX hZ hQU α hαs hker
    θ hθ
  apply le_antisymm
  · exact hle.trans (sup_le le_sup_left ((inf_le_inf_right _
      (pCoreOf_two_le_of_isSylowTwoOf hT)).trans le_sup_right))
  · exact sup_le (VolI.blockU_le_pCoreOf hL hTN) (VolI.inf_centralizer_le_pCoreOf hL hT hTN)

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem Usec_le_Qv (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) {F : Frame126 T L V} {v : G}
    {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S) (hQO : Qv T V ≤ pCoreOf 2 (Kv ⊔ S)) :
    Usec Kv S ≤ Qv T V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hV1 : V ≠ ⊥ := hH.hyp.irrPlus.2.1
  obtain ⟨hVT, -⟩ := V_facts h1222 hH
  have hV2 : IsPGroup 2 ↥V := (hH.hyp.sylow.1).to_le hVT
  have hVO : V ≤ pCoreOf 2 (Kv ⊔ S) := (V_le_Qv h1222 hH).trans hQO
  have hUC : Usec Kv S ≤ Subgroup.centralizer (V : Set G) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro u ⟨⟨-, huC⟩, -⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.1 huC w (hVO hw))
  have hNV : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    normalizer_le_M h331 hH hV1 hV2 (sup_le hLV hTV)
  have hUM : Usec Kv S ≤ Subgroup.normalizer (L : Set G) :=
    hUC.trans ((Subgroup.centralizer_le_normalizer _).trans hNV)
  have hKS : Kv ⊔ S ≤ Gv v := sup_le (le_of_mem_cComp hC.cComp) hC.sylow.1
  have hSX : CFSG.QuasithinUnique.IsSylowTwoOf S (Kv ⊔ S) :=
    A4.isSylowTwoOf_mono hC.sylow le_sup_right hKS
  have hUS : Usec Kv S ≤ S := (Usec_le Kv S).trans (pCoreOf_two_le_of_isSylowTwoOf hSX)
  have hUG : Usec Kv S ≤ Gv v := (Usec_le Kv S).trans ((pCoreOf_le 2 _).trans hKS)
  have hTvM := isSylowTwoOf_Tv_Mv h1222 F hH hv hβ
  have heq := CFSG.QuasithinUnique.IsSylowTwoOf.eq_of_le hTvM (le_sup_right : Tv T v ≤
    Usec Kv S ⊔ Tv T v) (sup_le (le_inf hUM hUG) hTvM.1)
    (hC.sylow.2.1.to_le (sup_le hUS hC.tv_le))
  intro u hu
  have huT : u ∈ Tv T v := heq ▸ (Subgroup.mem_sup_left hu : u ∈ Usec Kv S ⊔ Tv T v)
  exact ⟨huT.1, hUC hu⟩

theorem blockU_Kv_le_Usec {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hC : Ctx1262 F v Kv S) (hK : CFSG.QuasithinUnique.IsShort2 Kv) :
    blockU Kv ≤ Usec Kv S := by
  have hSK : S ≤ Subgroup.normalizer (Kv : Set G) := hC.sylow.1.trans hC.normal
  have hKS : Kv ⊔ S ≤ Gv v := sup_le (le_of_mem_cComp hC.cComp) hC.sylow.1
  have hSX : CFSG.QuasithinUnique.IsSylowTwoOf S (Kv ⊔ S) :=
    A4.isSylowTwoOf_mono hC.sylow le_sup_right hKS
  intro x hx
  refine Subgroup.subset_closure ⟨⟨VolI.blockU_le_pCoreOf hK hSK hx,
    Subgroup.mem_centralizer_iff.2 fun q hq => VolI.pCoreOf_comm_blockU hK hSX hSK hq hx⟩, ?_⟩
  exact hK.2.2.1.2 x hx

end S126T2

theorem final1262_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat) (h56 : AsB56) (hD2 : Lemma12_6_4_5)
    (hD5 : Lemma12_6_11) (hD7 : Lemma12_6_13) (hD9 : Lemma12_6_15) (hD12 : Lemma12_6_18)
    (hK4 : FactKv12618) : Final1262 := by
  have hC7 := CFSG.Quasithin.H13.asC113A7_holds
  intro G _ _ T L V _ F v Kv S hC
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hv := hC.mem
  obtain ⟨hL8, hK7, -, -⟩ := hD12 G T L V F v Kv S hC
  have hKM := (hD5 G T L V F v Kv S hC).2
  obtain ⟨⟨-, hO⟩, -, -⟩ := hD7 G T L V F v Kv S hC
  obtain ⟨-, hRvR, -, -, -, -, -, -, hReq⟩ := hD2 G T L V F v Kv S hC
  set U := Usec Kv S with hU
  have hXU : Kv ⊔ S ≤ Subgroup.normalizer (U : Set G) :=
    (le_normalizer_pCoreOf 2 _).trans (S126T2.normalizer_le_normalizer_Usec Kv S)
  have hSU : S ≤ Subgroup.normalizer (U : Set G) := (le_sup_right : S ≤ Kv ⊔ S).trans hXU
  have hRS : Rsec L Kv S v ≤ S := hReq ▸ centralizerSection_le_left _ _ _
  have hSK : S ≤ Subgroup.normalizer (Kv : Set G) := hC.sylow.1.trans hC.normal
  have hKS : Kv ⊔ S ≤ S126T2.Gv v := sup_le (le_of_mem_cComp hC.cComp) hC.sylow.1
  have hSX : CFSG.QuasithinUnique.IsSylowTwoOf S (Kv ⊔ S) :=
    A4.isSylowTwoOf_mono hC.sylow le_sup_right hKS
  have hA7 : IsAlt 7 ↥(autOn Kv U) := by
    obtain ⟨-, α, hαs, hαk, -⟩ := hK7
    exact ⟨((S126T2.autOn_Kv_equiv hD7 hC).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hαk.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hαs)⟩
  have hR1 : centralizerSection (autOn S U) (autOn (S126T2.Lv L v) U)
      (pCoreOf 2 (autOn (S126T2.Lv L v) U)) = ⊥ := by
    rcases S126T2.k4_cases h1222 h36 h56 hD2 hD5 hD7 hD9 hK4 hC hL8.1 with ⟨-, -, h⟩ | ⟨hA8, -⟩
    · exact h
    · exfalso
      obtain ⟨e7⟩ := hA7
      obtain ⟨e8⟩ := hA8
      have h1 := Nat.card_congr (e7.symm.trans e8).toEquiv
      rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at h1
      norm_num [Nat.factorial] at h1
  have hRaut : autOn (Rsec L Kv S v) U = ⊥ :=
    le_bot_iff.1 ((S126T2.autOn_le_centralizerSection hD2 hC).trans hR1.le)
  have hRO : Rsec L Kv S v ≤ pCoreOf 2 (Kv ⊔ S) := by
    have hRC : Rsec L Kv S v ≤ Subgroup.centralizer (U : Set G) := by
      by_contra h
      exact S126T2.autOn_ne_bot (hRS.trans hSU) h hRaut
    rw [hO]
    exact le_inf (hRS.trans le_sup_right) hRC
  have hQO : Qv T V ≤ pCoreOf 2 (Kv ⊔ S) :=
    (Qv_le_Rv h1222 hH hv).trans ((hRvR.le.trans inf_le_left).trans hRO)
  have hUQ := S126T2.Usec_le_Qv h331 h1222 hC hQO
  have hUKQ : blockU Kv ≤ Qv T V := (S126T2.blockU_Kv_le_Usec hC hK7.1).trans hUQ
  have hsplit := hC7 G Kv S hSX hSK hK7
  have hCN : S ⊓ Subgroup.centralizer (Kv : Set G) ≤
      Subgroup.normalizer (blockU Kv : Set G) :=
    inf_le_left.trans fun s hs => C1.mem_normalizer_blockU (hSK hs)
  have hKQ : Kv ≤ Subgroup.normalizer (Qv T V : Set G) := by
    intro k hk
    refine Subgroup.mem_normalizer_fintype fun q hq => ?_
    have hqO := hQO hq
    rw [hsplit] at hqO
    obtain ⟨u, hu, c, hc, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hCN hqO
    have hkc : k * c = c * k := Subgroup.mem_centralizer_iff.1 hc.2 k hk
    have hku : k * u * k⁻¹ * u⁻¹ ∈ blockU Kv := by
      have h1 : k * u * k⁻¹ ∈ blockU Kv :=
        (Subgroup.mem_normalizer_iff.1 (C1.le_normalizer_blockU Kv hk) u).1 hu
      exact (blockU Kv).mul_mem h1 ((blockU Kv).inv_mem hu)
    have e : k * (u * c) * k⁻¹ = (k * u * k⁻¹ * u⁻¹) * (u * c) := by
      calc k * (u * c) * k⁻¹ = k * u * k⁻¹ * (k * c * k⁻¹) := by group
        _ = k * u * k⁻¹ * (c * k * k⁻¹) := by rw [hkc]
        _ = (k * u * k⁻¹ * u⁻¹) * (u * c) := by group
    rw [e]
    exact (Qv T V).mul_mem (hUKQ hku) hq
  exact hKM (hKQ.trans (normalizer_Qv_le_M h331 h1222 hH))

theorem final1262_of_facts (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat) (h56 : AsB56) (hD2 : Lemma12_6_4_5)
    (hD5 : Lemma12_6_11) (hD7 : Lemma12_6_13) (hD9 : Lemma12_6_15) (hD10 : Lemma12_6_16)
    (hD11 : Lemma12_6_17) (hBL : BlockL12618) (hK4 : FactKv12618) (hM2 : FactUv12618)
    (hB7 : BlockKv12618) : Final1262 :=
  final1262_of h331 h1222 h36 h56 hD2 hD5 hD7 hD9
    (lemma12_6_18_of h331 h1222 h36 h56 hD2 hD5 hD7 hD9 hD10 hD11 hBL hK4 hM2 hB7) hK4

theorem factUv12617_of (hM2 : FactUv12618) : FactUv12617 := by
  intro G _ _ T L V _ F v Kv S hC e heK _
  refine hM2 G T L V F v Kv S hC (Or.inr ⟨?_⟩)
  have hKY : autOn Kv (Usec Kv S) ≤ autOn (Kv ⊔ S) (Usec Kv S) :=
    InternalSec.autOn_le_autOn_of_le le_sup_left
  exact ((Subgroup.subgroupOfEquivOfLe hKY).symm.trans
    (((autOn Kv (Usec Kv S)).subgroupOf (autOn (Kv ⊔ S) (Usec Kv S))).equivMapOfInjective
      e.toMonoidHom e.injective)).trans (MulEquiv.subgroupCongr heK)

end CFSG.Quasithin.H13
