module

public import CFSG.Quasithin.Vol2.Ch12Sec6L11b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem exists_mem_Delta_central (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    ∃ u ∈ Delta F v, u ∈ quasithinOmegaOneCenter (Tv T v) := by
  obtain ⟨hVT, hVe⟩ := V_facts h1222 hH
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  obtain ⟨u, huΔ, huV, hβu⟩ := exists_mem_Delta h1222 F hH hv hβ (a := 2) (b := 3) (by decide)
    (by decide) (by decide)
  have huv : u ∈ Vv L V v := huΔ.2.1
  have hc : ∀ t ∈ Tv T v, t * u * t⁻¹ = u := by
    intro t ht
    obtain ⟨σ, hσP, hσ⟩ := F.tAct t ht.1
    have htv : t * v * t⁻¹ = v := by
      have h := Subgroup.mem_centralizer_singleton_iff.1
        (show t ∈ Subgroup.centralizer {v} from ht.2)
      rw [h, mul_inv_cancel_right]
    have h01 : (QuotientGroup.mk (pe 0 1) : D8) = QuotientGroup.mk (pe (σ 0) (σ 1)) := by
      have := hσ ⟨v, hv⟩ ⟨v, hv⟩ htv.symm
      rwa [hβ, S126L20a.dAct_pe] at this
    have hσ01 := mk_pe_eq_mk_pe (by decide) h01
    have h4 : ∀ i : Fin 8, i.val < 4 → (σ i).val < 4 := by
      rcases hσP.2 with h | h
      · exact h
      · exfalso
        have := h 0 (by decide)
        rcases hσ01 with ⟨h0, -⟩ | ⟨h0, -⟩ <;> rw [h0] at this <;> exact absurd this (by decide)
    have hne : ∀ i j : Fin 8, i ≠ j → σ i ≠ σ j := fun i j hij h => hij (σ.injective h)
    have h23 : pe (σ 2) (σ 3) = pe 2 3 := by
      rcases pair23 (σ 0) (σ 1) (σ 2) (σ 3) hσ01 (h4 2 (by decide)) (h4 3 (by decide))
        (hne 2 0 (by decide)) (hne 2 1 (by decide)) (hne 3 0 (by decide)) (hne 3 1 (by decide))
        (hne 2 3 (by decide)) with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · rw [h2, h3]
      · rw [h2, h3, S126L20a.pe_comm]
    have htV : t ∈ Subgroup.normalizer (V : Set G) := hTV ht.1
    have hwV : t * u * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 htV u).1 huV
    have htLv : t ∈ Subgroup.normalizer (Lv L v : Set G) := by
      refine normalizer_le_normalizer_perfectCore _ ?_
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hH.hyp.normalizes ht.1, Subgroup.le_normalizer ht.2⟩
    have hwv : t * u * t⁻¹ ∈ Vv L V v :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_commutator_of_le
        (show Subgroup.zpowers t ≤ _ from (Subgroup.zpowers_le).2 htV)
        ((Subgroup.zpowers_le).2 htLv) (Subgroup.mem_zpowers t)) u).1 huv
    have hβw : F.β ⟨_, hwV⟩ = F.β ⟨u, huV⟩ := by
      rw [hσ ⟨u, huV⟩ ⟨_, hwV⟩ rfl, hβu, S126L20a.dAct_pe, h23]
    exact eq_of_beta_eq_of_mem_Vv h1222 hH hv hβ hwV huV hwv huv hβw
  refine ⟨u, huΔ, Subgroup.subset_closure ⟨⟨⟨hVT huV, ?_⟩, ?_⟩, hVe.2 u huV⟩⟩
  · show u ∈ Subgroup.centralizer {v}
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hVe.1.is_comm.comm ⟨u, huV⟩ ⟨v, hv⟩)
  · show u ∈ Subgroup.centralizer (Tv T v : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := hc t ht
    calc t * u = t * u * t⁻¹ * t := by group
      _ = u * t := by rw [this]

omit [Finite G] [IsMulCommutative ↥V] in
theorem le_normalizer_Hv {v : G} (hGL : Gv v ≤ Subgroup.normalizer (Lv L v : Set G)) :
    Gv v ≤ Subgroup.normalizer
      (centralizerSection (Gv v) (Lv L v) (pCoreOf 2 (Lv L v)) : Set G) := by
  intro g hg
  have key : ∀ g ∈ Gv v, ∀ m ∈ centralizerSection (Gv v) (Lv L v) (pCoreOf 2 (Lv L v)),
      g * m * g⁻¹ ∈ centralizerSection (Gv v) (Lv L v) (pCoreOf 2 (Lv L v)) := fun g hg m hm =>
    conj_mem_centralizerSection (Subgroup.le_normalizer hg) (hGL hg)
      (normalizer_le_normalizer_pCoreOf 2 _ (hGL hg)) hm
  rw [Subgroup.mem_normalizer_iff]
  intro m
  refine ⟨key g hg m, fun hm => ?_⟩
  have := key g⁻¹ ((Gv v).inv_mem hg) _ hm
  simpa [mul_assoc] using this

omit [IsMulCommutative ↥V] in
theorem pCoreOf_le_Hv {v : G} (hGL : Gv v ≤ Subgroup.normalizer (Lv L v : Set G)) :
    pCoreOf 2 (Gv v) ≤ centralizerSection (Gv v) (Lv L v) (pCoreOf 2 (Lv L v)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOG : pCoreOf 2 (Gv v) ≤ Gv v := pCoreOf_le 2 _
  have hN : Lv L v ⊓ pCoreOf 2 (Gv v) ≤ pCoreOf 2 (Lv L v) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (B2F.le_normalizer_inf Subgroup.le_normalizer
        ((Lv_le_Gv L v).trans (le_normalizer_pCoreOf 2 _)))
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
  intro y hy
  have hyG := hOG hy
  refine ⟨hyG, hGL hyG, normalizer_le_normalizer_pCoreOf 2 _ (hGL hyG), fun l hl => hN ⟨?_, ?_⟩⟩
  · have h1 : y * l⁻¹ * y⁻¹ ∈ Lv L v :=
      (Subgroup.mem_normalizer_iff.1 (hGL hyG) _).1 ((Lv L v).inv_mem hl)
    have e : l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) := by group
    rw [e]
    exact (Lv L v).mul_mem hl h1
  · have h1 : l * y * l⁻¹ ∈ pCoreOf 2 (Gv v) :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ (Lv_le_Gv L v hl)) _).1 hy
    exact (pCoreOf 2 (Gv v)).mul_mem h1 ((pCoreOf 2 (Gv v)).inv_mem hy)

omit [IsMulCommutative ↥V] in
theorem Qv_le_Hv (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) :
    Qv T V ≤ centralizerSection (Gv v) (Lv L v) (pCoreOf 2 (Lv L v)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQN : Qv T V ≤ Subgroup.normalizer (Lv L v : Set G) := by
    intro q hq
    refine normalizer_le_normalizer_perfectCore _ ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hH.hyp.normalizes hq.1, Subgroup.le_normalizer (Qv_le_Gv hv hq)⟩
  have hLQ : Lv L v ≤ Subgroup.normalizer (Qv T V : Set G) :=
    ((Lv_le_L L v).trans le_sup_left).trans (LT_le_normalizer_Qv h1222 hH)
  have hN : Lv L v ⊓ Qv T V ≤ pCoreOf 2 (Lv L v) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left (B2F.le_normalizer_inf Subgroup.le_normalizer hLQ)
      (hH.hyp.sylow.1.to_le (inf_le_right.trans inf_le_left))
  intro q hq
  refine ⟨Qv_le_Gv hv hq, hQN hq, normalizer_le_normalizer_pCoreOf 2 _ (hQN hq),
    fun l hl => hN ⟨?_, ?_⟩⟩
  · have h1 : q * l⁻¹ * q⁻¹ ∈ Lv L v :=
      (Subgroup.mem_normalizer_iff.1 (hQN hq) _).1 ((Lv L v).inv_mem hl)
    have e : l * q * l⁻¹ * q⁻¹ = l * (q * l⁻¹ * q⁻¹) := by group
    rw [e]
    exact (Lv L v).mul_mem hl h1
  · have h1 : l * q * l⁻¹ ∈ Qv T V := (Subgroup.mem_normalizer_iff.1 (hLQ hl) _).1 hq
    exact (Qv T V).mul_mem h1 ((Qv T V).inv_mem hq)

theorem false_of_le_Q (h1222 : Stmt12_2_2) (h56 : AsB56) (hD3 : Lemma12_6_6_9)
    {F : Frame126 T L V} {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S)
    (hLK : Lv L v = Kv) (hJ : thompsonJ (Tv T v) ≤ Qv T V) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hyp := hH.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  obtain ⟨hST, -, -, -, hNJ⟩ := (hD3 G T L V F v Kv S hC).2.2.2.1 hJ
  have hGL : Gv v ≤ Subgroup.normalizer (Lv L v : Set G) := hLK ▸ hC.normal
  have hO2 : pCoreOf 2 (Lv L v) ≤ pCoreOf 2 (Gv v) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (Lv_le_Gv L v))
      (hGL.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  obtain ⟨u, huΔ, huZ⟩ := exists_mem_Delta_central h1222 hH hv hβ
  have hZO : Subgroup.zpowers u ≤ pCoreOf 2 (Gv v) :=
    (Subgroup.zpowers_le).2 (hO2 (Vv_le_pCoreOf h1222 hH hv huΔ.2.1))
  have hZT : Subgroup.zpowers u ≤ quasithinOmegaOneCenter S := by
    rw [hST]
    exact (Subgroup.zpowers_le).2 huZ
  set W := conjClosure (Subgroup.zpowers u) (Gv v) with hW
  obtain ⟨hWZ, hred⟩ := isTwoReducedIn_conjClosure_of_isSylowTwoOf hC.sylow hZO hZT
  have hWe : IsElemAbelian 2 W := hred.2.2.1
  have : IsMulCommutative ↥W := hWe.1
  have hΔW : ∀ u' ∈ Delta F v, u' ∈ W := by
    intro u' hu'
    obtain ⟨l, hl, hlu⟩ := exists_Lv_conj_eq h1222 hH hv hβ huΔ hu'
    exact Subgroup.subset_closure ⟨l, Lv_le_Gv L v hl, u, Subgroup.mem_zpowers u, hlu⟩
  have hCWM : Subgroup.centralizer (W : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    intro x hx
    refine mem_M_of_perm_Delta h1222 hC hLK fun u' hu' => ?_
    have hxu : x * u' = u' * x := (Subgroup.mem_centralizer_iff.1 hx u' (hΔW u' hu')).symm
    rw [hxu, mul_inv_cancel_right]
    exact hu'
  set Hv := centralizerSection (Gv v) (Lv L v) (pCoreOf 2 (Lv L v)) with hHv
  have hHvG : Hv ≤ Gv v := centralizerSection_le_left _ _ _
  have hGHv := le_normalizer_Hv hGL
  have hWHv : W ≤ Hv := hWZ.trans (inf_le_left.trans (pCoreOf_le_Hv hGL))
  have hHvW : Hv ≤ Subgroup.normalizer (W : Set G) := hHvG.trans hred.2.1
  have hSH : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ Hv) Hv :=
    A4.isSylowTwoOf_inf_normal hC.sylow hHvG hGHv
  have h3 : ¬ 3 ∣ Nat.card ↥Hv := by
    intro h3
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Hv) 3 h3
    have hy3 : (y : G) ^ 3 = 1 := by
      rw [← Subgroup.orderOf_coe] at hy
      rw [← hy]
      exact pow_orderOf_eq_one _
    have hy1 : (y : G) ≠ 1 := by
      intro h1
      have : orderOf (y : G) = 1 := by rw [h1, orderOf_one]
      rw [Subgroup.orderOf_coe, hy] at this
      omega
    refine false_of_three_comm h1222 F hH hv hβ (hHvG y.2) hy3 hy1 fun l hl => ?_
    have h1 := y.2.2.2.2 l hl
    have e : (y : G) * l * (y : G)⁻¹ * l⁻¹ = (l * y * l⁻¹ * (y : G)⁻¹)⁻¹ := by group
    rw [e]
    exact hO2 ((pCoreOf 2 (Lv L v)).inv_mem h1)
  have hO2W : pCoreOf 2 (autOn (Gv v) W) = ⊥ := QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hred
  have hO2H : pCoreOf 2 (autOn Hv W) = ⊥ := by
    have hn : ((autOn Hv W).subgroupOf (autOn (Gv v) W)).Normal := by
      refine ⟨fun k hk x => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      exact InternalSec.autOn_normal_of hGHv _ x.2 _ hk
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _
      (InternalSec.autOn_le_autOn_of_le hHvG) hn
    rw [hO2W] at this
    exact le_bot_iff.1 this
  have hH2 : pCoreOf 2 (Gv v) ≠ ⊥ := pCoreOf_Gv_ne_bot h1222 F hH hv hβ
  have hSQ : SQTKGroup ↥Hv := InternalSec.sqtkGroup_mono
    (sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian hH2) hHvG
  have hJH : thompsonJ Hv ≤ Subgroup.centralizer (W : Set G) := by
    rcases B2_7 hWe hWHv hHvW hSH with ⟨h, -⟩ | ⟨-, hFF, -⟩
    · exact h
    · exact absurd hFF (not_isFFModule_of_three h56 hWe.2 hHvW hSQ hO2H h3)
  have hJSH : thompsonJ S ≤ S ⊓ Hv := by
    refine le_inf (thompsonJ_le_self S) ?_
    rw [hST]
    exact hJ.trans (Qv_le_Hv h1222 hH hv)
  have hJS : thompsonJ S ≤ Subgroup.centralizer (W : Set G) := by
    rw [thompsonJ_eq_of_le hJSH inf_le_left]
    exact (thompsonJ_le_thompsonJ_of_isSylowTwoOf hSH).trans hJH
  obtain ⟨-, hGeq⟩ := B2_7_of_le hred.2.1 hC.sylow hJS
  apply hC.not_le
  rw [hGeq]
  exact sup_le (inf_le_right.trans hNJ) (inf_le_right.trans hCWM)

end S126T2

end CFSG.Quasithin.H13
