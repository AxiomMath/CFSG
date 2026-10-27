module

public import CFSG.Quasithin.Vol2.Ch12Sec6L18Kv
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8E
public import CFSG.Quasithin.EmptyFaithful.S153MAR
public import CFSG.Quasithin.Background.C124BlkAlt
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8D
public import CFSG.Quasithin.Vol2.Ch12Sec6L18Stmt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.G6 S126
  S126L1a S126P S126E S126F S126L1b S126N S126T2 CFSG.LieType.BorelTits
  CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K8
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

theorem isQuasisimple_of_simple_nc {Q : Type*} [Group Q] (hs : IsSimpleGroup Q)
    (hnc : ∃ x y : Q, x * y ≠ y * x) : CFSG.IsQuasisimple Q := by
  have := hs
  have hZ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      exact hxy ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top y)) x)
  have hperf : Group.IsPerfect Q := by
    refine ⟨?_⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      have : ⁅x, y⁆ ∈ commutator Q :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact h
  let e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hperf, (MulEquiv.isSimpleGroup_congr e).2 hs, ?_⟩
  obtain ⟨x, y, hxy⟩ := hnc
  exact ⟨e.symm x, e.symm y, fun h => hxy (by simpa using congrArg e h)⟩

end S126T2

theorem blockKv12618_of (h51 : AsB51) (h1222 : Stmt12_2_2)
    (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat) (hD2 : Lemma12_6_4_5) (hD7 : Lemma12_6_13)
    (hD9 : Lemma12_6_15) : BlockKv12618 := by
  intro G _ _ T L V _ F v Kv S hC hL8 hA7
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hyp := hH.hyp
  obtain ⟨⟨-, hO⟩, -, hVU⟩ := hD7 G T L V F v Kv S hC
  obtain ⟨hUe, hFF⟩ := hD9 G T L V F v Kv S hC
  set U := Usec Kv S with hU
  set X := Kv ⊔ S with hX
  have : IsMulCommutative ↥U := hUe.1
  have hXU : X ≤ Subgroup.normalizer (U : Set G) :=
    (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_Usec Kv S)
  have hKvU : Kv ≤ Subgroup.normalizer (U : Set G) := Kv_le_normalizer_Usec hC
  have hSK : S ≤ Subgroup.normalizer (Kv : Set G) := hC.sylow.1.trans hC.normal
  have hXK : X ≤ Subgroup.normalizer (Kv : Set G) := sup_le Subgroup.le_normalizer hSK
  have hKS : X ≤ Gv v := sup_le (le_of_mem_cComp hC.cComp) hC.sylow.1
  have hKp : ⁅Kv, Kv⁆ = Kv := perfect_of_mem_cComp hC.cComp
  have hred := isTwoReducedIn_Usec hD7 hC
  have hO2 : pCoreOf 2 (autOn X U) = ⊥ := QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hred
  have hH2 : pCoreOf 2 (Gv v) ≠ ⊥ := pCoreOf_Gv_ne_bot h1222 F hH hv hβ
  have hSQ : SQTKGroup ↥(Gv v) := sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian hH2
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
    (MulEquiv.isSimpleGroup_congr (autOn_Kv_equiv hD7 hC)).1 (isSimple_Kv h1222 h36 hC)
  have hCKU : Kv ⊓ Subgroup.centralizer (U : Set G) ≤ pCoreOf 2 (Kv ⊔ S) := by
    rw [hO]
    exact inf_le_inf_right _ le_sup_left
  have hker : pCoreOf 2 Kv = Kv ⊓ Subgroup.centralizer (U : Set G) := by
    apply le_antisymm
    · refine le_inf (pCoreOf_le 2 _) ?_
      have hQP : pCoreOf 2 Kv ≤ pCoreOf 2 (Kv ⊔ S) :=
        le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left)
          (hXK.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
      rw [hO] at hQP
      exact hQP.trans inf_le_right
    · exact le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hk,
          B2F.le_normalizer_centralizer hKvU hk⟩)
        ((pCoreOf_isPGroup 2 (Kv ⊔ S)).to_le hCKU)
  have hBU := blockU_Kv_eq h1222 h36 hD2 hD7 hC hL8.1
  set Ls := autI hUe Kv with hLs
  set Xs := autI hUe X with hXs
  have hV2 : ∀ w : IntMod U hUe, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hLsX : Ls ≤ Xs := InternalSec.autOn_le_autOn_of_le le_sup_left
  have hn : ∀ x ∈ Xs, ∀ l ∈ Ls, x * l * x⁻¹ ∈ Ls := InternalSec.autOn_normal_of hXK
  have h2 : ∀ x ∈ Xs, ∃ e : ℕ, x ^ 2 ^ e ∈ Ls := by
    intro x hx
    obtain ⟨g, hgX, rfl⟩ := (mem_autI hUe).1 hx
    obtain ⟨k, hk⟩ := hpow (g : G) hgX
    refine ⟨k, (mem_autI hUe).2 ⟨g ^ 2 ^ k, by simpa using hk, ?_⟩⟩
    rw [map_pow]
  have h2520' : Nat.card ↥(autOn Kv U) = 2520 := by
    obtain ⟨e⟩ := hA7
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have h2520 : Nat.card ↥Ls = 2520 := h2520'
  have hnc : ∃ x y : ↥Ls, x * y ≠ y * x := by
    by_contra h
    push Not at h
    have hab : IsMulCommutative ↥Ls := ⟨⟨fun x y => h x y⟩⟩
    obtain ⟨e⟩ := hA7
    have : ∀ x y : ↥(alternatingGroup (Fin 7)), x * y = y * x := fun x y =>
      e.symm.injective (by rw [map_mul, map_mul]; exact h _ _)
    exact absurd (this ⟨Equiv.swap 0 1 * Equiv.swap 0 2,
      Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩
      ⟨Equiv.swap 0 1 * Equiv.swap 0 3, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩)
      (by decide)
  have hq : CFSG.IsQuasisimple ↥Ls := isQuasisimple_of_simple_nc hKs hnc
  have hSQK : SQTKGroup ↥Ls := InternalSec.sqtkGroup_autOn hKvU
    (InternalSec.sqtkGroup_mono hSQ (le_of_mem_cComp hC.cComp))
    ((pCoreOf_isPGroup 2 (Kv ⊔ S)).to_le hCKU)
  obtain ⟨-, hB⟩ := S153M.le_ffJ_of_ffModule hV2 hLsX hn h2 hq hSQK hO2 hFF
  obtain ⟨⟨-, hc⟩, h2', -, -, -, -⟩ := h51 (IntMod U hUe) hV2 (ffJ Xs) Ls hB
  have hdir := part2_direct h2' h2520
  have hZ0 : fixV Ls ⊓ commV Ls = ⊥ := by rw [inf_comm]; exact hdir.2
  have hN : Nat.card ↥Ls = 2520 ∨ Nat.card ↥Ls = 7560 := Or.inl h2520
  obtain ⟨hirr, hpair⟩ : commV Ls ∈ IrrPlus Ls ⊤ ∧
      (AlternatingNatural Ls (commV Ls) (fixV Ls ⊓ commV Ls) 7 ∨
        A7Four Ls (commV Ls) (fixV Ls ⊓ commV Ls)) := by
    rcases hc with hi | hii | ⟨n, hiii⟩ | hiv
    · exact ⟨hi.1, pair_shape hN hi.2.1⟩
    · exfalso
      obtain ⟨-, n, K, hF, hFin, hK, I, π, -, -, hreal, -⟩ := hii
      have hcd := card_eq_of_nat_realizes1527d (hreal 0)
      rw [card_statedSL_three1527d, hK] at hcd
      exact sl3_ne hN hcd.symm
    · exfalso
      obtain ⟨-, hn5, π, U₁, U₂, -, hr1, -⟩ := hiii
      exact not_surj_sl hn5 hN π hr1.1
    · exfalso
      obtain ⟨-, n, hn5, k, hk1, -, I, π, -, -, -, hreal⟩ := hiv
      exact not_surj_sl hn5 hN π (hreal ⟨0, hk1⟩).1
  have hUG : C124.toG hUe (commV Ls) = ⁅U, Kv⁆ := by
    rw [C124.toG_commV hUe hKvU, Subgroup.commutator_comm]
  obtain ⟨π, hπ⟩ : AlternatingNatural Ls (commV Ls) (fixV Ls ⊓ commV Ls) 7 := by
    rcases hpair with h | h
    · exact h
    · exfalso
      rw [hZ0] at h
      have h16 := card_of_a7Four_bot h
      have hc1 : Nat.card ↥(C124.toG hUe (commV Ls)) = 16 := by
        rw [← h16]
        exact Nat.card_congr ((commV Ls).equivMapOfInjective _
          (C124.valHom_injective hUe)).symm.toEquiv
      rw [hUG] at hc1
      have h32 := card_Vv h1222 hH hv hβ
      have hle := Subgroup.card_le_of_le hVU
      omega
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFC.altDn_faithful (by norm_num)) hπ
  have hQP : blockQ Kv ≤ pCoreOf 2 (Kv ⊔ S) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left)
      (hXK.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hWU : ⁅U, Kv⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro u hu k hk
    have h1 : k * u⁻¹ * k⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hKvU hk) _).1 (U.inv_mem hu)
    have e : u * k * u⁻¹ * k⁻¹ = u * (k * u⁻¹ * k⁻¹) := by group
    rw [commutatorElement_def, e]
    exact U.mul_mem hu h1
  have hUC : U ≤ Subgroup.centralizer (pCoreOf 2 (Kv ⊔ S) : Set G) :=
    (Subgroup.closure_le _).2 fun z hz => hz.1.2
  have hBQ : blockU Kv ≤ blockQ Kv := by
    show ⁅blockQ Kv, Kv⁆ ≤ blockQ Kv
    rw [Subgroup.commutator_le]
    intro q hq k hk
    have h1 : k * q⁻¹ * k⁻¹ ∈ blockQ Kv :=
      (Subgroup.mem_normalizer_iff.1 ((Subgroup.le_normalizer.trans
        (normalizer_le_normalizer_pCoreOf 2 Kv)) hk) _).1 ((blockQ Kv).inv_mem hq)
    have e : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
    rw [commutatorElement_def, e]
    exact (blockQ Kv).mul_mem hq h1
  have hUQ : blockU Kv ≤ blockQ Kv ⊓ Subgroup.centralizer (blockQ Kv : Set G) := by
    refine le_inf hBQ fun x hx => ?_
    rw [hBU] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact Subgroup.mem_centralizer_iff.1 (hUC (hWU hx)) q (hQP hq)
  have hU2 : ∀ x ∈ blockU Kv, x ^ 2 = 1 := by
    intro x hx
    rw [hBU] at hx
    exact hUe.2 x (hWU hx)
  have hchar : CharTwo Kv := by
    set N := Kv ⊓ Subgroup.centralizer ((⁅U, Kv⁆ : Subgroup G) : Set G) with hNdef
    have hKW : Kv ≤ Subgroup.normalizer ((⁅U, Kv⁆ : Subgroup G) : Set G) :=
      le_normalizer_commutator_of_le hKvU Subgroup.le_normalizer
    have hNn : ∀ k ∈ Kv, ∀ n ∈ N, k * n * k⁻¹ ∈ N := by
      intro k hk n hn
      refine ⟨Kv.mul_mem (Kv.mul_mem hk hn.1) (Kv.inv_mem hk), ?_⟩
      exact (Subgroup.mem_normalizer_iff.1 (B2F.le_normalizer_centralizer hKW hk) n).1 hn.2
    rcases le_centralizer_or_eq_of_normal h1222 h36 hD7 hC inf_le_left hNn with h | h
    · rintro c ⟨hcK, hcC⟩
      have hcN : c ∈ N := ⟨hcK, Subgroup.centralizer_le (fun x hx => by
        have : x ∈ blockU Kv := hBU ▸ hx
        exact hBQ this) hcC⟩
      rw [hker]
      exact ⟨hcK, h hcN⟩
    · exfalso
      have h1 : ⁅⁅U, Kv⁆, Kv⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (h.trans inf_le_right)
      have hUK : U ≤ Subgroup.normalizer (Kv : Set G) :=
        ((Usec_le Kv S).trans (pCoreOf_le 2 _)).trans hXK
      have h2 : ⁅U, Kv⁆ = ⊥ := le_bot_iff.1 ((le_comm_comm_of_perfect hKp hUK hKvU).trans h1.le)
      have h32 := card_Vv h1222 hH hv hβ
      have h3 : Vv L V v = ⊥ := le_bot_iff.1 (h2 ▸ hVU)
      rw [h3, Subgroup.card_bot] at h32
      exact absurd h32 (by decide)
  have hI := hirr.2.2.2
  have hZG : C124.toG hUe (XMod.fixed ↥Ls (commV Ls)) =
      ⁅U, Kv⁆ ⊓ Subgroup.centralizer (Kv : Set G) := by
    rw [C124.toG_fixed hUe hKvU, hUG]
  have hZb : blockZ Kv = ⁅U, Kv⁆ ⊓ Subgroup.centralizer (Kv : Set G) := by
    unfold blockZ
    rw [hBU]
  have hlt : blockZ Kv < blockU Kv := by
    have h := lt_of_le_of_ne ((C124.toG_le_iff hUe).2 hI.1.le)
      (fun h => hI.1.ne ((C124.toG_inj hUe).1 h))
    rw [hZG, hUG] at h
    rw [hZb, hBU]
    exact h
  have hirrG : ∀ W : Subgroup G, blockZ Kv ≤ W → W ≤ blockU Kv →
      Kv ≤ Subgroup.normalizer (W : Set G) → W = blockZ Kv ∨ W = blockU Kv := by
    intro W hZW hWU hKW
    rw [hZb, ← hZG] at hZW
    rw [hBU, ← hUG] at hWU
    rw [hZb, ← hZG, hBU, ← hUG]
    have hWV : W ≤ U := hWU.trans (C124.toG_le hUe _)
    set W' : Subgroup (IntMod U hUe) := W.comap (C124.valHom hUe) with hW'
    have hW'G : C124.toG hUe W' = W := by
      ext g
      constructor
      · intro hg
        obtain ⟨w, hw, rfl⟩ := (C124.mem_toG hUe).1 hg
        exact hw
      · intro hg
        exact (C124.mem_toG hUe).2 ⟨IntMod.mk hUe ⟨g, hWV hg⟩, hg, rfl⟩
    have hinv : XMod.IsInv ↥Ls W' := by
      rw [C124.isInv_iff hUe hKvU, hW'G]
      intro g hg w hw
      exact (Subgroup.mem_normalizer_iff.1 (hKW hg) w).1 hw
    have hfix : XMod.fixed ↥Ls (commV Ls) ≤ W' := by
      rw [← C124.toG_le_iff hUe, hW'G]
      exact hZW
    have hle : W' ≤ commV Ls := by
      rw [← C124.toG_le_iff hUe, hW'G]
      exact hWU
    rcases hI.2 W' hinv hfix hle with h | h
    · left
      rw [← hW'G, h]
    · right
      rw [← hW'G, h]
  have hshort : IsShort2 Kv :=
    ⟨C124.noTwoQuot_of_perfect hKp, hchar, ⟨hUQ, hU2⟩, Or.inl hC.quasisimple, hlt, hirrG⟩
  have hUeq : blockU Kv = ⁅U, Kv⁆ ⊔ blockZ Kv := by
    have hZU : blockZ Kv ≤ ⁅U, Kv⁆ := hZb.le.trans inf_le_left
    rw [hBU]
    exact (sup_eq_left.2 hZU).symm
  obtain ⟨α, hα⟩ := C124.exists_isAltBlockTypeWith hUe (by norm_num : 0 < 7) hKvU hker hBU.ge
    hUeq π hπ hinj
  exact ⟨hshort, α, hα⟩

end CFSG.Quasithin.H13
