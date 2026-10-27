module

public import CFSG.Quasithin.Background.C124BlockLift
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Block
public import CFSG.Quasithin.Background.C124BlockA

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem noTwoQuot_of_odd {K : Subgroup G} (hK : Odd (Nat.card ↥K)) :
    ∀ (N : Subgroup ↥K) [N.Normal], IsPGroup 2 (↥K ⧸ N) → N = ⊤ := by
  intro N _ hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 hp
  have hdvd : 2 ^ a ∣ Nat.card ↥K := by
    rw [← ha]
    exact Subgroup.index_dvd_card N
  have ha0 : a = 0 := by
    by_contra h
    exact (Nat.not_even_iff_odd.2 hK) (even_iff_two_dvd.2 ((dvd_pow_self 2 h).trans hdvd))
  rw [ha0, pow_zero] at ha
  exact Subgroup.index_eq_one.1 ha

theorem isBlock2_of_short_of_mem_cComp {X L : Subgroup G} (hL : L ∈ cComp X) (hs : IsShort2 L) :
    IsBlock2 X L :=
  ⟨hs, le_of_mem_cComp hL, by
    have := A4.subnormal_subgroupOf X (subnormal_of_mem_cComp hL)
    rw [Subgroup.subgroupOf_self] at this
    exact A3.subnormal_top_iff.1 this⟩

namespace EntryPlus

variable {X T V L R : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
  (E : EntryPlus X T V L R m hV)

include E

theorem comm_V_le_V : ⁅V, L⁆ ≤ V :=
  CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing V L E.hLN

theorem comm_Q_L_le {Y : Subgroup G} (hY : YData X V L R hV Y) (hs : IsShort2 Y) :
    ⁅pCoreOf 2 X, L⁆ ≤ ⁅V, L⁆ := by
  set Q := pCoreOf 2 X with hQ
  have hYX : Y ≤ X := hY.le_L.trans E.hLX
  have hYP : Y ≤ Y ⊔ Q := le_sup_left
  have hQP : Q ≤ Y ⊔ Q := le_sup_right
  have hPX : Y ⊔ Q ≤ X := sup_le hYX (pCoreOf_le 2 X)
  have hYn : (Y.subgroupOf (Y ⊔ Q)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYP).2
      (sup_le Subgroup.le_normalizer hY.Q_norm)
  have hsub : IsSubnormal Y (Y ⊔ Q) := A3.subnormal_of_normal hYP hYn
  have hQn : (Q.subgroupOf (Y ⊔ Q)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).2
      (hPX.trans (le_normalizer_pCoreOf 2 X))
  have hVQ : V ≤ Q := le_pCoreOf_of_reduced E.red
  have hVn : (V.subgroupOf (Y ⊔ Q)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hVQ.trans hQP)).2 (hPX.trans E.hXN)
  have h1 : ⁅Q, Y⁆ ≤ blockU Y :=
    L246C127.commutator_le_blockU hs hsub hQP hQn (pCoreOf_isPGroup 2 X)
  have h2 : ⁅V, Y⁆ ≤ blockU Y :=
    L246C127.commutator_le_blockU hs hsub (hVQ.trans hQP) hVn E.hV2
  have hne : ⁅V, Y⁆ ≠ ⊥ := by
    rw [Subgroup.commutator_comm, Ne, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hY.not_cent
  have h3 : blockU Y ≤ ⁅V, Y⁆ :=
    L246C127.blockU_le_commutator_of_ne_bot hs (hYX.trans E.hXN) E.hV2 h2 hne
  have h4 : ⁅Q, Y⁆ ≤ ⁅V, L⁆ := (h1.trans h3).trans (Subgroup.commutator_mono le_rfl hY.le_L)
  have hXU : X ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator' E.hXN E.normal
  set C := cqSub X Q ⁅V, L⁆ (le_normalizer_pCoreOf 2 X) hXU with hCdef
  have hCL : ((C ⊓ L).subgroupOf L).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx ⊢
    exact ⟨cqSub_conj hx.1 (E.hLX g.2), L.mul_mem (L.mul_mem g.2 hx.2) (L.inv_mem g.2)⟩
  have hYC : Y ≤ C ⊓ L := fun y hy =>
    ⟨⟨hYX hy, fun q hq => h4 (Subgroup.commutator_mem_commutator hq hy)⟩, hY.le_L hy⟩
  have hC : L ≤ C := (hY.closure _ inf_le_right hCL hYC).trans inf_le_left
  refine Subgroup.commutator_le.2 fun q hq l hl => ?_
  exact (hC hl).2 q hq

theorem blockU_eq {Y : Subgroup G} (hY : YData X V L R hV Y) (hs : IsShort2 Y) :
    blockU L = ⁅V, L⁆ := by
  apply le_antisymm
  · exact (Subgroup.commutator_mono E.pCoreOf_L_le_Q le_rfl).trans (E.comm_Q_L_le hY hs)
  · have h1 : ⁅V, L⁆ ≤ ⁅⁅V, L⁆, L⁆ :=
      L246C127.commutator_le_commutator_commutator_two E.hV2 E.hLN
        (L246C127.le_closure_oddPPow (noTwoQuot_of_perfect E.perf))
    exact h1.trans (Subgroup.commutator_mono E.comm_V_L_le le_rfl)

theorem ker_le (hU : blockU L = ⁅V, L⁆) :
    L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L := by
  set K := L ⊓ Subgroup.centralizer (V : Set G) with hK
  have hO2 : IsPGroup 2 (pCoreOf 2 L) := pCoreOf_isPGroup 2 L
  have hKL : K ≤ L := inf_le_left
  have hnorm : L ≤ Subgroup.normalizer (K : Set G) := fun l hl => by
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => ⟨L.mul_mem (L.mul_mem hl hc.1) (L.inv_mem hl),
      conj_mem_centralizer_of_le E.hLN hl hc.2⟩, fun hc => ?_⟩
    have h1 := L.mul_mem (L.mul_mem (L.inv_mem hl) hc.1) hl
    have h2 := conj_mem_centralizer_of_le E.hLN (L.inv_mem hl) hc.2
    exact ⟨by simpa [mul_assoc] using h1, by simpa [mul_assoc] using h2⟩
  have h2 : IsPGroup 2 K := by
    rintro ⟨c, hc⟩
    have hc0 : orderOf c ≠ 0 := (orderOf_pos c).ne'
    obtain ⟨k, b, hb, hkb⟩ := Nat.exists_eq_two_pow_mul_odd hc0
    set c' := c ^ 2 ^ k with hc'
    have hoc' : orderOf c' = b := by
      rw [hc', orderOf_pow_of_dvd (by positivity) (hkb ▸ dvd_mul_right _ _), hkb,
        Nat.mul_div_cancel_left _ (by positivity)]
    have hc'K : c' ∈ K := K.pow_mem hc _
    set K' := Subgroup.zpowers c' with hK'
    have hK'K : K' ≤ K := Subgroup.zpowers_le.2 hc'K
    have hodd : Odd (Nat.card ↥K') := by
      rw [Nat.card_zpowers, hoc']
      exact hb
    have hgen := L246C127.le_closure_oddPPow (noTwoQuot_of_odd hodd)
    have hK'O : K' ≤ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
      (hK'K.trans hKL).trans (le_normalizer_pCoreOf 2 L)
    have h3 := L246C127.commutator_le_commutator_commutator_two hO2 hK'O hgen
    have h4 : ⁅pCoreOf 2 L, K'⁆ ≤ V :=
      ((Subgroup.commutator_mono le_rfl (hK'K.trans hKL)).trans
        (show ⁅pCoreOf 2 L, L⁆ ≤ ⁅V, L⁆ from hU.le)).trans E.comm_V_le_V
    have h5 : ⁅⁅pCoreOf 2 L, K'⁆, K'⁆ = ⊥ := by
      refine le_bot_iff.1 ((Subgroup.commutator_mono h4 le_rfl).trans ?_)
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer.2
        (hK'K.trans inf_le_right)]
    have h6 : ⁅pCoreOf 2 L, K'⁆ = ⊥ := le_bot_iff.1 (h3.trans h5.le)
    have h7 : c' ∈ L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
      refine ⟨hKL hc'K, Subgroup.mem_centralizer_iff.2 fun o ho => ?_⟩
      have h8 : o ∈ Subgroup.centralizer (K' : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 h6 ho
      exact (Subgroup.mem_centralizer_iff.1 h8 c' (Subgroup.mem_zpowers c')).symm
    have h9 : c' ∈ pCoreOf 2 L := E.charTwoL h7
    obtain ⟨n, hn⟩ := hO2 ⟨c', h9⟩
    have hn' : c' ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hdvd : b ∣ 2 ^ n := hoc' ▸ orderOf_dvd_of_pow_eq_one hn'
    have hb1 : b = 1 := by
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simpa using hi
      · exfalso
        have : 2 ∣ b := hi ▸ dvd_pow_self 2 hi0.ne'
        exact (Nat.not_even_iff_odd.2 hb) (even_iff_two_dvd.2 this)
    refine ⟨k, Subtype.ext ?_⟩
    have : c ^ 2 ^ k = 1 := by
      rw [← hc', ← orderOf_eq_one_iff, hoc', hb1]
    simpa using this
  exact le_pCoreOf_of_le_normalizer 2 hKL hnorm h2

theorem blockData_of_short {Y : Subgroup G} (hY : YData X V L R hV Y) (hs : IsShort2 Y) :
    BlockData V L := by
  have hU := E.blockU_eq hY hs
  have hZ : blockZ L = ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) := by
    unfold blockZ
    rw [hU]
  have hirr := E.irr_group
  refine ⟨⟨noTwoQuot_of_perfect E.perf, E.charTwoL, ⟨?_, ?_⟩, Or.inl E.Lq, ?_⟩, ?_, hU.ge, ?_⟩
  · rw [hU]
    refine le_inf E.comm_V_L_le fun x hx => ?_
    refine Subgroup.mem_centralizer_iff.2 fun q hq => ?_
    have hqC : q ∈ Subgroup.centralizer (V : Set G) :=
      (E.pCoreOf_L_le_Q.trans (pCoreOf_le_centralizer E.red)) hq
    exact (Subgroup.mem_centralizer_iff.1 hqC x (E.comm_V_le_V hx)).symm
  · rw [hU]
    exact fun x hx => E.red.2.2.1.2 x (E.comm_V_le_V hx)
  · rw [hZ, hU]
    exact hirr
  · refine le_antisymm (le_inf (pCoreOf_le 2 L) ?_) (E.ker_le hU)
    exact E.pCoreOf_L_le_Q.trans (pCoreOf_le_centralizer E.red)
  · rw [hU]
    exact (sup_eq_left.2 (hZ.le.trans inf_le_left)).symm

end EntryPlus

end CFSG.Quasithin.C124
