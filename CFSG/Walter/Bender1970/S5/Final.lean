module

public import CFSG.Walter.Bender1970.S5.TwoCore

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem bender1970_5_4
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G)) {s : G}
    (hsT : s ∈ (T : Subgroup G)) (hs : orderOf s = 2) : benderM s = {H} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTab := hG.hasAbelianSylowTwo T
  have hHco := isCoatom_of_mem_benderM hH
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  obtain ⟨hC, hncyc⟩ := bender1970_5_3 hG ht hH
  have hO2T : qCoreOf H 2 ≤ T := qCoreOf_two_le_sylow T hTH
  have hO2ab : IsMulCommutative (qCoreOf H 2) :=
    ⟨⟨fun a b => Subtype.ext (show (a : G) * b = b * a from congrArg Subtype.val
      (hTab.is_comm.comm ⟨a, hO2T a.2⟩ ⟨b, hO2T b.2⟩))⟩⟩
  obtain ⟨V₀, hV₀O, hV₀⟩ :=
    exists_isKleinFour_le_of_not_isCyclic (qCoreOf_isPGroup H 2) hO2ab hncyc
  have key : ∀ M ∈ benderM s, M = H := by
    intro M hM
    have hMco := isCoatom_of_mem_benderM hM
    have hMA := hG.isAStar_of_isCoatom hMco
    have hMs := bender1970_5_1 hG hs hM
    have hTM := hG.sylow_le_of_mem_benderM T hsT hM
    have hO : oddCoreOf M ≤ H := le_of_forall_centralizer_le_of_odd hV₀
      (((hV₀O.trans hO2T).trans hTM).trans (le_normalizer_of_isNormalIn (oddCoreOf_isNormalIn' M)))
      (odd_card_oddCoreOf M) fun v hv hv1 => hC v (hV₀O hv) hv1
    have hMH := le_of_oddCoreOf_le hMA (bender1970_4_3 hG hs hM) T hTM hO
      (by rw [componentLayerOf_eq_bot_of_isSolvable hMs]; exact bot_le) hTH
      (inf_le_right.trans (bender1970_5_2 hG ht hH T htT))
    exact ((hMco.le_iff.mp hMH).resolve_left hHco.1).symm
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs
    omega
  obtain ⟨M₀, hM₀⟩ := hG.benderM_nonempty hs1
  rw [Set.eq_singleton_iff_unique_mem]
  exact ⟨key M₀ hM₀ ▸ hM₀, key⟩

theorem BenderCounterexample.false
    (hG : BenderCounterexample G) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 G) := inferInstance
  obtain ⟨t, htT, ht⟩ : ∃ t ∈ (T : Subgroup G), orderOf t = 2 := by
    obtain ⟨E, hET, -, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two (T : Subgroup G)
    have h3 := hG.three_le_rank_sylow T
    rw [rank_eq_pRank_of_isPGroup Nat.prime_two T.isPGroup'] at h3
    have h2 : 2 ∣ Nat.card E := by
      rw [hcard]
      exact dvd_pow_self 2 (by omega)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := E) 2 h2
    exact ⟨x, hET x.2, by rw [← hx, Subgroup.orderOf_coe]⟩
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  obtain ⟨H, hH⟩ := hG.benderM_nonempty ht1
  obtain ⟨R, hRT, hR⟩ := exists_le_rank_eq_sub_one T (hG.hasAbelianSylowTwo T) htT ht
  obtain ⟨s, hsR, hs, hsH⟩ := bender1970_3_3 hG ht hH T htT hRT hR
  exact hsH (bender1970_5_4 hG ht hH T htT (hRT hsR) hs)

end CFSG.Walter
