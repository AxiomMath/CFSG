module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCATwoFam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCATwoRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MSetting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MMembers
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2Ord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c13bcA_pairFix_of_family (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h4 : 3 < CFSG.Open.evenRank G) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hns : ¬ Case168_2Small D ⊥ V hV L) (h2 : Case168_2 D ⊥ V hV L)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))} {J₀ J₁ : Subgroup (Vtil ⊥ V hV)}
    (F : Cfg2Setting (Mbar D.M ⊥ V hV) (lBar ⊥ V hV L) J₀ J₁)
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hfam : s16c2m_FamilyJ (lBar ⊥ V hV L) L₀ J₀ J₁) :
    s16c13bcA_PairFix (lBar ⊥ V hV L) J₀ := by
  have hK : IsSym ↥(kBar D.M ⊥ V hV L) 3 := h2.1
  have hsig : D.sig = {3} := h2.2.2
  have hp3 : (3 : ℕ) ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 3
  have hK6 : Nat.card ↥(kBar D.M ⊥ V hV L) = 6 :=
    (s16c1610_card_of_isSym hK).trans (by decide)
  have hrank : 3 ≤ CFSG.Open.pRank 3 (Mbar D.M ⊥ V hV) :=
    s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 hc.setting.hyp16 hV h4 hp3
  rcases hfam with ⟨n, hn5, hn11, hL₀, hL, hrk, hN₀, hN₁⟩ | ⟨m, hm3, hm5, hL₀, hL, hN₀, hN₁, hsum⟩ |
      ⟨hL₀, hL, hrk, hN₀, hN₁⟩ | ⟨hL₀, hL, hrk, hN₀, hN₁⟩ | ⟨hL₀, hL, hrk, hN₀, hN₁⟩
  · rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7 ∨ 8 ≤ n) with rfl | rfl | rfl | h8
    · exact (s16c13bcA_false_of_three_le_pRank hdir hK6
        (Or.inl ((s16c1610_card_of_isSym hL₀).trans (by decide))) hrank).elim
    · exact (hns ⟨hK, ⟨L₀, hdir, Or.inl ⟨hL₀, hL,
        s16c13bcA_sumOfNat_of_two hN₀ hN₁ F.inf_eq F.sup_eq⟩⟩, hsig⟩).elim
    · exact (hns ⟨hK, ⟨L₀, hdir, Or.inr (Or.inl ⟨hL₀, hL,
        s16c13bcA_sumOfNat_of_two hN₀ hN₁ F.inf_eq F.sup_eq⟩)⟩, hsig⟩).elim
    · exact s16c13bcA_pair_alt h8 hN₀
  · rcases (by omega : m = 3 ∨ m = 4 ∨ m = 5) with rfl | rfl | rfl
    · exact (s16c13bcA_false_of_three_le_pRank hdir hK6 (Or.inr (s16c13bcA_card_isLn_three hL₀))
        hrank).elim
    · exact (hns ⟨hK, ⟨L₀, hdir, Or.inr (Or.inr (Or.inl ⟨hL₀, hL, hsum⟩))⟩, hsig⟩).elim
    · exact s16c13bcA_pair_sl hN₀
  · exact s16c13bcA_pair_sp le_rfl hN₀
  · exact (hns ⟨hK, ⟨L₀, hdir, Or.inr (Or.inr (Or.inr ⟨hL₀, hL,
      s16c13bcA_sumOfNat_of_two hN₀ hN₁ F.inf_eq F.sup_eq⟩))⟩, hsig⟩).elim
  · exact s16c13bcA_pair_omegaMinus le_rfl hN₀

theorem s16c13bcA_case168_2 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h4 : 3 < CFSG.Open.evenRank G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D ⊥ V L hV) (hns : ¬ Case168_2Small D ⊥ V hV L)
    (h2 : Case168_2 D ⊥ V hV L) : Insp1613U D V := by
  classical
  have h : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hp3 : (3 : ℕ) ∈ D.sig := by
    rw [h2.2.2]
    exact Set.mem_singleton 3
  obtain ⟨L₀, J₀, J₁, F, hLX, hKX, hKL, hK, hdir, hle, hE₀, hE₁, hfam⟩ := s16c2m_setting D hc h2
  have hpair : s16c13bcA_PairFix (lBar ⊥ V hV L) J₀ :=
    s16c13bcA_pairFix_of_family D hx h61 h127 h4 hc hns h2 F hdir hfam
  obtain ⟨G3, π, hinj, -, ⟨a, ha⟩, -, hact, hsurjK, -, -, -, -⟩ :=
    s16c2m_members F hKX hKL hK hE₀ hE₁
  obtain ⟨i₀, hi₀⟩ := s16c13bcA_exists_stable_index hinj (s16c13bcA_wBar_isPGroup D hV)
    (fun b hb i => ⟨π ⟨b, s16c13bcA_wBar_le_mbar D hV hb⟩ i,
      hact ⟨b, s16c13bcA_wBar_le_mbar D hV hb⟩ i⟩)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact ⟨1, rfl⟩)
  obtain ⟨κ, hκ⟩ := hsurjK (Equiv.swap a i₀)
  have hYκ : J₀.map (κ : MulAut (Vtil ⊥ V hV)).toMonoidHom = G3 i₀ := by
    have h1 := hact ⟨(κ : MulAut (Vtil ⊥ V hV)), hKX κ.2⟩ a
    rw [hκ, Equiv.swap_apply_left, ha] at h1
    exact h1
  have hJ0 : J₀ ≠ ⊥ := by
    have h1 := F.irr₀.2.1
    rw [F.fix, inf_bot_eq] at h1
    exact h1.ne'
  have hY0 : G3 i₀ ≠ ⊥ := by
    rw [← hYκ]
    intro h0
    exact hJ0 ((Subgroup.map_eq_bot_iff_of_injective J₀
      (f := (κ : MulAut (Vtil ⊥ V hV)).toMonoidHom) (κ : MulAut (Vtil ⊥ V hV)).injective).1 h0)
  obtain ⟨n, hnY, hn1, hnfix⟩ := s16c13bc_exists_fixed_in D h hY0
    (fun b hb => s16c13bcA_mem_stabSub_of_map_eq (hi₀ b hb))
  have htw := s16c13bcA_pairFix_twist hpair (κ := (κ : MulAut (Vtil ⊥ V hV)))
    (fun l hl => hKL κ κ.2 l hl)
  obtain ⟨a', ha', b', hb', ha3, hb3, hab, hnot, han, hbn⟩ :=
    htw n (hYκ ▸ hnY) hn1
  exact s16c13bcA_insp_of_pair D h hp3 (hLX ha') (hLX hb') ha3 hb3 hab hnot hn1 hnfix han hbn

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
