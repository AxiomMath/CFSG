module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCFix3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCATwoFam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCATwoRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MMembers
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MSetting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2Ord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16t_a_pairFix_or_oneFix_of_family (D : Data G) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hns : ¬ Case168_2Small D ⊥ V hV L)
    (h2 : Case168_2 D ⊥ V hV L)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))} {J₀ J₁ : Subgroup (Vtil ⊥ V hV)}
    (F : Cfg2Setting (Mbar D.M ⊥ V hV) (lBar ⊥ V hV L) J₀ J₁)
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hfam : s16c2m_FamilyJ (lBar ⊥ V hV L) L₀ J₀ J₁) :
    s16c13bcA_PairFix (lBar ⊥ V hV L) J₀ ∨
      (¬ 3 ^ 3 ∣ Nat.card ↥(Mbar D.M ⊥ V hV) ∧
        ∀ w ∈ J₀, w ≠ 1 → ∃ ψ ∈ lBar ⊥ V hV L, orderOf ψ = 3 ∧ ψ w = w) := by
  have hK : IsSym ↥(kBar D.M ⊥ V hV L) 3 := h2.1
  have hsig : D.sig = {3} := h2.2.2
  have hK6 : Nat.card ↥(kBar D.M ⊥ V hV L) = 6 :=
    (s16c1610_card_of_isSym hK).trans (by decide)
  rcases hfam with ⟨n, hn5, hn11, hL₀, hL, hrk, hN₀, hN₁⟩ | ⟨m, hm3, hm5, hL₀, hL, hN₀, hN₁, hsum⟩ |
      ⟨hL₀, hL, hrk, hN₀, hN₁⟩ | ⟨hL₀, hL, hrk, hN₀, hN₁⟩ | ⟨hL₀, hL, hrk, hN₀, hN₁⟩
  · rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7 ∨ 8 ≤ n) with rfl | rfl | rfl | h8
    · refine Or.inr ⟨?_, s16c13bc_fix3_alt le_rfl hN₀⟩
      rw [s16c13bcA_card_internalDirect hdir, hK6, s16c1610_card_of_isSym hL₀]
      decide
    · exact (hns ⟨hK, ⟨L₀, hdir, Or.inl ⟨hL₀, hL,
        s16c13bcA_sumOfNat_of_two hN₀ hN₁ F.inf_eq F.sup_eq⟩⟩, hsig⟩).elim
    · exact (hns ⟨hK, ⟨L₀, hdir, Or.inr (Or.inl ⟨hL₀, hL,
        s16c13bcA_sumOfNat_of_two hN₀ hN₁ F.inf_eq F.sup_eq⟩)⟩, hsig⟩).elim
    · exact Or.inl (s16c13bcA_pair_alt h8 hN₀)
  · rcases (by omega : m = 3 ∨ m = 4 ∨ m = 5) with rfl | rfl | rfl
    · refine Or.inr ⟨?_, s16c13bc_fix3_sl le_rfl hN₀⟩
      rw [s16c13bcA_card_internalDirect hdir, hK6, s16c13bcA_card_isLn_three hL₀]
      decide
    · exact (hns ⟨hK, ⟨L₀, hdir, Or.inr (Or.inr (Or.inl ⟨hL₀, hL, hsum⟩))⟩, hsig⟩).elim
    · exact Or.inl (s16c13bcA_pair_sl hN₀)
  · exact Or.inl (s16c13bcA_pair_sp le_rfl hN₀)
  · exact (hns ⟨hK, ⟨L₀, hdir, Or.inr (Or.inr (Or.inr ⟨hL₀, hL,
      s16c13bcA_sumOfNat_of_two hN₀ hN₁ F.inf_eq F.sup_eq⟩))⟩, hsig⟩).elim
  · exact Or.inl (s16c13bcA_pair_omegaMinus le_rfl hN₀)

theorem s16t_a_case168_2 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hns : ¬ Case168_2Small D ⊥ V hV L) (h2 : Case168_2 D ⊥ V hV L) : Insp1613U D V := by
  classical
  have h : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hp3 : (3 : ℕ) ∈ D.sig := by
    rw [h2.2.2]
    exact Set.mem_singleton 3
  obtain ⟨L₀, J₀, J₁, F, hLX, hKX, hKL, hK, hdir, hle, hE₀, hE₁, hfam⟩ := s16c2m_setting D hc h2
  have hdisj := s16t_a_pairFix_or_oneFix_of_family D hns h2 F hdir hfam
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
  rcases hdisj with hpair | ⟨hsmall, hone⟩
  ·
    have htw := s16c13bcA_pairFix_twist hpair (κ := (κ : MulAut (Vtil ⊥ V hV)))
      (fun l hl => hKL κ κ.2 l hl)
    obtain ⟨a', ha', b', hb', ha3, hb3, hab, hnot, han, hbn⟩ :=
      htw n (hYκ ▸ hnY) hn1
    exact s16c13bcA_insp_of_pair D h hp3 (hLX ha') (hLX hb') ha3 hb3 hab hnot hn1 hnfix han hbn
  ·
    obtain ⟨w, hw, hwn⟩ := Subgroup.mem_map.1 (hYκ ▸ hnY)
    have hw1 : w ≠ 1 := by
      rintro rfl
      exact hn1 (by rw [← hwn]; exact map_one _)
    obtain ⟨ψ, hψ, hψ3, hψw⟩ := hone w hw hw1
    refine s16t_a_insp_of_fixing_lift D hx h61 h127 h hp3 hsmall hn1 hnfix (hLX hψ) hψ3 ?_
    have hc' := hKL κ κ.2 ψ hψ
    rw [← hwn]
    calc ψ ((κ : MulAut (Vtil ⊥ V hV)).toMonoidHom w)
        = (ψ * (κ : MulAut (Vtil ⊥ V hV))) w := rfl
      _ = ((κ : MulAut (Vtil ⊥ V hV)) * ψ) w := by rw [← hc']
      _ = (κ : MulAut (Vtil ⊥ V hV)) (ψ w) := rfl
      _ = (κ : MulAut (Vtil ⊥ V hV)).toMonoidHom w := by rw [hψw]; rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
