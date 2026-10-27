module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC15TFrame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC15TDir
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC15TOmega
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC15TSym
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC15TTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenSmall

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16c15t_rk_subgroupOf {Y : Type*} [Group Y] {E L₀ : Subgroup Y} (h : E ≤ L₀) :
    rk ↥(E.subgroupOf L₀) = rk ↥E := by
  unfold rk
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]

private theorem s16c15t_rk_le_three_of_isSym {Y : Type} [Group Y] {n : ℕ} (hn : n / 2 = 3)
    {L₀ E : Subgroup Y} (hsym : IsSym ↥L₀ n) (hEL : E ≤ L₀)
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h2 : ∀ a ∈ E, a ^ 2 = 1) : rk ↥E ≤ 3 := by
  obtain ⟨e⟩ := hsym
  have h := s16c15t_rk_le_of_mulEquiv_perm e (E := E.subgroupOf L₀)
    (fun a ha b hb => Subtype.ext (hc _ ha _ hb)) (fun a ha => Subtype.ext (h2 _ ha))
  rw [s16c15t_rk_subgroupOf hEL, hn] at h
  exact h

private theorem s16c15t_rk_le_one_of_index_two {Y : Type*} [Group Y] [Finite Y]
    {L₀ N E : Subgroup Y} (hNL : N ≤ L₀) (hEL : E ≤ L₀) (hEN : E ⊓ N = ⊥)
    (hcard : Nat.card L₀ = 2 * Nat.card N) : rk ↥E ≤ 1 := by
  have hcardN' : Nat.card (N.subgroupOf L₀) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv
  have hidx : (N.subgroupOf L₀).index = 2 := by
    have h1 := Subgroup.card_mul_index (N.subgroupOf L₀)
    rw [hcardN', hcard] at h1
    have hpos : 0 < Nat.card N := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (mul_comm _ _))
  haveI : (N.subgroupOf L₀).Normal := Subgroup.normal_of_index_eq_two hidx
  let φ : ↥E →* ↥L₀ ⧸ N.subgroupOf L₀ :=
    (QuotientGroup.mk' (N.subgroupOf L₀)).comp (Subgroup.inclusion hEL)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro e he
    have h1 : (Subgroup.inclusion hEL e : ↥L₀) ∈ N.subgroupOf L₀ :=
      (QuotientGroup.eq_one_iff _).1 he
    have h3 : (e : Y) ∈ N := h1
    have h4 : (e : Y) ∈ E ⊓ N := ⟨e.2, h3⟩
    rw [hEN] at h4
    exact Subtype.ext (Subgroup.mem_bot.1 h4)
  have hle : Nat.card ↥E ≤ Nat.card (↥L₀ ⧸ N.subgroupOf L₀) :=
    Nat.card_le_card_of_injective _ hinj
  have hidx' : Nat.card (↥L₀ ⧸ N.subgroupOf L₀) = 2 := hidx
  have hdvd : 2 ^ rk ↥E ∣ Nat.card ↥E := pow_padicValNat_dvd
  have h2 : 2 ^ rk ↥E ≤ 2 ^ 1 := by
    calc 2 ^ rk ↥E ≤ Nat.card ↥E := Nat.le_of_dvd Nat.card_pos hdvd
      _ ≤ 2 := hidx' ▸ hle
      _ = 2 ^ 1 := by norm_num
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).1 h2

theorem s16c15t_rk_le_three (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hC : Counterex16 D ⊥ V L hV) (hS : Case168_2Small D ⊥ V hV L)
    {E : Subgroup (MulAut (Vtil ⊥ V hV))} (hE : E ≤ Mbar D.M ⊥ V hV)
    (hE2 : IsElemAbelian2 E) (hfix : rkIdx (fixV E) ≤ 3) : rk ↥E ≤ 3 := by
  have h2 : Case168_2 D ⊥ V hV L := hS.case168_2
  have hS' := hS
  obtain ⟨hsym, ⟨L₀, hI, hfam⟩, -⟩ := hS
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hsq : ∀ e ∈ E, e * e = 1 := fun e he => by
    have h := hE2.2 e he
    rwa [pow_two] at h
  have hrkJ : ∀ J : Subgroup (Vtil ⊥ V hV), Nat.card J = 2 ^ rk ↥J := fun J =>
    card_eq_two_pow hW J
  have hLM : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hC.setting.hyp151.le
  rcases hfam with ⟨hs6, ha6, hsum⟩ | ⟨hs7, ha7, hsum⟩ | ⟨hL0, hLb, hsum⟩ | ⟨hO, hΩ, hsum⟩
  · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two hsum
    have hr4 : 4 ≤ rk ↥J₀ := by
      have h := s16c1610_two_pow_le_card_alternatingNatural (by norm_num : 2 ≤ 6) hN₀
      rw [hrkJ J₀] at h
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h
    obtain ⟨hcomm, -, -, -⟩ := s16c15t_frame D hC hS'
      (s16c167_mem_irrSet_alt (n := 6) (by norm_num) hN₀)
      (s16c167_mem_irrSet_alt (n := 6) (by norm_num) hN₁) hinf hsup hr4 hE hsq hfix
    have hEL : E ≤ L₀ := fun e he =>
      s16c15t_mem_right_of_commute_oddBar D h2 hI (hE he) (hsq e he) (hcomm e he)
    exact s16c15t_rk_le_three_of_isSym (by norm_num) hs6 hEL hE2.1 hE2.2
  · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two hsum
    have hr4 : 4 ≤ rk ↥J₀ := by
      have h := s16c1610_two_pow_le_card_alternatingNatural (by norm_num : 2 ≤ 7) hN₀
      rw [hrkJ J₀] at h
      exact le_trans (by norm_num) ((Nat.pow_le_pow_iff_right (by norm_num)).1 h)
    obtain ⟨hcomm, -, -, -⟩ := s16c15t_frame D hC hS'
      (s16c167_mem_irrSet_alt (n := 7) (by norm_num) hN₀)
      (s16c167_mem_irrSet_alt (n := 7) (by norm_num) hN₁) hinf hsup hr4 hE hsq hfix
    have hEL : E ≤ L₀ := fun e he =>
      s16c15t_mem_right_of_commute_oddBar D h2 hI (hE he) (hsq e he) (hcomm e he)
    exact s16c15t_rk_le_three_of_isSym (by norm_num) hs7 hEL hE2.1 hE2.2
  · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two hsum
    have hr4 : rk ↥J₀ = 4 := by
      have h := s16c1610_rk_binaryNaturalSL hN₀
      omega
    obtain ⟨-, -, -, hrk⟩ := s16c15t_frame D hC hS'
      (s16c167_mem_irrSet_ln (m := 4) (by norm_num) hN₀)
      (s16c167_mem_irrSet_ln (m := 4) (by norm_num) hN₁) hinf hsup hr4.ge hE hsq hfix
    omega
  · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two hsum
    have hr4 : 4 ≤ rk ↥J₀ := by
      have h := s16c1610_rk_natOmegaMinus (by norm_num : 2 ≤ 6) hN₀
      omega
    obtain ⟨hcomm, hfaith, htr, -⟩ := s16c15t_frame D hC hS'
      (s16c167_mem_irrSet_omegaMinus (Or.inl rfl) hN₀)
      (s16c167_mem_irrSet_omegaMinus (Or.inl rfl) hN₁) hinf hsup hr4 hE hsq hfix
    have hEL : E ≤ L₀ := fun e he =>
      s16c15t_mem_right_of_commute_oddBar D h2 hI (hE he) (hsq e he) (hcomm e he)
    have hZ : ∀ k ∈ kBar D.M ⊥ V hV L, (∀ k' ∈ kBar D.M ⊥ V hV L, k * k' = k' * k) → k = 1 := by
      intro κ hκ hc
      have h1 := s16c167_center_of_isSym_three hsym ⟨κ, hκ⟩
        (fun y => Subtype.ext (hc y y.2).symm)
      simpa using congrArg Subtype.val h1
    have hLL₀ : lBar ⊥ V hV L ≤ L₀ := by
      refine s16c1614_le_right_of_centralizes hI hLM ?_ hZ
      intro n hn k hk
      exact (Subgroup.mem_centralizer_iff.1 hk.2) n hn
    have hEbot : E ⊓ lBar ⊥ V hV L = ⊥ := by
      rw [eq_bot_iff]
      intro e he
      have hfix0 : ∀ x ∈ J₀, e x = x := by
        rcases s16c15t_transvection_of_rk_commSub_le_one hW (htr e he.1) with h | ⟨c, hc, hcx⟩
        · exact h
        · exact s16c15t_noTrans_of_natOmegaMinus hN₀ he.2 hc hcx
      exact Subgroup.mem_bot.2 (hfaith e he.1 hfix0)
    have hcard : Nat.card ↥L₀ = 2 * Nat.card ↥(lBar ⊥ V hV L) :=
      s16e_card_eq_two_mul_of_isOMinus (Or.inl rfl) hO hΩ
    have h1 := s16c15t_rk_le_one_of_index_two hLL₀ hEL hEbot hcard
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
