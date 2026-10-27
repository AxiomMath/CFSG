module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Four
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gCase153
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gCase168
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gMParam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Generic

variable {T : Type} [CommGroup T] [Finite T]

private theorem s16c1610_eq_one_of_fix_summands {ι : Type} {Y : ι → Subgroup T}
    (hsup : ⨆ i, Y i = ⊤) {x : MulAut T} (h : ∀ i, ∀ v ∈ Y i, x v = v) : x = 1 := by
  have hle : (⨆ i, Y i) ≤ fixV (Subgroup.zpowers x) :=
    iSup_le fun i v hv => mem_fixV_zpowers_iff_apply.2 (h i v hv)
  rw [hsup] at hle
  ext v
  exact mem_fixV_zpowers_iff_apply.1 (hle (Subgroup.mem_top v))

theorem s16c1610_le_rkIdx_fixV_swap (hT : ∀ t : T, t ^ 2 = 1) {Ya Yb : Subgroup T}
    (hd : Disjoint Ya Yb) {d : ℕ} (hrka : rk ↥Ya = d) (hrkb : rk ↥Yb = d) {φ : MulAut T}
    (hφa : Ya.map φ.toMonoidHom = Yb) (hφb : Yb.map φ.toMonoidHom = Ya) :
    d ≤ rkIdx (fixV (Subgroup.zpowers φ)) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨z, hz, hz1, -⟩ := s16n9b_case4_rank_swap hT hd hrka hrkb hlt hφa hφb
    (U := fixV (Subgroup.zpowers φ)) le_rfl
  refine hz1 ?_
  have hle : s16n9bCommOn (fixV (Subgroup.zpowers φ)) φ ≤ ⊥ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨u, hu, rfl⟩
    rw [mem_fixV_zpowers_iff_apply.1 hu, mul_inv_cancel]
    exact Subgroup.one_mem _
  exact Subgroup.mem_bot.1 (hle hz)

theorem s16c1610_two_lt_mParam_of_case4_seven (hT : ∀ t : T, t ^ 2 = 1)
    {X A : Subgroup (MulAut T)} {r : ℕ} (hr : 1 < r) (hA : IsElemAbelianOfRank 7 r ↥A)
    (hAP : A ≤ pCoreOf 7 X) (hS : SymSumOfConj X (⊤ : Subgroup T) r (dParam 7))
    (hge : 3 ≤ CFSG.Open.pRank 7 X) : 2 < E3.mParam X := by
  classical
  obtain ⟨ι, hι, Y, hind, hinj, hsup, hcard, hrk, hperm, hsurj⟩ := s16n9b_case4_data hS
  obtain ⟨F, hFX, hF, hFn, hFY, hQ⟩ :=
    s16n9b_case4_kernel hT (Or.inr rfl) hr hA hAP hge hind hinj hsup hcard hrk hperm hsurj
  obtain ⟨Q, hQX, hQp, hQne, hnorm, hQY⟩ := hQ rfl
  have hd7 : dParam 7 = 3 := s16c1610_dParam_seven
  have hinv : ∀ φ ∈ X, orderOf φ = 2 → 3 ≤ rkIdx (fixV (Subgroup.zpowers φ)) := by
    intro φ hφX hφ
    by_contra hlt
    push Not at hlt
    have hC_lt : rkIdx (fixV (Subgroup.zpowers φ)) < 2 * dParam 7 := by
      rw [hd7]
      omega
    rcases s16n9b_case4_rank_moved hT hind hinj hrk (hperm φ hφX) hC_lt with
      hid | ⟨a, b, hab, hφa, hφb, -⟩
    · have hφne : φ ≠ 1 := by
        rintro rfl
        simp at hφ
      obtain ⟨i, y, hy, hφy⟩ : ∃ i, ∃ y ∈ Y i, φ y ≠ y := by
        by_contra hcon
        push Not at hcon
        exact hφne (s16c1610_eq_one_of_fix_summands hsup hcon)
      have hrki : rk ↥(Y i) = 3 := by rw [hrk i, hd7]
      have hQi := s16n9b_case4_aut_norm7 hT hrki hQp (fun q hq => hQY q hq i)
        ⟨1, by simpa using hφ⟩ (hid i) (hnorm φ hφX) ⟨y, hy, hφy⟩
      have hQall : ∀ q ∈ Q, ∀ j, ∀ v ∈ Y j, q v = v := by
        intro q hq j v hv
        obtain ⟨g, hgX, hg⟩ := hsurj (Equiv.swap i j)
        have hgi : (Y i).map g.toMonoidHom = Y j := by
          rw [hg i, Equiv.swap_apply_left]
        have hv' : v ∈ (Y i).map g.toMonoidHom := by
          rw [hgi]
          exact hv
        obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.1 hv'
        have hq' : g⁻¹ * q * g ∈ Q := by
          have h1 := Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hq
          rw [hnorm g⁻¹ (X.inv_mem hgX)] at h1
          simpa [MulAut.conj_apply] using h1
        have h2 : (g⁻¹ * q * g) v₀ = v₀ := hQi _ hq' v₀ hv₀
        have h3 : g⁻¹ (q (g v₀)) = v₀ := by simpa [MulAut.mul_apply] using h2
        have h4 : q (g v₀) = g v₀ := by
          have := congrArg g h3
          simpa using this
        exact h4
      obtain ⟨q, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQne
      exact hq1 (Subtype.ext (s16c1610_eq_one_of_fix_summands hsup (hQall q.1 q.2)))
    · have h := s16c1610_le_rkIdx_fixV_swap hT (hind.pairwiseDisjoint hab) (hrk a) (hrk b) hφa hφb
      rw [hd7] at h
      omega
  unfold E3.mParam
  split_ifs with hev
  · set S : Set ℕ := {n | ∃ t ∈ X, orderOf t = 2 ∧ n = rkIdx (fixV (Subgroup.zpowers t))} with hS'
    have hne : S.Nonempty := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 (even_iff_two_dvd.1 hev)
      exact ⟨_, (x : MulAut T), x.2, by rw [Subgroup.orderOf_coe]; exact hx, rfl⟩
    obtain ⟨t, htX, ht2, hn⟩ := Nat.sInf_mem hne
    rw [hn]
    have := hinv t htX ht2
    omega
  · have hpos : 0 < Fintype.card ι := by omega
    obtain ⟨i⟩ := Fintype.card_pos_iff.1 hpos
    have h1 : rk ↥(Y i) ≤ rk ↥(⊤ : Subgroup T) := rk_mono le_top
    rw [rk_top, hrk i, hd7] at h1
    omega

end Generic

section Counterexample

variable {G : Type} [Group G] [Finite G]

theorem s16c1610_two_lt_mBar_of_case4_seven (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h4 : 3 < CFSG.Open.evenRank G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) {r : ℕ} (hr : 1 < r)
    (h4At : Case168_4At D V₀ V hV L 7 r) : 2 < mBar D.M V₀ V hV := by
  have hge := s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 hc.setting.hyp16 hV h4 h4At.2.2
  exact s16c1610_two_lt_mParam_of_case4_seven (s15_Infra_vtil_sq_eq_one V₀ V hV) hr h4At.1
    (s16n9b_case4_pcore D hV hc (by norm_num) hr h4At.1) h4At.2.1 hge

theorem r1613g_one_lt_mBar_of_four (D : Data G) (hext : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1217 : R1217 D) (h153 : R15_3Small D) (h4 : 3 < CFSG.Open.evenRank G)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) :
    1 < mBar D.M V₀ V hV := by
  by_contra hlt
  have hS : Sect16 D V₀ V L hV := ⟨hc.setting, hc.ne_bot, hc.conc⟩
  have hMne : Mbar D.M V₀ V hV ≠ ⊥ := by
    intro hbot
    apply hc.ne_bot
    exact le_bot_iff.mp
      ((barSub_mono V₀ V hV hc.setting.hyp151.le).trans (le_of_eq hbot))
  have hne : mBar D.M V₀ V hV ≠ 0 :=
    r1613g_mParam_ne_zero (s15_Infra_vtil_sq_eq_one V₀ V hV) hMne
  have hm1 : mBar D.M V₀ V hV = 1 := by omega
  rcases sixteen_one D h1217 h153 hc.setting.hyp151 hc.setting.hyp16.small hV hc.ne_bot hm1 with
    h1 | h2 | h3
  · have h3sig : 3 ∈ D.sig := by rw [h1.2.2.1]; exact Set.mem_singleton 3
    have h4' := hext.four_le h4 3 h3sig
    have h3rk := h1.2.2.2.1
    omega
  · obtain ⟨K₀, p, -, -, -, hsig, hrk, -⟩ := h2
    have hp : p ∈ D.sig := by rw [hsig]; exact Set.mem_singleton p
    have h4' := hext.four_le h4 p hp
    omega
  · obtain ⟨hcard, hrk⟩ := r1613g_case153_3_summary D hc.conc h3
    have h8 := r1613g_case168_eight_of_card_three D hcard hrk hc.concl168
    exact r1613g_not_case168_8_of_four D hext h61 h127 h4 hS h8

theorem s16c1610_k_lt_mBar_of_case4_four (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    (h153 : R15_3Small D) (h4 : 3 < CFSG.Open.evenRank G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) {p r : ℕ} (hp : p = 3 ∨ p = 7)
    (hr : 1 < r) (h4At : Case168_4At D V₀ V hV L p r) : D.k < mBar D.M V₀ V hV := by
  rcases hp with rfl | rfl
  · have hk : D.k = 1 := Data.k_eq_one_of_three_mem D hin.hSg hin.h1219 h4At.2.2
    have h1 := r1613g_one_lt_mBar_of_four D hin.hx hin.h61 hin.h127 h1217 h153 h4 hc
    omega
  · have h2 := s16c1610_two_lt_mBar_of_case4_seven D hin.hx hin.h61 hin.h127 h4 hc hr h4At
    have hk := s16c167_k_le_two D
    omega

end Counterexample

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
