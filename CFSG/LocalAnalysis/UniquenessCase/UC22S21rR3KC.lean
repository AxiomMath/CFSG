module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3KB
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3KA
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3F3A
import CFSG.LocalAnalysis.UniquenessCase.UC1K31
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UFr
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UCheap
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101USyl
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100Res2
import CFSG.LocalAnalysis.UniquenessCase.UC6S898b
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtyEightOq
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem uc22r3k_sig_admissible {D : Data G} {Ch : Choice2011 G} (h15 : S21_15C D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {q : ℕ} (hSz : IsSz (Bar2 L) q) (hq : q.Prime)
    (hq7 : 7 ≤ q) {p : ℕ} (hp : p ∈ D.sig) : 5 ≤ p ∧ ¬ p ∣ q := by
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  have hpd := uc22r8100b_dvd_of_modEq (P2214S.sz_cong_of_s21_15C h15 h1930 c hL hc2 hSz hp)
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact UC6S898.not_three_dvd_two_pow_add_one_of_even (even_two_mul q) hpd
  refine ⟨hpP.five_le_of_ne_two_of_ne_three hp2 hp3, fun hd => ?_⟩
  have : Fact q.Prime := ⟨hq⟩
  rw [(Nat.prime_dvd_prime_iff_eq hpP hq).1 hd] at hpd
  have h5 : q ∣ 5 := by
    rw [← ZMod.natCast_eq_zero_iff] at hpd ⊢
    push_cast at hpd ⊢
    rw [pow_mul, ZMod.pow_card] at hpd
    linear_combination hpd
  have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).1 h5
  omega

theorem uc22r3k_omega_decomp {M L K : Subgroup G}
    (hL : L ∈ calC M) (hK : K ∈ calC M) (hne : K ≠ L) (hset : conjSetOf M L = {L, K}) {n : ℕ}
    (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrn : ¬ r ∣ n) {R B : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R M) (hBR : B ≤ R)
    (hBel : IsElemAbelian r B) (hΩ : ∀ x ∈ R, x ^ r = 1 → x ∈ B) {β : Bar2 M}
    (hβ : β ∈ barImage M B) :
    ∃ x₀ ∈ barImage M B ⊓ barImage M L, ∃ x₁ ∈ barImage M B ⊓ barImage M K,
      ∃ c ∈ barImage M B ⊓ centralizer
        ((barImage M L ⊔ barImage M K : Subgroup (Bar2 M)) : Set (Bar2 M)),
      β = x₀ * x₁ * c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hcomm, hinf, -, -, -, -, hXC⟩ := u4x_bar_structure hL hK hne hset hS
  have hmem : ∀ x ∈ barImage M R, x ^ r = 1 → x ∈ barImage M B := by
    intro x hx hx1
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hx
    have hmR : m ^ r ∈ R.subgroupOf M := by
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
      exact R.pow_mem hm _
    have hπ : uc22p21cPi M (m ^ r) = 1 := by rw [map_pow]; exact hx1
    have h1 := Subgroup.disjoint_def.1 (IsPGroup.disjoint_of_ne _ _ hr2 _ _
      hR.isPGroup.comap_subtype CFSG.pCore_isPGroup) hmR ((QuotientGroup.eq_one_iff _).1 hπ)
    refine uc22p21c_mem_barImage.2 ⟨m, hΩ _ hm ?_, rfl⟩
    rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  have hβr : β ^ r = 1 := by
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hβ
    rw [← map_pow, show m ^ r = 1 from Subtype.ext (by simpa using hBel.2 _ hm), map_one]
  obtain ⟨x₀, hx₀, x₁, hx₁, c, hc, rfl⟩ :=
    uc22r3k_decomp hL hK hne hset hS hr hr2 hrn hR (barImage_mono hBR hβ)
  have hc01 : Commute x₀ x₁ := hcomm x₀ hx₀.2 x₁ hx₁.2
  have hcc : Commute (x₀ * x₁) c :=
    mem_centralizer_iff.1 hc.2 _ (mul_mem (mem_sup_left hx₀.2) (mem_sup_right hx₁.2))
  rw [hcc.mul_pow, hc01.mul_pow] at hβr
  obtain ⟨e0, e1, e2⟩ := u81_eq_of_mul_mul_eq hinf hXC (pow_mem hx₀.2 r) (one_mem _)
    (pow_mem hx₁.2 r) (one_mem _) (pow_mem hc.2 r) (one_mem _) (by rw [hβr, mul_one, mul_one])
  exact ⟨x₀, ⟨hmem x₀ hx₀.1 e0, hx₀.2⟩, x₁, ⟨hmem x₁ hx₁.1 e1, hx₁.2⟩, c,
    ⟨hmem c hc.1 e2, hc.2⟩, rfl⟩

theorem uc22r3k_mem_zpowers_of_mem_inf {M Y R B : Subgroup G} (hY : Y ∈ calC M) {n : ℕ}
    (hSY : IsL2 (Bar2 Y) n ∨ IsSz (Bar2 Y) n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hR : CFSG.ABGLocalTools.IsSylowOf r R M) (hBR : B ≤ R) (hBel : IsElemAbelian r B)
    {α : Bar2 M} (hα : α ∈ barImage M B ⊓ barImage M Y) (hαo : orderOf α = r) {x : Bar2 M}
    (hx : x ∈ barImage M B ⊓ barImage M Y) : x ∈ zpowers α := by
  have : Fact r.Prime := ⟨hr⟩
  have hP : IsPGroup r ↥(barImage M B ⊓ barImage M Y) :=
    (u4x_isSylowOf_barImage hR).isPGroup.to_le (inf_le_left.trans (barImage_mono hBR))
  have : IsCyclic ↥(barImage M B ⊓ barImage M Y) := by
    refine UCK.K31.isCyclic_of_pRank_le_one hr hr2 hP ?_
    refine (CFSG.SectionRank.pRank_mono hr.one_lt inf_le_right).trans ?_
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barImage M Y)]
    exact pRank_le_one_of_isL2_or_isSz (u4x_shape_barImage hY hSY) hr hr2
  have hexp : Monoid.exponent ↥(barImage M B ⊓ barImage M Y) ∣ r :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
      obtain ⟨m, hm, hmg⟩ := uc22p21c_mem_barImage.1 g.2.1
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hmg, ← map_pow,
        show m ^ r = 1 from Subtype.ext (by simpa using hBel.2 _ hm), map_one]
  rw [IsCyclic.exponent_eq_card] at hexp
  have heq := Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hα) (by
    rw [Nat.card_zpowers, hαo]
    exact Nat.le_of_dvd hr.pos hexp)
  rw [← heq] at hx
  exact hx

theorem uc22r3k_false_of_commute {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h15 : S21_15C D Ch) (hNN : R847E3ThinNNOut D) (h1930 : H1930 D)
    (c : Ctx21 D Ch) (he : CFSG.Open.evenRank G = 3) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {q : ℕ} (hSz : IsSz (Bar2 L) q) (hq : q.Prime)
    {m : ℕ} (hm : Odd m) (hqm : q ∣ 2 ^ m - 1) {b : G} (hb : b ∈ c.B0) (hbo : orderOf b = q)
    (hbT : b ∈ normalizer (D.T : Set G)) (hbL : b ∈ normalizer (L : Set G))
    (hninn : ¬ ∃ y ∈ L, ∀ x ∈ L, b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M)
    {a : G} (haL : a ∈ L) (hao : orderOf a = 5) (hba : b * a = a * b) {p : ℕ} (hp : p ∈ D.sig)
    {x : G} (hxL : x ∈ L) (hxo : orderOf x = p) (hxa : x * a = a * x) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨K, hne, hset, hK⟩ := uc22s21ru4e_exists_second_member hc2 hL
  have hq7 := PartTwo.s13_seven_le_of_dvd hm hq hqm
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  have : Fact p.Prime := ⟨hpP⟩
  obtain ⟨hp5, hpq⟩ := uc22r3k_sig_admissible h15 h1930 c hL hc2 hSz hq hq7 hp
  have hLN : ¬ (L.subgroupOf D.M).Normal := fun hN => by
    have hle := (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hN
    have h1 : conjSetOf D.M L ⊆ {L} := by
      rintro _ ⟨g, hg, rfl⟩
      exact mem_normalizer_iff_map_conj_eq.1 (hle hg)
    have := Set.ncard_le_ncard h1 (Set.finite_singleton L)
    rw [Set.ncard_singleton, hc2] at this
    omega
  have hNA : normalizer (zpowers a : Set G) ≤ D.M :=
    hNN L hL hLN (PartTwo.S17.thin8_of_isSz hSz) (zpowers a) (zpowers_le.2 haL) 5
      (by norm_num) (by norm_num) (by rw [Nat.card_zpowers, hao]) p hp hp5
      fun h => hpq (h.trans (u81_card_outer_dvd (Or.inr hSz)))
  have hX5 : IsPGroup 5 ↥(zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao, pow_one])
  obtain ⟨R, hR, haR⟩ := PartTwo.exists_isSylowOf_ge_of_isPGroup hX5 (zpowers_le.2 (hL.1.le haL))
  have hn5 : ¬ 5 ∣ q := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hq).1 h
    omega
  have h53 : CFSG.Open.pRank 5 D.M ≤ 3 :=
    (CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 5 Nat.prime_five
      (by norm_num) D.M D.maxLocal.1).trans he.le
  obtain ⟨B, hBR, -, hBel, hΩ⟩ := uc22r3k_exists_omega hL hK hne hset (Or.inr hSz)
    Nat.prime_five (by norm_num) hn5 (uc22r3g_five_dvd_card hSz) h53 hR
  have haB : a ∈ B := hΩ a (haR (mem_zpowers a)) (by rw [← hao]; exact pow_orderOf_eq_one a)
  have haM : a ∈ D.M := hL.1.le haL
  have hxM : x ∈ D.M := hL.1.le hxL
  have hαB : uc22p21cPi D.M ⟨a, haM⟩ ∈ barImage D.M B ⊓ barImage D.M L :=
    ⟨uc22p21c_mem_barImage.2 ⟨⟨a, haM⟩, haB, rfl⟩, uc22p21c_mem_barImage.2 ⟨⟨a, haM⟩, haL, rfl⟩⟩
  have hxL' : uc22p21cPi D.M ⟨x, hxM⟩ ∈ barImage D.M L :=
    uc22p21c_mem_barImage.2 ⟨⟨x, hxM⟩, hxL, rfl⟩
  have hxa' : Commute (uc22p21cPi D.M ⟨x, hxM⟩) (uc22p21cPi D.M ⟨a, haM⟩) :=
    (show Commute (⟨x, hxM⟩ : ↥D.M) ⟨a, haM⟩ from Subtype.ext hxa).map (uc22p21cPi D.M)
  obtain ⟨hcomm, -⟩ := u4x_bar_structure hL hK hne hset (Or.inr hSz)
  have hz : uc22p21cPi D.M ⟨x, hxM⟩ ∈
      centralizer ((barImage D.M B : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) := by
    rw [mem_centralizer_iff]
    intro β hβ
    obtain ⟨x₀, hx₀, x₁, hx₁, c', hc', rfl⟩ := uc22r3k_omega_decomp hL hK hne hset (Or.inr hSz)
      Nat.prime_five (by norm_num) hn5 hR hBR hBel hΩ hβ
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 (uc22r3k_mem_zpowers_of_mem_inf hL (Or.inr hSz)
      Nat.prime_five (by norm_num) hR hBR hBel hαB
      (orderOf_bar_eq_of_prime haM Nat.prime_five (by norm_num) hao) hx₀)
    exact (((hxa'.zpow_right k).mul_right (hcomm _ hxL' x₁ hx₁.2)).mul_right
      (mem_centralizer_iff.1 hc'.2 _ (mem_sup_left hxL'))).eq.symm
  have hdvd := u81_dvd_card_centralizer (hBR.trans hR.le) Nat.prime_five (by norm_num)
    (hR.isPGroup.to_le hBR) hpP hp2 (orderOf_bar_eq_of_prime hxM hpP hp2 hxo) hz
  have hXU : zpowers a ∈ uniqueSet D.M :=
    u81_mem_uniqueSet_of_dvd (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hp)
      hR hBR hBel hΩ (zpowers_le.2 haB) hNA hdvd
  have ha1 : a ≠ 1 := by rintro rfl; rw [orderOf_one] at hao; omega
  exact uc22r3g_false_of_uniqueSet h1930 c hne hset (uc22r3g_comm_of_isSz hL hSz) hq (by omega)
    hb hbo hbT hbL (uc22r3g_not_inner hL (center_eq_bot_of_isSz hL.2.2 hSz) hbL hninn)
    (zpowers_ne_bot.2 ha1) ⟨5, Nat.prime_five, hX5⟩
    (zpowers_le.2 (mem_centralizer_singleton_iff.2 hba.symm)) hXU

@[expose] def S21_22R3F3SzQ5T (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ H₁ ∈ hSet D.T D.M, ∀ H₂ ∈ hSet D.T D.M, c.L0 ≤ H₁ ⊓ H₂ →
    (∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G)) →
    ⁅Hinf D.M, oTwoFOf D.M⁆ ≤ CFSG.Open.pCoreOf 2 D.M →
    (∀ p ∈ D.sig, CFSG.Open.pRank p (barPreimage D.M (centE D.M)) = 0) →
    D.sig = D.sig1 → CFSG.Open.evenRank G = 3 →
    ∀ L ∈ calC D.M, (conjSetOf D.M L).ncard = 2 → ∀ n : ℕ, 2 < n → IsSz (Bar2 L) n →
      ∀ (q : ℕ) (b : G), q.Prime → q ∣ n → ¬ q ∣ 2 ^ n - 1 →
        (∃ e m : ℕ, Odd m ∧ c.n = 2 ^ e * m ∧ q ∣ 2 ^ m - 1) →
        b ∈ c.B0 → orderOf b = q → b ∈ normalizer (D.T : Set G) →
        b ∈ normalizer (L : Set G) → n = q → 5 ∉ D.sig → CFSG.Open.pRank 5 D.M = 3 →
        (∀ a ∈ L, orderOf a = 5 → b * a = a * b → ∀ p ∈ D.sig, ∀ x ∈ L, orderOf x = p →
          x * a ≠ a * x) →
        (¬ ∃ y ∈ L, ∀ x ∈ L, b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) → False

theorem s21_22R3F3SzQ5_of_s21_22R3F3SzQ5T {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h15 : S21_15C D Ch) (hNN : R847E3ThinNNOut D)
    (h : S21_22R3F3SzQ5T D Ch) : S21_22R3F3SzQ5 D Ch := by
  intro h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hS1 hU3 hs he L hL hc2 n hn hSz q b hq hqd hqn hm hb hbo
    hbT hbL hnq h5 h53 hninn
  by_cases hT : ∀ a ∈ L, orderOf a = 5 → b * a = a * b → ∀ p ∈ D.sig, ∀ x ∈ L, orderOf x = p →
      x * a ≠ a * x
  · exact h h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hS1 hU3 hs he L hL hc2 n hn hSz q b hq hqd hqn hm hb
      hbo hbT hbL hnq h5 h53 hT hninn
  · push Not at hT
    obtain ⟨a, haL, hao, hba, p, hp, x, hxL, hxo, hxa⟩ := hT
    subst hnq
    obtain ⟨-, m, hmo, -, hqm⟩ := hm
    exact uc22r3k_false_of_commute hSg h15 hNN h1930 c he hL hc2 hSz hq hmo hqm hb hbo hbT hbL
      hninn haL hao hba hp hxL hxo hxa

end CFSG.LocalAnalysis.UniquenessCase.UC22
