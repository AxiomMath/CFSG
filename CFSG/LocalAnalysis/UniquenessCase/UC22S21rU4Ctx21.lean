module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4BC
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p2214_fix_ctx21 (D : Data G) {Ch : Choice2011 G} (c : Ctx21 D Ch) {K : Subgroup G}
    (hKM : K ≤ D.M)
    (hK : (K.subgroupOf D.M).Normal ∨ (conjSetOf D.M K).ncard = 2) :
    ∀ K' ∈ conjSetOf D.M K, c.B0 ≤ normalizer (K' : Set G) := by
  intro K' hK' b hb
  have hbM : b ∈ D.M := c.hBM hb
  rcases hK with hn | hc2
  · obtain ⟨g, hg, rfl⟩ := hK'
    have hMK : D.M ≤ normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).1 hn
    have hgK : K.map (MulAut.conj g).toMonoidHom = K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hMK hg)
    rw [hgK]
    exact hMK hbM
  · have hc2' : (conjSetOf D.M K').ncard = 2 := by rw [uc22p2214_conjSetOf_eq hK']; exact hc2
    exact uc22p2214_mem_normalizer_of_odd hc2' hbM (uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 hb)

theorem uc22p2214_false_of_centralizesBar_ctx21 (D : Data G) (Ch : Choice2011 G) (h1930 : H1930 D)
    (c : Ctx21 D Ch) {K : Subgroup G}
    (hN : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ A : Subgroup G, A ≤ D.M → Nat.card A = r →
      (conjClosure D.M K ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 (conjClosure D.M K) =
        conjClosure D.M K → normalizer (A : Set G) ≤ D.M)
    {a : G} (ha : a ∈ c.B0) (ha1 : a ≠ 1)
    (haX : CentralizesBar a (conjClosure D.M K)) : False := by
  have hodd : Odd (orderOf a) := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 ha
  have hne1 : orderOf a ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  have hr : (orderOf a).minFac.Prime := Nat.minFac_prime hne1
  have hrd : (orderOf a).minFac ∣ orderOf a := Nat.minFac_dvd _
  have hr2 : (orderOf a).minFac ≠ 2 := by
    intro h2
    rw [h2] at hrd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hrd)
  have hord : orderOf (a ^ (orderOf a / (orderOf a).minFac)) = (orderOf a).minFac :=
    orderOf_pow_orderOf_div (orderOf_pos a).ne' hrd
  set a' : G := a ^ (orderOf a / (orderOf a).minFac)
  set r : ℕ := (orderOf a).minFac
  have hAcard : Nat.card (zpowers a') = r := by rw [Nat.card_zpowers, hord]
  have hAB : zpowers a' ≤ c.B0 := zpowers_le.2 (c.B0.pow_mem ha _)
  have hAc : ∀ g ∈ zpowers a', CentralizesBar g (conjClosure D.M K) := fun g hg =>
    uc22p21d_centralizesBar_of_mem_zpowers (uc22p21d_centralizesBar_pow haX _) hg
  have hXQ : (conjClosure D.M K ⊓ centralizer ((zpowers a' : Subgroup G) : Set G)) ⊔
      pCoreOf 2 (conjClosure D.M K) = conjClosure D.M K :=
    uc22p21d_sup_pCore_eq hr hr2 hAcard hAc
  exact s21_2 D Ch h1930 { c with B := c.B0, hB := c.hB0, hle := le_rfl } (zpowers a') hAB
    (hN r hr hr2 (zpowers a') (hAB.trans c.hBM) hAcard hXQ)

theorem uc22p2213a_false_of_odd_dvd_ctx21 (D : Data G) (Ch : Choice2011 G)
    (h869P : F08.R869NPair D) (h1930 : H1930 D) (c : Ctx21 D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hc2 : (conjSetOf D.M K).ncard = 2) {n : ℕ}
    (hn2 : 2 < n) (hL2 : IsL2 (Bar2 K) n) (hpow : IsPowTwo n) {m : ℕ} (hmo : Odd m)
    (hm1 : 1 < m) (hmn : m ∣ c.n) : False := by
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hK.1
  have h4 : 4 ≤ 2 ^ m :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd (show 2 ^ m - 1 ≠ 1 by omega)
  have hr2 : r ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    omega
  have hrpi : r ∈ piSet c.B0 := by
    rw [c.hpi]
    refine ⟨hr, hrm.trans ?_⟩
    have h := Nat.pow_sub_one_gcd_pow_sub_one 2 m c.n
    rw [Nat.gcd_eq_left hmn] at h
    rw [← h]
    exact Nat.gcd_dvd_right _ _
  have hrn : ¬ r ∣ n := by
    obtain ⟨j, rfl⟩ := hpow
    intro h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  have hrL : ∀ {X : Type} [Group X] [Finite X], IsL2 X n → ¬ r ∣ Nat.card X := by
    intro X _ _ hX h
    rw [uc22p22r_L2_card hX] at h
    rcases (Nat.Prime.dvd_mul hr).1 h with h1 | h1
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h1))
    · rw [← pow_mul] at h1
      have h2 : r ∣ Nat.gcd (2 ^ m - 1) (2 ^ (n * 2) - 1) := Nat.dvd_gcd hrm h1
      rw [Nat.pow_sub_one_gcd_pow_sub_one] at h2
      have hg : Nat.gcd m (n * 2) = 1 := by
        obtain ⟨j, rfl⟩ := hpow
        rw [← pow_succ]
        exact Nat.Coprime.pow_right _ hmo.coprime_two_right
      rw [hg, pow_one] at h2
      exact hr.not_dvd_one (by simpa using h2)
  obtain ⟨a, haB, hao⟩ := uc22p22i_exists_elt_of_mem_piSet hrpi
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hao
    exact hr.one_lt.ne hao
  have har : a ^ r = 1 := by
    rw [← hao]
    exact pow_orderOf_eq_one a
  have hfix := uc22p2214_fix_ctx21 D c hKM (Or.inr hc2)
  obtain ⟨hXM, hMX, -⟩ := uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hK
  have haM : a ∈ D.M := c.hBM haB
  have haX : CentralizesBar a (conjClosure D.M K) := by
    refine uc22p2214_centralizesBar_conjClosure (hMX haM) fun K' hK' k hk => ?_
    have hK'C := uc22p2214_calC_of_mem_conjSetOf hK hK'
    have hL2' : IsL2 (Bar2 K') n := by
      obtain ⟨g, -, rfl⟩ := hK'
      obtain ⟨e⟩ := uc22p20d_bar2_conj g K
      exact CFSG.Blueprint.LieModel.of_mulEquiv e hL2
    have hcb := uc22p2213a_centralizesBar_of_prime hL2' hr hrn (hrL hL2') (hfix K' hK' haB) har
    have h1 : a * k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 D.M :=
      uc22p22r_pCoreOf_le_of_isSubnormal hK'C.1 (hcb.2 k hk)
    have hkX : k ∈ conjClosure D.M K :=
      le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf D.M K) => A) K' hK' le_rfl hk
    have h2 : a * k * a⁻¹ * k⁻¹ ∈ conjClosure D.M K :=
      (conjClosure D.M K).mul_mem ((mem_normalizer_iff.1 (hMX haM) k).1 hkX)
        ((conjClosure D.M K).inv_mem hkX)
    exact uc22p2214_pCoreOf_inf_le hXM ⟨h1, h2⟩
  exact uc22p2214_false_of_centralizesBar_ctx21 D Ch h1930 c (h869P K hK hc2 n hn2 hpow hL2) haB
    ha1 haX

theorem uc22p2213a_false_of_not_isPowTwo_ctx21 (D : Data G) (Ch : Choice2011 G)
    (h869P : F08.R869NPair D) (h1930 : H1930 D) (c : Ctx21 D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hc2 : (conjSetOf D.M K).ncard = 2) {n : ℕ}
    (hn2 : 2 < n) (hL2 : IsL2 (Bar2 K) n) (hpow : IsPowTwo n) (hn0 : ¬ IsPowTwo c.n) : False := by
  obtain ⟨k, m, hmo, hnk⟩ := Nat.exists_eq_two_pow_mul_odd (uc22p2213a_n_ne_zero D c)
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hn0 ⟨k, by rw [hnk, mul_one]⟩
  have hm0 : 0 < m := hmo.pos
  exact uc22p2213a_false_of_odd_dvd_ctx21 D Ch h869P h1930 c hK hc2 hn2 hL2 hpow hmo
    (by omega) (Dvd.intro_left _ hnk.symm)

theorem s21_22U4A_of_ctx21 (D : Data G) (Ch : Choice2011 G) (h869P : F08.R869NPair D)
    (h8100E : R8100E D) (h1930 : H1930 D) (he : 3 < CFSG.Open.evenRank G) (c : Ctx21 D Ch)
    (hn3 : 3 ≤ c.n) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hn : 2 < n) (hL2 : IsL2 (Bar2 L) n)
    (hpow : IsPowTwo n) : False := by
  by_cases hn0 : IsPowTwo c.n
  · exact uc22p2213f_false_of_powTwo D Ch h8100E h1930 he c hn3 hn0 hL hc2 hn.le hpow hL2
  · exact uc22p2213a_false_of_not_isPowTwo_ctx21 D Ch h869P h1930 c hL hc2 hn hL2 hpow hn0

theorem s21_22U4_of_U4BC_ctx21 (D : Data G) (Ch : Choice2011 G) (h869P : F08.R869NPair D)
    (h8100E : R8100E D) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (hBC : S21_22U4BC D Ch) :
    S21_22U4 D Ch := by
  intro h1930 c H₁ hH₁ H₂ hH₂ hL hfX hS1 hU3 he L hLC hc2 hn
  obtain ⟨n, hn2, hLn⟩ := hn
  rcases hLn with hL2 | hSz
  · by_cases hpow : IsPowTwo n
    · exact s21_22U4A_of_ctx21 D Ch h869P h8100E h1930 he c (hn3 h1930 c) hLC hc2 hn2 hL2 hpow
    · exact hBC h1930 c H₁ hH₁ H₂ hH₂ hL hfX hS1 hU3 he L hLC hc2
        ⟨n, hn2, Or.inr ⟨hL2, hpow⟩⟩
  · exact hBC h1930 c H₁ hH₁ H₂ hH₂ hL hfX hS1 hU3 he L hLC hc2 ⟨n, hn2, Or.inl hSz⟩

theorem uc22m57_exists_ctx21_ne_bot_ctx21 {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    (hn3 : 3 ≤ c.n) : ∃ c : Ctx21 D Ch, c.B ≠ ⊥ :=
  ⟨{ c with B := c.B0, hB := c.hB0, hle := le_rfl }, uc22s13xl_B0_ne_bot c (by omega)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
