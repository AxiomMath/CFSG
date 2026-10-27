module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrL
public import CFSG.Quasithin.Vol2.Ch10SecKHBC
public import CFSG.Quasithin.Vol2.Ch9FactsOdd
public import CFSG.Quasithin.Vol2.Ch4Sec3L4316L34
public import CFSG.Quasithin.Vol2.GoldschmidtP778A5Setup
public import CFSG.Quasithin.H13.U3L14Grp
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspNotRankLie
public import CFSG.Quasithin.Vol2.Ch12Sec2E22BorelLiftOne

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10.SecB CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS
open scoped Pointwise

namespace Fin125

theorem eq_two_of_two_pow_sub_one_eq_three_pow {n b : ℕ} (hn : 2 ≤ n)
    (h : 2 ^ n - 1 = 3 ^ b) : n = 2 := by
  by_contra hne
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have h8 : 2 ^ (k + 3) = 2 ^ k * 8 := by rw [pow_add]; norm_num
  have hb : ∀ c : ℕ, 3 ^ c % 8 = 1 ∨ 3 ^ c % 8 = 3 := by
    intro c
    induction c with
    | zero => simp
    | succ c ih => rw [pow_succ]; omega
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rcases hb b with h1 | h1 <;> omega

variable {G : Type} [Group G] [Finite G]

theorem hall_three_of_lift {H T MH : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hL : E2.E22BorelLift H T MH n)
    (hhall : ∀ C : Subgroup G, C ≤ MH → Odd (Nat.card C) → (∃ k : ℕ, C.relIndex MH = 2 ^ k) →
      C ≠ ⊥ ∧ IsPGroup 3 C) :
    n = 2 ∧ ∃ C : Subgroup G, Lin2.IsHallTwoPrimeOf C MH ∧ IsPGroup 3 C := by
  obtain ⟨-, R, -, -, -, ⟨C, hCM, hCodd, k, hCk⟩, hall⟩ := hL
  obtain ⟨-, -, -, Y, hYC, -, hYc, -⟩ := hall C hCM hCodd ⟨k, hCk⟩
  obtain ⟨-, hC3⟩ := hhall C hCM hCodd ⟨k, hCk⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hC3
  have hdvd : 2 ^ n - 1 ∣ 3 ^ a := by
    rw [← hYc, ← ha]
    exact Subgroup.card_dvd_of_le hYC
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  exact ⟨eq_two_of_two_pow_sub_one_eq_three_pow hn hb, C, ⟨hCM, hCodd, k, hCk⟩, hC3⟩

theorem odd_dvd_card_hall {H T X C : Subgroup G} (hXH : X ≤ H) (hT : IsSylowTwoOf T X)
    (hC : Lin2.IsHallTwoPrimeOf C X) {r : ℕ} (hr : Odd r)
    (hrX : r ∣ Nat.card (E2.star X H X)) : r ∣ Nat.card C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := card_star_mul_card_inf (X := X) hXH
  rw [card_eq_card_mul_card hT hC] at h1
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hT.2.1
  rw [ha] at h1
  have h2 : r ∣ 2 ^ a * Nat.card C := by
    rw [← h1]
    exact hrX.mul_right _
  exact (Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hr)).dvd_of_dvd_mul_left h2

theorem zpowers_le_normalizer_of_comm {Y : Type*} [Group Y] {a b : Y} (hab : a * b = b * a) :
    Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers a : Set Y) := by
  rw [Subgroup.zpowers_le]
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact ((show Commute a b from hab).zpow_left k).eq

theorem exists_borel_psu3_four {Y : Type} [Group Y] [Finite Y]
    (hY : IsPSU 3 2 2 Y) {S : Subgroup Y} (hS : IsSylowTwoOf S ⊤) :
    ∃ D : Subgroup Y, D ≤ Subgroup.normalizer (S : Set Y) ∧ Nat.card D = 15 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ S.index := by
    have h : ¬ 2 ∣ (S.subgroupOf ⊤).index := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right _] at h
  let T : Sylow 2 Y := hS.2.1.toSylow hidx
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hY
  have hcard : Nat.card K = 2 ^ (2 * 2) := by rw [hK, ← pow_mul, mul_comm]
  let e₀ : Y ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ 2)) := e
  let e' := e₀.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative 2 le_rfl hcard)
  obtain ⟨D, hD⟩ :=
    CFSG.Goldschmidt.G3a.exists_borelSetup (Or.inr (Or.inl ⟨2, le_rfl, ⟨e'⟩⟩)) T
  have hDc := (hD.orders_psu3 le_rfl e').2.2
  refine ⟨D, hD.le, ?_⟩
  rw [hDc]
  norm_num

theorem two_le_pRank_psp4_four {X : Type} [Group X] [Finite X] (h : IsPSp4 2 2 X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have hK3 : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, hK]
    norm_num
  have : Finite (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K)) :=
    Finite.of_equiv X e.toEquiv
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  refine CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) (A := Fin 2 → Kˣ)
    (fun a b => mul_comm a b) (fun a => ?_) (k := 2) ?_ (Ch9.FactsOdd.torusP K)
    Ch9.FactsOdd.torusP_injective le_top
  · funext i
    rw [Pi.pow_apply, Pi.one_apply, ← hK3]
    exact pow_card_eq_one'
  · rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hK3]

theorem two_le_pRank_of_star {H MH : Subgroup G} {S : Subgroup (E2.StarQuot MH H)}
    (h : 2 ≤ CFSG.Open.pRank 3 S) : 2 ≤ CFSG.Open.pRank 3 H := by
  have h1 : 2 ≤ CFSG.pRank 3 (E2.StarQuot MH H) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact h.trans (CFSG.SectionRank.pRank_mono (by norm_num) le_top)
  have h2 := Vol2Native.L239.two_le_pRank_of_surjective Nat.prime_three (by norm_num)
    (QuotientGroup.mk' ((kerIn MH H).subgroupOf H)) (QuotientGroup.mk'_surjective _) h1
  rwa [CFSG.SectionRank.pRank_eq_open_pRank_top,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h2

theorem isElemAbelian_sup_zpowers {Y : Type*} [Group Y] [Finite Y] {a b : Y}
    (hab : a * b = b * a) (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥) :
    IsElemAbelian 3 (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ∧
      Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) = 3 ^ 2 := by
  have hcard := QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
    (zpowers_le_normalizer_of_comm hab.symm)
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, ha, hb] at hcard
  have ha3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hb3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hexp : ∀ x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b, x ^ 3 = 1 := by
    intro x hx
    have hN : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers a : Set Y) :=
      zpowers_le_normalizer_of_comm hab
    have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers a)
      (Subgroup.zpowers b) hN
    obtain ⟨y, hy, q, hq, rfl⟩ : x ∈ (Subgroup.zpowers a : Set Y) * (Subgroup.zpowers b : Set Y) :=
      by rw [← hmul]; exact hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    have hc : Commute (a ^ i) (b ^ j) := Commute.zpow_zpow (show Commute a b from hab) i j
    rw [hc.mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm i,
      mul_comm j, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, ha3, hb3, one_zpow, one_zpow,
      mul_one]
  have hc9 : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) = 3 ^ 2 := by
    rw [hcard]
    norm_num
  exact ⟨⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hc9, hexp⟩, hc9⟩

theorem two_le_pRank_star_case_one
    {H T MH K : Subgroup G} (hmin : MinParabolic H T MH)
    (hns : ¬ Group.IsSolvable ↥H) (hKc : K ∈ cComp H) (hJ : kerIn MH H = pCoreOf 2 H) {t : G}
    (ht : t ∈ T) (hne : cjSub t K ≠ K) (hty : IsPSL 2 2 2 ↥(E2.star MH H K))
    (hB : E2.IsBorelIn (E2.star MH H K) (E2.star MH H (MH ⊓ K))) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (E2.StarQuot MH H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := hmin.isSylow.2.1
  have hTH : T ≤ H := hmin.isSylow.1
  have htype' : E2.IsBenderOf 2 ↥(E2.star MH H K) := ⟨le_rfl, Or.inl hty⟩
  have hJR := kerIn_eq_solvRad hmin.uniqueMax hT2 hns hJ
  have hsubJ := subgroupOf_kerIn_eq hJR
  have hrad := solvableRadical_star_eq_bot hsubJ
  have hker : Group.IsSolvable ↥((kerIn MH H).subgroupOf H) := by
    rw [hsubJ]
    exact A3.solvableRadical_isSolvable
  have htK := cjSub_mem_cComp' hKc (hTH ht)
  have hK1 := isComponent_of_mem_cComp_top hrad (mem_cComp_star hker hKc)
  have hK2 := isComponent_of_mem_cComp_top hrad (mem_cComp_star hker htK)
  have hne' : E2.star MH H (cjSub t K) ≠ E2.star MH H K := star_ne hker htK hKc hne
  have hcomm : ⁅E2.star MH H K, E2.star MH H (cjSub t K)⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hK1 hK2).resolve_left (Ne.symm hne')
  have hKC : E2.star MH H K ≤ Subgroup.centralizer (E2.star MH H (cjSub t K) : Set _) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  obtain ⟨d, hd, hdo⟩ := exists_borel_elt factBorelCartan le_rfl (Or.inl htype') hB
  set τ := starMk MH H ⟨t, hTH ht⟩ with hτ
  set d' := MulAut.conj τ d with hd'
  have hdK : d ∈ E2.star MH H K := star_mono inf_le_right hd
  have hd'K : d' ∈ E2.star MH H (cjSub t K) := by
    rw [star_cjSub (hTH ht)]
    exact ⟨d, hdK, rfl⟩
  have hdo3 : orderOf d = 3 := by rw [hdo]; norm_num
  have hd'o : orderOf d' = 3 := by rw [hd', MulEquiv.orderOf_eq, hdo3]
  have hdd' : d * d' = d' * d := (Subgroup.mem_centralizer_iff.mp (hKC hdK) d' hd'K).symm
  have hs : IsSimpleGroup ↥(E2.star MH H K) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 2 hty).2
  have hcen : Subgroup.center ↥(E2.star MH H K) = ⊥ := by
    obtain ⟨-, -, a, b, hab⟩ := hK1.1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(E2.star MH H K)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      have hb : b ∈ Subgroup.center ↥(E2.star MH H K) := h ▸ Subgroup.mem_top b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hb a]
  have hinter : Subgroup.zpowers d ⊓ Subgroup.zpowers d' = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    have hzK : z ∈ E2.star MH H K := (Subgroup.zpowers_le.mpr hdK) hz1
    have hzK' : z ∈ E2.star MH H (cjSub t K) := (Subgroup.zpowers_le.mpr hd'K) hz2
    have hzc : (⟨z, hzK⟩ : ↥(E2.star MH H K)) ∈ Subgroup.center ↥(E2.star MH H K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hKC g.2) z hzK').symm
    rw [hcen, Subgroup.mem_bot] at hzc
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hzc)
  obtain ⟨hE, hEc⟩ := isElemAbelian_sup_zpowers hdd' hdo3 hd'o hinter
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE hEc

end Fin125

open Fin125 in
theorem minPar125L24_of
    (hE22 : E2.E22StatementC) (hTor : E2.E22TorusCover) :
    ∀ (G : Type) [Group G] [Finite G] (H T MH : Subgroup G), MinParabolic H T MH →
      SQTKGroup ↥H → E1.nParam H = 2 → CFSG.Open.pRank 3 H ≤ 1 →
      (∀ C : Subgroup G, C ≤ MH → Odd (Nat.card C) → (∃ k : ℕ, C.relIndex MH = 2 ^ k) →
        C ≠ ⊥ ∧ IsPGroup 3 C) →
      Nonempty (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H) ≃* ↥(alternatingGroup (Fin 5))) := by
  intro G _ _ H T MH hmin hSQ hn2 hm3 hhall
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 < E1.nParam H := by rw [hn2]; norm_num
  have hns : ¬ Group.IsSolvable ↥H := fun hs =>
    absurd (E1.solvable_nParam_le_one hs) (not_le.mpr hn1)
  have hT : IsSylowTwoOf T H := hmin.isSylow
  have hTM : T ≤ MH := hmin.le
  have hMH : MH ≤ H := hmin.maximal.1.le
  have hTMs : IsSylowTwoOf T MH := A4.isSylowTwoOf_mono hT hTM hMH
  have hlift : ∀ S : Subgroup (E2.StarQuot MH H), 2 ≤ CFSG.Open.pRank 3 S → False :=
    fun S hS => by
      have := (two_le_pRank_of_star hS).trans hm3
      omega
  obtain ⟨⟨K, hKc, hHK, -, hc⟩, -⟩ := hE22.exists_cases hmin hSQ hns
  have hKH : K ≤ H := le_of_mem_cComp hKc
  dsimp only [E2.E22CasesC] at hc
  rcases hc with ⟨hJ, t, ht, hne, hMeq, h1⟩ | ⟨hTK, hJ, h2⟩
  ·
    exfalso
    rcases h1 with ⟨n, hn, hty, hB, -⟩ | ⟨_, _, _, _, _, _, hnH1⟩
    · obtain ⟨rfl, -⟩ := hall_three_of_lift hn
        (E2.BorelLift.lift_one hTor hmin hKc hHK hJ ht hMeq hn hty hB) hhall
      rcases hty with hty | hty
      · exact hlift ⊤ (two_le_pRank_star_case_one hmin hns hKc hJ ht hne hty hB)
      · exact C11AmS.not_isSz_two hty
    · exact absurd hn1 (by rw [hnH1]; exact lt_irrefl 1)
  · rcases h2 with ⟨n, hBen, hB, -, -⟩ | ⟨n, -, hty, -, hB, hnH, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hnH1⟩ | ⟨_, _, _, _, _, hnH1⟩
    ·
      obtain ⟨rfl, C, hC, hC3⟩ := hall_three_of_lift hBen.1
        (E2.BorelLift.lift_two hTor hmin hKc hHK hTK hJ hBen.1 (Or.inl hBen) hB) hhall
      obtain ⟨-, h | h | h⟩ := hBen
      ·
        have hHn : H ≤ Subgroup.normalizer (K : Set G) := by
          rw [hHK]
          exact sup_le Subgroup.le_normalizer hTK
        have hO : oTwoUpper H = K := by
          rw [hHK]
          exact U3.oTwoUpper_sup_eq (C2Nine.oTwoUpper_eq_of_perfect
            (perfect_of_mem_cComp hKc)).symm hT.2.1 hTK
        subst hO
        exact E1.ThinA5.exists_quot_equiv_alt hKc hHn hJ h
      · exact (C11AmS.not_isSz_two h).elim
      ·
        exfalso
        obtain ⟨S, hS, hBeq⟩ := hB
        have hSY := isSylowTwoOf_top_subgroupOf hS
        obtain ⟨D, hDN, hDc⟩ := exists_borel_psu3_four h hSY
        have hle : D.map (E2.star MH H K).subtype ≤ E2.star MH H MH := by
          rintro _ ⟨y, hy, rfl⟩
          apply star_mono (inf_le_left : MH ⊓ K ≤ MH)
          rw [hBeq]
          exact ⟨y.2, coe_mem_normalizer hS.1 (hDN hy)⟩
        have h15 : 15 ∣ Nat.card (E2.star MH H MH) := by
          rw [← hDc, ← Subgroup.card_map_of_injective (E2.star MH H K).subtype_injective]
          exact Subgroup.card_dvd_of_le hle
        have h5 := odd_dvd_card_hall hMH hTMs hC (r := 5) (by decide)
          ((show 5 ∣ 15 by norm_num).trans h15)
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hC3
        rw [ha] at h5
        have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_three).mp
          ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h5))
        omega
    ·
      exfalso
      have hn2' : 2 ≤ n := E2.E22A.two_le_of_one_lt_of_le hn1 hnH
      have hty' : IsPSL 3 2 n ↥(E2.star MH H K) ∨ IsPSp4 2 n ↥(E2.star MH H K) := by
        rcases hty with h | h
        · exact Or.inl h
        · right
          rw [E2.IsSp4Prime] at h
          split_ifs at h with h1
          · omega
          · exact h
      obtain ⟨rfl, -⟩ := hall_three_of_lift hn2'
        (E2.BorelLift.lift_two hTor hmin hKc hHK hTK hJ hn2' (Or.inr hty') hB) hhall
      refine hlift (E2.star MH H K) ?_
      rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      rcases hty' with h | h
      · exact Ch4.L4316.two_le_pRank_three_of_isPSL h
      · exact two_le_pRank_psp4_four h
    · exact absurd hn1 (by rw [hnH1]; exact lt_irrefl 1)
    · exact absurd hn1 (by rw [hnH1]; exact lt_irrefl 1)

end CFSG.Quasithin.H13
