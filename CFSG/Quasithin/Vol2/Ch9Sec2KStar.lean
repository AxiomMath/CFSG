module

public import CFSG.Quasithin.Vol2.Ch9Facts
public import CFSG.Quasithin.Vol2.Ch9Sec2Z
public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrL
public import CFSG.Quasithin.Vol2.Ch10SecKHBC
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting

public section

namespace CFSG.Quasithin.H13.Ch9.KStar

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10.SecB CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS

theorem eq_of_dvd_of_le_succ {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n) (hmn : n ≤ m + 1)
    (h : 2 ^ m - 1 ∣ 2 ^ n - 1) : m = n := by
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hle := Nat.le_of_dvd (by omega) h
  have hmn' : m ≤ n := by
    by_contra hc
    have : 2 ^ n < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  rcases eq_or_lt_of_le hmn' with heq | hlt
  · exact heq
  · exfalso
    have hn' : n = m + 1 := by omega
    subst hn'
    have h3 : 2 ^ (m + 1) - 1 = 2 * (2 ^ m - 1) + 1 := by rw [pow_succ]; omega
    rw [h3] at h
    have h5 : 2 ^ m - 1 ∣ 1 := (Nat.dvd_add_right (Dvd.intro_left 2 rfl)).mp h
    have := Nat.le_of_dvd (by norm_num) h5
    omega

variable {G : Type} [Group G] [Finite G]

theorem dvd_card_hall_of_dvd_star {H T X B : Subgroup G} (hXH : X ≤ H) (hT : IsSylowTwoOf T X)
    (hB : Lin2.IsHallTwoPrimeOf B X) {r : ℕ} (hr : Odd r)
    (hrX : r ∣ Nat.card (E2.star X H X)) : r ∣ Nat.card B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := card_star_mul_card_inf (X := X) hXH
  rw [card_eq_card_mul_card hT hB] at h1
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hT.2.1
  rw [ha] at h1
  have h2 : r ∣ 2 ^ a * Nat.card B := by
    rw [← h1]
    exact hrX.mul_right _
  exact (Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hr)).dvd_of_dvd_mul_left h2

theorem le_of_isPGroup_of_le_normalizer {Y : Type*} [Group Y] [Finite Y] {K S P : Subgroup Y}
    (hS : IsSylowTwoOf S K) (hP : IsPGroup 2 P) (hPK : P ≤ K)
    (hPN : P ≤ Subgroup.normalizer (S : Set Y)) : P ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPS : IsPGroup 2 ↥(P ⊔ S) := IsPGroup.to_sup_of_normal_right' hP hS.2.1 hPN
  have h1 := Subgroup.relIndex_mul_relIndex S (P ⊔ S) K le_sup_right (sup_le hPK hS.1)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPS
  have h2 : S.relIndex (P ⊔ S) ∣ 2 ^ k := by
    rw [← hk]
    exact Subgroup.relIndex_dvd_card S (P ⊔ S)
  have h3 : ¬ 2 ∣ S.relIndex K := hS.2.2
  have h4 : S.relIndex (P ⊔ S) = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    rcases j with _ | j
    · simpa using hj
    · exfalso
      apply h3
      rw [← h1, hj, pow_succ]
      exact dvd_mul_of_dvd_left (dvd_mul_left 2 _) _
  exact le_sup_left.trans (Subgroup.relIndex_eq_one.mp h4)

theorem zpowers_le_normalizer_of_commute {Y : Type*} [Group Y] {a b : Y} (hab : a * b = b * a) :
    Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set Y) := by
  have hc : Commute a b := hab
  rw [Subgroup.zpowers_le]
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact (hc.zpow_right k).eq.symm

theorem center_eq_bot_of_simple {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (hq : CFSG.IsQuasisimple Y) : Subgroup.center Y = ⊥ := by
  obtain ⟨-, -, a, b, hab⟩ := hq
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hb : b ∈ Subgroup.center Y := h ▸ Subgroup.mem_top b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hb a]

theorem exists_comp
    (hE22 : E2.E22StatementC) (hF1 : FactBorelOddLarge) {H T X : Subgroup G}
    (hmin : MinParabolic H T X) (hSQ : SQTKGroup ↥H) (hns : ¬ Group.IsSolvable ↥H)
    (hXH : X ≤ H) (hTX : T ≤ X) (hTXs : IsSylowTwoOf T X) (hn1 : 1 < E1.nParam H) {n : ℕ}
    (hn2 : 2 ≤ n) (hnH : (n : ℕ∞) ≤ E1.nParam H + 1) {B : Subgroup G}
    (hB : Lin2.IsHallTwoPrimeOf B X) (hBc : Nat.card B = 2 ^ n - 1) :
    ∃ K : Subgroup G, K ∈ cComp H ∧ H = K ⊔ T ∧ T ≤ Subgroup.normalizer (K : Set G) ∧
      IsPGroup 2 (kerIn X H) ∧ E2.IsBorelIn (E2.star X H K) (E2.star X H (X ⊓ K)) ∧
      (IsPSL 2 2 n ↥(E2.star X H K) ∨ IsSz n ↥(E2.star X H K) ∨
        (n = 2 ∧ IsPSL 3 2 2 ↥(E2.star X H K))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hTX.trans hXH
  have hT2 : IsPGroup 2 T := hTXs.2.1
  have h4n : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hoddp : ∀ m : ℕ, 1 ≤ m → Odd (2 ^ m - 1) := fun m hm =>
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hdvd : ∀ r : ℕ, Odd r → r ∣ Nat.card (E2.star X H X) → r ∣ 2 ^ n - 1 := fun r hr h =>
    hBc ▸ dvd_card_hall_of_dvd_star hXH hTXs hB hr h
  have hMX : ∀ K : Subgroup G, E2.star X H (X ⊓ K) ≤ E2.star X H X := fun K =>
    star_mono inf_le_left
  have hcart : ∀ (K : Subgroup G) (m : ℕ), 2 ≤ m →
      (E2.IsBenderOf m ↥(E2.star X H K) ∨ IsPSL 3 2 m ↥(E2.star X H K) ∨
        IsPSp4 2 m ↥(E2.star X H K)) →
      E2.IsBorelIn (E2.star X H K) (E2.star X H (X ⊓ K)) →
      2 ^ m - 1 ∣ Nat.card (E2.star X H X) := by
    intro K m hm htype hBor
    obtain ⟨d, hd, hdo⟩ := exists_borel_elt factBorelCartan hm htype hBor
    have h := orderOf_dvd_natCard (⟨d, hMX K hd⟩ : ↥(E2.star X H X))
    rwa [Subgroup.orderOf_mk, hdo] at h
  have hpar : ∀ m : ℕ, 2 ≤ m → E1.nParam H ≤ m → 2 ^ m - 1 ∣ Nat.card (E2.star X H X) →
      m = n := by
    intro m hm hnHm hdm
    have h1 := hdvd _ (hoddp m (by omega)) hdm
    have h2 : n ≤ m + 1 := by
      have h3 : (n : ℕ∞) ≤ (m + 1 : ℕ) := by
        push_cast
        exact hnH.trans (add_le_add hnHm le_rfl)
      exact_mod_cast h3
    exact eq_of_dvd_of_le_succ hm (by omega) h2 h1
  have hJ2 : 2 ^ n - 1 ∣ Nat.card (E2.star X H X) → IsPGroup 2 (kerIn X H) := by
    rintro ⟨y, hy⟩
    have h1 := card_star_mul_card_inf (X := X) hXH
    rw [card_eq_card_mul_card hTXs hB, hBc, hy, inf_of_le_right kerIn_le] at h1
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hT2
    rw [ha] at h1
    have h2 : y * Nat.card (kerIn X H) = 2 ^ a :=
      Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ n - 1 by omega) (by rw [← mul_assoc, h1, mul_comm])
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro_left _ h2)
    exact IsPGroup.of_card hk
  have hlarge : ∀ K : Subgroup G, E2.IsBorelIn (E2.star X H K) (E2.star X H (X ⊓ K)) →
      ¬ ((2 ≤ n ∧ IsPSU 3 2 n ↥(E2.star X H K)) ∨ (3 ≤ n ∧ IsPSL 3 2 n ↥(E2.star X H K)) ∨
        (2 ≤ n ∧ IsPSp4 2 n ↥(E2.star X H K))) := by
    rintro K ⟨S, hS, hBorEq⟩ htype
    have hSY := isSylowTwoOf_top_subgroupOf hS
    have hlt := hF1 _ n htype _ hSY
    set SY := S.subgroupOf (E2.star X H K) with hSYdef
    set NY := Subgroup.normalizer (SY : Set ↥(E2.star X H K)) with hNYdef
    have hNYX : Nat.card NY ∣ Nat.card (E2.star X H X) := by
      have hle : NY.map (E2.star X H K).subtype ≤ E2.star X H X := by
        rintro _ ⟨y, hy, rfl⟩
        apply hMX K
        rw [hBorEq]
        exact ⟨y.2, coe_mem_normalizer hS.1 hy⟩
      rw [← Subgroup.card_map_of_injective (E2.star X H K).subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    have hr : SY.relIndex NY ∣ Nat.card (E2.star X H X) :=
      (Subgroup.relIndex_dvd_card SY NY).trans hNYX
    have hrodd : Odd (SY.relIndex NY) := by
      have h1 : SY.relIndex NY ∣ SY.index :=
        Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer
      have h2 : ¬ 2 ∣ SY.index := by
        have := hSY.2.2
        rwa [show (SY.subgroupOf ⊤).index = SY.index from Subgroup.relIndex_top_right _] at this
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => h2 (h.trans h1))
    have := Nat.le_of_dvd (by omega) (hdvd _ hrodd hr)
    omega
  obtain ⟨⟨K, hKc, hHK, -, hcases⟩, -⟩ := hE22.exists_cases hmin hSQ hns
  dsimp only [E2.E22CasesC] at hcases
  rcases hcases with ⟨hJ, t, ht, hne, -, h1⟩ | ⟨hTK, -, h2⟩
  ·
    exfalso
    rcases h1 with ⟨m, hm2, htype, hBor, hnHm⟩ | ⟨_, _, _, _, _, _, hnH1⟩
    · have htype' : E2.IsBenderOf m ↥(E2.star X H K) :=
        ⟨hm2, htype.elim Or.inl fun h => Or.inr (Or.inl h)⟩
      have hm := hpar m hm2 hnHm (hcart K m hm2 (Or.inl htype') hBor)
      have hJR := kerIn_eq_solvRad hmin.uniqueMax hT2 hns hJ
      have hsubJ := subgroupOf_kerIn_eq hJR
      have hrad := solvableRadical_star_eq_bot hsubJ
      have hker : Group.IsSolvable ↥((kerIn X H).subgroupOf H) := by
        rw [hsubJ]
        exact A3.solvableRadical_isSolvable
      have htK := cjSub_mem_cComp' hKc (hTH ht)
      have hK1 := isComponent_of_mem_cComp_top hrad (mem_cComp_star hker hKc)
      have hK2 := isComponent_of_mem_cComp_top hrad (mem_cComp_star hker htK)
      have hne' : E2.star X H (cjSub t K) ≠ E2.star X H K := star_ne hker htK hKc hne
      have hcomm : ⁅E2.star X H K, E2.star X H (cjSub t K)⁆ = ⊥ :=
        (CFSG.LocalCores.distinct_components_commute hK1 hK2).resolve_left (Ne.symm hne')
      have hKC : E2.star X H K ≤ Subgroup.centralizer (E2.star X H (cjSub t K) : Set _) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      obtain ⟨d, hd, hdo⟩ := exists_borel_elt factBorelCartan hm2 (Or.inl htype') hBor
      set τ := starMk X H ⟨t, hTH ht⟩ with hτ
      set d' := MulAut.conj τ d with hd'
      have hdK : d ∈ E2.star X H K := star_mono inf_le_right hd
      have hd'K : d' ∈ E2.star X H (cjSub t K) := by
        rw [star_cjSub (hTH ht)]
        exact ⟨d, hdK, rfl⟩
      have hdX : d ∈ E2.star X H X := hMX K hd
      have hτX : τ ∈ E2.star X H X := ⟨⟨t, hTH ht⟩, Subgroup.mem_subgroupOf.mpr (hTX ht), rfl⟩
      have hd'X : d' ∈ E2.star X H X := by
        rw [hd', MulAut.conj_apply]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hτX hdX) (Subgroup.inv_mem _ hτX)
      have hd'o : orderOf d' = 2 ^ m - 1 := by rw [hd', MulEquiv.orderOf_eq, hdo]
      have hdd' : d * d' = d' * d := (Subgroup.mem_centralizer_iff.mp (hKC hdK) d' hd'K).symm
      have hs : IsSimpleGroup ↥(E2.star X H K) := by
        rcases htype with h | h
        · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 m h).2
        · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 m h).2
      have hcen := center_eq_bot_of_simple hK1.1
      have hinter : Subgroup.zpowers d ⊓ Subgroup.zpowers d' = ⊥ := by
        rw [eq_bot_iff]
        rintro z ⟨hz1, hz2⟩
        have hzK : z ∈ E2.star X H K := (Subgroup.zpowers_le.mpr hdK) hz1
        have hzK' : z ∈ E2.star X H (cjSub t K) := (Subgroup.zpowers_le.mpr hd'K) hz2
        have hzc : (⟨z, hzK⟩ : ↥(E2.star X H K)) ∈ Subgroup.center ↥(E2.star X H K) := by
          rw [Subgroup.mem_center_iff]
          intro g
          exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hKC g.2) z hzK').symm
        rw [hcen, Subgroup.mem_bot] at hzc
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val hzc)
      have hcard := QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
        (zpowers_le_normalizer_of_commute hdd')
      rw [hinter, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hd'o, hdo]
        at hcard
      have hle : Subgroup.zpowers d ⊔ Subgroup.zpowers d' ≤ E2.star X H X :=
        sup_le (Subgroup.zpowers_le.mpr hdX) (Subgroup.zpowers_le.mpr hd'X)
      have h3 : (2 ^ m - 1) * (2 ^ m - 1) ∣ Nat.card (E2.star X H X) := by
        rw [← hcard]
        exact Subgroup.card_dvd_of_le hle
      have h4 := hdvd _ ((hoddp m (by omega)).mul (hoddp m (by omega))) h3
      rw [hm] at h4
      have h5 := Nat.le_of_dvd (by omega) h4
      have h6 : 2 ^ n - 1 ≤ 1 :=
        Nat.le_of_mul_le_mul_left (show (2 ^ n - 1) * (2 ^ n - 1) ≤ (2 ^ n - 1) * 1 by
          rw [mul_one]; exact h5) (by omega)
      omega
    · exact absurd hn1 (by rw [hnH1]; exact lt_irrefl 1)
  ·
    rcases h2 with ⟨m, hBen, hBor, hnHm, -⟩ | ⟨m, -, htype, -, hBor, hnHm, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hnH1⟩ | ⟨_, _, _, _, _, hnH1⟩
    · have hd := hcart K m hBen.1 (Or.inl hBen) hBor
      have hm := hpar m hBen.1 hnHm hd
      rw [hm] at hBen hd
      refine ⟨K, hKc, hHK, hTK, hJ2 hd, hBor, ?_⟩
      obtain ⟨-, h | h | h⟩ := hBen
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact absurd (Or.inl ⟨hn2, h⟩) (hlarge K hBor)
    · have hm2 : 2 ≤ m := E2.E22A.two_le_of_one_lt_of_le hn1 hnHm
      have htype' : IsPSL 3 2 m ↥(E2.star X H K) ∨ IsPSp4 2 m ↥(E2.star X H K) := by
        rcases htype with h | h
        · exact Or.inl h
        · right
          rw [E2.IsSp4Prime] at h
          split_ifs at h with h1
          · omega
          · exact h
      have hd := hcart K m hm2 (Or.inr htype') hBor
      have hm := hpar m hm2 hnHm hd
      rw [hm] at htype' hd
      refine ⟨K, hKc, hHK, hTK, hJ2 hd, hBor, ?_⟩
      rcases htype' with h | h
      · rcases Nat.lt_or_ge n 3 with h3 | h3
        · have hn : n = 2 := by omega
          rw [hn] at h
          exact Or.inr (Or.inr ⟨hn, h⟩)
        · exact absurd (Or.inr (Or.inl ⟨h3, h⟩)) (hlarge K hBor)
      · exact absurd (Or.inr (Or.inr ⟨hn2, h⟩)) (hlarge K hBor)
    · exact absurd hn1 (by rw [hnH1]; exact lt_irrefl 1)
    · exact absurd hn1 (by rw [hnH1]; exact lt_irrefl 1)

theorem exists_conj_eq_pow (hF2 : FactBenderCartanFrob) {H T X K B : Subgroup G}
    (hXH : X ≤ H) (hTX : T ≤ X) (hTXs : IsSylowTwoOf T X) (hHK : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hJ2 : IsPGroup 2 (kerIn X H))
    (hBor : E2.IsBorelIn (E2.star X H K) (E2.star X H (X ⊓ K))) {n : ℕ} (hn2 : 2 ≤ n)
    (htype : IsPSL 2 2 n ↥(E2.star X H K) ∨ IsSz n ↥(E2.star X H K))
    (hB : Lin2.IsHallTwoPrimeOf B X) {b : G} (hb : b ∈ B) (hbo : orderOf b = 2 ^ n - 1)
    (hBc : Nat.card B = 2 ^ n - 1) {t : G} (ht : t ∈ T)
    (htB : t ∈ Subgroup.normalizer (B : Set G)) : ∃ j : ℕ, t * b * t⁻¹ = b ^ 2 ^ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hTX.trans hXH
  have hT2 : IsPGroup 2 T := hTXs.2.1
  have hHKn : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have h2K : ∀ x ∈ H, ∃ k : ℕ, x ^ 2 ^ k ∈ K :=
    B6.isTwoQuotient_of_sup_eq hT2 hHKn (by rw [hHK, sup_comm])
  have hBH : B ≤ H := hB.1.trans hXH
  have hBK : B ≤ K := le_of_odd hBH hB.2.1 h2K
  have hBb : B = Subgroup.zpowers b :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb)
      (by rw [Nat.card_zpowers, hbo, hBc])).symm
  have hinj : ∀ x (hx : x ∈ B) y (hy : y ∈ B),
      starMk X H ⟨x, hBH hx⟩ = starMk X H ⟨y, hBH hy⟩ → x = y := by
    intro x hx y hy hxy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxy
    have h1 : x⁻¹ * y ∈ kerIn X H := Subgroup.mem_subgroupOf.mp hxy
    have h2 := eq_one_of_mem_of_odd hJ2 h1
      (hB.2.1.of_dvd_nat (B.orderOf_dvd_natCard (B.mul_mem (B.inv_mem hx) hy)))
    exact inv_mul_eq_one.mp h2
  obtain ⟨S, hS, hBorEq⟩ := hBor
  set τ := starMk X H ⟨t, hTH ht⟩ with hτ
  have hτK : τ ∈ Subgroup.normalizer ((E2.star X H K : Subgroup _) : Set (E2.StarQuot X H)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
    change cjSub τ (E2.star X H K) = E2.star X H K
    rw [← star_cjSub (hTH ht), cjSub,
      Vol2.Ch11.SecB.map_conj_eq_self_of_mem_normalizer (hTK ht)]
  have hτM : cjSub τ (E2.star X H (X ⊓ K)) = E2.star X H (X ⊓ K) := by
    rw [← star_cjSub (hTH ht), cjSub, Vol2.Ch11.SecB.map_conj_eq_self_of_mem_normalizer
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hTX ht), hTK ht⟩)]
  have hSM : S ≤ E2.star X H (X ⊓ K) := by
    rw [hBorEq]
    exact le_inf hS.1 Subgroup.le_normalizer
  have hτS : τ ∈ Subgroup.normalizer (S : Set (E2.StarQuot X H)) := by
    have hle : cjSub τ S ≤ S := by
      have h1 : cjSub τ S ≤ E2.star X H (X ⊓ K) := hτM ▸ cjSub_mono hSM
      rw [hBorEq] at h1
      exact le_of_isPGroup_of_le_normalizer hS (hS.2.1.map _) (h1.trans inf_le_left)
        (h1.trans inf_le_right)
    have heq : cjSub τ S = S := Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj τ).injective).ge
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
    exact heq
  have hbK : starMk X H ⟨b, hBH hb⟩ ∈ E2.star X H K :=
    ⟨⟨b, hBH hb⟩, Subgroup.mem_subgroupOf.mpr (hBK hb), rfl⟩
  have hbM : starMk X H ⟨b, hBH hb⟩ ∈ E2.star X H (X ⊓ K) :=
    ⟨⟨b, hBH hb⟩, Subgroup.mem_subgroupOf.mpr ⟨hB.1 hb, hBK hb⟩, rfl⟩
  have hSY := isSylowTwoOf_top_subgroupOf hS
  set d : ↥(E2.star X H K) := ⟨starMk X H ⟨b, hBH hb⟩, hbK⟩ with hd
  have hdN : d ∈ Subgroup.normalizer ((S.subgroupOf (E2.star X H K) : Subgroup _) :
      Set ↥(E2.star X H K)) := by
    have h1 : (d : E2.StarQuot X H) ∈ Subgroup.normalizer (S : Set (E2.StarQuot X H)) := by
      have := hbM
      rw [hBorEq] at this
      exact this.2
    refine Subgroup.mem_normalizer_iff.mpr fun w => ?_
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp h1 (w : E2.StarQuot X H)
  have hdo : orderOf d = 2 ^ n - 1 := by
    rw [hd, Subgroup.orderOf_mk, ← hbo]
    apply le_antisymm
    · have := orderOf_map_dvd (starMk X H) (⟨b, hBH hb⟩ : ↥H)
      rw [Subgroup.orderOf_mk] at this
      exact Nat.le_of_dvd (orderOf_pos b) this
    · apply Nat.le_of_dvd (orderOf_pos _)
      apply orderOf_dvd_of_pow_eq_one
      refine hinj _ (B.pow_mem hb _) 1 B.one_mem ?_
      have h4 : (⟨b ^ orderOf (starMk X H ⟨b, hBH hb⟩), hBH (B.pow_mem hb _)⟩ : ↥H) =
          ⟨b, hBH hb⟩ ^ orderOf (starMk X H ⟨b, hBH hb⟩) := rfl
      have h5 : (⟨1, hBH B.one_mem⟩ : ↥H) = 1 := rfl
      rw [h4, h5, map_pow, pow_orderOf_eq_one, map_one]
  set α : MulAut ↥(E2.star X H K) := conjAct (E2.star X H K) ⟨τ, hτK⟩ with hαdef
  have hαapp : ∀ y : ↥(E2.star X H K), ((α y : ↥(E2.star X H K)) : E2.StarQuot X H) =
      τ * y * τ⁻¹ := fun y => coe_conjAct_apply (E2.star X H K) ⟨τ, hτK⟩ y
  have hα2 : ∃ k : ℕ, α ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
    refine ⟨k, ?_⟩
    have ht0 : t ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have ht1 : (⟨t, hTH ht⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by simpa using ht0)
    have hτ1 : (⟨τ, hτK⟩ : ↥(Subgroup.normalizer
        ((E2.star X H K : Subgroup _) : Set (E2.StarQuot X H)))) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      show τ ^ 2 ^ k = 1
      rw [hτ, ← map_pow, ht1, map_one]
    rw [hαdef, ← map_pow, hτ1, map_one]
  have hαS : (S.subgroupOf (E2.star X H K)).map α.toMonoidHom = S.subgroupOf (E2.star X H K) := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : E2.StarQuot X H) ∈ S := hy
      show ((α y : ↥(E2.star X H K)) : E2.StarQuot X H) ∈ S
      rw [hαapp]
      exact (Subgroup.mem_normalizer_iff.mp hτS _).mp hy'
    · intro hw
      have hw' : (w : E2.StarQuot X H) ∈ S := hw
      refine ⟨α.symm w, ?_, by simp⟩
      show ((α.symm w : ↥(E2.star X H K)) : E2.StarQuot X H) ∈ S
      have h1 : ((α.symm w : ↥(E2.star X H K)) : E2.StarQuot X H) = τ⁻¹ * w * τ := by
        have h2 := hαapp (α.symm w)
        rw [MulEquiv.apply_symm_apply] at h2
        rw [h2]
        group
      rw [h1]
      refine (Subgroup.mem_normalizer_iff.mp hτS _).mpr ?_
      have h3 : τ * (τ⁻¹ * (w : E2.StarQuot X H) * τ) * τ⁻¹ = w := by group
      rw [h3]
      exact hw'
  have htbH : t * b * t⁻¹ ∈ H := H.mul_mem (H.mul_mem (hTH ht) (hBH hb)) (H.inv_mem (hTH ht))
  have htbB : t * b * t⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp htB b).mp hb
  have hαd' : ((α d : ↥(E2.star X H K)) : E2.StarQuot X H) = starMk X H ⟨t * b * t⁻¹, htbH⟩ := by
    rw [hαapp, hd, hτ, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hαd : α d ∈ Subgroup.zpowers d := by
    have h1 : t * b * t⁻¹ ∈ Subgroup.zpowers b := hBb ▸ htbB
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    rw [hαd']
    have h2 : (⟨t * b * t⁻¹, htbH⟩ : ↥H) = ⟨b, hBH hb⟩ ^ k := Subtype.ext hk.symm
    rw [h2, map_zpow]
    rfl
  obtain ⟨j, hj⟩ := hF2 _ n hn2 htype _ hSY d hdN hdo α hα2 hαS hαd
  refine ⟨j, hinj _ htbB _ (B.pow_mem hb _) ?_⟩
  have h1 := congrArg Subtype.val hj
  rw [hαd'] at h1
  rw [h1]
  have h2 : (⟨b ^ 2 ^ j, hBH (B.pow_mem hb _)⟩ : ↥H) = ⟨b, hBH hb⟩ ^ 2 ^ j := rfl
  rw [h2, map_pow]
  rfl

end CFSG.Quasithin.H13.Ch9.KStar
