module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Excl
public import CFSG.Quasithin.EmptyFaithful.R3c3Rank
public import CFSG.Quasithin.Background.F918G1
public import CFSG.Quasithin.Vol2.KGFactLem1211G2
public import CFSG.Quasithin.EmptyFaithful.LRed3FourB
public import CFSG.Quasithin.EmptyFaithful.R3c2Types
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspFFL3

public section

namespace CFSG.Quasithin.H13.Ch4.FFSmall

open Matrix CFSG.Assembly.LowTwoRank

theorem exists_orderOf_nine {K : Type} [Group K] [Finite K] (hK : IsPSL 2 2 3 K) :
    ∃ x : K, orderOf x = 9 := by
  have hcard : Nat.card K = 504 := by
    rw [CFSG.Quasithin.F420.card_of_statedPSL_two_two hK]
    norm_num
  obtain ⟨-, F, _, _, hF, ⟨eK⟩⟩ := hK
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  let e : K ≃* ↥(StatedSL 2 F) :=
    eK.trans ((CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL 2 F).trans
      ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL F).trans
        (specialLinearGroupEquivStatedSL 2 F)))
  have hno : CFSG.Quasithin.F134.NoElemNine K :=
    CFSG.Quasithin.F134.NoElemNine.of_mulEquiv e (CFSG.Quasithin.R3c.noElemNine_statedSL_two hF)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 K := default
  have hP : Nat.card (P : Subgroup K) = 9 := by
    rw [P.card_eq_multiplicity, hcard, show (504 : ℕ) = 3 ^ 2 * 56 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 56)]
    norm_num
  by_contra hne
  push Not at hne
  refine hno (P : Subgroup K) hP fun x hx => ?_
  have hdvd : orderOf x ∣ 9 := by
    have := Subgroup.orderOf_dvd_natCard (P : Subgroup K) hx
    rwa [hP] at this
  have h9 := hne x
  have : orderOf x ∣ 3 := by
    rcases (Nat.dvd_prime_pow Nat.prime_three).mp (show orderOf x ∣ 3 ^ 2 by simpa using hdvd)
      with ⟨k, hk, hkx⟩
    interval_cases k
    · rw [hkx]; exact one_dvd _
    · rw [hkx]; norm_num
    · exact absurd (by simpa using hkx) h9
  exact orderOf_dvd_iff_pow_eq_one.mp this

theorem orderOf_ne_nine {L : Type} [Group L] [Finite L] (h27 : ¬ 27 ∣ Nat.card L)
    (hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)) (x : L) : orderOf x ≠ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S := {k | ∃ E : Subgroup L, E ≤ ⊤ ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k}
    with hS
  have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup L) = sSup S := rfl
  have hbot : CFSG.Open.IsElemAbelian 3 (⊥ : Subgroup L) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · apply Subtype.ext
      simp [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2]
    · rw [Subgroup.mem_bot.mp hy, one_pow]
  have hne : S.Nonempty := ⟨0, ⊥, bot_le, hbot, by simp⟩
  have hbdd : BddAbove S := by
    refine ⟨Nat.card L, fun k hkS => ?_⟩
    obtain ⟨E, -, -, hk⟩ := hkS
    have h1 : 3 ^ k ≤ Nat.card L := hk ▸ Subgroup.card_le_card_group E
    have h2 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
    omega
  obtain ⟨E, -, hE, hEcard⟩ := Nat.sSup_mem hne hbdd
  rw [← hrk] at hEcard
  set k := CFSG.Open.pRank 3 (⊤ : Subgroup L) with hk
  have hEdvd : 3 ^ k ∣ Nat.card L := hEcard ▸ Subgroup.card_subgroup_dvd_card E
  have hk2 : k = 2 := by
    by_contra hne2
    apply h27
    have : 3 ^ 3 ∣ 3 ^ k := Nat.pow_dvd_pow 3 (by omega)
    exact (by norm_num : (27 : ℕ) = 3 ^ 3) ▸ this.trans hEdvd
  rw [hk2] at hEcard hEdvd
  have hL0 : Nat.card L ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card L).factorization 3 = 2 := by
    have h1 : 2 ≤ (Nat.card L).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hL0).mp hEdvd
    have h2 : ¬ 3 ≤ (Nat.card L).factorization 3 := fun h =>
      h27 ((by norm_num : (27 : ℕ) = 3 ^ 3) ▸
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hL0).mpr h)
    omega
  intro hx
  let PE : Sylow 3 L := Sylow.ofCard E (by rw [hEcard, hfac])
  let PH : Sylow 3 L := Sylow.ofCard (Subgroup.zpowers x)
    (by rw [Nat.card_zpowers, hx, hfac]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L PE PH
  have hxmem : x ∈ ((g • PE : Sylow 3 L) : Subgroup L) := by
    rw [hg]
    exact Subgroup.mem_zpowers x
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxmem
  obtain ⟨y, hy, rfl⟩ := hxmem
  have hyE : y ∈ E := by
    have : (PE : Subgroup L) = E := Sylow.coe_ofCard _ _
    rwa [this] at hy
  have h3 : ((MulAut.conj g) • y) ^ 3 = 1 := by
    rw [MulAut.smul_def, ← map_pow, hE.2 y hyE, map_one]
  have := orderOf_dvd_of_pow_eq_one h3
  rw [hx] at this
  norm_num at this

theorem false_of_exception_simple {L : Type} [Group L] [Finite L]
    [IsSimpleGroup L] (hL : CFSG.Quasithin.H13.L34.ListOrd (Nat.card L))
    (h20160 : Nat.card L = 20160 → Nonempty (L ≃* alternatingGroup (Fin 8)))
    {S : Type} [Group S] (φ : L →* S) (hφ : Function.Surjective φ) (s : Bool) (q : ℕ)
    (hq : Int.ModEq 3 (q : ℤ) (if s then 1 else -1)) (hS : IsPSLEps3q s q S) : False := by
  have : IsSimpleGroup S := L436.isSimpleGroup_of_isPSLEps3q hS
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (1 : S)
      obtain ⟨x, rfl⟩ := hφ y
      exact hy ((MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top x))
  let ψ : L ≃* S := MulEquiv.ofBijective φ ⟨hinj, hφ⟩
  have hcard : Nat.card S = Nat.card L := (Nat.card_congr ψ.toEquiv).symm
  refine CFSG.Quasithin.H13.L34.not_isPSLEps3q_of_card (hcard ▸ hL) (fun h => ?_) s q hq hS
  obtain ⟨eA⟩ := h20160 (hcard ▸ h)
  exact ⟨ψ.symm.trans eA⟩

theorem false_of_pattern {G : Type} [Group G] [Finite G] {L : Subgroup G} {n p : ℕ}
    (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1)
    (hcase : CFSG.Open.pRank p L ≤ 1 ∨
      (p = 3 ∧ ∃ (S : Type) (_ : Group S) (φ : ↥L →* S), Function.Surjective φ ∧
        (∀ x ∈ φ.ker, ¬ 3 ∣ orderOf x) ∧
        ∃ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) ∧
          IsPSLEps3q s q S))
    (hn23 : n = 2 ∨ n = 3) (h3 : n = 3 → False)
    (hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L))
    (hexc : ∀ (S : Type) [Group S] (φ : ↥L →* S), Function.Surjective φ →
      (∀ x ∈ φ.ker, ¬ 3 ∣ orderOf x) → ∀ (s : Bool) (q : ℕ),
        Int.ModEq 3 (q : ℤ) (if s then 1 else -1) → IsPSLEps3q s q S → False) : False := by
  rcases hn23 with rfl | rfl
  · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using hpn)
    subst hp3
    rcases hcase with h | ⟨-, S, _, φ, hφ, hker, s, q, hq, hS⟩
    · rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h
      omega
    · exact hexc S φ hφ hker s q hq hS
  · exact h3 rfl

theorem le_of_dvd_two_pow_mul {n v u : ℕ} (hu : Odd u) (h : 2 ^ n * (4 ^ n - 1) ∣ 2 ^ v * u) :
    n ≤ v := by
  have h1 : 2 ^ n ∣ 2 ^ v * u := (Dvd.intro _ rfl).trans h
  have hcop : Nat.Coprime (2 ^ n) u :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hu)
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right h1)

theorem false_of_three {G : Type} [Group G] [Finite G] {L K : Subgroup G} (hKL : K ≤ L)
    (hK : IsPSL 2 2 3 ↥K) (h27 : ¬ 27 ∣ Nat.card ↥L)
    (hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L)) : False := by
  obtain ⟨x, hx⟩ := exists_orderOf_nine hK
  have : orderOf (Subgroup.inclusion hKL x) = 9 := by
    rw [orderOf_injective _ (Subgroup.inclusion_injective hKL), hx]
  exact orderOf_ne_nine h27 hrank _ this

theorem isSimpleGroup_of_mulEquiv {X Y : Type} [Group X] [Group Y] [IsSimpleGroup Y]
    (e : X ≃* Y) : IsSimpleGroup X := by
  have : Nontrivial X := e.toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem pRank_top_eq {G X : Type} [Group G] [Finite G] [Group X] [Finite X] {L : Subgroup G}
    (e : ↥L ≃* X) : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) = CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {n p : ℕ}

theorem false_of_alt {m : ℕ} (hm : m = 6 ∨ m = 7) (hn : 2 ≤ n)
    (e : ↥L ≃* alternatingGroup (Fin m)) (hKL : K ≤ L) (hK : IsPSL 2 2 n ↥K) (hp : p.Prime)
    (hpn : p ∣ 2 ^ n - 1)
    (hcase : CFSG.Open.pRank p L ≤ 1 ∨
      (p = 3 ∧ ∃ (S : Type) (_ : Group S) (φ : ↥L →* S), Function.Surjective φ ∧
        (∀ x ∈ φ.ker, ¬ 3 ∣ orderOf x) ∧
        ∃ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) ∧
          IsPSLEps3q s q S)) : False := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcardL : Nat.card ↥L = m.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  have hcardK : Nat.card ↥K = 2 ^ n * (4 ^ n - 1) :=
    CFSG.Quasithin.F420.card_of_statedPSL_two_two hK
  have hdvd : 2 ^ n * (4 ^ n - 1) ∣ m.factorial / 2 := by
    rw [← hcardK, ← hcardL]
    exact Subgroup.card_dvd_of_le hKL
  have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) :=
    CFSG.Quasithin.R3c3.two_le_pRank_three_alt (by omega) e
  have : IsSimpleGroup (alternatingGroup (Fin m)) :=
    CFSG.Quasithin.Vol2.Ch10.SecA.isSimpleGroup_alt (by omega)
  have : IsSimpleGroup ↥L := isSimpleGroup_of_mulEquiv e
  have hlist : CFSG.Quasithin.H13.L34.ListOrd (Nat.card ↥L) := by
    rw [hcardL, CFSG.Quasithin.H13.L34.ListOrd]
    rcases hm with rfl | rfl <;> decide
  refine false_of_pattern hp hpn hcase ?_ ?_ hrank ?_
  · have hle : n ≤ 3 := by
      rcases hm with rfl | rfl
      · rw [show (6 : ℕ).factorial / 2 = 2 ^ 3 * 45 by decide] at hdvd
        exact le_of_dvd_two_pow_mul (by decide) hdvd
      · rw [show (7 : ℕ).factorial / 2 = 2 ^ 3 * 315 by decide] at hdvd
        exact le_of_dvd_two_pow_mul (by decide) hdvd
    omega
  · intro h3
    subst h3
    rcases hm with rfl | rfl
    · revert hdvd
      decide
    · exact false_of_three hKL hK (by rw [hcardL]; decide) hrank
  · intro S _ φ hφ _ s q hq hS
    refine false_of_exception_simple hlist (fun h => ?_) φ hφ s q hq hS
    rw [hcardL] at h
    rcases hm with rfl | rfl <;> exact absurd h (by decide)

theorem false_of_hat (hn : 2 ≤ n) (hL : IsHat ↥L ↥(alternatingGroup (Fin 6))) (hKL : K ≤ L)
    (hK : IsPSL 2 2 n ↥K) (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1)
    (hcase : CFSG.Open.pRank p L ≤ 1 ∨
      (p = 3 ∧ ∃ (S : Type) (_ : Group S) (φ : ↥L →* S), Function.Surjective φ ∧
        (∀ x ∈ φ.ker, ¬ 3 ∣ orderOf x) ∧
        ∃ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) ∧
          IsPSLEps3q s q S)) : False := by
  have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) :=
    (CFSG.Quasithin.pRank_three_hatA6 hL).ge
  obtain ⟨hq, hZ, ⟨eq⟩⟩ := hL
  have hcardL : Nat.card ↥L = 1080 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
    rw [Nat.card_congr eq.toEquiv, nat_card_alternatingGroup, Nat.card_fin, hZ] at h1
    rw [h1]
    decide
  have hcardK : Nat.card ↥K = 2 ^ n * (4 ^ n - 1) :=
    CFSG.Quasithin.F420.card_of_statedPSL_two_two hK
  have hdvd : 2 ^ n * (4 ^ n - 1) ∣ 2 ^ 3 * 135 := by
    rw [← hcardK, show (2 : ℕ) ^ 3 * 135 = 1080 by norm_num, ← hcardL]
    exact Subgroup.card_dvd_of_le hKL
  refine false_of_pattern hp hpn hcase ?_ ?_ hrank ?_
  · have := le_of_dvd_two_pow_mul (by decide) hdvd
    omega
  · intro h3
    subst h3
    revert hdvd
    decide
  · intro S _ φ hφ hker s q _ hS
    have : IsSimpleGroup S := L436.isSimpleGroup_of_isPSLEps3q hS
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥L)) 3
      (by rw [hZ])
    have hSperf : Group.IsPerfect S := by
      rw [Group.isPerfect_def]
      have hL := Group.isPerfect_def.mp hq.1
      rw [commutator_def] at hL ⊢
      rw [← Subgroup.map_top_of_surjective φ hφ, ← Subgroup.map_commutator, hL]
    have hφz : φ z = 1 := L436.eq_one_of_forall_commute hSperf fun y => by
      obtain ⟨l, rfl⟩ := hφ y
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp z.2 l).symm]
    have h3 := hker (z : ↥L) hφz
    rw [Subgroup.orderOf_coe, hz] at h3
    exact h3 dvd_rfl

theorem false_of_sl4 (hn : 2 ≤ n)
    (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) (hKL : K ≤ L) (hK : IsPSL 2 2 n ↥K) (hp : p.Prime)
    (hpn : p ∣ 2 ^ n - 1)
    (hcase : CFSG.Open.pRank p L ≤ 1 ∨
      (p = 3 ∧ ∃ (S : Type) (_ : Group S) (φ : ↥L →* S), Function.Surjective φ ∧
        (∀ x ∈ φ.ker, ¬ 3 ∣ orderOf x) ∧
        ∃ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) ∧
          IsPSLEps3q s q S)) : False := by
  have hcardL : Nat.card ↥L = 20160 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.R3c.card_statedSL_four_two]
  have hcardK : Nat.card ↥K = 2 ^ n * (4 ^ n - 1) :=
    CFSG.Quasithin.F420.card_of_statedPSL_two_two hK
  have hdvd : 2 ^ n * (4 ^ n - 1) ∣ 2 ^ 6 * 315 := by
    rw [← hcardK, show (2 : ℕ) ^ 6 * 315 = 20160 by norm_num, ← hcardL]
    exact Subgroup.card_dvd_of_le hKL
  have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) := by
    rw [pRank_top_eq e]
    exact CFSG.Quasithin.R3c.two_le_pRank_three_statedSL_four_two
  have : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 4 2 1
    (CFSG.Quasithin.R3c2.isPSL_two_of_statedSL (by norm_num) e)).2
  have hA8 : Nonempty (↥L ≃* alternatingGroup (Fin 8)) := by
    have htop := CFSG.GH74.Exceptional.statedSL_eq_top_of_card_two (Nat.card_zmod 2) 4
    exact ⟨e.trans ((MulEquiv.subgroupCongr htop).trans (Subgroup.topEquiv.trans
      CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm))⟩
  refine false_of_pattern hp hpn hcase ?_ ?_ hrank ?_
  · have hle := le_of_dvd_two_pow_mul (by decide) hdvd
    interval_cases n
    · exact Or.inl rfl
    · exact Or.inr rfl
    all_goals revert hdvd; decide
  · intro h3
    subst h3
    exact false_of_three hKL hK (by rw [hcardL]; decide) hrank
  · intro S _ φ hφ _ s q hq hS
    exact false_of_exception_simple (by rw [hcardL, CFSG.Quasithin.H13.L34.ListOrd]; decide)
      (fun _ => hA8) φ hφ s q hq hS

theorem false_of_sl5 (hn : 2 ≤ n)
    (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (hKL : K ≤ L) (hK : IsPSL 2 2 n ↥K) (hp : p.Prime)
    (hpn : p ∣ 2 ^ n - 1)
    (hcase : CFSG.Open.pRank p L ≤ 1 ∨
      (p = 3 ∧ ∃ (S : Type) (_ : Group S) (φ : ↥L →* S), Function.Surjective φ ∧
        (∀ x ∈ φ.ker, ¬ 3 ∣ orderOf x) ∧
        ∃ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) ∧
          IsPSLEps3q s q S)) : False := by
  have hcardL : Nat.card ↥L = 9999360 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.R3c.card_statedSL_five_two]
  have hcardK : Nat.card ↥K = 2 ^ n * (4 ^ n - 1) :=
    CFSG.Quasithin.F420.card_of_statedPSL_two_two hK
  have hdvd : 2 ^ n * (4 ^ n - 1) ∣ 2 ^ 10 * 9765 := by
    rw [← hcardK, show (2 : ℕ) ^ 10 * 9765 = 9999360 by norm_num, ← hcardL]
    exact Subgroup.card_dvd_of_le hKL
  have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) := by
    rw [pRank_top_eq e]
    exact CFSG.Quasithin.R3c.two_le_pRank_three_statedSL_five_two
  have : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 5 2 1
    (CFSG.Quasithin.R3c2.isPSL_two_of_statedSL (by norm_num) e)).2
  refine false_of_pattern hp hpn hcase ?_ ?_ hrank ?_
  · have hle := le_of_dvd_two_pow_mul (by decide) hdvd
    interval_cases n
    · exact Or.inl rfl
    · exact Or.inr rfl
    all_goals revert hdvd; decide
  · intro h3
    subst h3
    exact false_of_three hKL hK (by rw [hcardL]; decide) hrank
  · intro S _ φ hφ _ s q hq hS
    refine false_of_exception_simple (by rw [hcardL, CFSG.Quasithin.H13.L34.ListOrd]; decide)
      (fun h => absurd (hcardL ▸ h) (by decide)) φ hφ s q hq hS

@[expose] def antiDiag (F' : Type) [Field F'] [CharP F' 2] : SpecialLinearGroup (Fin 2) F' :=
  ⟨!![0, 1; 1, 0], by rw [det_fin_two_of]; simp [CharTwo.neg_eq]⟩

theorem antiDiag_mul_diagHom {F' : Type} [Field F'] [CharP F' 2] (μ : F'ˣ) :
    antiDiag F' * FFL3.diagHom μ = FFL3.diagHom μ⁻¹ * antiDiag F' := by
  apply Subtype.ext
  show !![0, 1; 1, 0] * !![(μ : F'), 0; 0, ((μ⁻¹ : F'ˣ) : F')] =
    !![((μ⁻¹ : F'ˣ) : F'), 0; 0, ((μ⁻¹⁻¹ : F'ˣ) : F')] * !![0, 1; 1, 0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem antiDiag_sq {F' : Type} [Field F'] [CharP F' 2] : antiDiag F' ^ 2 = 1 := by
  rw [sq]
  apply Subtype.ext
  show !![(0 : F'), 1; 1, 0] * !![0, 1; 1, 0] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem antiDiag_ne_one {F' : Type} [Field F'] [CharP F' 2] : antiDiag F' ≠ 1 := by
  intro h
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) F' => (g : Matrix (Fin 2) (Fin 2) F') 0 0) h
  simp [antiDiag] at this

theorem false_of_g2Two
    (hn : 2 ≤ n) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2)
    (e : ↥L ≃* ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆) (hKL : K ≤ L)
    (hK : IsPSL 2 2 n ↥K) : False := by
  obtain ⟨eP⟩ := CFSG.Quasithin.lred3_equiv_g2derived_psu33 hF
  have hK9 : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  have hne : ((3 : ℕ), 3 ^ 1) ≠ (3, 2) := fun h => absurd (congrArg Prod.snd h) (by norm_num)
  have hPSU : IsPSU 3 3 1 ↥L := ⟨⟨Nat.prime_three, le_rfl, le_rfl, hne⟩, GaloisField 3 (2 * 1),
    inferInstance, inferInstance, hK9, ⟨e.trans eP.symm⟩⟩
  have hcardL : Nat.card ↥L = 6048 := CFSG.Quasithin.SBc11.card_of_isPSU_three_three hPSU
  obtain ⟨eQ⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (K := ↥L) (Or.inl ⟨by decide, hPSU⟩)
  have hcardK : Nat.card ↥K = 2 ^ n * (4 ^ n - 1) :=
    CFSG.Quasithin.F420.card_of_statedPSL_two_two hK
  have hdvd : 2 ^ n * (4 ^ n - 1) ∣ 2 ^ 5 * 189 := by
    rw [← hcardK, show (2 : ℕ) ^ 5 * 189 = 6048 by norm_num, ← hcardL]
    exact Subgroup.card_dvd_of_le hKL
  have hn3 : n = 3 := by
    have hle := le_of_dvd_two_pow_mul (by decide) hdvd
    interval_cases n
    all_goals first | rfl | (revert hdvd; decide)
  subst hn3
  obtain ⟨-, F', _, _, hF', ⟨eK⟩⟩ := hK
  have : CharP F' 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF'
  let eK' : ↥K ≃* SpecialLinearGroup (Fin 2) F' :=
    eK.trans ((CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL 2 F').trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL F'))
  let θ : SpecialLinearGroup (Fin 2) F' →* ↥L :=
    (Subgroup.inclusion hKL).comp eK'.symm.toMonoidHom
  have hθ : Function.Injective θ :=
    (Subgroup.inclusion_injective hKL).comp eK'.symm.injective
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨μ, hμ⟩ := exists_prime_orderOf_dvd_card' (G := F'ˣ) 7
    (by rw [Nat.card_units, hF']; norm_num)
  set y := θ (FFL3.diagHom μ) with hy
  have hy7 : orderOf y = 7 := by
    rw [hy, orderOf_injective θ hθ, orderOf_injective _ FFL3.diagHom_injective, hμ]
  let Q : Sylow 7 ↥L := Sylow.ofCard (Subgroup.zpowers y) (by
    rw [Nat.card_zpowers, hy7, hcardL, show (6048 : ℕ) = 7 * 864 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num : Nat.Prime 7),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 864)]
    norm_num)
  have hN := CFSG.Quasithin.H13.KGG2.card_normalizer_sylow_seven eQ Q
  have hwN : θ (antiDiag F') ∈
      Subgroup.normalizer (((Q : Subgroup ↥L) : Subgroup ↥L) : Set ↥L) := by
    rw [Sylow.coe_ofCard, CFSG.Quasithin.H13.KGG2.mem_normalizer_zpowers_iff, hy,
      ← map_mul, ← map_inv, ← map_mul, antiDiag_mul_diagHom, mul_assoc,
      mul_inv_cancel, mul_one, map_inv, map_inv]
    exact inv_mem (Subgroup.mem_zpowers _)
  have h2 := Subgroup.orderOf_dvd_natCard _ hwN
  rw [hN, orderOf_injective θ hθ, orderOf_eq_prime antiDiag_sq antiDiag_ne_one] at h2
  norm_num at h2

end CFSG.Quasithin.H13.Ch4.FFSmall
