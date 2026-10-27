module

public import CFSG.Quasithin.Background.RonanD321FiveP
public import CFSG.Quasithin.Background.GoldschmidtAmalgamNVertex
public import CFSG.Quasithin.Background.SmithD321SzK

public section

namespace CFSG.Quasithin.RonanD321.Five

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Open
  CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem five_not_dvd_two_pow_sub_one {n : ℕ} (hn : Odd n) : ¬ 5 ∣ 2 ^ n - 1 := by
  obtain ⟨a, rfl⟩ := hn
  have key : ∀ a : ℕ, 2 ^ (2 * a + 1) % 5 = 2 ∨ 2 ^ (2 * a + 1) % 5 = 3 := by
    intro a
    induction a with
    | zero => left; rfl
    | succ a ih =>
      have e : 2 ^ (2 * (a + 1) + 1) = 2 ^ (2 * a + 1) * 4 := by ring
      rw [e]
      generalize 2 ^ (2 * a + 1) = x at ih ⊢
      omega
  have h := key a
  generalize 2 ^ (2 * a + 1) = x at h ⊢
  omega

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem eq_one_of_pow_prime_pow_ne_five (hB : D321Base M Mp T L V t) (h2 : D321Two L) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5) {x : MulAut W}
    (hx : x ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) {k : ℕ} (hxk : x ^ (p ^ k) = 1) :
    x = 1 := by
  induction k generalizing x with
  | zero => simpa using hxk
  | succ k ih =>
    have hy : (x ^ (p ^ k)) ^ p = 1 := by rw [← pow_mul, ← pow_succ]; exact hxk
    exact ih hx (eq_one_of_prime_ne_five hB h2 (Subgroup.pow_mem _ hx _) hp hp2 hp5 hy)

theorem not_isComponentOf (hA23 : A23SQTKListFact)
    (hSzF : H13.SimpleThreePrimeSuzukiFact) (hB : D321Base M Mp T L V t) (h2 : D321Two L)
    (E : Subgroup ↥(M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) :
    ¬ CFSG.GorensteinWalter.IsComponentOf E ⊤ := by
  intro hE
  have hEq : CFSG.IsQuasisimple ↥E := H13.isQuasisimple_of_gw hE.2.2
  set K := E.map (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))).subtype with hK
  have hKq : CFSG.IsQuasisimple ↥K := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (E.equivMapOfInjective _ (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))).subtype_injective)
    hEq
  have hKC : K ≤ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) := Subgroup.map_subtype_le E
  have h3K : ¬ 3 ∣ Nat.card ↥K := not_three_dvd_card_of_pow fun x hx hx3 =>
    eq_one_of_prime_ne_five hB h2 (hKC hx) Nat.prime_three (by norm_num) (by norm_num) hx3
  obtain ⟨n, hn⟩ :=
    suzukiModel_of_le_of_not_dvd hA23 hSzF hB.hD.hyp.qsqtk (hKC.trans inf_le_left) hKq h3K
  have hSz : IsSz n (↥K ⧸ Subgroup.center ↥K) := hn
  obtain ⟨hnodd, hn3⟩ := odd_of_isSz hSz
  obtain ⟨r, hr, hr2, hrd⟩ := exists_prime_dvd_two_pow_sub_one (by omega : 2 ≤ n)
  have hr5 : r ≠ 5 := by
    rintro rfl
    exact five_not_dvd_two_pow_sub_one hnodd hrd
  have hrK : r ∣ Nat.card ↥K :=
    (dvd_card_of_isSz hSz hrd).trans (Subgroup.card_quotient_dvd_card _)
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' r hrK
  have hgr : (g : MulAut W) ^ r = 1 := by
    have h1 := pow_orderOf_eq_one g
    rw [hg] at h1
    rw [← Subgroup.coe_pow, h1]
    rfl
  have hg1 : g = 1 := Subtype.ext (eq_one_of_prime_ne_five hB h2 (hKC g.2) hr hr2 hr5 hgr)
  rw [hg1, orderOf_one] at hg
  exact hr.one_lt.ne hg

theorem twoResidual_eq_pCoreOf (hA23 : A23SQTKListFact)
    (hSzF : H13.SimpleThreePrimeSuzukiFact) (hB : D321Base M Mp T L V t) (h2 : D321Two L) :
    twoResidual (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) =
      pCoreOf 5 (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) := by
  classical
  set C := M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) with hC
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hO2 : CFSG.pCore 2 ↥C = ⊥ := by
    have h := pCoreOf_two_cent_eq_bot hB.hD
    unfold CFSG.Open.pCoreOf at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp h
  have hOp : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 5 → CFSG.pCore p ↥C = ⊥ := by
    intro p hp hp2 hp5
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (⟨x, hx⟩ : ↥(CFSG.pCore p ↥C))
    have hk' : (x : MulAut W) ^ (p ^ k) = 1 := by
      have h1 := congrArg (fun z : ↥(CFSG.pCore p ↥C) => ((z : ↥C) : MulAut W)) hk
      simpa using h1
    rw [Subgroup.mem_bot]
    exact Subtype.ext (eq_one_of_pow_prime_pow_ne_five hB h2 hp hp2 hp5 x.2 hk')
  have hE : CFSG.GorensteinWalter.componentLayerOf (⊤ : Subgroup ↥C) = ⊥ := by
    unfold CFSG.GorensteinWalter.componentLayerOf
    rw [sSup_eq_bot]
    intro E hEc
    exact absurd hEc (not_isComponentOf hA23 hSzF hB h2 E)
  have hF : CFSG.GorensteinWalter.generalizedFittingSubgroupOf (⊤ : Subgroup ↥C) ≤
      CFSG.pCore 5 ↥C := by
    unfold CFSG.GorensteinWalter.generalizedFittingSubgroupOf
    rw [show CFSG.GorensteinWalter.fittingSubgroupOf (⊤ : Subgroup ↥C) = CFSG.fittingSubgroup ↥C from
        CFSG.Adapters.fittingSubgroupOf_top_eq_foundations _,
      CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore, hE, sup_bot_eq]
    refine iSup_le fun p => ?_
    have hp := Nat.prime_of_mem_primeFactors p.2
    by_cases hp5 : (p : ℕ) = 5
    · rw [hp5]
    by_cases hp2 : (p : ℕ) = 2
    · rw [hp2, hO2]
      exact bot_le
    · rw [hOp p hp hp2 hp5]
      exact bot_le
  have hmem : ∀ z : ↥C, (∃ k : ℕ, z ^ (5 ^ k) = 1) → z ∈ CFSG.pCore 5 ↥C := by
    rintro z ⟨k, hk⟩
    have hz : IsPGroup 5 ↥(Subgroup.zpowers z) := IsPGroup.of_card_dvd_pow (n := k)
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hk)
    obtain ⟨S, hS⟩ := hz.exists_le_sylow
    have hScomm : ∀ a ∈ (S : Subgroup ↥C), ∀ b ∈ (S : Subgroup ↥C), a * b = b * a := by
      have hS'5 : IsPGroup 5 ↥((S : Subgroup ↥C).map C.subtype) := S.isPGroup'.map C.subtype
      obtain ⟨hcard, -⟩ := card_le_and_pow_five hB h2 (Subgroup.map_subtype_le _) hS'5
      rw [Subgroup.card_map_of_injective C.subtype_injective] at hcard
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 S.isPGroup'
      have hcm : IsMulCommutative ↥(S : Subgroup ↥C) := by
        rcases m with _ | _ | _ | m
        · rw [pow_zero] at hm
          have : Subsingleton ↥(S : Subgroup ↥C) := (Nat.card_eq_one_iff_unique.1 hm).1
          exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
        · have : IsCyclic ↥(S : Subgroup ↥C) :=
            isCyclic_of_prime_card (p := 5) (by rw [hm, zero_add, pow_one])
          infer_instance
        · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hm
        · exfalso
          have h1 : 5 ^ 3 ≤ Nat.card ↥(S : Subgroup ↥C) := by
            rw [hm]
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
          norm_num at h1
          omega
      intro a ha b hb
      exact congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := ↥(S : Subgroup ↥C))).comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hOS : CFSG.pCore 5 ↥C ≤ (S : Subgroup ↥C) := CFSG.pCore_isPGroup.le_sylow_of_normal S
    have hSF : (S : Subgroup ↥C) ≤ CFSG.pCore 5 ↥C := by
      intro s hs
      apply hF
      apply CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      exact hScomm f (hOS (hF hf)) s hs
    exact hSF (hS (Subgroup.mem_zpowers z))
  apply le_antisymm
  · refine twoResidual_le_of_isTwoQuotient (CFSG.LieType.BorelTits.pCoreOf_le 5 C)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 5 C) fun y hy => ?_
    obtain ⟨a, m, hm, hym⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
    refine ⟨a, ?_⟩
    have hz : orderOf (y ^ 2 ^ a) = m := by
      rw [orderOf_pow_of_dvd (by positivity) (by rw [hym]; exact dvd_mul_right _ _), hym,
        Nat.mul_div_cancel_left _ (by positivity)]
    have hm5 : m = 5 ^ m.primeFactorsList.length := by
      refine Nat.eq_prime_pow_of_unique_prime_dvd hm.pos.ne' fun {r} hr hrm => ?_
      by_contra hr5
      have hr2 : r ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 hrm)
      obtain ⟨d, hd⟩ := hrm
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hd
        exact hm.pos.ne' hd
      have hw : orderOf ((y ^ 2 ^ a) ^ d) = r := by
        rw [orderOf_pow_of_dvd hd0 (by rw [hz, hd]; exact dvd_mul_left _ _), hz, hd,
          Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd0)]
      have hwC : (y ^ 2 ^ a) ^ d ∈ C := C.pow_mem (C.pow_mem hy _) _
      have hw1 := eq_one_of_prime_ne_five hB h2 hwC hr hr2 hr5
        (by rw [← hw]; exact pow_orderOf_eq_one _)
      rw [hw1, orderOf_one] at hw
      exact hr.one_lt.ne hw
    refine ⟨⟨y ^ 2 ^ a, C.pow_mem hy _⟩, hmem _ ⟨m.primeFactorsList.length, ?_⟩, rfl⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hm5, ← hz, pow_orderOf_eq_one]
  · rintro x ⟨x₀, hx₀, rfl⟩
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (⟨x₀, hx₀⟩ : ↥(CFSG.pCore 5 ↥C))
    have hk' : (x₀ : MulAut W) ^ (5 ^ k) = 1 := by
      have h1 := congrArg (fun z : ↥(CFSG.pCore 5 ↥C) => ((z : ↥C) : MulAut W)) hk
      simpa using h1
    obtain ⟨j, hj⟩ := twoResidual_isTwoQuotient C (x₀ : MulAut W) x₀.2
    refine B6.mem_of_pow_mem_of_coprime hj ?_
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk')
      (Nat.Coprime.pow _ _ (by norm_num))

end CFSG.Quasithin.RonanD321.Five
