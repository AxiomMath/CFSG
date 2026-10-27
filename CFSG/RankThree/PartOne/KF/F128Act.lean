module

public import CFSG.RankThree.PartOne.K1214.CycAlg
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.RankThree.PartOne.S11d.OutCentral
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.RankThree.PartOne.S11c.Sec66Glue
public import CFSG.RankThree.PartOne.S11d.FixedFacts

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
  CFSG.RankThree.PartOne.Torsion37

variable {G : Type} [Group G]

theorem centerQuotientConj_of_centralizer {J : Subgroup G} {z : G}
    (hz : z ∈ Subgroup.centralizer (J : Set G)) :
    centerQuotientConj J ⟨z, Subgroup.centralizer_le_normalizer _ hz⟩ = 1 := by
  have hzn : z ∈ Subgroup.normalizer (J : Set G) := Subgroup.centralizer_le_normalizer _ hz
  ext q
  induction q using QuotientGroup.induction_on with
  | H l =>
    have h1 : centerQuotientConj J ⟨z, hzn⟩ (l : ↥J ⧸ Subgroup.center ↥J) =
        ((⟨z * (l : G) * z⁻¹, (Subgroup.mem_normalizer_iff.mp hzn (l : G)).mp l.2⟩ : ↥J) :
          ↥J ⧸ Subgroup.center ↥J) := rfl
    rw [h1]
    show _ = (l : ↥J ⧸ Subgroup.center ↥J)
    congr 1
    apply Subtype.ext
    show z * (l : G) * z⁻¹ = l
    have := Subgroup.mem_centralizer_iff.1 hz l l.2
    calc z * (l : G) * z⁻¹ = (z * l) * z⁻¹ := rfl
      _ = (l * z) * z⁻¹ := by rw [← this]
      _ = l := by group

theorem centerQuotientConj_mem_innerAut_iff {J : Subgroup G} (hJ : Group.IsPerfect ↥J) {v : G}
    (hv : v ∈ Subgroup.normalizer (J : Set G)) :
    centerQuotientConj J ⟨v, hv⟩ ∈ innerAut (↥J ⧸ Subgroup.center ↥J) ↔
      v ∈ J ⊔ Subgroup.centralizer (J : Set G) := by
  constructor
  · rintro ⟨q, hq⟩
    exact mem_sup_of_inner hJ hv hq.symm
  · intro h
    obtain ⟨j, hj, z, hz, rfl⟩ := (K1214.mem_sup_centralizer_iff J).1 h
    have hjn : j ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hj
    have hzn : z ∈ Subgroup.normalizer (J : Set G) := Subgroup.centralizer_le_normalizer _ hz
    have h1 : (⟨j * z, hv⟩ : Subgroup.normalizer (J : Set G)) = ⟨j, hjn⟩ * ⟨z, hzn⟩ := rfl
    rw [h1, map_mul, centerQuotientConj_of_centralizer hz, mul_one]
    exact ⟨((⟨j, hj⟩ : J) : ↥J ⧸ Subgroup.center ↥J),
      (centerQuotientConj_of_mem ⟨j, hj⟩).symm⟩

theorem zpow_eq_of_dvd_sub {p : ℕ} {x : G} (hx : x ^ p = 1) {n m : ℤ} (h : (p : ℤ) ∣ n - m) :
    x ^ n = x ^ m := by
  obtain ⟨t, ht⟩ := h
  have hn : n = m + p * t := by linarith
  rw [hn, zpow_add, zpow_mul, zpow_natCast, hx, one_zpow, mul_one]

theorem acts_trivially_of_mem_sup [Finite G] {p : ℕ} (hp : p.Prime) {J P E : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P J) (hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hEP : E ≤ Subgroup.normalizer (P : Set G)) (hEel : IsElementaryAbelian p E)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) {w : G} (hwE : w ∈ E)
    (hw : w ∈ J ⊔ Subgroup.centralizer (J : Set G)) : ∀ x ∈ P, w * x * w⁻¹ = x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hPJ : P ≤ J := hP.le
  obtain ⟨j, hjJ, z, hzC, rfl⟩ := (K1214.mem_sup_centralizer_iff J).1 hw
  have hwp : (j * z) ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) (j * z) hwE
  have hjz : Commute j z := Subgroup.mem_centralizer_iff.1 hzC j hjJ
  have hjp : j ^ p * z ^ p = 1 := by
    rw [← hjz.mul_pow]
    exact hwp
  have hζC : j ^ p ∈ Subgroup.centralizer (J : Set G) := by
    have : j ^ p = (z ^ p)⁻¹ := eq_inv_of_mul_eq_one_left hjp
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hzC p)
  set ζ : ↥(Subgroup.center ↥J) := ⟨⟨j ^ p, J.pow_mem hjJ p⟩, Subgroup.mem_center_iff.2 fun g =>
    Subtype.ext (Subgroup.mem_centralizer_iff.1 hζC g g.2)⟩ with hζdef
  have hord : orderOf ζ ∣ Nat.card (Subgroup.center ↥J) := orderOf_dvd_natCard _
  have hcop : Nat.Coprime p (orderOf ζ) :=
    Nat.Coprime.coprime_dvd_right hord ((Nat.Prime.coprime_iff_not_dvd hp).2 hZ)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hm' : ((j ^ p) ^ p) ^ m = j ^ p := by
    have := congrArg (fun t : ↥(Subgroup.center ↥J) => ((t : ↥J) : G)) hm
    simpa [hζdef] using this
  set u : G := (j ^ p) ^ m with hu
  have huC : u ∈ Subgroup.centralizer (J : Set G) := Subgroup.pow_mem _ hζC m
  have hup : u ^ p = j ^ p := by
    rw [hu, ← pow_mul, mul_comm m p, pow_mul]
    exact hm'
  set j₁ : G := j * u⁻¹ with hj₁
  have hj₁p : j₁ ^ p = 1 := by
    have hc : Commute j u⁻¹ :=
      (((Commute.refl j).pow_right p).pow_right m).inv_right
    rw [hj₁, hc.mul_pow, inv_pow, hup, mul_inv_cancel]
  have hj_eq : j = j₁ * u := (inv_mul_cancel_right j u).symm
  have hj₁J : j₁ ∈ J := J.mul_mem hjJ (J.inv_mem (J.pow_mem (J.pow_mem hjJ p) m))
  have hCN : ∀ {y : G}, y ∈ Subgroup.centralizer (J : Set G) → y ∈ Subgroup.normalizer (P : Set G) :=
    fun hy => Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hPJ) hy)
  have hjN : j ∈ Subgroup.normalizer (P : Set G) := by
    have : j = (j * z) * z⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (hEP hwE) (Subgroup.inv_mem _ (hCN hzC))
  have hj₁N : j₁ ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.mul_mem _ hjN (Subgroup.inv_mem _ (hCN huC))
  have hj₁ord : ∃ k : ℕ, orderOf j₁ = p ^ k := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hj₁p) with h1 | h1
    · exact ⟨0, by simpa using h1⟩
    · exact ⟨1, by simpa using h1⟩
  have hj₁P : j₁ ∈ P := mem_of_pElement_mem_normalizer hP hj₁J hj₁N hj₁ord
  intro x hx
  have hxJ : x ∈ J := hPJ hx
  have hzx : z * x * z⁻¹ = x := by
    have := Subgroup.mem_centralizer_iff.1 hzC x hxJ
    calc z * x * z⁻¹ = (x * z) * z⁻¹ := by rw [← this]
      _ = x := by group
  have hux : u * x * u⁻¹ = x := by
    have := Subgroup.mem_centralizer_iff.1 huC x hxJ
    calc u * x * u⁻¹ = (x * u) * u⁻¹ := by rw [← this]
      _ = x := by group
  have hj₁x : j₁ * x * j₁⁻¹ = x := by
    have := hPab j₁ hj₁P x hx
    calc j₁ * x * j₁⁻¹ = (x * j₁) * j₁⁻¹ := by rw [this]
      _ = x := by group
  calc j * z * x * (j * z)⁻¹ = j * (z * x * z⁻¹) * j⁻¹ := by group
    _ = j * x * j⁻¹ := by rw [hzx]
    _ = (j₁ * u) * x * (j₁ * u)⁻¹ := by rw [← hj_eq]
    _ = j₁ * (u * x * u⁻¹) * j₁⁻¹ := by group
    _ = j₁ * x * j₁⁻¹ := by rw [hux]
    _ = x := hj₁x

theorem exists_pow_mul_mem_sup [Finite G] {p : ℕ} (hp : p.Prime) {J E : Subgroup G}
    (hJ : Group.IsPerfect ↥J) (hEel : IsElementaryAbelian p E)
    (hEN : E ≤ Subgroup.normalizer (J : Set G)) {a : G} (haE : a ∈ E)
    (haJ : a ∉ J ⊔ Subgroup.centralizer (J : Set G))
    (hK2 : ∀ E' : Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J)), IsElementaryAbelian p ↥E' →
      Nat.card E' = p ^ 2 → E' ⊓ innerAut (↥J ⧸ Subgroup.center ↥J) = ⊥ →
      (∀ α ∈ E', LocalRankAut p (↥J ⧸ Subgroup.center ↥J) α) → False)
    (hLRA : ∀ (v : G) (hv : v ∈ E),
      LocalRankAut p (↥J ⧸ Subgroup.center ↥J) (centerQuotientConj J ⟨v, hEN hv⟩))
    {e : G} (heE : e ∈ E) : ∃ k : ℕ, a ^ k * e ∈ J ⊔ Subgroup.centralizer (J : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_contra hH
  push Not at hH
  have haN : a ∈ Subgroup.normalizer (J : Set G) := hEN haE
  have heN : e ∈ Subgroup.normalizer (J : Set G) := hEN heE
  have hap : a ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) a haE
  have hep : e ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) e heE
  have hae : a * e = e * a := mul_comm_of_isElementaryAbelian hEel haE heE
  have hH' : ∀ i : ℤ, a ^ i * e ∉ J ⊔ Subgroup.centralizer (J : Set G) := by
    intro i
    obtain ⟨k, hk⟩ : ∃ k : ℕ, a ^ k = a ^ i :=
      (Submonoid.mem_powers_iff _ _).1
        (mem_powers_iff_mem_zpowers.2 (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) i))
    rw [← hk]
    exact hH k
  have hΦpow : ∀ (v : G) (hv : v ∈ E) (i : ℤ), centerQuotientConj J ⟨v, hEN hv⟩ ^ i =
      centerQuotientConj J ⟨v ^ i, hEN (E.zpow_mem hv i)⟩ := by
    intro v hv i
    rw [← map_zpow]
    exact congrArg _ (Subtype.ext (by simp))
  have hΦmul : ∀ (v w : G) (hv : v ∈ E) (hw : w ∈ E),
      centerQuotientConj J ⟨v, hEN hv⟩ * centerQuotientConj J ⟨w, hEN hw⟩ =
        centerQuotientConj J ⟨v * w, hEN (E.mul_mem hv hw)⟩ := by
    intro v w hv hw
    rw [← map_mul]
    rfl
  have hinner : ∀ (v : G) (hv : v ∈ E), centerQuotientConj J ⟨v, hEN hv⟩ ∈
      innerAut (↥J ⧸ Subgroup.center ↥J) ↔ v ∈ J ⊔ Subgroup.centralizer (J : Set G) :=
    fun v hv => centerQuotientConj_mem_innerAut_iff hJ (hEN hv)
  set α := centerQuotientConj J ⟨a, haN⟩ with hα
  set ε := centerQuotientConj J ⟨e, heN⟩ with hε
  have hα1 : α ≠ 1 := centerQuotientConj_ne_one hJ haN haJ
  have hε1 : ε ≠ 1 := centerQuotientConj_ne_one hJ heN (by simpa using hH' 0)
  have hαp : α ^ p = 1 := centerQuotientConj_pow haN hap
  have hεp : ε ^ p = 1 := centerQuotientConj_pow heN hep
  have hαord : orderOf α = p := orderOf_eq_prime hαp hα1
  have hεord : orderOf ε = p := orderOf_eq_prime hεp hε1
  have hαε : Commute α ε := by
    show α * ε = ε * α
    rw [hα, hε, hΦmul a e haE heE, hΦmul e a heE haE]
    exact congrArg _ (Subtype.ext hae)
  have hcomm : ∀ k ∈ Subgroup.zpowers α, ∀ l ∈ Subgroup.zpowers ε, k * l = l * k := by
    intro k hk l hl
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hl
    exact (hαε.zpow_zpow i j).eq
  have hdisj : Disjoint (Subgroup.zpowers α) (Subgroup.zpowers ε) := by
    rw [Subgroup.disjoint_def]
    intro x hxα hxε
    by_contra hx1
    have h1 : Subgroup.zpowers x = Subgroup.zpowers α :=
      K1214.zpowers_eq_of_card_prime hp (by rw [Nat.card_zpowers, hαord]) hxα hx1
    have h2 : Subgroup.zpowers x = Subgroup.zpowers ε :=
      K1214.zpowers_eq_of_card_prime hp (by rw [Nat.card_zpowers, hεord]) hxε hx1
    have hεα : ε ∈ Subgroup.zpowers α := by
      rw [← h1, h2]
      exact Subgroup.mem_zpowers ε
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hεα
    have hv : a ^ (-i) * e ∈ E := E.mul_mem (E.zpow_mem haE _) heE
    have hΦv : centerQuotientConj J ⟨a ^ (-i) * e, hEN hv⟩ = 1 := by
      rw [← hΦmul (a ^ (-i)) e (E.zpow_mem haE _) heE, ← hΦpow a haE (-i), ← hα, ← hε, ← hi,
        zpow_neg, inv_mul_cancel]
    have hvJC : a ^ (-i) * e ∈ J ⊔ Subgroup.centralizer (J : Set G) := by
      refine (hinner _ hv).1 ?_
      rw [hΦv]
      exact (innerAut _).one_mem
    exact hH' (-i) hvJC
  have hel : IsElementaryAbelian p ↥(Subgroup.zpowers α ⊔ Subgroup.zpowers ε) :=
    isElementaryAbelian_sup_of_commute (IsElementaryAbelian.zpowers_of_pow_eq_one hαp)
      (IsElementaryAbelian.zpowers_of_pow_eq_one hεp) hcomm
  have hcard : Nat.card ↥(Subgroup.zpowers α ⊔ Subgroup.zpowers ε) = p ^ 2 := by
    rw [card_sup_of_commute_disjoint hcomm hdisj, Nat.card_zpowers, Nat.card_zpowers, hαord, hεord]
    ring
  have hLR : ∀ β ∈ Subgroup.zpowers α ⊔ Subgroup.zpowers ε,
      LocalRankAut p (↥J ⧸ Subgroup.center ↥J) β := by
    intro β hβ
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hβ
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hvE : a ^ i * e ^ j ∈ E := E.mul_mem (E.zpow_mem haE i) (E.zpow_mem heE j)
    have hΦ : α ^ i * ε ^ j = centerQuotientConj J ⟨a ^ i * e ^ j, hEN hvE⟩ := by
      rw [hα, hε, hΦpow a haE i, hΦpow e heE j, hΦmul (a ^ i) (e ^ j) (E.zpow_mem haE i) (E.zpow_mem heE j)]
    rw [hΦ]
    exact hLRA _ hvE
  have hinn : (Subgroup.zpowers α ⊔ Subgroup.zpowers ε) ⊓ innerAut (↥J ⧸ Subgroup.center ↥J) =
      ⊥ := by
    rw [eq_bot_iff]
    rintro β ⟨hβ, hβinn⟩
    rw [Subgroup.mem_bot]
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hβ
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hvE : a ^ i * e ^ j ∈ E := E.mul_mem (E.zpow_mem haE i) (E.zpow_mem heE j)
    have hΦ : α ^ i * ε ^ j = centerQuotientConj J ⟨a ^ i * e ^ j, hEN hvE⟩ := by
      rw [hα, hε, hΦpow a haE i, hΦpow e heE j, hΦmul (a ^ i) (e ^ j) (E.zpow_mem haE i) (E.zpow_mem heE j)]
    rw [hΦ] at hβinn ⊢
    have hvJC : a ^ i * e ^ j ∈ J ⊔ Subgroup.centralizer (J : Set G) :=
      (hinner _ hvE).1 hβinn
    by_cases hj : (p : ℤ) ∣ j
    · have hej : e ^ j = 1 := by
        simpa using zpow_eq_of_dvd_sub hep (m := 0) (by simpa using hj)
      rw [hej, mul_one] at hvJC
      by_cases hi : (p : ℤ) ∣ i
      · have hai : a ^ i = 1 := by
          simpa using zpow_eq_of_dvd_sub hap (m := 0) (by simpa using hi)
        have : (⟨a ^ i * e ^ j, hEN hvE⟩ : Subgroup.normalizer (J : Set G)) = 1 :=
          Subtype.ext (by simp [hai, hej])
        rw [this, map_one]
      · exfalso
        obtain ⟨i', hi'⟩ := K1214.exists_dvd_add_mul (s := -1) hp hi
        have h1 : (p : ℤ) ∣ 1 - i * i' := by
          have := dvd_neg.2 hi'
          rwa [show -(-1 + i * i') = 1 - i * i' by ring] at this
        have h2 : a = (a ^ i) ^ i' := by
          rw [← zpow_mul]
          simpa using zpow_eq_of_dvd_sub hap (n := 1) (m := i * i') h1
        apply haJ
        rw [h2]
        exact Subgroup.zpow_mem _ hvJC i'
    · exfalso
      obtain ⟨j', hj'⟩ := K1214.exists_dvd_add_mul (s := -1) hp hj
      have h1 : (p : ℤ) ∣ j * j' - 1 := by
        rwa [show (-1 + j * j' : ℤ) = j * j' - 1 by ring] at hj'
      have hcomm' : Commute (a ^ i) (e ^ j) :=
        ((show Commute a e from hae).zpow_zpow i j)
      have h2 : (a ^ i * e ^ j) ^ j' = a ^ (i * j') * e := by
        rw [hcomm'.mul_zpow, ← zpow_mul, ← zpow_mul, zpow_eq_of_dvd_sub hep h1, zpow_one]
      apply hH' (i * j')
      rw [← h2]
      exact Subgroup.zpow_mem _ hvJC j'
  exact hK2 _ hel hcard hinn hLR

theorem exists_act_pow [Finite G] {p : ℕ} (hp : p.Prime) {J P E : Subgroup G}
    (hJ : Group.IsPerfect ↥J) (hP : CFSG.ABGLocalTools.IsSylowOf p P J)
    (hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hEP : E ≤ Subgroup.normalizer (P : Set G))
    (hEel : IsElementaryAbelian p E) (hEN : E ≤ Subgroup.normalizer (J : Set G))
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) {a : G} (haE : a ∈ E)
    (haJ : a ∉ J ⊔ Subgroup.centralizer (J : Set G))
    (hK2 : ∀ E' : Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J)), IsElementaryAbelian p ↥E' →
      Nat.card E' = p ^ 2 → E' ⊓ innerAut (↥J ⧸ Subgroup.center ↥J) = ⊥ →
      (∀ α ∈ E', LocalRankAut p (↥J ⧸ Subgroup.center ↥J) α) → False)
    (hLRA : ∀ (v : G) (hv : v ∈ E),
      LocalRankAut p (↥J ⧸ Subgroup.center ↥J) (centerQuotientConj J ⟨v, hEN hv⟩))
    {e : G} (heE : e ∈ E) : ∃ k : ℕ, ∀ x ∈ P, e * x * e⁻¹ = a ^ k * x * (a ^ k)⁻¹ := by
  obtain ⟨k, hk⟩ := exists_pow_mul_mem_sup hp hJ hEel hEN haE haJ hK2 hLRA heE
  have hwE : a ^ k * e ∈ E := E.mul_mem (E.pow_mem haE k) heE
  have htriv := acts_trivially_of_mem_sup hp hP hPab hEP hEel hZ hwE hk
  obtain ⟨k', hk'⟩ : ∃ k' : ℕ, a ^ k' = (a ^ k)⁻¹ :=
    (Submonoid.mem_powers_iff _ _).1
      (mem_powers_iff_mem_zpowers.2 (Subgroup.inv_mem _ (Subgroup.pow_mem _
        (Subgroup.mem_zpowers a) k)))
  refine ⟨k', fun x hx => ?_⟩
  have he_eq : e = a ^ k' * (a ^ k * e) := by rw [hk', inv_mul_cancel_left]
  have hxP : a ^ k' * x * (a ^ k')⁻¹ ∈ P := by
    have hak : a ^ k' ∈ Subgroup.normalizer (P : Set G) := Subgroup.pow_mem _ (hEP haE) k'
    exact (Subgroup.mem_normalizer_iff.1 hak x).1 hx
  have h1 := htriv _ hxP
  calc e * x * e⁻¹ = a ^ k' * ((a ^ k * e) * x * (a ^ k * e)⁻¹) * (a ^ k')⁻¹ := by
        conv_lhs => rw [he_eq]
        group
    _ = a ^ k' * x * (a ^ k')⁻¹ := by rw [htriv x hx]

end CFSG.RankThree.PartOne
