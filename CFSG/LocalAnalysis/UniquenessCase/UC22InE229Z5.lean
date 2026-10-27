module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.AbelianSylowCentre
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightDefs
import CFSG.LocalAnalysis.SignalizerFunctor.CoprimeQuotientNormalizers
import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Planes
import CFSG.LocalAnalysis.UniquenessCase.UC22S206c
import CFSG.LocalAnalysis.UniquenessCase.UC6S846a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.AbelianSylowCentre in
theorem uc22ine229_exists_mem_normalizer_not_mem_centralizer {H : Type*} [Group H] [Finite H]
    (hperf : _root_.commutator H = ⊤) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hrank : CFSG.Open.pRank q (⊤ : Subgroup H) ≤ 1) {X : Subgroup H} (hXc : Nat.card X = q) :
    ∃ w ∈ normalizer (X : Set H), w ∉ centralizer (X : Set H) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hXq : IsPGroup q X := IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])
  obtain ⟨P, hXP⟩ := hXq.exists_le_sylow
  have hcyc : IsCyclic (P : Subgroup H) :=
    RankFourTheoremC.Nongeneration.isCyclic_sylow_of_pRank_le_one hq2 hrank P
  haveI := hcyc
  haveI : IsMulCommutative (P : Subgroup H) := IsCyclic.isMulCommutative
  haveI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by rw [hXc]; exact hq.one_lt)
  obtain ⟨⟨x, hxX⟩, hx1⟩ := exists_ne (1 : X)
  by_contra hcon
  push Not at hcon
  have hfix : ∀ n ∈ normalizer ((P : Subgroup H) : Set H), n⁻¹ * x * n = x := by
    intro n hn
    have hnC := hcon n
      (CFSG.GorensteinWalter.prime_order_subgroup_fixed_by_normalizer_of_cyclic hcyc hXP hq hXc hn)
    rw [mul_assoc, Subgroup.mem_centralizer_iff.1 hnC x hxX, inv_mul_cancel_left]
  exact hx1 (Subtype.ext (eq_one_of_normalizer_fixed hperf P x (hXP hxX) hfix))

theorem uc22ine229_exists_lift {Y X : Subgroup G} (hXY : X ≤ Y) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hXq : IsPGroup q X) {w : Bar2 Y}
    (hw : w ∈ normalizer
      (((X.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) : Set (Bar2 Y))) :
    ∃ y : ↥Y, (y : G) ∈ normalizer (X : Set G) ∧ QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y = w := by
  have hcop : Nat.Coprime q (Nat.card (CFSG.pCore 2 ↥Y)) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hq Nat.prime_two).2 hq2)
  rw [← CFSG.SignalizerFunctor.Helpers.coprime_quotient_normalizer_image q hq
    (CFSG.pCore 2 ↥Y) (X.subgroupOf Y) hcop hXq.comap_subtype] at hw
  obtain ⟨y, hy, rfl⟩ := hw
  rw [← Subgroup.subgroupOf_normalizer_eq hXY, SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
  exact ⟨y, hy, rfl⟩

theorem uc22ine229_mk_mem_centralizer {Y X : Subgroup G} {y : ↥Y}
    (hy : (y : G) ∈ centralizer (X : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y ∈ centralizer
      (((X.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) : Set (Bar2 Y)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext (Subgroup.mem_centralizer_iff.1 hy x hx))

theorem uc22ine229_card_map {Y X : Subgroup G} (hXY : X ≤ Y) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hXc : Nat.card X = q) :
    Nat.card ((X.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) = q := by
  have hXq : IsPGroup q X := IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])
  have hdisj : Disjoint (X.subgroupOf Y) (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).ker := by
    rw [QuotientGroup.ker_mk', Subgroup.disjoint_def]
    intro x hxX hxO
    exact UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup hq hq2 hXq.comap_subtype
      CFSG.pCore_isPGroup hxX hxO
  rw [UC6S846.card_map_of_disjoint_ker _ _ hdisj, ← hXc]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXY).toEquiv

theorem uc22ine229_exists_not_mem_centralizer {M Y : Subgroup G} (hY : Y ∈ calC M) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hrank : CFSG.Open.pRank q (⊤ : Subgroup (Bar2 Y)) ≤ 1)
    {X : Subgroup G} (hXY : X ≤ Y) (hXc : Nat.card X = q) :
    ∃ w ∈ Y ⊓ normalizer (X : Set G), w ∉ centralizer (X : Set G) := by
  obtain ⟨w, hwN, hwC⟩ := uc22ine229_exists_mem_normalizer_not_mem_centralizer hY.2.2.1 hq hq2
    hrank (uc22ine229_card_map hXY hq hq2 hXc)
  obtain ⟨y, hyN, rfl⟩ := uc22ine229_exists_lift hXY hq hq2
    (IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])) hwN
  exact ⟨y, ⟨y.2, hyN⟩, fun h => hwC (uc22ine229_mk_mem_centralizer h)⟩

theorem uc22ine229_exists_not_mem_centralizer_of_thin {M Y : Subgroup G} (hY : Y ∈ calC M)
    (hthin : F08.Thin8 Y) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {X : Subgroup G} (hXY : X ≤ Y)
    (hXc : Nat.card X = q) :
    ∃ w ∈ Y ⊓ normalizer (X : Set G), w ∉ centralizer (X : Set G) :=
  uc22ine229_exists_not_mem_centralizer hY hq hq2
    ((uc22s206c_pRank_le Y hq hq2).trans (hthin q hq hq2)) hXY hXc

theorem uc22ine229_exists_prime_part {X : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hXc : Nat.card X = q) {w : G} (hwN : w ∈ normalizer (X : Set G))
    (hwC : w ∉ centralizer (X : Set G)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ q - 1 ∧ ∃ u ∈ zpowers w, (∃ e : ℕ, u ^ ℓ ^ e = 1) ∧
      u ∉ centralizer (X : Set G) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsCyclic X := isCyclic_of_prime_card hXc
  have hker : ∀ n : normalizer (X : Set G), X.normalizerMonoidHom n = 1 →
      (n : G) ∈ centralizer (X : Set G) := by
    intro n hn
    have h : n ∈ X.normalizerMonoidHom.ker := hn
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h
    exact h
  let a : MulAut X := X.normalizerMonoidHom ⟨w, hwN⟩
  have hd : orderOf a ∣ q - 1 := by
    have h := orderOf_dvd_natCard a
    rwa [IsCyclic.card_mulAut, hXc, Nat.totient_prime hq] at h
  have hd1 : orderOf a ≠ 1 := fun h => hwC (hker _ (orderOf_eq_one_iff.1 h))
  obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd hd1
  obtain ⟨e, m', hm', hm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos w).ne' ℓ hℓ.one_lt.ne'
  refine ⟨ℓ, hℓ, hℓd.trans hd, w ^ m', pow_mem (mem_zpowers w) m', ⟨e, ?_⟩, fun hC => ?_⟩
  · rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]
  · have h1 : X.normalizerMonoidHom (⟨w, hwN⟩ ^ m') = 1 := by
      rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
        SubgroupClass.coe_pow]
      exact hC
    rw [map_pow] at h1
    exact hm' (hℓd.trans (orderOf_dvd_of_pow_eq_one h1))

theorem uc22ine229_orderOf_pow_eq_prime {ℓ : ℕ} (hℓ : ℓ.Prime) {u : G} (hu : u ≠ 1) {e : ℕ}
    (he : u ^ ℓ ^ e = 1) : orderOf (u ^ (orderOf u / ℓ)) = ℓ := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hℓ).1 (orderOf_dvd_of_pow_eq_one he)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hu hj
  exact orderOf_pow_orderOf_div (orderOf_pos u).ne' (hj ▸ dvd_pow_self ℓ hj0)

theorem uc22ine229_trichotomy {W X : Subgroup G} {q : ℕ} (hq : q.Prime) (hXc : Nat.card X = q)
    {w : G} (hwW : w ∈ W) (hwN : w ∈ normalizer (X : Set G)) (hwC : w ∉ centralizer (X : Set G))
    (p : ℕ) :
    (∃ t ∈ W ⊓ normalizer (X : Set G), orderOf t = 2) ∨
      (∃ y ∈ W ⊓ normalizer (X : Set G), (orderOf y).Prime ∧ orderOf y ≠ 2 ∧ orderOf y ≠ p ∧
        orderOf y < q) ∨
      (p ∣ q - 1 ∧ ∃ u ∈ W ⊓ normalizer (X : Set G), IsPGroup p (zpowers u) ∧
        u ∉ centralizer (X : Set G)) := by
  obtain ⟨ℓ, hℓ, hℓq, u, hu, ⟨e, he⟩, huC⟩ := uc22ine229_exists_prime_part hq hXc hwN hwC
  have huW : u ∈ W ⊓ normalizer (X : Set G) :=
    (Subgroup.zpowers_le.2 (show w ∈ W ⊓ normalizer (X : Set G) from ⟨hwW, hwN⟩)) hu
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact huC (Subgroup.one_mem _)
  have hy := uc22ine229_orderOf_pow_eq_prime hℓ hu1 he
  have hyW : u ^ (orderOf u / ℓ) ∈ W ⊓ normalizer (X : Set G) := pow_mem huW _
  by_cases h2 : ℓ = 2
  · exact Or.inl ⟨_, hyW, hy.trans h2⟩
  by_cases hp : ℓ = p
  · subst hp
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hℓ).1 (orderOf_dvd_of_pow_eq_one he)
    exact Or.inr (Or.inr ⟨hℓq, u, huW, IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj]),
      huC⟩)
  · have hℓlt : ℓ < q := by
      have := Nat.le_of_dvd (by have := hq.two_le; omega) hℓq
      have := hq.two_le
      omega
    exact Or.inr (Or.inl ⟨_, hyW, by rw [hy]; exact hℓ, by rw [hy]; exact h2, by rw [hy]; exact hp,
      by rw [hy]; exact hℓlt⟩)

theorem uc22ine229_exists_involution_of_three {M Y : Subgroup G} (hY : Y ∈ calC M)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 Y)) ≤ 1) {X : Subgroup G} (hXY : X ≤ Y)
    (hXc : Nat.card X = 3) : ∃ t ∈ Y ⊓ normalizer (X : Set G), orderOf t = 2 := by
  obtain ⟨w, ⟨hwY, hwN⟩, hwC⟩ :=
    uc22ine229_exists_not_mem_centralizer hY Nat.prime_three (by norm_num) hrank hXY hXc
  rcases uc22ine229_trichotomy Nat.prime_three hXc hwY hwN hwC 3 with
    h | ⟨y, -, hy, hy2, -, hylt⟩ | ⟨h, -⟩
  · exact h
  · have := hy.two_le
    omega
  · exact absurd h (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.UC22
