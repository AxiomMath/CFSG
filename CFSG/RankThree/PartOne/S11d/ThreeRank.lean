module

public import CFSG.RankThree.PartOne.S11b.Sec109EvenRankFour
public import CFSG.RankThree.PartOne.S11b.Sec109LnTwoOuter
public import CFSG.RankThree.PartOne.S12.Sec12Two
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven
open CFSG.Assembly.LowTwoRank (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SectionRank.ClassicalEven (rotMatrix)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Matrix

namespace S11d

section ElementaryAbelian

theorem exists_elemAbelian_three_gens {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    {x y z : G} (hxN : x ∈ N) (hyN : y ∈ N) (hzN : z ∈ N)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1)
    (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z)
    (hx1 : x ≠ 1) (hy1 : ∀ n : ℕ, x ^ n ≠ y) (hz1 : ∀ n m : ℕ, x ^ n * y ^ m ≠ z) :
    ∃ X : Subgroup G, X ≤ N ∧ IsMulCommutative X ∧ (∀ g ∈ X, g ^ 3 = 1) ∧
      Nat.card X = 3 ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B₀ : Subgroup G := ⊥
  have h₀ : ∀ b : B₀, B₀.subtype b = 1 := fun b => Subgroup.mem_bot.1 b.2
  have hc₀ : ∀ a b : B₀, a * b = b * a := fun a b => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2])
  have hp₀ : ∀ a : B₀, a ^ 3 = 1 := fun a => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [Subgroup.mem_bot.1 a.2, one_pow])
  have hcard₀ : Nat.card B₀ = 3 ^ 0 := by rw [pow_zero]; exact Subgroup.card_bot
  obtain ⟨F₁, hF₁, hc₁, hp₁, hcard₁, hr₁⟩ := CFSG.SectionRank.exists_extend hc₀ hp₀ hcard₀
    B₀.subtype Subtype.val_injective (y := x) hx (by
      rintro ⟨b, hb⟩
      exact hx1 (hb ▸ h₀ b))
    (fun b => by rw [h₀ b]; exact Commute.one_left x)
  have hr₁' : ∀ a, ∃ n : ℕ, F₁ a = x ^ n := fun a => by
    obtain ⟨b, n, hb⟩ := hr₁ a
    exact ⟨n, by rw [hb, h₀ b, one_mul]⟩
  obtain ⟨F₂, hF₂, hc₂, hp₂, hcard₂, hr₂⟩ := CFSG.SectionRank.exists_extend hc₁ hp₁ hcard₁ F₁
    hF₁ (y := y) hy
    (by
      rintro ⟨a, ha⟩
      obtain ⟨n, hn⟩ := hr₁' a
      exact hy1 n (hn ▸ ha))
    (fun a => by
      obtain ⟨n, hn⟩ := hr₁' a
      rw [hn]
      exact hxy.pow_left n)
  have hr₂' : ∀ a, ∃ n m : ℕ, F₂ a = x ^ n * y ^ m := fun a => by
    obtain ⟨b, m, hb⟩ := hr₂ a
    obtain ⟨n, hn⟩ := hr₁' b
    exact ⟨n, m, by rw [hb, hn]⟩
  obtain ⟨F₃, hF₃, hc₃, hp₃, hcard₃, hr₃⟩ := CFSG.SectionRank.exists_extend hc₂ hp₂ hcard₂ F₂
    hF₂ (y := z) hz
    (by
      rintro ⟨a, ha⟩
      obtain ⟨n, m, hnm⟩ := hr₂' a
      exact hz1 n m (hnm ▸ ha))
    (fun a => by
      obtain ⟨n, m, hnm⟩ := hr₂' a
      rw [hnm]
      exact (hxz.pow_left n).mul_left (hyz.pow_left m))
  refine ⟨F₃.range, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    obtain ⟨b, l, hbl⟩ := hr₃ a
    obtain ⟨n, m, hnm⟩ := hr₂' b
    rw [hbl, hnm]
    exact N.mul_mem (N.mul_mem (N.pow_mem hxN n) (N.pow_mem hyN m)) (N.pow_mem hzN l)
  · exact ⟨⟨by
      rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      refine Subtype.ext ?_
      change F₃ a * F₃ b = F₃ b * F₃ a
      rw [← map_mul, ← map_mul, hc₃ a b]⟩⟩
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, hp₃ a, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hF₃).toEquiv]
    exact hcard₃

end ElementaryAbelian

section Normalizer

variable {n : ℕ} {K : Type*} [Field K]

theorem exists_elemAbelian_normalizer_radical_three [Finite K] (hn : 6 ≤ n) :
    ∃ X : Subgroup (Matrix.SpecialLinearGroup (Fin n) K),
      X ≤ Subgroup.normalizer (Sec109.twoPlaneRadical n K : Set _) ∧ IsMulCommutative X ∧
        (∀ g ∈ X, g ^ 3 = 1) ∧ Nat.card X = 3 ^ 3 := by
  obtain ⟨ι, hι⟩ : ∃ ι : Fin 6 → Fin n, ι = Fin.castLE hn := ⟨_, rfl⟩
  have hinj : Function.Injective ι := hι ▸ Fin.castLE_injective hn
  have hval : ∀ a : Fin 6, (ι a : ℕ) = a := fun a => hι ▸ Fin.val_castLE _ _
  have hne : ∀ a b : Fin 6, a ≠ b → ι a ≠ ι b := fun a b h => hinj.ne h
  have hlevi : ∀ a b : Fin 6, ((a : ℕ) < 2 ∧ (b : ℕ) < 2) ∨ (2 ≤ (a : ℕ) ∧ 2 ≤ (b : ℕ)) →
      Sec109.rotationSL (K := K) (ι a) (ι b) ∈
        Subgroup.normalizer (Sec109.twoPlaneRadical n K : Set _) :=
    fun a b h => Sec109.twoPlaneLevi_le_normalizer
      (Sec109.rotationSL_mem_twoPlaneLevi (by simpa only [hval] using h))
  refine exists_elemAbelian_three_gens
    (N := Subgroup.normalizer (Sec109.twoPlaneRadical n K : Set _))
    (x := Sec109.rotationSL (K := K) (ι 0) (ι 1)) (y := Sec109.rotationSL (K := K) (ι 2) (ι 3))
    (z := Sec109.rotationSL (K := K) (ι 4) (ι 5))
    (hlevi _ _ (by decide)) (hlevi _ _ (by decide)) (hlevi _ _ (by decide))
    (Sec109.rotationSL_pow_three _ _) (Sec109.rotationSL_pow_three _ _)
    (Sec109.rotationSL_pow_three _ _)
    (Sec109.rotationSL_commute (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)) (hne _ _ (by decide)))
    (Sec109.rotationSL_commute (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)) (hne _ _ (by decide)))
    (Sec109.rotationSL_commute (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)) (hne _ _ (by decide)))
    (Sec109.sl_ne_of_smul_single (hne _ _ (by decide)) (one_smul _ _)
      (Sec109.rotationSL_smul_single_left _ _)).symm
    (fun m => Sec109.sl_ne_of_smul_single (hne _ _ (by decide))
      (Sec109.rotationSL_pow_smul_single_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) m)
      (Sec109.rotationSL_smul_single_left _ _))
    (fun m k => Sec109.sl_ne_of_smul_single (hne _ _ (by decide)) (by
      rw [mul_smul, Sec109.rotationSL_pow_smul_single_of_ne (hne _ _ (by decide))
        (hne _ _ (by decide)) k,
        Sec109.rotationSL_pow_smul_single_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) m])
      (Sec109.rotationSL_smul_single_left _ _))

end Normalizer

theorem three_le_localRank_three_SL {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {n : ℕ} (hn : 6 ≤ n) : 3 ≤ localRank 3 (Matrix.SpecialLinearGroup (Fin n) K) := by
  obtain ⟨X, hXN, hXc, hXe, hXcard⟩ := exists_elemAbelian_normalizer_radical_three (K := K) hn
  exact Sec9Excl.le_localRank_of_normalizes (by norm_num : 1 < 3)
    (Sec109.twoPlaneRadical_ne_bot (by omega))
    (Sec109.twoPlaneRadical_isPGroup (Sec109.two_eq_zero_of_card_eq_two hK))
    hXc hXe hXcard hXN

theorem three_le_localRank_model {L : Type} [Group L] [Finite L] {n : ℕ}
    (hmodel : StatedClassicalModel L .PSL n 2 1) (hn : 6 ≤ n) : 3 ≤ localRank 3 L := by
  obtain ⟨⟨-, -, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hmodel
  have hK2 : Nat.card K = 2 := by simpa using hK
  let e' : L ≃* projectiveSL n K :=
    e.trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
  have : Finite (projectiveSL n K) := Finite.of_equiv L e'.toEquiv
  let eSL : Matrix.SpecialLinearGroup (Fin n) K ≃* projectiveSL n K :=
    MulEquiv.ofBijective (proj n K)
      ⟨Sec109.proj_injective_of_card_eq_two hK2 n, proj_surjective n K⟩
  calc 3 ≤ localRank 3 (Matrix.SpecialLinearGroup (Fin n) K) := three_le_localRank_three_SL hK2 hn
    _ ≤ localRank 3 (projectiveSL n K) :=
        CFSG.RankThree.PartTwo.Census.localRank_le_of_mulEquiv eSL Nat.prime_three
    _ ≤ localRank 3 L :=
        CFSG.RankThree.PartTwo.Census.localRank_le_of_mulEquiv e'.symm Nat.prime_three

variable {G : Type} [Group G] [Finite G]

theorem false_of_three_element_centralizing (hev : evenRank G ≤ 3) {M : Subgroup G} {n : ℕ}
    (hM : StatedClassicalModel ↥M .PSL n 2 1) (hn : 6 ≤ n) {z : G}
    (hz : z ∈ centralizer (M : Set G)) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) : False := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hel : IsElementaryAbelian 3 (zpowers z) := IsElementaryAbelian.zpowers_of_pow_eq_one hz3
  have hP : CFSG.Assembly.IsElemAbelian 3 (zpowers z) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mp hel
  have hPM : zpowers z ≤ centralizer (M : Set G) := (zpowers_le).mpr hz
  have hcenter : Subgroup.center ↥M = ⊥ := (Sec109.lnTwoOuter ↥M n hM).1
  have hdisj : zpowers z ⊓ M = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyz, hyM⟩
    rw [Subgroup.mem_bot]
    have hyc : y ∈ centralizer (M : Set G) := hPM hyz
    have hmem : (⟨y, hyM⟩ : M) ∈ Subgroup.center ↥M := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.mp hyc g g.2)
    rw [hcenter, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have h3 := three_le_localRank_model hM hn
  have hR := Sec12Two.localRank_add_le_evenRank hp (by norm_num) (M := M) (P := zpowers z)
    (by omega) hP hPM hdisj (k := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  omega

theorem exists_inner_of_pow_prime {M : Subgroup G} {n : ℕ}
    (hM : StatedClassicalModel ↥M .PSL n 2 1) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {h : G}
    (hN : h ∈ normalizer (M : Set G)) {a : ℕ} (ha : h ^ (r ^ a) = 1) :
    ∃ m ∈ M, ∀ g ∈ M, h * g * h⁻¹ = m * g * m⁻¹ := by
  have hout := (Sec109.lnTwoOuter ↥M n hM).2
  set α : MulAut ↥M := M.normalizerMonoidHom ⟨h, hN⟩ with hα
  set q := QuotientGroup.mk' (inner ↥M) α with hq
  have hqpow : q ^ (r ^ a) = 1 := by
    rw [hq, ← map_pow, hα, ← map_pow]
    have : (⟨h, hN⟩ : normalizer (M : Set G)) ^ (r ^ a) = 1 := Subtype.ext (by simpa using ha)
    rw [this, map_one, map_one]
  have hqdvd : orderOf q ∣ r ^ a := orderOf_dvd_of_pow_eq_one hqpow
  have hqle : orderOf q ≤ 2 := (Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard q)).trans hout
  have hq1 : orderOf q = 1 := by
    rcases (Nat.dvd_prime_pow hr).mp hqdvd with ⟨j, -, hj⟩
    rw [hj] at hqle ⊢
    rcases j with _ | j
    · rfl
    · exfalso
      have hr3 : 3 ≤ r := by
        have := hr.two_le
        omega
      have : r ≤ r ^ (j + 1) := Nat.le_self_pow (Nat.succ_ne_zero j) r
      omega
  have hα1 : α ∈ inner ↥M := (QuotientGroup.eq_one_iff α).mp (orderOf_eq_one_iff.mp hq1)
  obtain ⟨m, hm⟩ := hα1
  refine ⟨(m : G), m.2, fun g hg => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥M => ((φ ⟨g, hg⟩ : M) : G)) hm
  simp only [hα, Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
  simpa using h1.symm

theorem mem_of_pow_three (hev : evenRank G ≤ 3) {M : Subgroup G} {n : ℕ}
    (hM : StatedClassicalModel ↥M .PSL n 2 1) (hn : 6 ≤ n) {h : G}
    (hN : h ∈ normalizer (M : Set G)) {a : ℕ} (ha : h ^ (3 ^ a) = 1) : h ∈ M := by
  obtain ⟨m, hmM, hm⟩ := exists_inner_of_pow_prime hM Nat.prime_three (by norm_num) hN ha
  have hcenter : Subgroup.center ↥M = ⊥ := (Sec109.lnTwoOuter ↥M n hM).1
  set z₀ : G := m⁻¹ * h with hz₀
  have hz₀C : z₀ ∈ centralizer (M : Set G) := by
    rw [mem_centralizer_iff]
    intro g hg
    have h1 := hm g hg
    have : m⁻¹ * h * g = g * (m⁻¹ * h) := by
      calc m⁻¹ * h * g = m⁻¹ * (h * g * h⁻¹) * h := by group
        _ = m⁻¹ * (m * g * m⁻¹) * h := by rw [h1]
        _ = g * (m⁻¹ * h) := by group
    exact this.symm
  have hhm : Commute m⁻¹ h := by
    have h1 := hm m hmM
    have h2 : h * m * h⁻¹ = m := by rw [h1]; group
    have h3 : h * m = m * h := by
      calc h * m = (h * m * h⁻¹) * h := by group
        _ = m * h := by rw [h2]
    exact (Commute.inv_left (show Commute m h from h3.symm))
  have hpow : z₀ ^ (3 ^ a) = 1 := by
    have h1 : z₀ ^ (3 ^ a) = (m⁻¹) ^ (3 ^ a) * h ^ (3 ^ a) := hhm.mul_pow _
    rw [ha, mul_one] at h1
    have h2 : z₀ ^ (3 ^ a) ∈ centralizer (M : Set G) := Subgroup.pow_mem _ hz₀C _
    have h3 : z₀ ^ (3 ^ a) ∈ M := by rw [h1]; exact M.pow_mem (M.inv_mem hmM) _
    have hmem : (⟨z₀ ^ (3 ^ a), h3⟩ : M) ∈ Subgroup.center ↥M := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.mp h2 g g.2)
    rw [hcenter, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hz₀1 : z₀ = 1 := by
    by_contra hne
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hpow)
    have hj1 : j ≠ 0 := by
      rintro rfl
      exact hne (orderOf_eq_one_iff.mp (by simpa using hj))
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hz3 : (z₀ ^ (3 ^ i)) ^ 3 = 1 := by
      rw [← pow_mul, ← pow_succ]
      exact hj ▸ pow_orderOf_eq_one z₀
    have hz1 : z₀ ^ (3 ^ i) ≠ 1 := by
      apply pow_ne_one_of_lt_orderOf (by positivity)
      rw [hj]
      exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self i)
    exact false_of_three_element_centralizing hev hM hn (Subgroup.pow_mem _ hz₀C _) hz3 hz1
  have hh : h = m := by
    have : m⁻¹ * h = 1 := hz₀1
    calc h = m * (m⁻¹ * h) := by group
      _ = m := by rw [this, mul_one]
  rw [hh]
  exact hmM

end S11d

end CFSG.RankThree.PartOne
