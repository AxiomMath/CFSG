module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open scoped commutatorElement

namespace CFSG.Quasithin

namespace LRed12

variable {G : Type*} [Group G]

private theorem lred12_mem_normalizer_of_pow_eq_one {P : Subgroup G} {j : G} {m : ℕ} (hm : 0 < m)
    (hjm : j ^ m = 1) (hjP : ∀ y ∈ P, j * y * j⁻¹ ∈ P) :
    j ∈ Subgroup.normalizer (P : Set G) := by
  have hpow : ∀ k : ℕ, ∀ y ∈ P, j ^ k * y * (j ^ k)⁻¹ ∈ P := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      have h1 := hjP _ (ih y hy)
      have e : j ^ (k + 1) * y * (j ^ (k + 1))⁻¹ = j * (j ^ k * y * (j ^ k)⁻¹) * j⁻¹ := by
        rw [pow_succ', mul_inv_rev]; group
      rw [e]; exact h1
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hjP y, fun hy => ?_⟩
  have h1 := hpow (m - 1) _ hy
  have haj : j ^ (m - 1) * j = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hm]; exact hjm
  have hja : j ^ (m - 1) = j⁻¹ := eq_inv_of_mul_eq_one_left haj
  rw [hja] at h1
  simpa [mul_assoc] using h1

private theorem lred12_mem_normalizer_of_finite {P : Subgroup G} [Finite P] {j : G}
    (hjP : ∀ y ∈ P, j * y * j⁻¹ ∈ P) : j ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hjP y, fun hy => ?_⟩
  let f : P → P := fun x => ⟨j * x * j⁻¹, hjP x x.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h := congrArg Subtype.val hab
    simp only [f] at h
    exact Subtype.ext (by simpa using h)
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hf) ⟨j * y * j⁻¹, hy⟩
  have h : j * (x : G) * j⁻¹ = j * y * j⁻¹ := congrArg Subtype.val hx
  have hxy : (x : G) = y := by simpa using h
  rw [← hxy]; exact x.2

theorem commutator_mem_sup_zpowers_of_mem_normalizer {P : Subgroup G} {j : G}
    (hj : j ∈ Subgroup.normalizer (P : Set G)) :
    ∀ x ∈ P ⊔ Subgroup.zpowers j, ∀ y ∈ P ⊔ Subgroup.zpowers j, ⁅x, y⁆ ∈ P := by
  have hle : Subgroup.zpowers j ≤ Subgroup.normalizer (P : Set G) := Subgroup.zpowers_le.mpr hj
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left P (Subgroup.zpowers j) hle
  have hconj : ∀ c ∈ Subgroup.zpowers j, ∀ q ∈ P, c * q * c⁻¹ ∈ P := fun c hc q hq =>
    ((Subgroup.mem_normalizer_iff.mp (hle hc)) q).mp hq
  intro x hx y hy
  have hx' : x ∈ (↑(P ⊔ Subgroup.zpowers j) : Set G) := hx
  have hy' : y ∈ (↑(P ⊔ Subgroup.zpowers j) : Set G) := hy
  rw [hcoe] at hx' hy'
  obtain ⟨p, hp, a, ha, rfl⟩ := hx'
  obtain ⟨q, hq, b, hb, rfl⟩ := hy'
  have hab : a * b * a⁻¹ = b := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [(Commute.zpow_zpow_self j k l).eq, mul_inv_cancel_right]
  have e : ⁅p * a, q * b⁆ = p * (a * q * a⁻¹) * (b * p⁻¹ * b⁻¹) * q⁻¹ := by
    rw [commutatorElement_def]
    calc p * a * (q * b) * (p * a)⁻¹ * (q * b)⁻¹
        = p * (a * q * a⁻¹) * (a * b * a⁻¹) * p⁻¹ * b⁻¹ * q⁻¹ := by group
      _ = p * (a * q * a⁻¹) * b * p⁻¹ * b⁻¹ * q⁻¹ := by rw [hab]
      _ = p * (a * q * a⁻¹) * (b * p⁻¹ * b⁻¹) * q⁻¹ := by group
  rw [e]
  exact P.mul_mem (P.mul_mem (P.mul_mem hp (hconj a ha q hq))
    (hconj b hb p⁻¹ (P.inv_mem hp))) (P.inv_mem hq)

theorem isPGroup_three_sup_zpowers {P : Subgroup G} (hP : IsPGroup 3 P) {j : G}
    (hj : ∃ n : ℕ, j ^ 3 ^ n = 1) (hjP : ∀ y ∈ P, j * y * j⁻¹ ∈ P) :
    IsPGroup 3 ↥(P ⊔ Subgroup.zpowers j) := by
  obtain ⟨n, hn⟩ := hj
  have hjn : j ∈ Subgroup.normalizer (P : Set G) :=
    lred12_mem_normalizer_of_pow_eq_one (pow_pos (by norm_num) n) hn hjP
  have hZ : IsPGroup 3 ↥(Subgroup.zpowers j) := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
    refine ⟨n, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn, one_zpow]
  exact hP.to_sup_of_normal_left' hZ (Subgroup.zpowers_le.mpr hjn)

theorem commutator_mem_of_sup_zpowers {P : Subgroup G} {j : G} [Finite ↥P]
    (hjP : ∀ y ∈ P, j * y * j⁻¹ ∈ P) :
    ∀ x ∈ P ⊔ Subgroup.zpowers j, ∀ y ∈ P ⊔ Subgroup.zpowers j, ⁅x, y⁆ ∈ P :=
  commutator_mem_sup_zpowers_of_mem_normalizer (lred12_mem_normalizer_of_finite hjP)

theorem exists_central_comm_eigen [Finite G] {L : Subgroup G} (hL : IsPGroup 3 L) {b : G}
    (hb2 : b ^ 2 = 1) (hbL : ∀ y ∈ L, b * y * b⁻¹ ∈ L)
    (hnc : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x) :
    ∃ z ∈ L, z ∈ ⁅L, L⁆ ∧ z ≠ 1 ∧ z ^ 3 = 1 ∧ (∀ g ∈ L, g * z = z * g) ∧
      (b * z * b⁻¹ = z ∨ b * z * b⁻¹ = z⁻¹) := by
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy⟩ := hnc
  have hnil : Group.IsNilpotent ↥L := hL.isNilpotent
  have hcne : commutator ↥L ≠ ⊥ := by
    intro hbot
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    have h1 := Subgroup.mem_centralizer_iff.mp (hbot (Subgroup.mem_top (⟨x₀, hx₀⟩ : ↥L)))
      ⟨y₀, hy₀⟩ (Subgroup.mem_top _)
    exact hxy (congrArg Subtype.val h1).symm
  obtain ⟨n, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hcne)
  have hnC : (n : ↥L) ∈ commutator ↥L := n.2.1
  have hnZ : (n : ↥L) ∈ Subgroup.center ↥L := n.2.2
  set w : G := ((n : ↥L) : G) with hw
  have hwL : w ∈ L := (n : ↥L).2
  have hw1 : w ≠ 1 := fun e => hn1 (Subtype.ext (Subtype.ext e))
  have hwC : w ∈ ⁅L, L⁆ := by
    have hmap : (commutator ↥L).map L.subtype ≤ ⁅L, L⁆ := by
      have e : (⊤ : Subgroup L).map L.subtype = L := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [commutator_def, Subgroup.map_commutator, e]
    exact hmap ⟨(n : ↥L), hnC, rfl⟩
  have hwZ : ∀ g ∈ L, g * w = w * g := fun g hg => by
    have h := Subgroup.mem_center_iff.mp hnZ ⟨g, hg⟩
    exact congrArg Subtype.val h
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hL) ⟨w, hwL⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hw1 (orderOf_eq_one_iff.mp (by simpa using hk))
  have hord0 : orderOf w ≠ 0 := by rw [hk]; exact pow_ne_zero _ (by norm_num)
  have hdvd3 : 3 ∣ orderOf w := by rw [hk]; exact dvd_pow_self 3 hk0
  have hz₀ord : orderOf (w ^ (orderOf w / 3)) = 3 := orderOf_pow_orderOf_div hord0 hdvd3
  generalize hz₀def : w ^ (orderOf w / 3) = z₀ at hz₀ord
  have hz₀L : z₀ ∈ L := by rw [← hz₀def]; exact L.pow_mem hwL _
  have hz₀C : z₀ ∈ ⁅L, L⁆ := by rw [← hz₀def]; exact Subgroup.pow_mem _ hwC _
  have hz₀Z : ∀ g ∈ L, g * z₀ = z₀ * g := fun g hg => by
    rw [← hz₀def]; exact (Commute.pow_right (hwZ g hg) _).eq
  have hz₀3 : z₀ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one z₀
    rwa [hz₀ord] at h
  have hz₀1 : z₀ ≠ 1 := by
    intro e
    rw [e, orderOf_one] at hz₀ord
    omega
  have hbb : b * b = 1 := by rw [← pow_two]; exact hb2
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hcomm : ∀ y ∈ ⁅L, L⁆, b * y * b⁻¹ ∈ ⁅L, L⁆ := by
    have hle : ⁅L, L⁆ ≤ (⁅L, L⁆).comap (MulAut.conj b).toMonoidHom := by
      refine Subgroup.commutator_le.mpr fun u hu v hv => ?_
      show b * ⁅u, v⁆ * b⁻¹ ∈ ⁅L, L⁆
      have e : b * ⁅u, v⁆ * b⁻¹ = ⁅b * u * b⁻¹, b * v * b⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.commutator_mem_commutator (hbL u hu) (hbL v hv)
    intro y hy
    exact hle hy
  set z₁ : G := b * z₀ * b⁻¹ with hz₁
  have hz₁L : z₁ ∈ L := hbL _ hz₀L
  have hz₁C : z₁ ∈ ⁅L, L⁆ := hcomm _ hz₀C
  have hz₁Z : ∀ g ∈ L, g * z₁ = z₁ * g := by
    intro g hg
    have hgb : b⁻¹ * g * b ∈ L := by
      have h := hbL g hg
      rw [hbinv] at h ⊢
      exact h
    calc g * z₁ = b * ((b⁻¹ * g * b) * z₀) * b⁻¹ := by rw [hz₁]; group
      _ = b * (z₀ * (b⁻¹ * g * b)) * b⁻¹ := by rw [hz₀Z _ hgb]
      _ = z₁ * g := by rw [hz₁]; group
  have hz₁3 : z₁ ^ 3 = 1 := by
    rw [hz₁, conj_pow, hz₀3]; simp
  have hc01 : z₀ * z₁ = z₁ * z₀ := (hz₀Z z₁ hz₁L).symm
  have hbz₁ : b * z₁ * b⁻¹ = z₀ := by
    rw [hz₁]
    calc b * (b * z₀ * b⁻¹) * b⁻¹ = (b * b) * z₀ * (b * b)⁻¹ := by group
      _ = z₀ := by rw [hbb]; simp
  by_cases hp : z₀ * z₁ = 1
  · have hm : z₀ * z₁⁻¹ ≠ 1 := by
      intro hm
      have key : (z₀ * z₁) * (z₀ * z₁⁻¹) = z₀ * z₀ := by
        calc (z₀ * z₁) * (z₀ * z₁⁻¹) = z₀ * (z₁ * z₀) * z₁⁻¹ := by group
          _ = z₀ * (z₀ * z₁) * z₁⁻¹ := by rw [hc01]
          _ = z₀ * z₀ := by group
      have hsq : z₀ * z₀ = 1 := by rw [← key, hp, hm, one_mul]
      apply hz₀1
      calc z₀ = (z₀ * z₀) * z₀ := by rw [hsq, one_mul]
        _ = z₀ ^ 3 := (pow_three' z₀).symm
        _ = 1 := hz₀3
    have hc : Commute z₀ z₁ := hc01
    refine ⟨z₀ * z₁⁻¹, L.mul_mem hz₀L (L.inv_mem hz₁L), Subgroup.mul_mem _ hz₀C
      (Subgroup.inv_mem _ hz₁C), hm, ?_, ?_, Or.inr ?_⟩
    · rw [hc.inv_right.mul_pow, hz₀3, inv_pow, hz₁3]; simp
    · intro g hg
      have hcg : Commute g z₁ := hz₁Z g hg
      exact (Commute.mul_right (hz₀Z g hg) hcg.inv_right).eq
    · calc b * (z₀ * z₁⁻¹) * b⁻¹ = (b * z₀ * b⁻¹) * (b * z₁ * b⁻¹)⁻¹ := by group
        _ = (z₀ * z₁⁻¹)⁻¹ := by rw [hbz₁, ← hz₁]; group
  · have hc : Commute z₀ z₁ := hc01
    refine ⟨z₀ * z₁, L.mul_mem hz₀L hz₁L, Subgroup.mul_mem _ hz₀C hz₁C, hp, ?_, ?_, Or.inl ?_⟩
    · rw [hc.mul_pow, hz₀3, hz₁3]; simp
    · intro g hg
      exact (Commute.mul_right (hz₀Z g hg) (hz₁Z g hg)).eq
    · calc b * (z₀ * z₁) * b⁻¹ = (b * z₀ * b⁻¹) * (b * z₁ * b⁻¹) := by group
        _ = z₀ * z₁ := by rw [hbz₁, ← hz₁, hc01]

theorem inv_of_involution_of_cyclic {Y : Subgroup G} [IsCyclic Y] (hY : IsPGroup 3 Y) {σ : G}
    (hσ2 : σ ^ 2 = 1) (hσY : ∀ y ∈ Y, σ * y * σ⁻¹ ∈ Y)
    (hnt : ∃ y ∈ Y, σ * y ≠ y * σ) :
    ∀ y ∈ Y, σ * y * σ⁻¹ = y⁻¹ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Y)
  have hpow : ∀ y ∈ Y, ∃ k : ℤ, (g : G) ^ k = y := by
    intro y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨r, hr⟩ := hpow _ (hσY _ g.2)
  have hσσ : σ * σ = 1 := by rw [← pow_two]; exact hσ2
  have hgg : σ * (σ * (g : G) * σ⁻¹) * σ⁻¹ = g := by
    calc σ * (σ * (g : G) * σ⁻¹) * σ⁻¹ = (σ * σ) * g * (σ * σ)⁻¹ := by group
      _ = g := by rw [hσσ]; simp
  have h1 : σ * (g : G) ^ r * σ⁻¹ = (g : G) ^ (r * r) := by
    rw [← conj_zpow, ← hr, ← zpow_mul]
  have hrr : (g : G) ^ (r * r - 1) = 1 := by
    have h2 : (g : G) = (g : G) ^ (r * r) := by
      rw [← hr] at hgg
      exact hgg.symm.trans h1
    rw [zpow_sub_one, ← h2]; simp
  obtain ⟨n, hn⟩ := hY g
  have hn' : (g : G) ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hn')
  have hdvd : (3 : ℤ) ^ m ∣ (r - 1) * (r + 1) := by
    have h3 := (orderOf_dvd_iff_zpow_eq_one (x := (g : G)) (i := r * r - 1)).mpr hrr
    rw [hm] at h3
    have e : r * r - 1 = (r - 1) * (r + 1) := by ring
    rw [e] at h3
    exact_mod_cast h3
  have hconjpow : ∀ k : ℤ, σ * (g : G) ^ k * σ⁻¹ = (σ * (g : G) * σ⁻¹) ^ k :=
    fun k => conj_zpow.symm
  by_cases h3 : (3 : ℤ) ∣ r - 1
  ·
    exfalso
    have h4 : ¬ (3 : ℤ) ∣ r + 1 := by omega
    have h5 : (3 : ℤ) ^ m ∣ r - 1 := Prime.pow_dvd_of_dvd_mul_right Int.prime_three m h4 hdvd
    have h6 : (g : G) ^ (r - 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hm]; exact_mod_cast h5
    have h7 : (g : G) ^ r = g := by
      rw [zpow_sub_one] at h6; exact mul_inv_eq_one.mp h6
    have h8 : σ * (g : G) * σ⁻¹ = g := by rw [← hr, h7]
    obtain ⟨y, hy, hσy⟩ := hnt
    obtain ⟨k, rfl⟩ := hpow y hy
    apply hσy
    have h9 : σ * (g : G) ^ k * σ⁻¹ = (g : G) ^ k := by rw [hconjpow, h8]
    calc σ * (g : G) ^ k = (σ * (g : G) ^ k * σ⁻¹) * σ := by group
      _ = (g : G) ^ k * σ := by rw [h9]
  ·
    have h5 : (3 : ℤ) ^ m ∣ r + 1 := Prime.pow_dvd_of_dvd_mul_left Int.prime_three m h3 hdvd
    have h6 : (g : G) ^ (r + 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hm]; exact_mod_cast h5
    have h7 : (g : G) ^ r = (g : G)⁻¹ := by
      rw [zpow_add_one] at h6; exact eq_inv_of_mul_eq_one_left h6
    have h8 : σ * (g : G) * σ⁻¹ = (g : G)⁻¹ := by rw [← hr, h7]
    intro y hy
    obtain ⟨k, rfl⟩ := hpow y hy
    rw [hconjpow, h8, inv_zpow]

end LRed12

end CFSG.Quasithin
