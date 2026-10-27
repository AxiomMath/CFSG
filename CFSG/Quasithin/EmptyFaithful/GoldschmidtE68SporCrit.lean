module

public import CFSG.CharacterTheory.Burnside
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingLocalComponents

public section

namespace CFSG.Quasithin.E6.Spor

open Subgroup CFSG.Open

theorem isSolvable_of_card_two_pow_mul_three_pow {C : Type*} [Group C] [Finite C] {a b : ℕ}
    (h : Nat.card C = 2 ^ a * 3 ^ b) : Group.IsSolvable C := by
  have := Fintype.ofFinite C
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem not_isQuasisimple_of_isSolvable {B : Type*} [Group B] [Group.IsSolvable B] :
    ¬ CFSG.IsQuasisimple B := by
  rintro ⟨hperf, -, a, b, hab⟩
  have hnt : Nontrivial B := by
    obtain ⟨a₀, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b₀, rfl⟩ := QuotientGroup.mk_surjective b
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hab (by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subsingleton.elim (a₀ * b₀) (b₀ * a₀)])
  have : Group.IsPerfect B := hperf
  exact Group.IsPerfect.not_isSolvable B inferInstance

theorem noComponent_of_card_two_pow_mul_three_pow {C : Type*} [Group C] [Finite C] {a b : ℕ}
    (h : Nat.card C = 2 ^ a * 3 ^ b) (B : Subgroup C) : ¬ CFSG.IsComponent B := by
  rintro ⟨hq, -⟩
  have := isSolvable_of_card_two_pow_mul_three_pow h
  have : Group.IsSolvable ↥B := Group.isSolvable_of_isSolvable_injective B.subtype_injective
  exact not_isQuasisimple_of_isSolvable hq

theorem noComponent_of_card_le {C : Type*} [Group C] [Finite C] {k N : ℕ} (hN : Odd N)
    (hdvd : Nat.card C ∣ 2 ^ k * N) (hS : 2 ^ k ∣ Nat.card C) (hle : Nat.card C ≤ 3 * 2 ^ k)
    (B : Subgroup C) : ¬ CFSG.IsComponent B := by
  obtain ⟨m, hm⟩ := hS
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hmN : m ∣ N := by
    rw [hm] at hdvd
    exact (Nat.mul_dvd_mul_iff_left hpos).mp hdvd
  have hmodd : Odd m := hN.of_dvd_nat hmN
  have hm3 : m ≤ 3 := by
    rw [hm] at hle
    nlinarith
  have hm1 : 1 ≤ m := by
    obtain ⟨j, hj⟩ := hmodd
    omega
  have hcases : m = 1 ∨ m = 3 := by
    obtain ⟨j, hj⟩ := hmodd
    omega
  rcases hcases with rfl | rfl
  · exact noComponent_of_card_two_pow_mul_three_pow (a := k) (b := 0) (by rw [hm]; ring) B
  · exact noComponent_of_card_two_pow_mul_three_pow (a := k) (b := 1) (by rw [hm]; ring) B

theorem noComponent_of_rElement {C : Type*} [Group C] [Finite C] {k r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hcard : Nat.card C = 2 ^ k * 3 * r) {y n : C}
    (hy : orderOf y = r) (hn : n ∈ CFSG.Open.pCore 2 C) (hyn : y * n ≠ n * y) (B : Subgroup C) :
    ¬ CFSG.IsComponent B := by
  intro hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact r.Prime := ⟨hr⟩
  have hNn : (CFSG.Open.pCore 2 C).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hNp : IsPGroup 2 (CFSG.Open.pCore 2 C) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hBX : B ≤ centralizer (CFSG.Open.pCore 2 C : Set C) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponent_le_centralizer_of_isPGroup hB hNn hNp
  have hXn : ∀ c x : C, x ∈ centralizer (CFSG.Open.pCore 2 C : Set C) →
      c * x * c⁻¹ ∈ centralizer (CFSG.Open.pCore 2 C : Set C) := by
    intro c x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro m hm
    have hm' : c⁻¹ * m * c ∈ CFSG.Open.pCore 2 C := by simpa using hNn.conj_mem m hm c⁻¹
    have h1 := hx _ hm'
    calc m * (c * x * c⁻¹) = c * ((c⁻¹ * m * c) * x) * c⁻¹ := by group
      _ = c * (x * (c⁻¹ * m * c)) * c⁻¹ := by rw [h1]
      _ = (c * x * c⁻¹) * m := by group
  have hrB : r ∣ Nat.card B := by
    by_contra hnd
    have hdvd : Nat.card B ∣ 2 ^ k * 3 * r := hcard ▸ Subgroup.card_subgroup_dvd_card B
    have hcop : Nat.Coprime (Nat.card B) r :=
      ((Nat.Prime.coprime_iff_not_dvd hr).2 hnd).symm
    have hd2 : Nat.card B ∣ 2 ^ k * 3 := hcop.dvd_of_dvd_mul_right hdvd
    obtain ⟨d₁, d₂, h₁, h₂, h12⟩ := Nat.dvd_mul.mp hd2
    obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h₁
    obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (by simpa using h₂ : d₂ ∣ 3 ^ 1)
    have hsolv : Group.IsSolvable ↥B :=
      isSolvable_of_card_two_pow_mul_three_pow (a := a) (b := b) h12.symm
    exact not_isQuasisimple_of_isSolvable hB.1
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) r hrB
  have hg' : orderOf (g : C) = r := (Subgroup.orderOf_coe g).trans hg
  have hg'X : (g : C) ∈ centralizer (CFSG.Open.pCore 2 C : Set C) := hBX g.2
  have hind : ∀ x : C, orderOf x = r → ¬ r ∣ (Subgroup.zpowers x).index := by
    intro x hx hdvd
    have h1 := Subgroup.card_mul_index (Subgroup.zpowers x)
    rw [Nat.card_zpowers, hx, hcard] at h1
    have h2 : (Subgroup.zpowers x).index = 2 ^ k * 3 :=
      Nat.eq_of_mul_eq_mul_left hr.pos (by rw [h1]; ring)
    rw [h2] at hdvd
    rcases (Nat.Prime.dvd_mul hr).1 hdvd with h | h
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
    · exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h)
  have hpg : ∀ x : C, orderOf x = r → IsPGroup r (Subgroup.zpowers x) := fun x hx =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; simp)
  let P : Sylow r C := (hpg y hy).toSylow (hind y hy)
  let Q : Sylow r C := (hpg (g : C) hg').toSylow (hind (g : C) hg')
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C P Q
  have hc' : (Subgroup.zpowers y).map (MulAut.conj c).toMonoidHom = Subgroup.zpowers (g : C) := by
    have h := congrArg (fun T : Sylow r C => (T : Subgroup C)) hc
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    exact h
  have hyc : c * y * c⁻¹ ∈ Subgroup.zpowers (g : C) :=
    hc' ▸ ⟨y, Subgroup.mem_zpowers y, rfl⟩
  have hyc' : c * y * c⁻¹ ∈ centralizer (CFSG.Open.pCore 2 C : Set C) :=
    (Subgroup.zpowers_le.mpr hg'X) hyc
  have hyX : y ∈ centralizer (CFSG.Open.pCore 2 C : Set C) := by
    have := hXn c⁻¹ _ hyc'
    simpa [mul_assoc] using this
  exact hyn (Subgroup.mem_centralizer_iff.mp hyX n hn).symm

end CFSG.Quasithin.E6.Spor
