module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Families
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups

public section

namespace CFSG.Quasithin.H13.Rank8

open CFSG.Open CFSG.SectionRank CFSG.Assembly.LowTwoRank Matrix Polynomial

theorem pow_eq_pow_mod_three {G : Type*} [Monoid G] {x : G} (hx : x ^ 3 = 1) (n : ℕ) :
    x ^ n = x ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one]

theorem two_le_pRank_three_of {G : Type*} [Group G] [Finite G] {x y : G} (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) (h0 : y ≠ 1) (h1 : x ≠ y)
    (h2 : x ^ 2 ≠ y) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.QuasithinUnique.Vol2Native.two_le_pRank_of_gens hx hy hxy hx1 fun n hn => ?_
  rw [pow_eq_pow_mod_three hx] at hn
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h <;> rw [h] at hn
  · exact h0 (by rw [← hn, pow_zero])
  · exact h1 (by rw [← hn, pow_one])
  · exact h2 hn

@[expose] def r4a : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], by decide⟩

@[expose] def r4b : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1], by decide⟩

theorem two_le_pRank_sl_four :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2))) :=
  two_le_pRank_three_of (x := r4a) (y := r4b) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

@[expose] def r5a : SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨!![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1], by
    decide +kernel⟩

@[expose] def r5b : SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1], by
    decide +kernel⟩

theorem two_le_pRank_sl_five :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (SpecialLinearGroup (Fin 5) (ZMod 2))) :=
  two_le_pRank_three_of (x := r5a) (y := r5b) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

@[expose] def c012 (n : ℕ) (hn : 6 ≤ n) : alternatingGroup (Fin n) :=
  ⟨List.formPerm [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩],
    Equiv.Perm.mem_alternatingGroup.mpr (by
      rw [List.formPerm_cons_cons, List.formPerm_pair]
      simp [Fin.ext_iff])⟩

@[expose] def c345 (n : ℕ) (hn : 6 ≤ n) : alternatingGroup (Fin n) :=
  ⟨List.formPerm [⟨3, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩],
    Equiv.Perm.mem_alternatingGroup.mpr (by
      rw [List.formPerm_cons_cons, List.formPerm_pair]
      simp [Fin.ext_iff])⟩

theorem two_le_pRank_alternating_six :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 6))) :=
  two_le_pRank_three_of (x := c012 6 le_rfl) (y := c345 6 le_rfl) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem two_le_pRank_alternating_seven :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 7))) :=
  two_le_pRank_three_of (x := c012 7 (by norm_num)) (y := c345 7 (by norm_num))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem two_le_pRank_alternating_eight :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 8))) :=
  two_le_pRank_three_of (x := c012 8 (by norm_num)) (y := c345 8 (by norm_num))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem cube_mul_of_central {G : Type*} [Group G] {x y c : G} (hc : ∀ g, c * g = g * c)
    (hyx : y * x = x * y * c) (h3 : c ^ 3 = 1) : (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  have hyx' : ∀ r, y * (x * r) = x * (y * (c * r)) := fun r => by
    rw [← mul_assoc, hyx, mul_assoc, mul_assoc]
  have hpush : ∀ g r, c * (g * r) = g * (c * r) := fun g r => by
    rw [← mul_assoc, hc g, mul_assoc]
  have hlast : c * y = y * c := hc y
  have hcc : c * (c * c) = 1 := by rw [← h3, pow_succ, pow_two, mul_assoc]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc, hyx', hpush, hlast, hcc, mul_one]

theorem two_le_pRank_of_central_three {Q A : Type*} [Group Q] [Finite Q] [Group A]
    (π : Q →* A) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center Q)
    (hZ : Nat.card (Subgroup.center Q) = 3) {t₁ t₂ : A} (h₁ : t₁ ^ 3 = 1) (h₂ : t₂ ^ 3 = 1)
    (hc' : t₁ * t₂ = t₂ * t₁)
    (hind : ∀ a b : ℕ, a < 3 → b < 3 → t₁ ^ a * t₂ ^ b = 1 → a = 0 ∧ b = 0) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Q) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Commute t₁ t₂ := hc'
  set Z := Subgroup.center Q with hZdef
  have hmemZ : ∀ g : Q, g ∈ Z ↔ π g = 1 := fun g => by rw [← MonoidHom.mem_ker, hker]
  have hZ1 : Z ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hZ; omega
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ1
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hz3 : z ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := Z) (x := ⟨z, hzZ⟩)
    rw [hZ] at h
    exact congrArg Subtype.val h
  have hzc : ∀ g : Q, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hzZ g).symm
  have hzpow : ∀ w ∈ Z, ∃ i : ℕ, i < 3 ∧ w = z ^ i := by
    intro w hw
    have hZz : Subgroup.zpowers z ≤ Z := Subgroup.zpowers_le.mpr hzZ
    have hcz : Nat.card (Subgroup.zpowers z) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1']
    have heq : Subgroup.zpowers z = Z :=
      Subgroup.eq_of_le_of_card_ge hZz (by rw [hcz, hZ])
    rw [← heq] at hw
    obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff.mp hw)
    have hoz : orderOf z = 3 := orderOf_eq_prime hz3 hz1'
    have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    refine ⟨(k % 3).toNat, by omega, ?_⟩
    rw [← hk, ← zpow_natCast, Int.toNat_of_nonneg h0, ← zpow_mod_orderOf, hoz]
    rfl
  obtain ⟨u₁, hu₁⟩ := hπ t₁
  obtain ⟨u₂, hu₂⟩ := hπ t₂
  have hu₁Z : u₁ ^ 3 ∈ Z := (hmemZ _).mpr (by rw [map_pow, hu₁, h₁])
  have hu₂Z : u₂ ^ 3 ∈ Z := (hmemZ _).mpr (by rw [map_pow, hu₂, h₂])
  obtain ⟨i, hi, hi'⟩ := hzpow _ hu₁Z
  obtain ⟨j, hj, hj'⟩ := hzpow _ hu₂Z
  have hcube : ∀ a b : ℕ, (u₁ ^ a * u₂ ^ b) ^ 3 = z ^ (i * a + j * b) := by
    intro a b
    set c := (u₁ ^ a * u₂ ^ b)⁻¹ * (u₂ ^ b * u₁ ^ a) with hcdef
    have hcZ : c ∈ Z := (hmemZ _).mpr (by
      rw [hcdef, map_mul, map_inv, map_mul, map_mul, map_pow, map_pow, hu₁, hu₂,
        ((hc.pow_left a).pow_right b).eq, inv_mul_cancel])
    have hc3 : c ^ 3 = 1 := by
      obtain ⟨k, -, hk⟩ := hzpow c hcZ
      rw [hk, ← pow_mul, mul_comm, pow_mul, hz3, one_pow]
    have hyx : u₂ ^ b * u₁ ^ a = u₁ ^ a * u₂ ^ b * c := by rw [hcdef]; group
    rw [cube_mul_of_central (fun g => (Subgroup.mem_center_iff.mp hcZ g).symm) hyx hc3,
      ← pow_mul, ← pow_mul, mul_comm a 3, mul_comm b 3, pow_mul, pow_mul, hi', hj', ← pow_mul,
      ← pow_mul, pow_add]
  obtain ⟨a, b, ha, hb, hab, hy3⟩ : ∃ a b : ℕ, a < 3 ∧ b < 3 ∧ ¬ (a = 0 ∧ b = 0) ∧
      (u₁ ^ a * u₂ ^ b) ^ 3 = 1 := by
    by_cases hi0 : i = 0
    · exact ⟨1, 0, by norm_num, by norm_num, by omega, by rw [hcube, hi0]; simp⟩
    · by_cases hj0 : j = 0
      · exact ⟨0, 1, by norm_num, by norm_num, by omega, by rw [hcube, hj0]; simp⟩
      · refine ⟨j, 3 - i, hj, by omega, by omega, ?_⟩
        rw [hcube, show i * j + j * (3 - i) = 3 * j by
          rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl <;> ring,
          pow_mul, hz3, one_pow]
  set y := u₁ ^ a * u₂ ^ b with hydef
  have hyZ : y ∉ Z := by
    rw [hmemZ, hydef, map_mul, map_pow, map_pow, hu₁, hu₂]
    exact fun h => hab (hind a b ha hb h)
  refine two_le_pRank_three_of hz3 hy3 (hzc y) hz1'
    (fun h => hyZ (h ▸ Z.one_mem)) (fun h => hyZ (h ▸ hzZ))
    (fun h => hyZ (h ▸ Z.pow_mem hzZ 2))

theorem two_le_pRank_of_isHatAlt {Q : Type*} [Group Q] [Finite Q] {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hZ : Nat.card (Subgroup.center Q) = 3)
    (e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin n)) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Q) := by
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))).ker =
      Subgroup.center Q := by
    ext g
    simp
  have hsurj : Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  rcases hn with rfl | rfl
  · refine two_le_pRank_of_central_three _ hsurj hker hZ (t₁ := c012 6 le_rfl)
      (t₂ := c345 6 le_rfl) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
    intro a b ha hb h
    interval_cases a <;> interval_cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by
      decide +kernel)
  · refine two_le_pRank_of_central_three _ hsurj hker hZ (t₁ := c012 7 (by norm_num))
      (t₂ := c345 7 (by norm_num)) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
    intro a b ha hb h
    interval_cases a <;> interval_cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by
      decide +kernel)

theorem pow_three_eq_one_of_charP {F : Type*} [Field F] [CharP F 3]
    {M : Matrix (Fin 3) (Fin 3) F} {k : ℕ} (h : M ^ (3 ^ k) = 1) : M ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Commute M 1 := Commute.one_right M
  have hN : IsNilpotent (M - 1) := ⟨3 ^ k, by
    rw [sub_pow_char_pow_of_commute (p := 3) (n := k) hc, h, one_pow, sub_self]⟩
  have hpoly : (M - 1).charpoly = X ^ 3 := by
    have h1 := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN
    rw [Fintype.card_fin] at h1
    exact sub_eq_zero.mp (IsReduced.eq_zero _ h1)
  have h3 : (M - 1) ^ 3 = 0 := by
    have := Matrix.aeval_self_charpoly (M - 1)
    rw [hpoly, map_pow, aeval_X] at this
    exact this
  have h4 := sub_pow_char_of_commute (p := 3) hc
  rw [h3, one_pow] at h4
  exact sub_eq_zero.mp h4.symm

theorem two_le_pRank_su_three_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 9) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSU 3 3 F)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF' : Nat.card F = (3 ^ 1) ^ 2 := by rw [hF]; norm_num
  have : CharP F 3 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 3) (f := 1) hF'
  have hcard := CFSG.LinearGroups.UnitaryThreeOverNine.card_statedSU hF
  have hexp : ∀ g : ↥(StatedSU 3 3 F), (∃ k : ℕ, g ^ (3 ^ k) = 1) → g ^ 3 = 1 := by
    rintro g ⟨k, hk⟩
    have hk' : (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ^ (3 ^ k) = 1 := by
      have := congrArg
        (fun h : ↥(StatedSU 3 3 F) => ((h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hk
      simpa using this
    apply Subtype.ext
    apply Units.ext
    simpa using pow_three_eq_one_of_charP hk'
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥(StatedSU 3 3 F)) := inferInstance
  have hP : Nat.card P = 27 := by
    rw [Sylow.card_eq_multiplicity, hcard]
    rw [show (6048 : ℕ) = 3 ^ 3 * 224 by norm_num, Nat.factorization_mul (by norm_num)
      (by norm_num), Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three]
    simp [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 224)]
  have hP2 : IsPGroup 3 P := P.isPGroup'
  have hPnt : Nontrivial (Subgroup.center P) := by
    have : Nontrivial P := by
      rw [← Finite.one_lt_card_iff_nontrivial, hP]
      norm_num
    exact hP2.center_nontrivial
  obtain ⟨⟨z, hzc⟩, hz1⟩ := exists_ne (1 : Subgroup.center P)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hz3 : (z : ↥(StatedSU 3 3 F)) ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := hP2 z
    exact hexp z ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hzP : Nat.card (Subgroup.zpowers z) ≤ 3 := by
    rw [Nat.card_zpowers]
    have h3 : (z : P) ^ 3 = 1 := Subtype.ext hz3
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h3)
  obtain ⟨y, hy⟩ : ∃ y : P, y ∉ Subgroup.zpowers z := by
    by_contra hall
    push Not at hall
    have : (⊤ : Subgroup P) ≤ Subgroup.zpowers z := fun y _ => hall y
    have h1 := Subgroup.card_le_of_le this
    rw [Subgroup.card_top, hP] at h1
    omega
  have hy3 : (y : ↥(StatedSU 3 3 F)) ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := hP2 y
    exact hexp y ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hcomm : Commute (z : ↥(StatedSU 3 3 F)) (y : ↥(StatedSU 3 3 F)) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc y).symm
  have hzy : ∀ m : ℕ, (z : P) ^ m ≠ y := fun m h => hy (h ▸ Subgroup.npow_mem_zpowers z m)
  refine two_le_pRank_three_of hz3 hy3 hcomm (fun h => hz1' (Subtype.ext h)) ?_ ?_ ?_
  · intro h
    apply hzy 0
    rw [pow_zero]
    exact Subtype.ext h.symm
  · intro h
    apply hzy 1
    rw [pow_one]
    exact Subtype.ext h
  · intro h
    apply hzy 2
    exact Subtype.ext (by simpa using h)

end CFSG.Quasithin.H13.Rank8
