module

public import CFSG.RankThree.PartTwo.Sec21.FF84S23Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21

section Helpers

variable {X : Type} [Group X]

private theorem pow_card3 {Z : Subgroup X} (hZ : Nat.card Z = 3) {x : X} (hx : x ∈ Z) :
    x ^ 3 = 1 := by
  have h : (⟨x, hx⟩ : Z) ^ Nat.card Z = 1 := pow_card_eq_one'
  rw [hZ] at h
  exact congrArg Subtype.val h

private theorem zpow_eq_one_of_dvd {u : X} (hu : u ^ 3 = 1) {k : ℤ} (hk : (3 : ℤ) ∣ k) :
    u ^ k = 1 := by
  obtain ⟨m, rfl⟩ := hk
  have h3 : u ^ (3 : ℤ) = 1 := by simpa using hu
  rw [zpow_mul, h3, one_zpow]

private theorem exists_ne_one_of_card3 [Finite X] {Y : Subgroup X} (hY : Nat.card Y = 3) :
    ∃ y ∈ Y, y ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : Y = ⊥ := (Subgroup.eq_bot_iff_forall Y).mpr hcon
  rw [hbot, Subgroup.card_bot] at hY
  norm_num at hY

private theorem eq_of_mem_card3 [Finite X] {Y Q : Subgroup X} (hY : Nat.card Y = 3)
    (hQ : Nat.card Q = 3) {y : X} (hyY : y ∈ Y) (hyQ : y ∈ Q) (hy1 : y ≠ 1) : Y = Q := by
  have hle : Y ⊓ Q ≤ Y := inf_le_left
  have hdvd : Nat.card ↥(Y ⊓ Q) ∣ 3 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hY] at this
  have hne1 : Nat.card ↥(Y ⊓ Q) ≠ 1 := by
    intro h1
    have hbot := Subgroup.eq_bot_of_card_eq (Y ⊓ Q) h1
    have hyy : y ∈ Y ⊓ Q := ⟨hyY, hyQ⟩
    rw [hbot, Subgroup.mem_bot] at hyy
    exact hy1 hyy
  have h3 : Nat.card ↥(Y ⊓ Q) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hYQ : Y ⊓ Q = Y := Subgroup.eq_of_le_of_card_ge hle (by rw [h3, hY])
  have hYleQ : Y ≤ Q := inf_eq_left.mp hYQ
  exact Subgroup.eq_of_le_of_card_ge hYleQ (by rw [hY, hQ])

theorem mem_conjBy_iff (g : X) (H : Subgroup X) (x : X) :
    x ∈ conjBy g H ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · intro hx
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hx
    have e : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    show g⁻¹ * (g * h * g⁻¹) * g ∈ H
    rw [e]
    exact hh
  · intro hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hx, ?_⟩
    show g * (g⁻¹ * x * g) * g⁻¹ = x
    group

theorem conjBy_one (H : Subgroup X) : conjBy 1 H = H := by
  ext x
  rw [mem_conjBy_iff]
  simp

theorem conjBy_conjBy (g h : X) (H : Subgroup X) :
    conjBy g (conjBy h H) = conjBy (g * h) H := by
  ext x
  rw [mem_conjBy_iff, mem_conjBy_iff, mem_conjBy_iff]
  have e : h⁻¹ * (g⁻¹ * x * g) * h = (g * h)⁻¹ * x * (g * h) := by group
  rw [e]

theorem card_conjBy (g : X) (H : Subgroup X) : Nat.card (conjBy g H) = Nat.card H :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective

theorem conjBy_zpowers (g u : X) :
    conjBy g (Subgroup.zpowers u) = Subgroup.zpowers (g * u * g⁻¹) :=
  MonoidHom.map_zpowers (MulAut.conj g).toMonoidHom u

instance normAct (M : Subgroup X) : MulAction M (Subgroup X) where
  smul m Z := conjBy (m : X) Z
  one_smul Z := by
    show conjBy ((1 : M) : X) Z = Z
    rw [Subgroup.coe_one, conjBy_one]
  mul_smul m n Z := by
    show conjBy ((m * n : M) : X) Z = conjBy (m : X) (conjBy (n : X) Z)
    rw [Subgroup.coe_mul, conjBy_conjBy]

theorem mem_orbit_norm_iff (M : Subgroup X) (Z W : Subgroup X) :
    W ∈ MulAction.orbit M Z ↔ ∃ m ∈ M, conjBy m Z = W := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, m.2, hm⟩
  · rintro ⟨m, hm, hW⟩
    exact ⟨⟨m, hm⟩, hW⟩

theorem orbit_coprime [Finite X] (P Z : Subgroup X)
    (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hcop : Nat.Coprime 3 (P.relIndex ⊤)) (hZ : Z ≤ P) :
    Nat.Coprime 3 (MulAction.orbit (Nor P) Z).ncard := by
  have hPN : P ≤ Nor P := Subgroup.le_normalizer
  have hstab : P.subgroupOf (Nor P) ≤ MulAction.stabilizer (Nor P) Z := by
    intro m hm
    rw [Subgroup.mem_subgroupOf] at hm
    rw [MulAction.mem_stabilizer_iff]
    show conjBy (m : X) Z = Z
    have hle : conjBy (m : X) Z ≤ Z := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
      have hc : (m : X) * z = z * m := hPc _ hm _ (hZ hz)
      show (m : X) * z * (m : X)⁻¹ ∈ Z
      rw [hc, mul_inv_cancel_right]
      exact hz
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjBy])
  have h1 := Subgroup.index_dvd_of_le hstab
  have h3 : P.relIndex (Nor P) ∣ P.relIndex ⊤ :=
    ⟨(Nor P).relIndex ⊤, (Subgroup.relIndex_mul_relIndex P (Nor P) ⊤ hPN le_top).symm⟩
  have h4 : (MulAction.stabilizer (Nor P) Z).index ∣ P.relIndex ⊤ := h1.trans h3
  rw [← MulAction.index_stabilizer (Nor P) Z]
  exact Nat.Coprime.coprime_dvd_right h4 hcop

theorem fusion [Finite X] (P : Subgroup X) (hP : IsSylowOf 3 P ⊤)
    (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {x y : X} (hx : x ∈ P) (hy : y ∈ P) {g : X}
    (hg : g * x * g⁻¹ = y) : ∃ n ∈ Nor P, n * x * n⁻¹ = y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop' : ¬ 3 ∣ P.index := by
    rw [← Subgroup.relIndex_top_right]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hP.2.2
  obtain ⟨S, rfl⟩ : ∃ S : Sylow 3 X, (S : Subgroup X) = P :=
    ⟨hP.2.1.toSylow hcop', IsPGroup.toSylow_coe hP.2.1 hcop'⟩
  haveI hcomm' : IsMulCommutative (S : Subgroup X) :=
    ⟨⟨fun a b => Subtype.ext (hPc a.1 a.2 b.1 b.2)⟩⟩
  obtain ⟨n, hn, hn'⟩ := S.conj_eq_normalizer_conj_of_mem x g⁻¹ hx
    (by rw [inv_inv, hg]; exact hy)
  refine ⟨n⁻¹, inv_mem hn, ?_⟩
  rw [inv_inv]
  rw [inv_inv, hg] at hn'
  exact hn'.symm

theorem core_closure [Finite X] (P Z W : Subgroup X) (z w t : X)
    (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hcop : Nat.Coprime 3 (P.relIndex ⊤))
    (hZP : Z ≤ P) (hWP : W ≤ P) (hZ3 : Nat.card Z = 3) (hW3 : Nat.card W = 3)
    (hZW : Z ⊓ W = ⊥) (hnot : ∀ g : X, conjBy g Z ≠ W)
    (hz : z ∈ Z) (hz1 : z ≠ 1) (hw : w ∈ W) (hw1 : w ≠ 1)
    (hdec : ∀ p ∈ P, ∃ i j : ℤ, p = z ^ i * w ^ j)
    (ht : (t * z * t⁻¹ = z⁻¹ ∧ t * w * t⁻¹ = w) ∨ (t * z * t⁻¹ = z ∧ t * w * t⁻¹ = w⁻¹)) :
    ∀ n ∈ Nor P, conjBy n Z = Z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzP : z ∈ P := hZP hz
  have hwP : w ∈ P := hWP hw
  have hc : Commute z w := hPc z hzP w hwP
  have hcinv : Commute z w⁻¹ := hc.inv_right
  have hz3 : z ^ 3 = 1 := pow_card3 hZ3 hz
  have hw3 : w ^ 3 = 1 := pow_card3 hW3 hw
  have hwZbot : ∀ u : X, u ∈ Z → u ∈ W → u = 1 := by
    intro u h1 h2
    have h : u ∈ Z ⊓ W := ⟨h1, h2⟩
    rw [hZW, Subgroup.mem_bot] at h
    exact h
  have hzw1 : z * w ≠ 1 := by
    intro h
    have hw' : w = z⁻¹ := eq_inv_of_mul_eq_one_right h
    exact hw1 (hwZbot w (by rw [hw']; exact inv_mem hz) hw)
  have hzw'1 : z * w⁻¹ ≠ 1 := by
    intro h
    have hw' : w⁻¹ = z⁻¹ := eq_inv_of_mul_eq_one_right h
    have hwinv : w⁻¹ = 1 := hwZbot w⁻¹ (by rw [hw']; exact inv_mem hz) (inv_mem hw)
    exact hw1 (inv_eq_one.mp hwinv)
  obtain ⟨D, hD⟩ : ∃ D : Subgroup X, D = Subgroup.zpowers (z * w) := ⟨_, rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D' : Subgroup X, D' = Subgroup.zpowers (z * w⁻¹) := ⟨_, rfl⟩
  have hDc : Nat.card D = 3 := by
    rw [hD, Nat.card_zpowers]
    refine orderOf_eq_prime ?_ hzw1
    rw [hc.mul_pow, hz3, hw3, one_mul]
  have hD'c : Nat.card D' = 3 := by
    rw [hD', Nat.card_zpowers]
    refine orderOf_eq_prime ?_ hzw'1
    rw [hcinv.mul_pow, hz3, one_mul, inv_pow, hw3, inv_one]
  have hzD : z * w ∈ D := by rw [hD]; exact Subgroup.mem_zpowers _
  have hzD' : z * w⁻¹ ∈ D' := by rw [hD']; exact Subgroup.mem_zpowers _
  have hclass : ∀ Y : Subgroup X, Y ≤ P → Nat.card Y = 3 → Y = Z ∨ Y = W ∨ Y = D ∨ Y = D' := by
    intro Y hYP hY3
    obtain ⟨y, hy, hy1⟩ := exists_ne_one_of_card3 hY3
    obtain ⟨i, j, rfl⟩ := hdec y (hYP hy)
    by_cases h1 : (3 : ℤ) ∣ j
    · left
      have hwj : w ^ j = 1 := zpow_eq_one_of_dvd hw3 h1
      refine eq_of_mem_card3 hY3 hZ3 hy ?_ hy1
      rw [hwj, mul_one]
      exact zpow_mem hz i
    by_cases h2 : (3 : ℤ) ∣ i
    · right; left
      have hzi : z ^ i = 1 := zpow_eq_one_of_dvd hz3 h2
      refine eq_of_mem_card3 hY3 hW3 hy ?_ hy1
      rw [hzi, one_mul]
      exact zpow_mem hw j
    by_cases h3 : (3 : ℤ) ∣ (i - j)
    · right; right; left
      have hsplit : w ^ j = w ^ i * w ^ (j - i) := by
        rw [← zpow_add]; congr 1; ring
      have hwj : w ^ j = w ^ i := by
        rw [hsplit, zpow_eq_one_of_dvd hw3 (show (3 : ℤ) ∣ j - i by omega), mul_one]
      refine eq_of_mem_card3 hY3 hDc hy ?_ hy1
      rw [hD, hwj]
      exact Subgroup.mem_zpowers_iff.mpr ⟨i, hc.mul_zpow i⟩
    by_cases h4 : (3 : ℤ) ∣ (i + j)
    · right; right; right
      have hwj : w ^ j = w⁻¹ ^ i := by
        have hsplit : w ^ j = w ^ (-i) * w ^ (i + j) := by
          rw [← zpow_add]; congr 1; ring
        rw [hsplit, zpow_eq_one_of_dvd hw3 h4, mul_one, zpow_neg, inv_zpow]
      refine eq_of_mem_card3 hY3 hD'c hy ?_ hy1
      rw [hD', hwj]
      exact Subgroup.mem_zpowers_iff.mpr ⟨i, hcinv.mul_zpow i⟩
    exfalso
    have hi : i % 3 = 1 ∨ i % 3 = 2 := by omega
    have hj : j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hi with hi | hi <;> rcases hj with hj | hj <;> omega
  have hk : ∀ (u : X) (k : ℤ), t * u ^ k * t⁻¹ = (t * u * t⁻¹) ^ k := fun u k =>
    map_zpow (MulAut.conj t) u k
  have hconjP : ∀ p ∈ P, t * p * t⁻¹ ∈ P := by
    intro p hp
    obtain ⟨i, j, rfl⟩ := hdec p hp
    have e : t * (z ^ i * w ^ j) * t⁻¹ = (t * z * t⁻¹) ^ i * (t * w * t⁻¹) ^ j := by
      calc t * (z ^ i * w ^ j) * t⁻¹ = (t * z ^ i * t⁻¹) * (t * w ^ j * t⁻¹) := by group
        _ = (t * z * t⁻¹) ^ i * (t * w * t⁻¹) ^ j := by rw [hk z i, hk w j]
    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [e, h1, h2]
      exact mul_mem (zpow_mem (inv_mem hzP) i) (zpow_mem hwP j)
    · rw [e, h1, h2]
      exact mul_mem (zpow_mem hzP i) (zpow_mem (inv_mem hwP) j)
  have hconjPle : conjBy t P ≤ P := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
    exact hconjP p hp
  have htP : conjBy t P = P :=
    Subgroup.eq_of_le_of_card_ge hconjPle (card_conjBy t P).symm.le
  have htN : t ∈ Nor P := by
    refine Subgroup.mem_normalizer_iff.mpr (fun h => ⟨fun hh => hconjP h hh, fun hh => ?_⟩)
    have h' : t * h * t⁻¹ ∈ conjBy t P := by rw [htP]; exact hh
    rw [mem_conjBy_iff] at h'
    have e : t⁻¹ * (t * h * t⁻¹) * t = h := by group
    rw [e] at h'
    exact h'
  have hclassN : ∀ n ∈ Nor P, conjBy n Z = Z ∨ conjBy n Z = D ∨ conjBy n Z = D' := by
    intro n hn
    have hZ'P : conjBy n Z ≤ P := by
      intro x hx
      obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hx
      exact (Subgroup.mem_normalizer_iff.mp hn z').mp (hZP hz')
    have hcard : Nat.card (conjBy n Z) = 3 := (card_conjBy n Z).trans hZ3
    rcases hclass _ hZ'P hcard with h | h | h | h
    · exact Or.inl h
    · exact absurd h (hnot n)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have htDD : conjBy t D = D' ∧ conjBy t D' = D := by
    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 : t * (z * w) * t⁻¹ = z⁻¹ * w := by
        rw [show t * (z * w) * t⁻¹ = (t * z * t⁻¹) * (t * w * t⁻¹) by group, h1, h2]
      have e2 : t * (z * w⁻¹) * t⁻¹ = z⁻¹ * w⁻¹ := by
        rw [show t * (z * w⁻¹) * t⁻¹ = (t * z * t⁻¹) * (t * w * t⁻¹)⁻¹ by group, h1, h2]
      constructor
      · rw [hD, hD', conjBy_zpowers, e1, ← @Subgroup.zpowers_inv X _ (z * w⁻¹), mul_inv_rev,
          inv_inv]
        exact congrArg Subgroup.zpowers (Commute.inv_left hc).eq
      · rw [hD', hD, conjBy_zpowers, e2, ← @Subgroup.zpowers_inv X _ (z * w), mul_inv_rev]
        exact congrArg Subgroup.zpowers (Commute.inv_inv hc).eq
    · have e1 : t * (z * w) * t⁻¹ = z * w⁻¹ := by
        rw [show t * (z * w) * t⁻¹ = (t * z * t⁻¹) * (t * w * t⁻¹) by group, h1, h2]
      have e2 : t * (z * w⁻¹) * t⁻¹ = z * w := by
        rw [show t * (z * w⁻¹) * t⁻¹ = (t * z * t⁻¹) * (t * w * t⁻¹)⁻¹ by group, h1, h2, inv_inv]
      constructor
      · rw [hD, hD', conjBy_zpowers, e1]
      · rw [hD', hD, conjBy_zpowers, e2]
  have hZD : Z ≠ D := by
    intro h
    have hzZ : z * w ∈ Z := by rw [h]; exact hzD
    have hwZ : w ∈ Z := by simpa using mul_mem (inv_mem hz) hzZ
    exact hw1 (hwZbot w hwZ hw)
  have hZD' : Z ≠ D' := by
    intro h
    have hzZ : z * w⁻¹ ∈ Z := by rw [h]; exact hzD'
    have hwZ : w⁻¹ ∈ Z := by simpa using mul_mem (inv_mem hz) hzZ
    exact hw1 (inv_eq_one.mp (hwZbot w⁻¹ hwZ (inv_mem hw)))
  have hDD' : D ≠ D' := by
    intro h
    have h1 : z * w⁻¹ ∈ D := by rw [h]; exact hzD'
    have hzz : z * z ∈ D := by
      have e : (z * w) * (z * w⁻¹) = z * z := by
        calc (z * w) * (z * w⁻¹) = z * (w * z) * w⁻¹ := by group
          _ = z * (z * w) * w⁻¹ := by rw [← hc.eq]
          _ = z * z := by group
      rw [← e]
      exact mul_mem hzD h1
    have hzD2 : z ∈ D := by
      have e2 : z = (z * z) * (z * z) := by
        calc z = z * z ^ 3 := by rw [hz3, mul_one]
          _ = (z * z) * (z * z) := by rw [pow_three]; simp only [mul_assoc]
      rw [e2]
      exact mul_mem hzz hzz
    exact hZD (eq_of_mem_card3 hZ3 hDc hz hzD2 hz1)
  intro n0 hn0
  by_contra hne
  have hcase : conjBy n0 Z = D ∨ conjBy n0 Z = D' := by
    rcases hclassN n0 hn0 with h | h | h
    · exact absurd h hne
    · exact Or.inl h
    · exact Or.inr h
  have hZO : Z ∈ MulAction.orbit (Nor P) Z :=
    (mem_orbit_norm_iff _ _ _).mpr ⟨1, one_mem _, conjBy_one Z⟩
  have hDO : D ∈ MulAction.orbit (Nor P) Z ∧ D' ∈ MulAction.orbit (Nor P) Z := by
    rcases hcase with h | h
    · refine ⟨(mem_orbit_norm_iff _ _ _).mpr ⟨n0, hn0, h⟩,
        (mem_orbit_norm_iff _ _ _).mpr ⟨t * n0, mul_mem htN hn0, ?_⟩⟩
      rw [← conjBy_conjBy, h, htDD.1]
    · refine ⟨(mem_orbit_norm_iff _ _ _).mpr ⟨t * n0, mul_mem htN hn0, ?_⟩,
        (mem_orbit_norm_iff _ _ _).mpr ⟨n0, hn0, h⟩⟩
      rw [← conjBy_conjBy, h, htDD.2]
  have hO : MulAction.orbit (Nor P) Z = {Z, D, D'} := by
    apply Set.Subset.antisymm
    · intro W' hW'
      obtain ⟨m, hm, rfl⟩ := (mem_orbit_norm_iff _ _ _).mp hW'
      rcases hclassN m hm with h | h | h <;> simp [h]
    · intro W' hW'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hW'
      rcases hW' with h | h | h
      · rw [h]; exact hZO
      · rw [h]; exact hDO.1
      · rw [h]; exact hDO.2
  have hcard3 : (MulAction.orbit (Nor P) Z).ncard = 3 := by
    rw [hO]
    exact Set.ncard_eq_three.mpr ⟨Z, D, D', hZD, hZD', hDD', rfl⟩
  have hcop3 := orbit_coprime P Z hPc hcop hZP
  rw [hcard3] at hcop3
  exact absurd hcop3 (by norm_num)

theorem lemmaQ_strong_closure {X : Type} [Group X] [Finite X]
    (P A B : Subgroup X) (hP : IsSylowOf 3 P ⊤) (hP9 : Nat.card P = 9)
    (hA : A ≤ P) (hB : B ≤ P) (hA3 : Nat.card A = 3) (hB3 : Nat.card B = 3)
    (hAB : A ⊓ B = ⊥) (hiii : ¬ ∃ g : X, conjBy g A = B)
    (t a : X) (ha : a ∈ A) (ha1 : a ≠ 1) (ht : t * a * t⁻¹ = a⁻¹)
    (htB : ∀ b ∈ B, t * b = b * t) :
    IsStronglyClosedIn P (A : Set X) ∧ IsStronglyClosedIn P (B : Set X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP9' : Nat.card P = 3 ^ 2 := by rw [hP9]; norm_num
  have hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsPGroup.commutative_of_card_eq_prime_sq hP9' ⟨x, hx⟩ ⟨y, hy⟩)
  have hcop : Nat.Coprime 3 (P.relIndex ⊤) := hP.2.2
  obtain ⟨b, hbB, hb1⟩ := exists_ne_one_of_card3 hB3
  have hcomAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := fun x hx y hy => hPc x (hA hx) y (hB hy)
  have hsup : A ⊔ B = P := by
    have hQP : A ⊔ B ≤ P := sup_le hA hB
    have hne3 : Nat.card ↥(A ⊔ B) ≠ 3 := by
      intro h3
      have hAQ : A = A ⊔ B :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq (by rw [h3, hA3]))
      have hBA : B ≤ A := by rw [hAQ]; exact le_sup_right
      have hBA' : B = A := Subgroup.eq_of_le_of_card_ge hBA (le_of_eq (by rw [hA3, hB3]))
      have ha' : a ∈ A ⊓ B := ⟨ha, by rw [hBA']; exact ha⟩
      rw [hAB, Subgroup.mem_bot] at ha'
      exact ha1 ha'
    have hdvd : Nat.card ↥(A ⊔ B) ∣ 9 := by
      have := Subgroup.card_dvd_of_le hQP
      rwa [hP9] at this
    have h3dvd : 3 ∣ Nat.card ↥(A ⊔ B) := by
      have := Subgroup.card_dvd_of_le (le_sup_left : A ≤ A ⊔ B)
      rwa [hA3] at this
    have hcard9 : Nat.card ↥(A ⊔ B) = 9 := by
      generalize Nat.card ↥(A ⊔ B) = c at hdvd h3dvd hne3 ⊢
      have hc9 : c ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases c <;> first | omega | norm_num at hdvd
    exact Subgroup.eq_of_le_of_card_ge hQP (le_of_eq (by rw [hcard9, hP9]))
  have hAa : Subgroup.zpowers a = A :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ha)
      (le_of_eq (by rw [Nat.card_zpowers, orderOf_eq_prime (pow_card3 hA3 ha) ha1, hA3]))
  have hBb : Subgroup.zpowers b = B :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbB)
      (le_of_eq (by rw [Nat.card_zpowers, orderOf_eq_prime (pow_card3 hB3 hbB) hb1, hB3]))
  have hdecAB : ∀ p ∈ P, ∃ i j : ℤ, p = a ^ i * b ^ j := by
    intro p hp
    have hp' : p ∈ A ⊔ B := by rw [hsup]; exact hp
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomAB hp'
    rw [← hAa] at hx
    rw [← hBb] at hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨i, j, rfl⟩
  have hdecBA : ∀ p ∈ P, ∃ i j : ℤ, p = b ^ i * a ^ j := by
    intro p hp
    obtain ⟨i, j, hij⟩ := hdecAB p hp
    refine ⟨j, i, ?_⟩
    rw [hij]
    exact hPc _ (zpow_mem (hA ha) i) _ (zpow_mem (hB hbB) j)
  have htb : t * b * t⁻¹ = b := by rw [htB b hbB, mul_inv_cancel_right]
  have hA_closed : ∀ n ∈ Nor P, conjBy n A = A :=
    core_closure P A B a b t hPc hcop hA hB hA3 hB3 hAB (fun g h => hiii ⟨g, h⟩) ha ha1 hbB hb1
      hdecAB (Or.inl ⟨ht, htb⟩)
  have hBA : B ⊓ A = ⊥ := by rw [inf_comm]; exact hAB
  have hnotBA : ∀ g : X, conjBy g B ≠ A := by
    intro g h
    apply hiii
    refine ⟨g⁻¹, ?_⟩
    rw [← h, conjBy_conjBy, inv_mul_cancel, conjBy_one]
  have hB_closed : ∀ n ∈ Nor P, conjBy n B = B :=
    core_closure P B A b a t hPc hcop hB hA hB3 hA3 hBA hnotBA hbB hb1 ha ha1 hdecBA
      (Or.inr ⟨htb, ht⟩)
  have key : ∀ Z : Subgroup X, Z ≤ P → (∀ n ∈ Nor P, conjBy n Z = Z) →
      ∀ x ∈ Z, ∀ g : X, g⁻¹ * x * g ∈ P → g⁻¹ * x * g ∈ Z := by
    intro Z hZP hZn x hx g hg
    obtain ⟨n, hn, hn'⟩ := fusion P hP hPc (hZP hx) hg (g := g⁻¹) (by rw [inv_inv])
    have hmem : n * x * n⁻¹ ∈ conjBy n Z := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hZn n hn, hn'] at hmem
    exact hmem
  have hsc : ∀ Z : Subgroup X, Z ≤ P → (∀ n ∈ Nor P, conjBy n Z = Z) →
      IsStronglyClosedIn P (Z : Set X) := by
    intro Z hZP hZn
    unfold IsStronglyClosedIn
    exact ⟨fun x hx => hZP hx, fun x hx g hg => key Z hZP hZn x hx g hg⟩
  exact ⟨hsc A hA hA_closed, hsc B hB hB_closed⟩

end Helpers

end CFSG.RankThree.PartTwo.Sec21.FF84
