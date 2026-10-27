module

public import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.GroupTheory.SteinbergBYQD32Extraspecial

public section

namespace CFSG.RankThree.PartOne.QD32Facts

open CFSG CFSG.RankThree.PartOne.Torsion37 CFSG.RankThree.GroupTheory.SteinbergBY Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem eq_one_of_sq_eq_one {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {c : G} (h2 : c ^ 2 = 1)
    (hc : c ^ q = 1) : c = 1 := by
  have hdvd : orderOf c ∣ Nat.gcd 2 q :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hc)
  have hcop : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)
  rw [hcop.gcd_eq_one] at hdvd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

theorem exists_odd {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : ∃ k : ℕ, q = 2 * k + 1 := by
  rcases hq.eq_two_or_odd' with h | h
  · exact absurd h hq2
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, hk⟩

theorem eq_of_le_of_ne_bot_of_card_prime [Finite G] {A B : Subgroup G} {p : ℕ} (hp : p.Prime)
    (h : A ≤ B) (hA : A ≠ ⊥) (hB : Nat.card B = p) : A = B := by
  have hdvd : Nat.card A ∣ p := hB ▸ Subgroup.card_dvd_of_le h
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
  · exact absurd (Subgroup.eq_bot_of_card_eq A h1) hA
  · exact Subgroup.eq_of_le_of_card_ge h (by rw [hB, h1])

theorem exists_generator_aux [Finite G] {p : ℕ} (hp : p.Prime) {Y : Subgroup G}
    (hY : Nat.card Y = p) (hexp : ∀ x ∈ Y, x ^ p = 1) :
    ∃ y ∈ Y, y ≠ 1 ∧ Subgroup.zpowers y = Y := by
  have : Fact p.Prime := ⟨hp⟩
  have hne : Y ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hY
    exact hp.one_lt.ne hY
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  refine ⟨y, hy, hy1', ?_⟩
  have hoy : orderOf y = p := orderOf_eq_prime (hexp y hy) hy1'
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy)
    (by rw [Nat.card_zpowers, hoy, hY])).symm ▸ rfl

theorem exp_one_add_two_mul {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {p : G} (hp : p ^ q = 1) :
    ∃ k : ℕ, p = (p ^ 2) ^ (k + 1) := by
  obtain ⟨k, hk⟩ := exists_odd hq hq2
  refine ⟨k, ?_⟩
  rw [← pow_mul]
  have : p ^ (2 * (k + 1)) = p ^ q * p := by
    rw [hk, ← pow_succ]
    congr 1
  rw [this, hp, one_mul]

theorem mem_normalizer_of_involution {K : Subgroup G} {w : G} (hw : w * w = 1)
    (h : ∀ x ∈ K, w * x * w⁻¹ ∈ K) : w ∈ normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have := h _ hx
  have e : w * (w * x * w⁻¹) * w⁻¹ = x := by
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
    rw [hwi]
    calc w * (w * x * w) * w = (w * w) * x * (w * w) := by group
      _ = x := by rw [hw]; group
  rwa [e] at this

structure OddGeometry (q : ℕ) (D Z : Subgroup G) (r z : G) : Prop where
  prime : q.Prime
  odd : q ≠ 2
  le : Z ≤ D
  exp : ∀ x ∈ D, x ^ q = 1
  comm_mem : ∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ ∈ Z
  central : ∀ ζ ∈ Z, ∀ x ∈ D, ζ * x = x * ζ
  center_le : ∀ x ∈ D, (∀ y ∈ D, x * y = y * x) → x ∈ Z
  card_Z : Nat.card Z = q
  card_D : Nat.card D = q ^ 5
  r_norm : r ∈ normalizer (D : Set G)
  r_mul_self : r * r = 1
  r_Z : ∀ ζ ∈ Z, r * ζ = ζ * r
  z_norm : z ∈ normalizer (D : Set G)
  z_ne_one : z ≠ 1
  z_mul_self : z * z = 1
  z_Z : ∀ ζ ∈ Z, z * ζ = ζ * z
  z_inv : ∀ d ∈ D, z * d * z⁻¹ * d ∈ Z
  split : ∀ d ∈ D, ∃ f ∈ D, r * f * r⁻¹ = f ∧ ∃ m ∈ D, d = f * m ∧ r * m * r⁻¹ * m ∈ Z
  card_F : Nat.card ↥(D ⊓ centralizer ({r} : Set G)) = q ^ 3

variable {q : ℕ} {D Z : Subgroup G} {r z : G}

theorem conj_mem_of_normalizer {g x : G} (hg : g ∈ normalizer (D : Set G)) (hx : x ∈ D) :
    g * x * g⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hg x).mp hx

theorem mem_F_iff {x : G} : x ∈ D ⊓ centralizer ({r} : Set G) ↔ x ∈ D ∧ r * x * r⁻¹ = x := by
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    calc r * x * r⁻¹ = x * r * r⁻¹ := by rw [h]
      _ = x := by group
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    calc x * r = (r * x * r⁻¹) * r := by rw [h]
      _ = r * x := by group

namespace OddGeometry

theorem Z_le_F (h : OddGeometry q D Z r z) : Z ≤ D ⊓ centralizer ({r} : Set G) := fun ζ hζ =>
  mem_F_iff.mpr ⟨h.le hζ, by
    have := h.r_Z ζ hζ
    calc r * ζ * r⁻¹ = ζ * r * r⁻¹ := by rw [this]
      _ = ζ := by group⟩

theorem split_exact (h : OddGeometry q D Z r z) :
    ∀ d ∈ D, ∃ f ∈ D, r * f * r⁻¹ = f ∧ ∃ m ∈ D, d = f * m ∧ r * m * r⁻¹ = m⁻¹ := by
  intro d hd
  obtain ⟨f, hf, hfr, m, hm, hdm, hζ⟩ := h.split d hd
  obtain ⟨k, hk⟩ := exists_odd h.prime h.odd
  set ζ := r * m * r⁻¹ * m with hζdef
  have hwZ : ζ ^ k ∈ Z := pow_mem hζ k
  have hwD : ζ ^ k ∈ D := h.le hwZ
  have hwc : ∀ x ∈ D, ζ ^ k * x = x * ζ ^ k := fun x hx => h.central _ hwZ x hx
  have hrw : r * ζ ^ k * r⁻¹ = ζ ^ k := by
    have := h.r_Z _ hwZ
    calc r * ζ ^ k * r⁻¹ = ζ ^ k * r * r⁻¹ := by rw [this]
      _ = ζ ^ k := by group
  have hmr : r * m * r⁻¹ = ζ * m⁻¹ := by rw [hζdef]; group
  have hζq : ζ ^ q = 1 := h.exp ζ (h.le hζ)
  refine ⟨f * (ζ ^ k)⁻¹, mul_mem hf (inv_mem hwD), ?_, m * ζ ^ k, mul_mem hm hwD, ?_, ?_⟩
  ·
    have h1 : r * (ζ ^ k)⁻¹ * r⁻¹ = (ζ ^ k)⁻¹ := by
      have : r * (ζ ^ k)⁻¹ * r⁻¹ = (r * ζ ^ k * r⁻¹)⁻¹ := by group
      rw [this, hrw]
    calc r * (f * (ζ ^ k)⁻¹) * r⁻¹ = (r * f * r⁻¹) * (r * (ζ ^ k)⁻¹ * r⁻¹) := by group
      _ = f * (ζ ^ k)⁻¹ := by rw [hfr, h1]
  ·
    rw [hdm]
    have := hwc m hm
    calc f * m = f * (ζ ^ k)⁻¹ * (ζ ^ k * m) := by group
      _ = f * (ζ ^ k)⁻¹ * (m * ζ ^ k) := by rw [this]
  ·
    calc r * (m * ζ ^ k) * r⁻¹ = (r * m * r⁻¹) * (r * ζ ^ k * r⁻¹) := by group
      _ = ζ * m⁻¹ * ζ ^ k := by rw [hmr, hrw]
      _ = ζ * ζ ^ k * m⁻¹ := by
          have := hwc m⁻¹ (inv_mem hm)
          rw [mul_assoc, ← this]
          group
      _ = (m * ζ ^ k)⁻¹ := by
          have h2 : ζ * ζ ^ k = (ζ ^ k)⁻¹ := by
            have : ζ * ζ ^ k * ζ ^ k = 1 := by
              calc ζ * ζ ^ k * ζ ^ k = ζ ^ (2 * k + 1) := by group
                _ = 1 := by rw [← hk]; exact hζq
            exact mul_eq_one_iff_eq_inv.mp this
          rw [h2, mul_inv_rev]


theorem comm_fixed_inverted (h : OddGeometry q D Z r z) {x m : G} (hx : x ∈ D)
    (hxr : r * x * r⁻¹ = x) (hm : m ∈ D) (hmr : r * m * r⁻¹ = m⁻¹) : x * m = m * x := by
  set c := ⁅x, m⁆ with hc
  have hcZ : c ∈ Z := h.comm_mem x hx m hm
  have h1 : r * c * r⁻¹ = c := by
    have := h.r_Z c hcZ
    calc r * c * r⁻¹ = c * r * r⁻¹ := by rw [this]
      _ = c := by group
  have hcm : c * m = m * c := h.central c hcZ m hm
  have h2 : r * c * r⁻¹ = c⁻¹ := by
    have e : r * c * r⁻¹ =
        (r * x * r⁻¹) * (r * m * r⁻¹) * (r * x * r⁻¹)⁻¹ * (r * m * r⁻¹)⁻¹ := by
      simp only [hc, commutatorElement_def]; group
    rw [e, hxr, hmr]
    have hxmx : x * m * x⁻¹ = c * m := by simp only [hc, commutatorElement_def]; group
    have hmcm : m⁻¹ * c * m = c := by
      calc m⁻¹ * c * m = m⁻¹ * (c * m) := by group
        _ = c := by rw [hcm]; group
    calc x * m⁻¹ * x⁻¹ * m⁻¹⁻¹ = (x * m * x⁻¹)⁻¹ * m := by group
      _ = (c * m)⁻¹ * m := by rw [hxmx]
      _ = (m⁻¹ * c * m)⁻¹ := by group
      _ = c⁻¹ := by rw [hmcm]
  have hcc : c * c = 1 := by
    have : c = c⁻¹ := h1.symm.trans h2
    calc c * c = c⁻¹ * c := by rw [← this]
      _ = 1 := by group
  have hc1 : c = 1 :=
    eq_one_of_sq_eq_one h.prime h.odd (by rw [pow_two]; exact hcc) (h.exp c (h.le hcZ))
  have : x * m * x⁻¹ * m⁻¹ = 1 := hc1
  calc x * m = (x * m * x⁻¹ * m⁻¹) * (m * x) := by group
    _ = m * x := by rw [this, one_mul]


theorem center_F (h : OddGeometry q D Z r z) {x : G} (hx : x ∈ D ⊓ centralizer ({r} : Set G))
    (hc : ∀ y ∈ D ⊓ centralizer ({r} : Set G), x * y = y * x) : x ∈ Z := by
  obtain ⟨hxD, hxr⟩ := mem_F_iff.mp hx
  refine h.center_le x hxD fun y hy => ?_
  obtain ⟨f, hf, hfr, m, hm, hym, hmr⟩ := h.split_exact y hy
  have hfF : f ∈ D ⊓ centralizer ({r} : Set G) := mem_F_iff.mpr ⟨hf, hfr⟩
  have h1 : x * f = f * x := hc f hfF
  have h2 : x * m = m * x := h.comm_fixed_inverted hxD hxr hm hmr
  rw [hym]
  calc x * (f * m) = (x * f) * m := by group
    _ = f * (x * m) := by rw [h1]; group
    _ = f * (m * x) := by rw [h2]
    _ = f * m * x := by group

theorem exists_inverted [Finite G] (h : OddGeometry q D Z r z) :
    ∃ m ∈ D, m ∉ Z ∧ r * m * r⁻¹ = m⁻¹ := by
  have hFD : ¬ D ≤ D ⊓ centralizer ({r} : Set G) := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    rw [h.card_D, h.card_F] at h1
    have h2 : q ^ 3 < q ^ 5 := Nat.pow_lt_pow_right h.prime.one_lt (by norm_num)
    omega
  rw [IsConcreteLE.not_le_iff_exists] at hFD
  obtain ⟨d, hdD, hdF⟩ := hFD
  obtain ⟨f, hf, hfr, m, hm, hdm, hmr⟩ := h.split_exact d hdD
  refine ⟨m, hm, fun hmZ => hdF ?_, hmr⟩
  rw [hdm]
  exact mul_mem (mem_F_iff.mpr ⟨hf, hfr⟩) (h.Z_le_F hmZ)


theorem commutator_F [Finite G] (h : OddGeometry q D Z r z) :
    ⁅D ⊓ centralizer ({r} : Set G), D ⊓ centralizer ({r} : Set G)⁆ = Z := by
  set F := D ⊓ centralizer ({r} : Set G) with hF
  have hle : ⁅F, F⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact h.comm_mem x (mem_F_iff.mp hx).1 y (mem_F_iff.mp hy).1
  have hne : ⁅F, F⁆ ≠ ⊥ := by
    have hFZ : ¬ F ≤ Z := by
      intro hFZ
      have h1 := Subgroup.card_le_of_le hFZ
      rw [h.card_F, h.card_Z] at h1
      have h2 : q ^ 1 < q ^ 3 := Nat.pow_lt_pow_right h.prime.one_lt (by norm_num)
      rw [pow_one] at h2
      omega
    rw [IsConcreteLE.not_le_iff_exists] at hFZ
    obtain ⟨x, hxF, hxZ⟩ := hFZ
    have hnc : ¬ ∀ y ∈ F, x * y = y * x := fun hc => hxZ (h.center_F hxF hc)
    push Not at hnc
    obtain ⟨y, hyF, hxy⟩ := hnc
    intro hbot
    apply hxy
    have hmem : ⁅x, y⁆ ∈ ⁅F, F⁆ := Subgroup.commutator_mem_commutator hxF hyF
    rw [hbot, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  exact eq_of_le_of_ne_bot_of_card_prime h.prime hle hne h.card_Z

theorem center_F_eq [Finite G] (h : OddGeometry q D Z r z) :
    (D ⊓ centralizer ({r} : Set G)) ⊓
      centralizer ((D ⊓ centralizer ({r} : Set G) : Subgroup G) : Set G) = Z := by
  apply le_antisymm
  · rintro x ⟨hx, hxc⟩
    exact h.center_F hx fun y hy => (Subgroup.mem_centralizer_iff.mp hxc y hy).symm
  · intro ζ hζ
    refine ⟨h.Z_le_F hζ, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact (h.central ζ hζ y (mem_F_iff.mp hy).1).symm


theorem exists_inverted_pair [Finite G] (h : OddGeometry q D Z r z) :
    ∃ m ∈ D, m ∉ Z ∧ r * m * r⁻¹ = m⁻¹ ∧
      ∃ m' ∈ D, r * m' * r⁻¹ = m'⁻¹ ∧ m * m' ≠ m' * m := by
  obtain ⟨m, hmD, hmZ, hmr⟩ := h.exists_inverted
  have hnc : ¬ ∀ d ∈ D, m * d = d * m := fun hc => hmZ (h.center_le m hmD hc)
  push Not at hnc
  obtain ⟨d, hdD, hmd⟩ := hnc
  obtain ⟨f, hf, hfr, m', hm', hdm, hm'r⟩ := h.split_exact d hdD
  refine ⟨m, hmD, hmZ, hmr, m', hm', hm'r, fun heq => hmd ?_⟩
  have h1 : m * f = f * m := h.comm_fixed_inverted hf hfr hmD hmr |>.symm
  rw [hdm]
  calc m * (f * m') = (m * f) * m' := by group
    _ = f * (m * m') := by rw [h1]; group
    _ = f * (m' * m) := by rw [heq]
    _ = f * m' * m := by group

theorem three_le_pRank [Finite G] (h : OddGeometry q D Z r z) {Y : Subgroup G}
    (hY : Y ≤ D ⊓ centralizer ({r} : Set G)) (hYq : Nat.card Y = q) (hYZ : ¬ Y ≤ Z) :
    3 ≤ CFSG.pRank q ↥(D ⊓ centralizer (Y : Set G)) := by
  have hYD : ∀ x ∈ Y, x ∈ D := fun x hx => (mem_F_iff.mp (hY hx)).1
  obtain ⟨y, hyY, hy1, hYy⟩ :=
    exists_generator_aux h.prime hYq (fun x hx => h.exp x (hYD x hx))
  have hyD : y ∈ D := hYD y hyY
  have hyr : r * y * r⁻¹ = y := (mem_F_iff.mp (hY hyY)).2
  have hyZ : y ∉ Z := fun hyZ => hYZ (by rw [← hYy]; exact Subgroup.zpowers_le.mpr hyZ)
  obtain ⟨ζ₀, hζ₀Z, hζ₀1, hZζ⟩ :=
    exists_generator_aux h.prime h.card_Z (fun x hx => h.exp x (h.le hx))
  obtain ⟨m, hmD, hmZ, hmr⟩ := h.exists_inverted
  have : Fact q.Prime := ⟨h.prime⟩
  have hoy : orderOf y = q := orderOf_eq_prime (h.exp y hyD) hy1
  have hζD : ζ₀ ∈ D := h.le hζ₀Z
  have hym : y * m = m * y := h.comm_fixed_inverted hyD hyr hmD hmr
  have hyζ : y * ζ₀ = ζ₀ * y := (h.central ζ₀ hζ₀Z y hyD).symm
  have hmζ : m * ζ₀ = ζ₀ * m := h.central ζ₀ hζ₀Z m hmD |>.symm
  have hcY : ∀ {w : G}, (∀ y' ∈ Y, y' * w = w * y') → w ∈ centralizer (Y : Set G) :=
    fun hw => Subgroup.mem_centralizer_iff.mpr hw
  have hyC : y ∈ D ⊓ centralizer (Y : Set G) := by
    refine ⟨hyD, hcY fun y' hy' => ?_⟩
    rw [← hYy] at hy'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
    exact ((Commute.refl y).zpow_left i).eq
  have hζC : ζ₀ ∈ D ⊓ centralizer (Y : Set G) :=
    ⟨hζD, hcY fun y' hy' => h.central ζ₀ hζ₀Z y' (hYD y' hy') |>.symm⟩
  have hmC : m ∈ D ⊓ centralizer (Y : Set G) := by
    refine ⟨hmD, hcY fun y' hy' => ?_⟩
    obtain ⟨hy'D, hy'r⟩ := mem_F_iff.mp (hY hy')
    exact h.comm_fixed_inverted hy'D hy'r hmD hmr
  have hζy : ζ₀ ∉ Subgroup.zpowers y := by
    intro hmem
    have h1 := zpowers_eq_of_mem_of_ne_one h.prime hoy hmem hζ₀1
    apply hyZ
    have : y ∈ Subgroup.zpowers ζ₀ := by rw [h1]; exact Subgroup.mem_zpowers y
    exact (Subgroup.zpowers_le.mpr hζ₀Z) this
  have hmyζ : m ∉ Subgroup.zpowers y ⊔ Subgroup.zpowers ζ₀ := by
    intro hmem
    have hcomm : ∀ a ∈ Subgroup.zpowers y, ∀ b ∈ Subgroup.zpowers ζ₀, a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ((show Commute y ζ₀ from hyζ).zpow_zpow i j).eq
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute hcomm hmem
    have hra : r * a * r⁻¹ = a := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [← conj_zpow, hyr]
    have hrb : r * b * r⁻¹ = b := by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have hrζ : r * ζ₀ * r⁻¹ = ζ₀ := by
        have := h.r_Z ζ₀ hζ₀Z
        calc r * ζ₀ * r⁻¹ = ζ₀ * r * r⁻¹ := by rw [this]
          _ = ζ₀ := by group
      rw [← conj_zpow, hrζ]
    have hrm : r * m * r⁻¹ = m := by
      rw [hab]
      calc r * (a * b) * r⁻¹ = (r * a * r⁻¹) * (r * b * r⁻¹) := by group
        _ = a * b := by rw [hra, hrb]
    have hmm : m = m⁻¹ := hrm.symm.trans hmr
    have hm1 : m = 1 := by
      refine eq_one_of_sq_eq_one h.prime h.odd ?_ (h.exp m hmD)
      rw [pow_two]
      calc m * m = m⁻¹ * m := by rw [← hmm]
        _ = 1 := by group
    exact hmZ (hm1 ▸ one_mem Z)
  exact three_le_pRank_of_commuting h.prime hyC hζC hmC hyζ hym hmζ.symm
    (h.exp y hyD) (h.exp ζ₀ hζD) (h.exp m hmD) hy1 hζ₀1 hζy hmyζ

end OddGeometry

theorem commutatorElement_mul_central {a b ζ₁ ζ₂ : G}
    (h2 : ζ₁ * b = b * ζ₁) (h3 : ζ₂ * a = a * ζ₂) (h5 : ζ₁ * ζ₂ = ζ₂ * ζ₁) :
    ⁅a * ζ₁, b * ζ₂⁆ = ⁅a, b⁆ := by
  have hconj : ∀ {u v : G}, u * v = v * u → u * v * u⁻¹ = v := fun {u v} huv => by
    calc u * v * u⁻¹ = v * u * u⁻¹ := by rw [huv]
      _ = v := by group
  have h2' := hconj h2
  have h3' : ζ₂ * (a * ζ₁) * ζ₂⁻¹ = a * ζ₁ := by
    have e : ζ₂ * (a * ζ₁) = (a * ζ₁) * ζ₂ := by
      calc ζ₂ * (a * ζ₁) = (ζ₂ * a) * ζ₁ := by group
        _ = a * (ζ₂ * ζ₁) := by rw [h3]; group
        _ = a * (ζ₁ * ζ₂) := by rw [h5]
        _ = (a * ζ₁) * ζ₂ := by group
    exact hconj e
  have step1 : ⁅a * ζ₁, b * ζ₂⁆ = ⁅a * ζ₁, b⁆ := by
    simp only [commutatorElement_def]
    calc a * ζ₁ * (b * ζ₂) * (a * ζ₁)⁻¹ * (b * ζ₂)⁻¹
        = a * ζ₁ * b * (ζ₂ * (a * ζ₁)⁻¹ * ζ₂⁻¹) * b⁻¹ := by group
      _ = a * ζ₁ * b * (a * ζ₁)⁻¹ * b⁻¹ := by
          have : ζ₂ * (a * ζ₁)⁻¹ * ζ₂⁻¹ = (a * ζ₁)⁻¹ := by
            have := congrArg (fun x => x⁻¹) h3'
            simp only [mul_inv_rev, inv_inv] at this
            calc ζ₂ * (a * ζ₁)⁻¹ * ζ₂⁻¹ = (ζ₂ * (a * ζ₁) * ζ₂⁻¹)⁻¹ := by group
              _ = (a * ζ₁)⁻¹ := by rw [h3']
          rw [this]
  have step2 : ⁅a * ζ₁, b⁆ = ⁅a, b⁆ := by
    simp only [commutatorElement_def]
    calc a * ζ₁ * b * (a * ζ₁)⁻¹ * b⁻¹ = a * (ζ₁ * b * ζ₁⁻¹) * a⁻¹ * b⁻¹ := by group
      _ = a * b * a⁻¹ * b⁻¹ := by rw [h2']
  rw [step1, step2]

namespace OddGeometry

theorem eq_commutator_zpowers [Finite G] (h : OddGeometry q D Z r z) {Y : Subgroup G}
    (hY : Y ≤ D ⊓ centralizer ({r} : Set G)) (hzY : z ∈ normalizer (Y : Set G)) :
    D ⊓ centralizer (Y : Set G) = ⁅D ⊓ centralizer (Y : Set G), Subgroup.zpowers z⁆ := by
  set P := D ⊓ centralizer (Y : Set G) with hP
  set K := ⁅P, Subgroup.zpowers z⁆ with hK
  have hzo : orderOf z = 2 := by
    refine orderOf_eq_prime ?_ h.z_ne_one
    rw [pow_two]; exact h.z_mul_self
  have hzD : ∀ x ∈ D, z * x * z⁻¹ ∈ D := fun x hx => conj_mem_of_normalizer h.z_norm hx
  have hYD : ∀ x ∈ Y, x ∈ D := fun x hx => (mem_F_iff.mp (hY hx)).1
  have hzP : ∀ p ∈ P, z * p * z⁻¹ ∈ P := by
    intro p hp
    refine ⟨hzD p hp.1, Subgroup.mem_centralizer_iff.mpr fun y' hy' => ?_⟩
    have hy'' : z⁻¹ * y' * z ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp hzY (z⁻¹ * y' * z)).mp
      apply (Subgroup.mem_normalizer_iff.mp hzY (z⁻¹ * y' * z)).mpr
      have e : z * (z⁻¹ * y' * z) * z⁻¹ = y' := by group
      rw [e]; exact hy'
    have hc := Subgroup.mem_centralizer_iff.mp hp.2 _ hy''
    calc y' * (z * p * z⁻¹) = z * ((z⁻¹ * y' * z) * p) * z⁻¹ := by group
      _ = z * (p * (z⁻¹ * y' * z)) * z⁻¹ := by rw [hc]
      _ = z * p * z⁻¹ * y' := by group
  have hKP : K ≤ P := by
    rw [hK, Subgroup.commutator_le]
    intro p hp w hw
    rcases (mem_zpowers_of_orderOf_eq_two hzo).mp hw with hw1 | hw1
    · rw [hw1, commutatorElement_one_right]; exact one_mem P
    · have := mul_mem hp (inv_mem (hzP p hp))
      have e : p * (z * p * z⁻¹)⁻¹ = ⁅p, w⁆ := by
        rw [hw1]; simp only [commutatorElement_def]; group
      rw [← e]; exact this
  have hdecomp : ∀ p ∈ P, ∃ κ ∈ K, ∃ ζ ∈ Z, p = κ * ζ := by
    intro p hp
    have hpD : p ∈ D := hp.1
    obtain ⟨k, hk⟩ := exp_one_add_two_mul h.prime h.odd (h.exp p hpD)
    set ζ := z * p * z⁻¹ * p with hζ
    have hζZ : ζ ∈ Z := h.z_inv p hpD
    have hcz : ⁅p, z⁆ ∈ K := Subgroup.commutator_mem_commutator hp (Subgroup.mem_zpowers z)
    have hczD : ⁅p, z⁆ ∈ D := by
      have : ⁅p, z⁆ = p * (z * p⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact mul_mem hpD (by
        have := hzD p⁻¹ (inv_mem hpD)
        exact this)
    have hp2 : p ^ 2 = ⁅p, z⁆ * ζ := by
      rw [pow_two]; simp only [hζ, commutatorElement_def]; group
    have hcomm : Commute ⁅p, z⁆ ζ := (h.central ζ hζZ _ hczD).symm
    refine ⟨⁅p, z⁆ ^ (k + 1), pow_mem hcz _, ζ ^ (k + 1), pow_mem hζZ _, ?_⟩
    rw [← hcomm.mul_pow, ← hp2]
    exact hk
  have hPP : ⁅P, P⁆ = Z := by
    have hle : ⁅P, P⁆ ≤ Z := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      exact h.comm_mem x hx.1 y hy.1
    have hne : ⁅P, P⁆ ≠ ⊥ := by
      obtain ⟨m, hmD, -, hmr, m', hm'D, hm'r, hmm'⟩ := h.exists_inverted_pair
      have hmP : ∀ w ∈ D, r * w * r⁻¹ = w⁻¹ → w ∈ P := by
        intro w hwD hwr
        refine ⟨hwD, Subgroup.mem_centralizer_iff.mpr fun y' hy' => ?_⟩
        obtain ⟨hy'D, hy'r⟩ := mem_F_iff.mp (hY hy')
        exact h.comm_fixed_inverted hy'D hy'r hwD hwr
      intro hbot
      apply hmm'
      have hmem : ⁅m, m'⁆ ∈ ⁅P, P⁆ :=
        Subgroup.commutator_mem_commutator (hmP m hmD hmr) (hmP m' hm'D hm'r)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact commutatorElement_eq_one_iff_mul_comm.mp hmem
    exact eq_of_le_of_ne_bot_of_card_prime h.prime hle hne h.card_Z
  have hZK : Z ≤ K := by
    rw [← hPP, Subgroup.commutator_le]
    intro p₁ hp₁ p₂ hp₂
    obtain ⟨κ₁, hκ₁, ζ₁, hζ₁, rfl⟩ := hdecomp p₁ hp₁
    obtain ⟨κ₂, hκ₂, ζ₂, hζ₂, rfl⟩ := hdecomp p₂ hp₂
    have hκ₂D : κ₂ ∈ D := (hKP hκ₂).1
    have hκ₁D : κ₁ ∈ D := (hKP hκ₁).1
    rw [commutatorElement_mul_central (h.central ζ₁ hζ₁ κ₂ hκ₂D) (h.central ζ₂ hζ₂ κ₁ hκ₁D)
      (h.central ζ₂ hζ₂ ζ₁ (h.le hζ₁) |>.symm)]
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hκ₁ hκ₂) (inv_mem hκ₁)) (inv_mem hκ₂)
  refine le_antisymm (fun p hp => ?_) hKP
  obtain ⟨κ, hκ, ζ, hζ, rfl⟩ := hdecomp p hp
  exact mul_mem hκ (hZK hζ)

theorem exists_conjugate [Finite G] (h : OddGeometry q D Z r z) {Y : Subgroup G}
    (hY : Y ≤ D ⊓ centralizer ({r} : Set G)) (hYq : Nat.card Y = q) (hYZ : ¬ Y ≤ Z)
    (B : Subgroup G) (hBz : ∀ b ∈ B, b * z = z * b)
    (hB : ∀ b ∈ B, ∃ l : ℕ, ∀ d ∈ D, b * d * b⁻¹ * (d ^ l)⁻¹ ∈ Z) :
    ∃ f ∈ D ⊓ centralizer ({r} : Set G), B ≤ normalizer (conjugate Y f : Set G) ∧
      z ∈ normalizer (conjugate Y f : Set G) := by
  have : Fact q.Prime := ⟨h.prime⟩
  have hYD : ∀ x ∈ Y, x ∈ D := fun x hx => (mem_F_iff.mp (hY hx)).1
  obtain ⟨y, hyY, hy1, hYy⟩ :=
    exists_generator_aux h.prime hYq (fun x hx => h.exp x (hYD x hx))
  have hyF : y ∈ D ⊓ centralizer ({r} : Set G) := hY hyY
  have hyD : y ∈ D := hYD y hyY
  have hyZ : y ∉ Z := fun hyZ => hYZ (by rw [← hYy]; exact Subgroup.zpowers_le.mpr hyZ)
  obtain ⟨k, hk⟩ := exists_odd h.prime h.odd
  set ζy := z * y * z⁻¹ * y with hζy
  have hζyZ : ζy ∈ Z := h.z_inv y hyD
  set ζ' := (ζy⁻¹) ^ (k + 1) with hζ'
  have hζ'Z : ζ' ∈ Z := pow_mem (inv_mem hζyZ) _
  have hζ'D : ζ' ∈ D := h.le hζ'Z
  set y₀ := y * ζ' with hy₀
  have hy₀D : y₀ ∈ D := mul_mem hyD hζ'D
  have hzζ' : z * ζ' * z⁻¹ = ζ' := by
    have := h.z_Z ζ' hζ'Z
    calc z * ζ' * z⁻¹ = ζ' * z * z⁻¹ := by rw [this]
      _ = ζ' := by group
  have hzy₀ : z * y₀ * z⁻¹ = y₀⁻¹ := by
    have hq1 : ζy * ζ' * ζ' = 1 := by
      have hu : (ζy⁻¹) ^ q = 1 := h.exp _ (inv_mem (h.le hζyZ))
      calc ζy * ζ' * ζ' = (ζy⁻¹)⁻¹ * (ζy⁻¹) ^ (k + 1) * (ζy⁻¹) ^ (k + 1) := by rw [hζ', inv_inv]
        _ = (ζy⁻¹) ^ (2 * k + 1) := by group
        _ = 1 := by rw [← hk]; exact hu
    have hc1 : ζ' * y⁻¹ = y⁻¹ * ζ' := (h.central ζ' hζ'Z y⁻¹ (inv_mem hyD))
    calc z * y₀ * z⁻¹ = (z * y * z⁻¹) * (z * ζ' * z⁻¹) := by rw [hy₀]; group
      _ = (ζy * y⁻¹) * ζ' := by rw [hzζ', hζy]; group
      _ = ζy * (y⁻¹ * ζ') := by group
      _ = ζy * (ζ' * y⁻¹) := by rw [hc1]
      _ = (ζy * ζ' * ζ') * (ζ'⁻¹ * ζ'⁻¹ * ζ' * y⁻¹) := by group
      _ = y₀⁻¹ := by
          rw [hq1, one_mul, hy₀, mul_inv_rev]
          group
  set cc : G → G := fun f => y⁻¹ * f⁻¹ * y * f with hcc
  have hccZ : ∀ f ∈ D, cc f ∈ Z := fun f hf => by
    have e : cc f = ⁅y⁻¹, f⁻¹⁆ := by simp [hcc, commutatorElement_def]
    rw [e]
    exact h.comm_mem y⁻¹ (inv_mem hyD) f⁻¹ (inv_mem hf)
  have hccmul : ∀ f ∈ D, ∀ g ∈ D, cc (f * g) = cc f * cc g := by
    intro f hf g hg
    have hcfZ := hccZ f hf
    have hcgZ := hccZ g hg
    have hcen : cc f * g = g * cc f := (h.central _ hcfZ g hg)
    have e1 : f⁻¹ * y * f = y * cc f := by simp only [hcc]; group
    have e2 : g⁻¹ * cc f * g = cc f := by
      calc g⁻¹ * cc f * g = g⁻¹ * (cc f * g) := by group
        _ = g⁻¹ * (g * cc f) := by rw [hcen]
        _ = cc f := by group
    calc cc (f * g) = y⁻¹ * g⁻¹ * (f⁻¹ * y * f) * g := by simp only [hcc]; group
      _ = y⁻¹ * g⁻¹ * (y * cc f) * g := by rw [e1]
      _ = (y⁻¹ * g⁻¹ * y * g) * (g⁻¹ * cc f * g) := by group
      _ = cc g * cc f := by rw [e2]
      _ = cc f * cc g := h.central (cc g) hcgZ (cc f) (h.le hcfZ)
  have hccpow : ∀ f ∈ D, ∀ n : ℕ, cc (f ^ n) = cc f ^ n := by
    intro f hf n
    induction n with
    | zero => simp [hcc]
    | succ n ih => rw [pow_succ, hccmul _ (pow_mem hf n) f hf, ih, pow_succ]
  have hnc : ¬ ∀ y' ∈ D ⊓ centralizer ({r} : Set G), y * y' = y' * y :=
    fun hc => hyZ (h.center_F hyF hc)
  push Not at hnc
  obtain ⟨f₀, hf₀F, hyf₀⟩ := hnc
  have hf₀D : f₀ ∈ D := (mem_F_iff.mp hf₀F).1
  have hcc1 : cc f₀ ≠ 1 := by
    intro h1
    apply hyf₀
    have h1' : y⁻¹ * f₀⁻¹ * y * f₀ = 1 := h1
    have e : f₀⁻¹ * y * f₀ = y := by
      calc f₀⁻¹ * y * f₀ = y * (y⁻¹ * f₀⁻¹ * y * f₀) := by group
        _ = y := by rw [h1', mul_one]
    calc y * f₀ = f₀ * (f₀⁻¹ * y * f₀) := by group
      _ = f₀ * y := by rw [e]
  obtain ⟨ζ₀, hζ₀Z, hζ₀1, hZζ⟩ :=
    exists_generator_aux h.prime h.card_Z (fun x hx => h.exp x (h.le hx))
  have hoζ₀ : orderOf ζ₀ = q := orderOf_eq_prime (h.exp ζ₀ (h.le hζ₀Z)) hζ₀1
  have hcc0Z : cc f₀ ∈ Subgroup.zpowers ζ₀ := by rw [hZζ]; exact hccZ f₀ hf₀D
  have hZcc : Subgroup.zpowers (cc f₀) = Z := by
    rw [zpowers_eq_of_mem_of_ne_one h.prime hoζ₀ hcc0Z hcc1, hZζ]
  have hζ'cc : ζ' ∈ Subgroup.zpowers (cc f₀) := by rw [hZcc]; exact hζ'Z
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hζ'cc)
  have hfF : f₀ ^ n ∈ D ⊓ centralizer ({r} : Set G) := pow_mem hf₀F n
  have hfD : f₀ ^ n ∈ D := (mem_F_iff.mp hfF).1
  have hccf : cc (f₀ ^ n) = ζ' := by rw [hccpow f₀ hf₀D n, hn]
  have hfy : (f₀ ^ n)⁻¹ * y * f₀ ^ n = y₀ := by
    have : (f₀ ^ n)⁻¹ * y * f₀ ^ n = y * cc (f₀ ^ n) := by simp only [hcc]; group
    rw [this, hccf]
  have hconj : conjugate Y (f₀ ^ n) = Subgroup.zpowers y₀ := by
    rw [← hYy, conjugate, MonoidHom.map_zpowers]
    congr 1
    change (MulAut.conj (f₀ ^ n)⁻¹) y = y₀
    rw [MulAut.conj_apply, inv_inv]
    exact hfy
  refine ⟨f₀ ^ n, hfF, ?_, ?_⟩
  · rw [hconj]
    apply le_normalizer_of_forall
    intro b hb x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hby : b * y₀ * b⁻¹ ∈ Subgroup.zpowers y₀ := by
      obtain ⟨l, hl⟩ := hB b hb
      set ζ₃ := b * y₀ * b⁻¹ * (y₀ ^ l)⁻¹ with hζ₃
      have hζ₃Z : ζ₃ ∈ Z := hl y₀ hy₀D
      have hbζ : b * y₀ * b⁻¹ = ζ₃ * y₀ ^ l := by simp only [hζ₃]; group
      have hbz := hBz b hb
      have hzb : z * (b * y₀ * b⁻¹) * z⁻¹ = (b * y₀ * b⁻¹)⁻¹ := by
        calc z * (b * y₀ * b⁻¹) * z⁻¹ = (z * b) * y₀ * (z * b)⁻¹ := by group
          _ = (b * z) * y₀ * (b * z)⁻¹ := by rw [hbz]
          _ = b * (z * y₀ * z⁻¹) * b⁻¹ := by group
          _ = b * y₀⁻¹ * b⁻¹ := by rw [hzy₀]
          _ = (b * y₀ * b⁻¹)⁻¹ := by group
      rw [hbζ] at hzb
      have hzζ₃ : z * ζ₃ * z⁻¹ = ζ₃ := by
        have := h.z_Z ζ₃ hζ₃Z
        calc z * ζ₃ * z⁻¹ = ζ₃ * z * z⁻¹ := by rw [this]
          _ = ζ₃ := by group
      have hzl : z * y₀ ^ l * z⁻¹ = (y₀⁻¹) ^ l := by rw [← hzy₀, conj_pow]
      have hζ₃sq : ζ₃ = ζ₃⁻¹ := by
        have h1 : z * (ζ₃ * y₀ ^ l) * z⁻¹ = ζ₃ * (y₀⁻¹) ^ l := by
          calc z * (ζ₃ * y₀ ^ l) * z⁻¹ = (z * ζ₃ * z⁻¹) * (z * y₀ ^ l * z⁻¹) := by group
            _ = ζ₃ * (y₀⁻¹) ^ l := by rw [hzζ₃, hzl]
        have h2 : (ζ₃ * y₀ ^ l)⁻¹ = ζ₃⁻¹ * (y₀⁻¹) ^ l := by
          calc (ζ₃ * y₀ ^ l)⁻¹ = (y₀ ^ l)⁻¹ * ζ₃⁻¹ := by group
            _ = (y₀⁻¹) ^ l * ζ₃⁻¹ := by rw [inv_pow]
            _ = ζ₃⁻¹ * (y₀⁻¹) ^ l :=
                (h.central ζ₃⁻¹ (inv_mem hζ₃Z) _ (pow_mem (inv_mem hy₀D) l)).symm
        rw [h1, h2] at hzb
        exact mul_right_cancel hzb
      have hζ₃1 : ζ₃ = 1 := by
        refine eq_one_of_sq_eq_one h.prime h.odd ?_ (h.exp ζ₃ (h.le hζ₃Z))
        rw [pow_two]
        calc ζ₃ * ζ₃ = ζ₃⁻¹ * ζ₃ := by rw [← hζ₃sq]
          _ = 1 := by group
      rw [hbζ, hζ₃1, one_mul]
      exact pow_mem (Subgroup.mem_zpowers y₀) l
    rw [← conj_zpow]
    exact zpow_mem hby i
  · rw [hconj]
    apply mem_normalizer_of_involution h.z_mul_self
    intro x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, hzy₀]
    exact zpow_mem (inv_mem (Subgroup.mem_zpowers y₀)) i

end OddGeometry

theorem inSubgroup_frattini_eq_commutator [Finite G] {q : ℕ} (hq : q.Prime) {X : Subgroup G}
    (hX : IsPGroup q X) (hexp : ∀ x ∈ X, x ^ q = 1) : inSubgroup frattini X = ⁅X, X⁆ := by
  have : Fact q.Prime := ⟨hq⟩
  have hexp' : ∀ x : ↥X, x ^ q = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  unfold inSubgroup
  rw [CFSG.RankThree.PartTwo.frattini_eq_commutator hX hexp']
  exact CFSG.RankThree.PartOne.OddCore37.map_subtype_commutator X

end CFSG.RankThree.PartOne.QD32Facts
