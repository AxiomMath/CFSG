module

public import CFSG.Quasithin.Background.A1bPGroups

public section

namespace CFSG.Quasithin.H13.L32A.Heis

open CFSG.Open
open scoped commutatorElement

variable {X : Type*} [Group X]

section Basic

variable (h : IsPOnePlusTwo 3 X)
include h

theorem pow_three_eq (x : X) : x ^ 3 = 1 := h.2.2 x

theorem card_eq : Nat.card X = 27 := by
  rw [h.2.1]
  norm_num

theorem finite : Finite X := Nat.finite_of_card_ne_zero (by rw [card_eq h]; norm_num)

theorem card_center : Nat.card (Subgroup.center X) = 3 := by
  have := h.1
  exact CFSG.IsExtraspecial.center_order_p 3 X

theorem quot_comm (a b : X ⧸ Subgroup.center X) : a * b = b * a := by
  have := h.1
  have hab := (CFSG.IsExtraspecial.quotient_elementary_abelian 3 X).toIsMulCommutative
  exact mul_comm' a b

omit h in
theorem mem_center_iff_mk {u : X} : u ∈ Subgroup.center X ↔ (u : X ⧸ Subgroup.center X) = 1 :=
  (QuotientGroup.eq_one_iff u).symm

theorem comm_mem_center (a b : X) : ⁅a, b⁆ ∈ Subgroup.center X := by
  rw [mem_center_iff_mk, commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
    quot_comm h (a : X ⧸ Subgroup.center X) (b : X ⧸ Subgroup.center X)]
  group

theorem comm_comm (a b c : X) : ⁅a, b⁆ * c = c * ⁅a, b⁆ :=
  (Subgroup.mem_center_iff.mp (comm_mem_center h a b) c).symm

theorem center_ne_top : Subgroup.center X ≠ ⊤ := by
  intro htop
  have h1 := card_center h
  rw [htop, Subgroup.card_top, card_eq h] at h1
  norm_num at h1

theorem exists_comm_ne_one : ∃ a b : X, ⁅a, b⁆ ≠ 1 := by
  by_contra hno
  push Not at hno
  apply center_ne_top h
  refine eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => ?_
  exact (commutatorElement_eq_one_iff_mul_comm.mp (hno y x))

omit h in
theorem exists_comm_ne_one_of_not_mem {a : X} (ha : a ∉ Subgroup.center X) :
    ∃ b : X, ⁅a, b⁆ ≠ 1 := by
  by_contra hno
  push Not at hno
  apply ha
  refine Subgroup.mem_center_iff.mpr fun y => ?_
  exact (commutatorElement_eq_one_iff_mul_comm.mp (hno y)).symm

theorem comm_mul_left (a c b : X) : ⁅a * c, b⁆ = ⁅a, b⁆ * ⁅c, b⁆ := by
  have e : ⁅a * c, b⁆ = a * ⁅c, b⁆ * a⁻¹ * ⁅a, b⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, ← comm_comm h c b a, mul_inv_cancel_right, comm_comm h c b]

theorem comm_mul_right (a b d : X) : ⁅a, b * d⁆ = ⁅a, b⁆ * ⁅a, d⁆ := by
  rw [← commutatorElement_inv, comm_mul_left h, mul_inv_rev, commutatorElement_inv,
    commutatorElement_inv, comm_comm h a d]

theorem comm_inv_left (a b : X) : ⁅a⁻¹, b⁆ = ⁅a, b⁆⁻¹ := by
  have h1 := comm_mul_left h a⁻¹ a b
  rw [inv_mul_cancel, commutatorElement_one_left] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem comm_inv_right (a b : X) : ⁅a, b⁻¹⁆ = ⁅a, b⁆⁻¹ := by
  rw [← commutatorElement_inv, comm_inv_left h, commutatorElement_inv]

theorem comm_center_left {a c : X} (b : X) (hc : c ∈ Subgroup.center X) : ⁅c * a, b⁆ = ⁅a, b⁆ := by
  rw [comm_mul_left h, commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_center_iff.mp hc b).symm, one_mul]

theorem comm_center_right {b d : X} (a : X) (hd : d ∈ Subgroup.center X) :
    ⁅a, d * b⁆ = ⁅a, b⁆ := by
  rw [comm_mul_right h, commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_center_iff.mp hd a), one_mul]

theorem eq_one_of_eq_inv {u : X} (hu : u = u⁻¹) : u = 1 := by
  have h3 := pow_three_eq h u
  have h2 : u ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [hu]
    exact mul_inv_cancel u
  calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; group

theorem mem_center_of_sq {u : X} (hu : u ^ 2 ∈ Subgroup.center X) : u ∈ Subgroup.center X := by
  have e : u = (u ^ 2) ^ 2 * (u ^ 3)⁻¹ := by group
  rw [e, pow_three_eq h, inv_one, mul_one]
  exact Subgroup.pow_mem _ hu 2

theorem card_centralizer {a : X} (ha : a ∉ Subgroup.center X) :
    Nat.card (Subgroup.centralizer ({a} : Set X)) = 9 := by
  have := finite h
  set C := Subgroup.centralizer ({a} : Set X) with hC
  have hZC : Subgroup.center X < C := by
    refine lt_of_le_of_ne (fun z hz => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_) ?_
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact (Subgroup.mem_center_iff.mp hz a)
    · intro he
      apply ha
      rw [he]
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => by rw [Set.mem_singleton_iff.mp hy]
  have hCt : C < ⊤ := by
    refine lt_of_le_of_ne le_top fun he => ha (Subgroup.mem_center_iff.mpr fun y => ?_)
    have hy : y ∈ C := he ▸ Subgroup.mem_top y
    exact (Subgroup.mem_centralizer_iff.mp hy a (Set.mem_singleton a)).symm
  have h1 := Subgroup.card_lt_of_lt hZC
  have h2 := Subgroup.card_lt_of_lt hCt
  rw [card_center h] at h1
  rw [Subgroup.card_top, card_eq h] at h2
  have h3 : Nat.card C ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← card_eq h]
    exact Subgroup.card_subgroup_dvd_card C
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h3
  rw [hk'] at h1 h2 ⊢
  interval_cases k
  · norm_num at h1
  · norm_num at h1
  · norm_num
  · norm_num at h2

theorem comm_eq_one_of_comm {a b c : X} (ha : a ∉ Subgroup.center X) (hb : ⁅a, b⁆ = 1)
    (hc : ⁅a, c⁆ = 1) : ⁅b, c⁆ = 1 := by
  have := finite h
  set C := Subgroup.centralizer ({a} : Set X) with hC
  have hcard := card_centralizer h ha
  have hp : IsPGroup 3 C := IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm := commutative_of_card_le_prime_sq (p := 3) (P := ↥C) hp (by rw [hcard]; norm_num)
  have hbC : b ∈ C := Subgroup.mem_centralizer_iff.mpr fun y hy => by
    rw [Set.mem_singleton_iff.mp hy]
    exact commutatorElement_eq_one_iff_mul_comm.mp hb
  have hcC : c ∈ C := Subgroup.mem_centralizer_iff.mpr fun y hy => by
    rw [Set.mem_singleton_iff.mp hy]
    exact commutatorElement_eq_one_iff_mul_comm.mp hc
  have := hcomm ⟨b, hbC⟩ ⟨c, hcC⟩
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact congrArg Subtype.val this

end Basic

section Aut

variable (h : IsPOnePlusTwo 3 X)
include h

omit h in
theorem apply_apply_of_mul_self {φ : MulAut X} (hφ : φ * φ = 1) (x : X) : φ (φ x) = x := by
  rw [← MulAut.mul_apply, hφ, MulAut.one_apply]

omit h in
theorem map_mem_center (φ : MulAut X) {z : X} (hz : z ∈ Subgroup.center X) :
    φ z ∈ Subgroup.center X := by
  refine Subgroup.mem_center_iff.mpr fun g => ?_
  obtain ⟨g', rfl⟩ := φ.surjective g
  rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz g')]

omit h in
theorem symm_mem_center (φ : MulAut X) {z : X} (hz : z ∈ Subgroup.center X) :
    φ.symm z ∈ Subgroup.center X :=
  map_mem_center φ.symm hz

theorem sup_eq_of_card_nine {W : Subgroup X} (hZW : Subgroup.center X ≤ W)
    (hW : Nat.card W = 9) {w : X} (hwW : w ∈ W) (hw : w ∉ Subgroup.center X) :
    Subgroup.zpowers w ⊔ Subgroup.center X = W := by
  have := finite h
  have hle : Subgroup.zpowers w ⊔ Subgroup.center X ≤ W :=
    sup_le ((Subgroup.zpowers_le).mpr hwW) hZW
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hlt : Subgroup.center X < Subgroup.zpowers w ⊔ Subgroup.center X :=
    lt_of_le_of_ne le_sup_right fun he =>
      hw (he ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers w))
  have h1 := Subgroup.card_lt_of_lt hlt
  rw [card_center h] at h1
  have h2 : Nat.card ↥(Subgroup.zpowers w ⊔ Subgroup.center X) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hW]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
  rw [hk'] at h1 ⊢
  rw [hW]
  interval_cases k
  · norm_num at h1
  · norm_num at h1
  · norm_num

theorem exists_zpow_of_card_nine {W : Subgroup X} (hZW : Subgroup.center X ≤ W)
    (hW : Nat.card W = 9) {w : X} (hwW : w ∈ W) (hw : w ∉ Subgroup.center X) {u : X}
    (hu : u ∈ W) : ∃ n : ℤ, (w ^ n)⁻¹ * u ∈ Subgroup.center X := by
  rw [← sup_eq_of_card_nine h hZW hW hwW hw, Subgroup.mem_sup_of_normal_right] at hu
  obtain ⟨y, hy, z, hz, rfl⟩ := hu
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨n, ?_⟩
  rw [inv_mul_cancel_left]
  exact hz

theorem comm_eq_one_of_fix_inv {φ : MulAut X} (hZ : ∀ z ∈ Subgroup.center X, φ z = z) {c i : X}
    (hc : φ c * c⁻¹ ∈ Subgroup.center X) (hi : φ i * i ∈ Subgroup.center X) : ⁅c, i⁆ = 1 := by
  have e1 : φ ⁅c, i⁆ = ⁅c, i⁆ := hZ _ (comm_mem_center h c i)
  have ec : φ c = (φ c * c⁻¹) * c := by group
  have ei : φ i = (φ i * i) * i⁻¹ := by group
  rw [map_commutatorElement, ec, ei, comm_center_left h _ hc, comm_center_right h _ hi,
    comm_inv_right h] at e1
  exact eq_one_of_eq_inv h e1.symm

theorem comm_eq_one_of_inv_fix {φ : MulAut X} (hZ : ∀ z ∈ Subgroup.center X, φ z = z) {c i : X}
    (hi : φ i * i ∈ Subgroup.center X) (hc : φ c * c⁻¹ ∈ Subgroup.center X) : ⁅i, c⁆ = 1 := by
  rw [← commutatorElement_inv, comm_eq_one_of_fix_inv h hZ hc hi, inv_one]

omit h in
theorem mk_eq_one {u : X} (hu : u ∈ Subgroup.center X) : (u : X ⧸ Subgroup.center X) = 1 :=
  mem_center_iff_mk.mp hu

theorem decomp {φ : MulAut X} (hφ : φ * φ = 1) (x : X) :
    ∃ c i z : X, φ c * c⁻¹ ∈ Subgroup.center X ∧ φ i * i = 1 ∧ z ∈ Subgroup.center X ∧
      x = c * i * z := by
  have hφx := apply_apply_of_mul_self hφ x
  have hcomm : Commute (x : X ⧸ Subgroup.center X) ((φ x : X) : X ⧸ Subgroup.center X) :=
    quot_comm h _ _
  refine ⟨(x * φ x) ^ 2, x⁻¹ * φ x, ((x * φ x) ^ 2 * (x⁻¹ * φ x))⁻¹ * x, ?_, ?_, ?_, ?_⟩
  · rw [mem_center_iff_mk, map_pow, map_mul, hφx, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_pow, QuotientGroup.mk_pow, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      hcomm.eq]
    group
  · rw [map_mul, map_inv, hφx]
    group
  · rw [mem_center_iff_mk]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]
    rw [inv_mul_eq_one]
    have h3 : ((φ x : X) : X ⧸ Subgroup.center X) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, pow_three_eq h, QuotientGroup.mk_one]
    have e : ((x : X ⧸ Subgroup.center X) * ((φ x : X) : X ⧸ Subgroup.center X)) ^ 2 *
        ((x : X ⧸ Subgroup.center X)⁻¹ * ((φ x : X) : X ⧸ Subgroup.center X)) =
        (x : X ⧸ Subgroup.center X) * ((φ x : X) : X ⧸ Subgroup.center X) ^ 3 := by
      rw [sq, show (x : X ⧸ Subgroup.center X) * ((φ x : X) : X ⧸ Subgroup.center X) *
          ((x : X ⧸ Subgroup.center X) * ((φ x : X) : X ⧸ Subgroup.center X)) =
          (x : X ⧸ Subgroup.center X) * ((φ x : X) : X ⧸ Subgroup.center X) *
          (((φ x : X) : X ⧸ Subgroup.center X) * (x : X ⧸ Subgroup.center X)) by rw [hcomm.eq],
        pow_three]
      group
    rw [e, h3, mul_one]
  · group

theorem inverts_of_involution {φ : MulAut X} (hφ : φ * φ = 1)
    (hZ : ∀ z ∈ Subgroup.center X, φ z = z) (hne : φ ≠ 1) (x : X) :
    φ x * x ∈ Subgroup.center X := by
  by_contra hx
  obtain ⟨c₀, i₀', z₀, hc₀, hi₀', hz₀, hx₀⟩ := decomp h hφ x
  have hc₀Z : c₀ ∉ Subgroup.center X := by
    intro hcZ
    apply hx
    rw [mem_center_iff_mk, hx₀, map_mul, map_mul, hZ z₀ hz₀]
    simp only [QuotientGroup.mk_mul]
    rw [mk_eq_one (map_mem_center φ hcZ), mk_eq_one hcZ, mk_eq_one hz₀]
    simp only [one_mul, mul_one]
    rw [← QuotientGroup.mk_mul, hi₀', QuotientGroup.mk_one]
  have hI : ∃ i₁ : X, φ i₁ * i₁ = 1 ∧ i₁ ∉ Subgroup.center X := by
    by_contra hno
    push Not at hno
    apply hne
    ext y
    rw [MulAut.one_apply]
    obtain ⟨c, i, z, hc, hi, hz, hy⟩ := decomp h hφ y
    have hiZ := hno i hi
    have hyZ : φ y * y⁻¹ ∈ Subgroup.center X := by
      rw [mem_center_iff_mk, hy, map_mul, map_mul, hZ z hz]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_rev]
      rw [mk_eq_one (map_mem_center φ hiZ), mk_eq_one hiZ, mk_eq_one hz]
      simp only [one_mul, mul_one, inv_one]
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      exact mk_eq_one hc
    set w := φ y * y⁻¹ with hw
    have hφy : φ y = w * y := by rw [hw]; group
    have h2 := apply_apply_of_mul_self hφ y
    rw [hφy, map_mul, hZ w hyZ, hφy] at h2
    have hw1 : w * w = 1 := by
      have e : w * (w * y) * y⁻¹ = y * y⁻¹ := by rw [h2]
      rw [mul_inv_cancel] at e
      rw [← e]
      group
    have hw' : w = 1 := eq_one_of_eq_inv h (eq_inv_of_mul_eq_one_left hw1)
    rw [hφy, hw', one_mul]
  obtain ⟨i₁, hi₁, hi₁Z⟩ := hI
  have hi₁c : φ i₁ * i₁ ∈ Subgroup.center X := by rw [hi₁]; exact Subgroup.one_mem _
  obtain ⟨a, b, hab⟩ := exists_comm_ne_one h
  apply hab
  obtain ⟨ca, ia, za, hca, hia, hza, rfl⟩ := decomp h hφ a
  obtain ⟨cb, ib, zb, hcb, hib, hzb, rfl⟩ := decomp h hφ b
  have hia' : φ ia * ia ∈ Subgroup.center X := by rw [hia]; exact Subgroup.one_mem _
  have hib' : φ ib * ib ∈ Subgroup.center X := by rw [hib]; exact Subgroup.one_mem _
  have e1 : ⁅ca, cb⁆ = 1 :=
    comm_eq_one_of_comm h hi₁Z (comm_eq_one_of_inv_fix h hZ hi₁c hca)
      (comm_eq_one_of_inv_fix h hZ hi₁c hcb)
  have e2 : ⁅ia, ib⁆ = 1 :=
    comm_eq_one_of_comm h hc₀Z (comm_eq_one_of_fix_inv h hZ hc₀ hia')
      (comm_eq_one_of_fix_inv h hZ hc₀ hib')
  rw [commutatorElement_mul_center_left _ hza, commutatorElement_mul_center_right _ hzb,
    comm_mul_left h, comm_mul_right h, comm_mul_right h,
    comm_eq_one_of_fix_inv h hZ hca hib', comm_eq_one_of_inv_fix h hZ hia' hcb, e1, e2]
  group

omit h in
theorem exists_pow_lt_three_of_zpow {Y : Type*} [Group Y] {g : Y} (hg : g ^ 3 = 1) (n : ℤ) :
    ∃ k : ℕ, k < 3 ∧ g ^ n = g ^ k := by
  refine ⟨(n % 3).toNat, by omega, ?_⟩
  have h0 : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
  have hg' : g ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hg]
  have e : g ^ n = g ^ (3 * (n / 3) + ((n % 3).toNat : ℤ)) := by
    congr 1
    rw [Int.toNat_of_nonneg h0]
    omega
  rw [e, zpow_add, zpow_mul, hg', one_zpow, one_mul, zpow_natCast]

omit h in
theorem zpow_emod_three {Y : Type*} [Group Y] {g : Y} (hg : g ^ 3 = 1) (m : ℤ) :
    g ^ m = g ^ (m % 3) := by
  have hg' : g ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hg]
  have e : g ^ m = g ^ (3 * (m / 3) + m % 3) := by
    congr 1
    omega
  rw [e, zpow_add, zpow_mul, hg', one_zpow, one_mul]

theorem eq_one_of_trivial {ψ : MulAut X} (hZ : ∀ z ∈ Subgroup.center X, ψ z = z)
    (htriv : ∀ x, ψ x * x⁻¹ ∈ Subgroup.center X) {m : ℕ} (hpow : ψ ^ (2 ^ m) = 1) : ψ = 1 := by
  ext x
  rw [MulAut.one_apply]
  set w := ψ x * x⁻¹ with hw
  have hwZ : w ∈ Subgroup.center X := htriv x
  have hψx : ψ x = w * x := by rw [hw]; group
  have key : ∀ n : ℕ, (ψ ^ n) x = w ^ n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hZ w hwZ, hψx, pow_succ]
      group
  have h1 := key (2 ^ m)
  rw [hpow, MulAut.one_apply] at h1
  have h2 : w ^ (2 ^ m) = 1 := by
    have e := congrArg (· * x⁻¹) h1
    simp only [mul_inv_cancel, mul_inv_cancel_right] at e
    exact e.symm
  have h3 : w ^ 3 = 1 := pow_three_eq h w
  have hord : orderOf w ∣ Nat.gcd (2 ^ m) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  have hgcd : Nat.gcd (2 ^ m) 3 = 1 := Nat.Coprime.pow_left m (by norm_num)
  rw [hgcd, Nat.dvd_one, orderOf_eq_one_iff] at hord
  rw [hψx, hord, one_mul]

omit h in
theorem mk_inv_of_inverts {φ : MulAut X} {y : X} (hy : φ y * y ∈ Subgroup.center X) :
    ((φ y : X) : X ⧸ Subgroup.center X) = ((y : X) : X ⧸ Subgroup.center X)⁻¹ := by
  have e := mk_eq_one hy
  rw [QuotientGroup.mk_mul] at e
  exact eq_inv_of_mul_eq_one_left e

theorem eq_of_involutions {φ₁ φ₂ : MulAut X} (h₁ : φ₁ * φ₁ = 1) (h₂ : φ₂ * φ₂ = 1)
    (hZ₁ : ∀ z ∈ Subgroup.center X, φ₁ z = z) (hZ₂ : ∀ z ∈ Subgroup.center X, φ₂ z = z)
    (hne₁ : φ₁ ≠ 1) (hne₂ : φ₂ ≠ 1) {m : ℕ} (hpow : (φ₁ * φ₂) ^ (2 ^ m) = 1) : φ₁ = φ₂ := by
  have hψ : φ₁ * φ₂ = 1 := by
    refine eq_one_of_trivial h (fun z hz => ?_) (fun x => ?_) hpow
    · rw [MulAut.mul_apply, hZ₂ z hz, hZ₁ z hz]
    · rw [mem_center_iff_mk, QuotientGroup.mk_mul, MulAut.mul_apply,
        mk_inv_of_inverts (inverts_of_involution h h₁ hZ₁ hne₁ (φ₂ x)),
        mk_inv_of_inverts (inverts_of_involution h h₂ hZ₂ hne₂ x), QuotientGroup.mk_inv]
      group
  calc φ₁ = φ₁ * (φ₂ * φ₂) := by rw [h₂, mul_one]
    _ = (φ₁ * φ₂) * φ₂ := by rw [mul_assoc]
    _ = φ₂ := by rw [hψ, one_mul]

theorem card_of_between {W : Subgroup X} (hZW : Subgroup.center X ≤ W)
    (hWZ : W ≠ Subgroup.center X) (hWt : W ≠ ⊤) : Nat.card W = 9 := by
  have := finite h
  have h1 := Subgroup.card_lt_of_lt (lt_of_le_of_ne hZW (Ne.symm hWZ))
  have h2 := Subgroup.card_lt_of_lt (lt_of_le_of_ne le_top hWt)
  rw [card_center h] at h1
  rw [Subgroup.card_top, card_eq h] at h2
  have h3 : Nat.card W ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← card_eq h]
    exact Subgroup.card_subgroup_dvd_card W
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h3
  rw [hk'] at h1 h2 ⊢
  interval_cases k
  · norm_num at h1
  · norm_num at h1
  · norm_num
  · norm_num at h2

omit h in
theorem exists_not_mem_of_ne {W : Subgroup X} (hZW : Subgroup.center X ≤ W)
    (hWZ : W ≠ Subgroup.center X) : ∃ w ∈ W, w ∉ Subgroup.center X := by
  by_contra hno
  push Not at hno
  exact hWZ (le_antisymm hno hZW)

theorem not_invariant_of_order_four {ψ : MulAut X} (hZ : ∀ z ∈ Subgroup.center X, ψ z = z)
    (h4 : ψ ^ 4 = 1) (h2 : ψ ^ 2 ≠ 1) {W : Subgroup X} (hZW : Subgroup.center X ≤ W)
    (hWZ : W ≠ Subgroup.center X) (hWt : W ≠ ⊤) (hψW : ∀ w ∈ W, ψ w ∈ W) : False := by
  have hcard := card_of_between h hZW hWZ hWt
  obtain ⟨w, hwW, hwZ⟩ := exists_not_mem_of_ne hZW hWZ
  have hr : ψ ^ 2 * ψ ^ 2 = 1 := by rw [← pow_add]; exact h4
  have hrZ : ∀ z ∈ Subgroup.center X, (ψ ^ 2) z = z := by
    intro z hz
    rw [sq, MulAut.mul_apply, hZ z hz, hZ z hz]
  have hinv := inverts_of_involution h hr hrZ h2 w
  obtain ⟨n, hn⟩ := exists_zpow_of_card_nine h hZW hcard hwW hwZ (hψW w hwW)
  set z := (w ^ n)⁻¹ * ψ w with hz
  have hψw : ψ w = w ^ n * z := by rw [hz]; group
  have hψ2w : (ψ ^ 2) w = (w ^ n * z) ^ n * z := by
    rw [sq, MulAut.mul_apply, hψw, map_mul, map_zpow, hψw, hZ z hn]
  rw [hψ2w, mem_center_iff_mk] at hinv
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, mk_eq_one hn, mul_one] at hinv
  have h3 : ((w : X) : X ⧸ Subgroup.center X) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, pow_three_eq h, QuotientGroup.mk_one]
  have e : (((w : X) : X ⧸ Subgroup.center X) ^ n) ^ n * ((w : X) : X ⧸ Subgroup.center X) =
      ((w : X) : X ⧸ Subgroup.center X) ^ (n * n + 1) := by
    rw [← zpow_mul, zpow_add_one]
  rw [e, zpow_emod_three h3] at hinv
  have hmod : (n * n + 1) % 3 = 1 ∨ (n * n + 1) % 3 = 2 := by
    have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with h0 | h0 | h0 <;> simp [Int.add_emod, Int.mul_emod, h0]
  apply hwZ
  rcases hmod with hm | hm
  · rw [hm, zpow_one] at hinv
    exact mem_center_iff_mk.mpr hinv
  · refine mem_center_of_sq h ?_
    rw [hm, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast] at hinv
    rw [mem_center_iff_mk, QuotientGroup.mk_pow]
    exact hinv

end Aut

section Irred

variable (h : IsPOnePlusTwo 3 X)
include h

theorem exists_center_ne_one : ∃ z₀ ∈ Subgroup.center X, z₀ ≠ 1 := by
  by_contra hno
  push Not at hno
  have hb : Subgroup.center X = ⊥ := eq_bot_iff.mpr fun z hz => Subgroup.mem_bot.mpr (hno z hz)
  have h1 := card_center h
  rw [hb, Subgroup.card_bot] at h1
  norm_num at h1

theorem center_eq_zpowers {z₀ : X} (hz₀ : z₀ ∈ Subgroup.center X) (hne : z₀ ≠ 1) :
    Subgroup.zpowers z₀ = Subgroup.center X := by
  have := finite h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf z₀ = 3 := orderOf_eq_prime (pow_three_eq h z₀) hne
  refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hz₀) ?_
  rw [Nat.card_zpowers, hord, card_center h]

theorem fix_or_inv_center (φ : MulAut X) :
    (∀ z ∈ Subgroup.center X, φ z = z) ∨ (∀ z ∈ Subgroup.center X, φ z = z⁻¹) := by
  obtain ⟨z₀, hz₀, hne⟩ := exists_center_ne_one h
  have hZ := center_eq_zpowers h hz₀ hne
  have h1 : φ z₀ ∈ Subgroup.zpowers z₀ := hZ ▸ map_mem_center φ hz₀
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h1
  have h3 : z₀ ^ 3 = 1 := pow_three_eq h z₀
  rw [zpow_emod_three h3] at hj
  have hm : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hm with hm | hm | hm
  · exfalso
    rw [hm, zpow_zero] at hj
    exact hne (φ.injective (by rw [← hj, map_one]))
  · left
    intro z hz
    rw [← hZ] at hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [map_zpow, ← hj, hm, zpow_one]
  · right
    intro z hz
    rw [← hZ] at hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have e : z₀ ^ (2 : ℤ) = z₀⁻¹ := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
      calc z₀ ^ 2 = z₀ ^ 3 * z₀⁻¹ := by group
        _ = z₀⁻¹ := by rw [h3, one_mul]
    rw [map_zpow, ← hj, hm, e, inv_zpow]

omit h in
@[expose] def fixMod (φ : MulAut X) : Subgroup X where
  carrier := {x | φ x * x⁻¹ ∈ Subgroup.center X}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [mem_center_iff_mk] at hx hy ⊢
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, mul_inv_rev] at hx hy ⊢
    rw [mul_inv_eq_one.mp hx, mul_inv_eq_one.mp hy]
    group
  one_mem' := by simp
  inv_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [mem_center_iff_mk] at hx ⊢
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_inv, inv_inv] at hx ⊢
    rw [mul_inv_eq_one.mp hx]
    group

omit h in
theorem mem_fixMod {φ : MulAut X} {x : X} : x ∈ fixMod φ ↔ φ x * x⁻¹ ∈ Subgroup.center X :=
  Iff.rfl

omit h in
theorem center_le_fixMod (φ : MulAut X) : Subgroup.center X ≤ fixMod φ := fun _ hz =>
  Subgroup.mul_mem _ (map_mem_center φ hz) (Subgroup.inv_mem _ hz)

omit h in
theorem map_mem_fixMod {φ : MulAut X} {x : X} (hx : x ∈ fixMod φ) : φ x ∈ fixMod φ := by
  rw [mem_fixMod] at hx ⊢
  have e : φ (φ x) * (φ x)⁻¹ = φ (φ x * x⁻¹) := by rw [map_mul, map_inv]
  rw [e]
  exact map_mem_center φ hx

omit h in
theorem map_mem_of_inverts {φ : MulAut X} (hφ : ∀ x, φ x * x ∈ Subgroup.center X)
    {W : Subgroup X} (hZW : Subgroup.center X ≤ W) {w : X} (hw : w ∈ W) : φ w ∈ W := by
  have e : φ w = (φ w * w) * w⁻¹ := by group
  rw [e]
  exact W.mul_mem (hZW (hφ w)) (W.inv_mem hw)

theorem false_of_comm_fix {φ : MulAut X} (hinv : ∀ z ∈ Subgroup.center X, φ z = z⁻¹)
    (hfix : ∀ a b : X, φ ⁅a, b⁆ = ⁅a, b⁆) : False := by
  obtain ⟨a, b, hab⟩ := exists_comm_ne_one h
  apply hab
  have e := hfix a b
  rw [hinv _ (comm_mem_center h a b)] at e
  exact eq_one_of_eq_inv h e.symm

theorem fixMod_ne_of_involution {φ : MulAut X} (hφ : φ * φ = 1)
    (hinv : ∀ z ∈ Subgroup.center X, φ z = z⁻¹) :
    fixMod φ ≠ Subgroup.center X ∧ fixMod φ ≠ ⊤ := by
  constructor
  · intro hC
    refine false_of_comm_fix h hinv fun a b => ?_
    have hφinv : ∀ x, φ x * x ∈ Subgroup.center X := by
      intro x
      obtain ⟨c, i, z, hc, hi, hz, rfl⟩ := decomp h hφ x
      have hcZ : c ∈ Subgroup.center X := hC ▸ (mem_fixMod.mpr hc)
      rw [mem_center_iff_mk, map_mul, map_mul]
      simp only [QuotientGroup.mk_mul]
      rw [mk_eq_one (map_mem_center φ hcZ), mk_eq_one hcZ, mk_eq_one hz,
        mk_eq_one (map_mem_center φ hz)]
      simp only [one_mul, mul_one]
      rw [← QuotientGroup.mk_mul, hi, QuotientGroup.mk_one]
    have ea : φ a = (φ a * a) * a⁻¹ := by group
    have eb : φ b = (φ b * b) * b⁻¹ := by group
    rw [map_commutatorElement, ea, eb, comm_center_left h _ (hφinv a),
      comm_center_right h _ (hφinv b), comm_inv_left h, comm_inv_right h, inv_inv]
  · intro hC
    refine false_of_comm_fix h hinv fun a b => ?_
    have ha : φ a * a⁻¹ ∈ Subgroup.center X := mem_fixMod.mp (hC ▸ Subgroup.mem_top a)
    have hb : φ b * b⁻¹ ∈ Subgroup.center X := mem_fixMod.mp (hC ▸ Subgroup.mem_top b)
    have ea : φ a = (φ a * a⁻¹) * a := by group
    have eb : φ b = (φ b * b⁻¹) * b := by group
    rw [map_commutatorElement, ea, eb, comm_center_left h _ ha, comm_center_right h _ hb]

theorem comm_apply_eq_one {t : MulAut X} (hinv : ∀ z ∈ Subgroup.center X, t z = z⁻¹)
    (hr : ∀ x, (t * t) x * x ∈ Subgroup.center X) (a : X) : ⁅a, t a⁆ = 1 := by
  have e1 : t ⁅a, t a⁆ = ⁅a, t a⁆⁻¹ := hinv _ (comm_mem_center h a (t a))
  have hra : t (t a) = ((t * t) a * a) * a⁻¹ := by rw [MulAut.mul_apply]; group
  rw [map_commutatorElement, hra, comm_center_right h _ (hr a), comm_inv_right h,
    commutatorElement_inv] at e1
  exact eq_one_of_eq_inv h e1

theorem map_mem_centralizer {t : MulAut X} {a : X} (ha : a ∉ Subgroup.center X)
    (hta : ⁅a, t a⁆ = 1) {w : X} (hw : w ∈ Subgroup.centralizer ({a} : Set X)) :
    t w ∈ Subgroup.centralizer ({a} : Set X) := by
  have hwa : ⁅a, w⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hw a rfl)
  have h1 : ⁅t a, t w⁆ = 1 := by rw [← map_commutatorElement, hwa, map_one]
  have h2 : ⁅t a, a⁆ = 1 := by rw [← commutatorElement_inv, hta, inv_one]
  have hta' : t a ∉ Subgroup.center X := fun hc => ha (by
    have := symm_mem_center t hc
    rwa [MulEquiv.symm_apply_apply] at this)
  have h3 := comm_eq_one_of_comm h hta' h2 h1
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  rw [Set.mem_singleton_iff.mp hy]
  exact commutatorElement_eq_one_iff_mul_comm.mp h3

theorem exists_order_four {𝒯 : Subgroup (MulAut X)} (h𝒯 : IsPGroup 2 𝒯)
    (hirr : ∀ W : Subgroup X, Subgroup.center X ≤ W → (∀ t ∈ 𝒯, ∀ w ∈ W, t w ∈ W) →
      W = Subgroup.center X ∨ W = ⊤)
    (hnot : ∃ t ∈ 𝒯, ¬ ∀ z ∈ Subgroup.center X, t z = z) :
    ∃ y ∈ 𝒯, (∀ z ∈ Subgroup.center X, y z = z) ∧ y ^ 2 ≠ 1 ∧ y ^ 4 = 1 := by
  classical
  obtain ⟨t₀, ht₀, hnt₀⟩ := hnot
  have ht₀inv : ∀ z ∈ Subgroup.center X, t₀ z = z⁻¹ := (fix_or_inv_center h t₀).resolve_left hnt₀
  have h2pow : ∀ s ∈ 𝒯, ∃ m : ℕ, s ^ (2 ^ m) = 1 := fun s hs => by
    obtain ⟨m, hm⟩ := h𝒯 ⟨s, hs⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  have key : ∃ y ∈ 𝒯, (∀ z ∈ Subgroup.center X, y z = z) ∧ y * y ≠ 1 := by
    by_contra hno
    push Not at hno
    have huniq : ∀ y₁ ∈ 𝒯, ∀ y₂ ∈ 𝒯, (∀ z ∈ Subgroup.center X, y₁ z = z) →
        (∀ z ∈ Subgroup.center X, y₂ z = z) → y₁ ≠ 1 → y₂ ≠ 1 → y₁ = y₂ := by
      intro y₁ hy₁ y₂ hy₂ hz₁ hz₂ hne₁ hne₂
      obtain ⟨m, hm⟩ := h2pow (y₁ * y₂) (𝒯.mul_mem hy₁ hy₂)
      exact eq_of_involutions h (hno y₁ hy₁ hz₁) (hno y₂ hy₂ hz₂) hz₁ hz₂ hne₁ hne₂ hm
    have hfixW : ∀ s ∈ 𝒯, (∀ z ∈ Subgroup.center X, s z = z) → ∀ W : Subgroup X,
        Subgroup.center X ≤ W → ∀ w ∈ W, s w ∈ W := by
      intro s hs hsZ W hZW w hw
      by_cases hs1 : s = 1
      · rw [hs1, MulAut.one_apply]; exact hw
      · exact map_mem_of_inverts (inverts_of_involution h (hno s hs hsZ) hsZ hs1) hZW hw
    have hdecomp : ∀ s ∈ 𝒯, (∀ z ∈ Subgroup.center X, s z = z) ∨
        (∃ ρ ∈ 𝒯, (∀ z ∈ Subgroup.center X, ρ z = z) ∧ s = ρ * t₀) := by
      intro s hs
      rcases fix_or_inv_center h s with hsZ | hsZ
      · exact Or.inl hsZ
      · refine Or.inr ⟨s * t₀⁻¹, 𝒯.mul_mem hs (𝒯.inv_mem ht₀), fun z hz => ?_, by group⟩
        have hz' : t₀⁻¹ z = z⁻¹ := by
          have e := ht₀inv (z⁻¹) (Subgroup.inv_mem _ hz)
          rw [inv_inv] at e
          calc t₀⁻¹ z = t₀⁻¹ (t₀ z⁻¹) := by rw [e]
            _ = z⁻¹ := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
        rw [MulAut.mul_apply, hz', hsZ _ (Subgroup.inv_mem _ hz), inv_inv]
    have hinvW : ∀ W : Subgroup X, Subgroup.center X ≤ W → (∀ w ∈ W, t₀ w ∈ W) →
        ∀ s ∈ 𝒯, ∀ w ∈ W, s w ∈ W := by
      intro W hZW ht₀W s hs w hw
      rcases hdecomp s hs with hsZ | ⟨ρ, hρ, hρZ, rfl⟩
      · exact hfixW s hs hsZ W hZW w hw
      · rw [MulAut.mul_apply]
        exact hfixW ρ hρ hρZ W hZW _ (ht₀W w hw)
    by_cases ht₀2 : t₀ * t₀ = 1
    ·
      obtain ⟨hne1, hne2⟩ := fixMod_ne_of_involution h ht₀2 ht₀inv
      rcases hirr (fixMod t₀) (center_le_fixMod t₀)
        (hinvW _ (center_le_fixMod t₀) fun w hw => map_mem_fixMod hw) with he | he
      · exact hne1 he
      · exact hne2 he
    ·
      have hrZ : ∀ z ∈ Subgroup.center X, (t₀ * t₀) z = z := by
        intro z hz
        rw [MulAut.mul_apply, ht₀inv z hz, ht₀inv _ (Subgroup.inv_mem _ hz), inv_inv]
      have hr := inverts_of_involution h (hno _ (𝒯.mul_mem ht₀ ht₀) hrZ) hrZ ht₀2
      obtain ⟨a, ha⟩ : ∃ a : X, a ∉ Subgroup.center X := by
        by_contra hno'
        push Not at hno'
        exact center_ne_top h (eq_top_iff.mpr fun x _ => hno' x)
      have hta := comm_apply_eq_one h ht₀inv hr a
      set W := Subgroup.centralizer ({a} : Set X) with hW
      have hZW : Subgroup.center X ≤ W := fun z hz =>
        Subgroup.mem_centralizer_iff.mpr fun y hy => by
          rw [Set.mem_singleton_iff.mp hy]
          exact Subgroup.mem_center_iff.mp hz a
      have haW : a ∈ W := Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff.mp hy]
      rcases hirr W hZW (hinvW W hZW fun w hw => map_mem_centralizer h ha hta hw) with he | he
      · exact ha (he ▸ haW)
      · apply ha
        refine Subgroup.mem_center_iff.mpr fun y => ?_
        have hyW : y ∈ W := by rw [he]; exact Subgroup.mem_top y
        exact (Subgroup.mem_centralizer_iff.mp hyW a rfl).symm
  obtain ⟨y, hy, hyZ, hy2⟩ := key
  obtain ⟨m, hm⟩ := h2pow y hy
  have hex : ∃ n : ℕ, y ^ (2 ^ n) = 1 := ⟨m, hm⟩
  set n := Nat.find hex with hn
  have hn1 : y ^ (2 ^ n) = 1 := Nat.find_spec hex
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    interval_cases hnv : n
    · apply hy2
      rw [pow_zero, pow_one] at hn1
      rw [hn1, mul_one]
    · apply hy2
      rw [pow_one, sq] at hn1
      exact hn1
  have hmin : ¬ y ^ (2 ^ (n - 1)) = 1 := Nat.find_min hex (by omega)
  refine ⟨y ^ (2 ^ (n - 2)), 𝒯.pow_mem hy _, fun z hz => ?_, ?_, ?_⟩
  · have key2 : ∀ k : ℕ, (y ^ k) z = z := by
      intro k
      induction k with
      | zero => rw [pow_zero, MulAut.one_apply]
      | succ k ih => rw [pow_succ, MulAut.mul_apply, hyZ z hz, ih]
    exact key2 _
  · rw [← pow_mul, show 2 ^ (n - 2) * 2 = 2 ^ (n - 1) by
      rw [← pow_succ]; congr 1; omega]
    exact hmin
  · rw [← pow_mul, show 2 ^ (n - 2) * 4 = 2 ^ n by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega]
    exact hn1

end Irred

end CFSG.Quasithin.H13.L32A.Heis
